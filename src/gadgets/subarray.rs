use std::alloc::alloc;

use crate::utils::{
    alloc_constant, alloc_num_equals_constant, boolean_implies, conditionally_select, less_than,
    normalize_half_q, num_to_bits, shake_sample_u16,
};
use crate::utils::{select_from_vec_linear, select_from_vector_512};
use bellpepper::gadgets::Assignment;
use bellpepper_core::{
    boolean::Boolean, num::AllocatedNum, ConstraintSystem, LinearCombination, SynthesisError,
};
use blstrs::Scalar;
use falcon_rust::{Polynomial, PublicKey, LOG_N, MODULUS, MODULUS_THRESHOLD, N};
use ff::PrimeFieldBits;

/// 5,131 constraints, independent of shift value
/// Shift left by shift % n, 0 <= shift <= 2*n - 1
pub(crate) fn var_shift_left<CS, Scalar>(
    mut cs: CS,
    input: &Vec<AllocatedNum<Scalar>>,
    shift: &AllocatedNum<Scalar>,
    n: usize,
    nbits: usize,
) -> Result<Vec<AllocatedNum<Scalar>>, SynthesisError>
where
    Scalar: PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    assert_eq!(input.len(), n);

    // if shift > n then use shift as shift % n, but we can just enforce shift < n since we have n bits to represent shift
    let var_n = alloc_constant(
        cs.namespace(|| "alloc_constant n for shift_minus_n"),
        Scalar::from(n as u64),
    )?;
    let shift_lt_n = less_than(cs.namespace(|| "less_than shift n"), shift, &var_n, nbits)?;
    let shift_minus_n = AllocatedNum::alloc(cs.namespace(|| "alloc shift minus n"), || {
        let mut v = shift.get_value().ok_or(SynthesisError::AssignmentMissing)?;
        v.sub_assign(&Scalar::from(n as u64));
        Ok(v)
    })?;
    cs.enforce(
        || "enforce shift_minus_n = shift - n",
        |lc| lc + shift.get_variable() - var_n.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + shift_minus_n.get_variable(),
    );

    // shift = shift % n
    let shift_res = conditionally_select(
        cs.namespace(|| "conditionally_select shift_res"),
        &shift,
        &shift_minus_n,
        &shift_lt_n,
    )?;

    let mut output: Vec<AllocatedNum<Scalar>> = input.clone();
    let shift_bits = num_to_bits(
        cs.namespace(|| "num_to_bits var_shift_left"),
        &shift_res,
        nbits,
    )?;

    for j in 0..nbits {
        let mut next = Vec::with_capacity(n);
        for i in 0..n {
            let off = (i + (1 << j)) % n;
            let val = conditionally_select(
                cs.namespace(|| format!("conditionally_select var_shift_left_{}_{}", j, i)),
                &output[off],
                &output[i],
                &shift_bits[j],
            )?;
            next.push(val);
        }
        output = next;
    }
    Ok(output)
}

pub(crate) fn var_subarray_from_zero_index<CS, Scalar>(
    cs: &mut CS,
    input: &Vec<AllocatedNum<Scalar>>,
    end: &AllocatedNum<Scalar>,
    n: usize,
    nbits: usize,
) -> Result<Vec<AllocatedNum<Scalar>>, SynthesisError>
where
    Scalar: PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    assert_eq!(input.len(), n);

    let mut output: Vec<AllocatedNum<Scalar>> = Vec::with_capacity(n);
    let zero = alloc_constant(
        cs.namespace(|| "alloc_constant var_subarray_from_zero_index"),
        Scalar::from(0u64),
    )?;
    for i in 0..n {
        let i_const = alloc_constant(
            cs.namespace(|| format!("const_i_{i}")),
            Scalar::from(i as u64),
        )?;
        let lt = less_than(
            cs.namespace(|| format!("less_than_var_subarray_from_zero_index_{}", i)),
            &i_const,
            &end,
            nbits,
        )?;
        output.push(conditionally_select(
            cs.namespace(|| format!("conditionally_select var_subarray_from_zero_index_{}", i)),
            &input[i],
            &zero,
            &lt,
        )?);
    }
    Ok(output)
}

// 5,145 constraints without var_subarray_from_zero_index for n = 512
/// left shift input by offset end - start
pub(crate) fn var_subarray<CS, Scalar>(
    cs: &mut CS,
    input: Vec<AllocatedNum<Scalar>>,
    start: AllocatedNum<Scalar>,
    end: AllocatedNum<Scalar>,
    n: usize,
    nbits: usize,
) -> Result<Vec<AllocatedNum<Scalar>>, SynthesisError>
where
    Scalar: PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    // enforce start < end
    let lt = less_than(
        cs.namespace(|| "less_than var_subarray"),
        &start,
        &end,
        nbits,
    )?;
    Boolean::enforce_equal(
        cs.namespace(|| "enforce_start_lt_end"),
        &lt,
        &Boolean::constant(true),
    )?;

    // shift left "start" times
    let shift_left = var_shift_left(cs, &input, &start, n, nbits)?;

    // len_subarray = end - start
    // let len_subarray = AllocatedNum::alloc(cs.namespace(|| "alloc_len_end_minus_start"), || {
    //     let mut v = end.get_value().ok_or(SynthesisError::AssignmentMissing)?;
    //     let s = start.get_value().ok_or(SynthesisError::AssignmentMissing)?;
    //     v.sub_assign(&s);
    //     Ok(v)
    // })?;

    // cs.enforce(
    //     || "enforce_len_eq_end_minus_start",
    //     |lc| lc + end.get_variable() - start.get_variable(),
    //     |lc| lc + CS::one(),
    //     |lc| lc + len_subarray.get_variable(),
    // );

    // // take first (end - start) indices
    // let subarray_from_zero_index = var_subarray_from_zero_index(cs, &shift_left, &len_subarray, n, nbits)?;

    Ok(shift_left)
}

// Given input as shake256 output create an array of 1 and 0 where 1 is current 16 bits in big endian form < floor(2^{16}/12289)*12289 and 0 otherwise.
pub fn create_bit_array(state: [bool; 1600]) -> [bool; 68] {
    let mut bit_array = [false; 68];
    for k in 0..68 {
        bit_array[k] = shake_sample_u16(&state, 16 * k) < MODULUS_THRESHOLD; // floor(2^{16}/12289)*12289
    }
    bit_array
}

// 18,836 constraints for input.len() == 512
/// prefix[i] = number of 1s before index i
/// output[i] = input[prefix[i]]
/// eg. bit_array = [1,0,1,0,1,1,1] then prefix = [0,1,1,2,2,3,4] and output =
///     [input[0], input[1], input[1], input[2], input[2], input[3], input[4]]
///     (if input = [a,b,c,d,e,f,g] then output = [a,b,b,c,c,d,e])
// pub fn pad_coeff<CS, Scalar>(
//     cs: &mut CS,
//     input: Vec<AllocatedNum<Scalar>>,
//     bit_array: Vec<Boolean>,
// ) -> Result<Vec<AllocatedNum<Scalar>>, SynthesisError>
// where
//     Scalar: PrimeFieldBits,
//     CS: ConstraintSystem<Scalar>,
// {
//     // assert_eq!(input.len(), 68);
//     assert_eq!(bit_array.len(), 68);

//     let mut prefix: Vec<AllocatedNum<Scalar>> = Vec::with_capacity(68);
//     prefix.push(alloc_constant(cs.namespace(|| "prefix0"), Scalar::ZERO)?);
//     for i in 1..68 {
//         let next = AllocatedNum::alloc(cs.namespace(|| format!("prefix_{i}")), || {
//             let prev = *prefix[i - 1].get_value().get()?;

//             let bit = if bit_array[i - 1].get_value().unwrap_or(false) {
//                 Scalar::ONE
//             } else {
//                 Scalar::ZERO
//             };

//             Ok(prev + bit)
//         })?;

//         cs.enforce(
//             || format!("prefix update {i}"),
//             |lc| lc + next.get_variable(),
//             |lc| lc + CS::one(),
//             |lc| lc + prefix[i - 1].get_variable() + &bit_array[i - 1].lc(CS::one(), Scalar::ONE),
//         );

//         prefix.push(next);
//     }

//     let mut output: Vec<AllocatedNum<Scalar>> = Vec::with_capacity(68);
//     for i in 0..68 {
//         let selected = select_from_vec_linear(
//             cs.namespace(|| format!("select_from_vector_512_{i} pad_coeff")),
//             &input,
//             &prefix[i],
//         )?;
//         output.push(selected);
//     }

//     Ok(output)
// }
pub fn pad_coeff<CS, Scalar>(
    mut cs: CS,
    input: Vec<AllocatedNum<Scalar>>,
    bit_array: &[Boolean; 68],
) -> Result<Vec<AllocatedNum<Scalar>>, SynthesisError>
where
    Scalar: PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    assert_eq!(bit_array.len(), 68);
    assert!(input.len() <= 68);

    // pad input up to length 68 with zero entries.
    let mut padded_input = input.clone();
    if padded_input.len() < 68 {
        for i in padded_input.len()..68 {
            padded_input.push(alloc_constant(
                cs.namespace(|| format!("pad_coeff dummy input {i}")),
                Scalar::ZERO,
            )?);
        }
    }

    let mut prefix: Vec<AllocatedNum<Scalar>> = Vec::with_capacity(68);
    prefix.push(alloc_constant(cs.namespace(|| "prefix0"), Scalar::ZERO)?);
    for i in 1..68 {
        let next = AllocatedNum::alloc(cs.namespace(|| format!("prefix_{i}")), || {
            let prev = *prefix[i - 1].get_value().get()?;
            let bit = if bit_array[i - 1].get_value().unwrap_or(false) {
                Scalar::ONE
            } else {
                Scalar::ZERO
            };
            Ok(prev + bit)
        })?;
        cs.enforce(
            || format!("prefix update {i}"),
            |lc| lc + next.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + prefix[i - 1].get_variable() + &bit_array[i - 1].lc(CS::one(), Scalar::ONE),
        );
        prefix.push(next);
    }

    let mut output: Vec<AllocatedNum<Scalar>> = Vec::with_capacity(68);
    for i in 0..68 {
        let selected = select_from_vec_linear(
            cs.namespace(|| format!("select_from_vector_512_{i} pad_coeff")),
            &padded_input,
            &prefix[i],
        )?;
        output.push(selected);
    }
    Ok(output)
}

/// prefix[i] = number of 1s before index i; output[i] = input[prefix[i]].
pub fn pad_vec_from_bit_array(input: Vec<u16>, bit_array: [bool; 68]) -> [u16; 68] {
    assert_eq!(input.len(), 68, "input must have length 68");
    let mut output = [0u16; 68];
    let mut prefix = 0usize;
    for i in 0..68 {
        output[i] = input[prefix];
        if bit_array[i] {
            prefix += 1;
        }
    }
    output
}

// square of first wt(bit_array) coefficients
pub fn l2normsquare_subarray<CS, Scalar>(
    mut cs: CS,
    input: &Vec<AllocatedNum<Scalar>>,
    bit_array: &[Boolean; 68],
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
    Scalar: PrimeFieldBits + PartialOrd,
    CS: ConstraintSystem<Scalar>,
{
    let mut acc: AllocatedNum<Scalar> = alloc_constant(
        cs.namespace(|| "acc l2normsquare_subarray initialise"),
        Scalar::from(0u64),
    )?;

    let var_0 = alloc_constant(
        cs.namespace(|| "l2normsquare_subarray const_0"),
        Scalar::from(0u64),
    )?;
    let var_1 = alloc_constant(
        cs.namespace(|| "l2normsquare_subarray const_1"),
        Scalar::from(1u64),
    )?;

    let mut weight_bit_array =
        alloc_constant(cs.namespace(|| "weight_bit_array init"), Scalar::from(0u64))?;
    for (i, b) in bit_array.iter().enumerate() {
        let bit_val = conditionally_select(
            cs.namespace(|| format!("weight_bit_array select_{i}")),
            &var_1,
            &var_0,
            b,
        )?;
        weight_bit_array = weight_bit_array.add(
            cs.namespace(|| format!("weight_bit_array add_{i}")),
            &bit_val,
        )?;
    }

    let sub = &input[..input.len().min(68)];

    for i in 0..sub.len() {
        let var_i = alloc_constant(
            cs.namespace(|| format!("l2normsquare_subarray const_i_{i}")),
            Scalar::from(i as u64),
        )?;
        let cur_coeff = &sub[i];
        // let cur_coeff_squared =
        //     cur_coeff.square(cs.namespace(|| format!("l2normsquare_subarray square_{i}")))?;
        let cur_coeff_normalized = normalize_half_q(
            &mut cs.namespace(|| format!("l2normsquare_select normalize_{i}")),
            cur_coeff,
        )?;
        let cur_coeff_squared = cur_coeff_normalized.mul(
            cs.namespace(|| format!("l2normsquare_select square_{i}")),
            &cur_coeff_normalized,
        )?;
        let i_less_than_wt = less_than(
            cs.namespace(|| format!("l2normsquare_subarray less_than_{i}")),
            &var_i,
            &weight_bit_array,
            LOG_N,
        )?;
        let operand = conditionally_select(
            cs.namespace(|| format!("l2normsquare_subarray select_{i}")),
            &cur_coeff_squared,
            &var_0,
            &i_less_than_wt,
        )?;
        acc = acc.add(
            cs.namespace(|| format!("l2normsquare_subarray add_{i}")),
            &operand,
        )?;
    }

    Ok(acc)
}

// l2 norm of a vector of coefficients which can have non-zero values used for padding at indices indicating rejection sampling using bit_array as a selector
pub fn l2normsquare_select<CS, Scalar>(
    mut cs: CS,
    input: &Vec<AllocatedNum<Scalar>>,
    bit_array: &[Boolean; 68],
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
    Scalar: PrimeFieldBits + PartialOrd,
    CS: ConstraintSystem<Scalar>,
{
    let mut acc = alloc_constant(
        cs.namespace(|| "acc l2normsquare_select initialise"),
        Scalar::from(0u64),
    )?;

    let var_0 = alloc_constant(
        cs.namespace(|| "l2normsquare_select const_0"),
        Scalar::from(0u64),
    )?;

    for i in 0..input.len() {
        let cur_coeff = &input[i];
        // let cur_coeff_squared =
        //     cur_coeff.square(cs.namespace(|| format!("l2normsquare_select square_{i}")))?;
        let cur_coeff_normalized = normalize_half_q(
            &mut cs.namespace(|| format!("l2normsquare_select normalize_{i}")),
            cur_coeff,
        )?;
        let cur_coeff_squared = cur_coeff_normalized.mul(
            cs.namespace(|| format!("l2normsquare_select square_{i}")),
            &cur_coeff_normalized,
        )?;
        let operand = conditionally_select(
            cs.namespace(|| format!("l2normsquare_select select_{i}")),
            &cur_coeff_squared,
            &var_0,
            &bit_array[i],
        )?;
        acc = acc.add(
            cs.namespace(|| format!("l2normsquare_select add_{i}")),
            &operand,
        )?;
    }

    Ok(acc)
}

#[cfg(test)]
mod tests {
    use super::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use blstrs::Scalar as Fr;
    use ff::Field;
    use rand::{rngs::StdRng, RngExt, SeedableRng};

    fn alloc_input(cs: &mut TestConstraintSystem<Fr>, n: usize) -> Vec<AllocatedNum<Fr>> {
        let mut rng = StdRng::seed_from_u64(42);

        (0..n)
            .map(|i| {
                let v = Fr::from(rng.random::<u64>());
                alloc_constant(cs.namespace(|| format!("input_{i}")), v).unwrap()
            })
            .collect()
    }

    fn alloc_scalar(cs: &mut TestConstraintSystem<Fr>, name: &str, v: u64) -> AllocatedNum<Fr> {
        alloc_constant(cs.namespace(|| name), Fr::from(v)).unwrap()
    }

    fn get_vals(v: &[AllocatedNum<Fr>]) -> Vec<Fr> {
        v.iter().map(|x| x.get_value().unwrap()).collect()
    }

    #[test]
    fn test_var_shift_left_zero_is_identity() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let n = N;
        let nbits = LOG_N;

        let input = alloc_input(&mut cs, n);
        let shift = alloc_scalar(&mut cs, "shift", 0);

        let out = var_shift_left(&mut cs, &input, &shift, n, nbits).unwrap();

        let input_vals = get_vals(&input);
        let out_vals = get_vals(&out);

        assert_eq!(input_vals, out_vals);
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_var_shift_left_by_three() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let n = N;
        let nbits = LOG_N;

        let input = alloc_input(&mut cs, n);
        let shift = alloc_scalar(&mut cs, "shift", 3);

        let out = var_shift_left(&mut cs, &input, &shift, n, nbits).unwrap();

        let input_vals = get_vals(&input);

        let expected: Vec<_> = (0..n).map(|i| input_vals[(i + 3) % n]).collect();

        let out_vals = get_vals(&out);

        assert_eq!(expected, out_vals);

        println!(
            "number of constrainst for var_shift_left by 3: {}",
            cs.num_constraints()
        );

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_var_subarray_from_zero_index_and_zero_tail() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let n = N;
        let nbits = LOG_N;

        let input = alloc_input(&mut cs, n);

        let end = alloc_scalar(&mut cs, "end", 4);

        let out = var_subarray_from_zero_index(&mut cs, &input, &end, n, nbits).unwrap();

        let input_vals = get_vals(&input);

        let mut expected = vec![Fr::ZERO; n];
        for i in 0..4 {
            expected[i] = input_vals[i];
        }

        let out_vals = get_vals(&out);

        assert_eq!(expected, out_vals);

        println!(
            "number constraints for var_subarray_from_zero_index by 4: {}",
            cs.num_constraints()
        );

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_var_subarray() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let n = N;
        let nbits = LOG_N;

        let input = alloc_input(&mut cs, n);

        let start_val = 2u64;
        let start = alloc_scalar(&mut cs, "start", start_val);
        let end = alloc_scalar(&mut cs, "end", 5); // only used for start < end constraint

        let out = var_subarray(&mut cs, input.clone(), start, end, n, nbits).unwrap();

        let input_vals = get_vals(&input);
        let expected: Vec<_> = (0..n)
            .map(|i| input_vals[(i + start_val as usize) % n])
            .collect();

        let out_vals = get_vals(&out);
        assert_eq!(expected, out_vals);

        println!(
            "number of constraints for var_subarray: {}",
            cs.num_constraints()
        );

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_var_subarray_randomized() {
        let mut rng = StdRng::seed_from_u64(123);

        for _ in 0..50 {
            let mut cs = TestConstraintSystem::<Fr>::new();

            let n = N;
            let nbits = LOG_N;

            let input = alloc_input(&mut cs, n);

            let start_val: u64 = rng.random_range(0..n as u64);
            let end_val: u64 = rng.random_range(start_val + 1..=n as u64);

            let start = alloc_scalar(&mut cs, "start", start_val);
            let end = alloc_scalar(&mut cs, "end", end_val);

            let out = var_subarray(&mut cs, input.clone(), start, end, n, nbits).unwrap();

            let input_vals = get_vals(&input);
            let expected: Vec<_> = (0..n)
                .map(|i| input_vals[(i + start_val as usize) % n])
                .collect();

            let out_vals = get_vals(&out);
            assert_eq!(expected, out_vals);

            assert!(cs.is_satisfied());
        }
    }

    #[test]
    fn test_pad_coeff() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let mut rng = StdRng::seed_from_u64(999);

        let input_vars = alloc_input(&mut cs, 68);
        let input_vals = get_vals(&input_vars);

        let mut bit_vals = Vec::with_capacity(68);
        let mut bit_vars: Vec<Boolean> = Vec::with_capacity(68);

        for _ in 0..68 {
            let b: bool = rng.random::<bool>();
            bit_vals.push(b);
            bit_vars.push(Boolean::constant(b));
        }

        let before = cs.num_constraints();

        let bit_array: &[Boolean; 68] = bit_vars.as_slice().try_into().unwrap();

        let output = pad_coeff(
            &mut cs.namespace(|| "pad_coeff"),
            input_vars.clone(),
            bit_array,
        )
        .unwrap();

        let after = cs.num_constraints();

        let mut expected = vec![Fr::ZERO; 68];
        let mut prefix = 0usize;
        for i in 0..68 {
            expected[i] = input_vals[prefix];
            if bit_vals[i] {
                prefix += 1;
            }
        }

        for i in 0..68 {
            assert_eq!(
                output[i].get_value().unwrap(),
                expected[i],
                "Mismatch at index {i}"
            );
        }

        println!("number of constraints for pad_coeff: {}", after - before);
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_pad_vec_from_bit_array() {
        let mut rng = StdRng::seed_from_u64(999);
        let input: Vec<u16> = (0..68).map(|_| rng.random::<u16>()).collect();
        let bit_array: [bool; 68] = std::array::from_fn(|_| rng.random::<bool>());

        let output = pad_vec_from_bit_array(input.clone(), bit_array);

        let mut expected = [0u16; 68];
        let mut prefix = 0usize;
        for i in 0..68 {
            expected[i] = input[prefix];
            if bit_array[i] {
                prefix += 1;
            }
        }

        assert_eq!(output, expected);
    }

    #[test]
    fn test_pad_vec_from_bit_array_all_ones() {
        // all bits set: prefix advances every step → output[i] == input[i]
        let input: Vec<u16> = (0..68).map(|i| i as u16).collect();
        let output = pad_vec_from_bit_array(input.clone(), [true; 68]);
        let expected: [u16; 68] = std::array::from_fn(|i| i as u16);
        assert_eq!(output, expected);
    }

    #[test]
    fn test_pad_vec_from_bit_array_all_zeros() {
        // no bits set: prefix never advances → every slot is input[0]
        let input: Vec<u16> = (0..68).map(|i| i as u16 + 100).collect();
        let output = pad_vec_from_bit_array(input.clone(), [false; 68]);
        assert!(output.iter().all(|&v| v == input[0]));
    }

    // fn set_chunk(bits: &mut [bool; 1600], chunk: usize, value: u16) {
    //     for j in 0..16 {
    //         bits[chunk * 16 + (15 - j)] = (value >> j) & 1 == 1;
    //     }
    // }
    fn set_chunk(bits: &mut [bool; 1600], chunk: usize, value: u16) {
        let hi = (value >> 8) as u8;
        let lo = (value & 0xff) as u8;
        for j in 0..8 {
            bits[chunk * 16 + j] = (hi >> j) & 1 == 1;
            bits[chunk * 16 + 8 + j] = (lo >> j) & 1 == 1;
        }
    }

    #[test]
    fn test_bit_array_known_values() {
        // SAMPLING_THREHOLD = floor(2^16 / 12289) * 12289 = 61445.
        // The test is driven by hand-crafted chunk values whose accept/reject
        // outcome is obvious without running bit_array at all.
        let mut input = [false; 1600];

        set_chunk(&mut input, 0, 0); // 0       < 61445 → true
        set_chunk(&mut input, 1, 1); // 1       < 61445 → true
        set_chunk(&mut input, 2, 61444); // 61444   < 61445 → true  (one below threshold)
        set_chunk(&mut input, 3, 61445); // 61445  == 61445 → false (exactly at threshold)
        set_chunk(&mut input, 4, 61446); // 61446   > 61445 → false
        set_chunk(&mut input, 5, 65535); // 0xFFFF  > 61445 → false
                                         // chunks 6..68 remain all-zero → all true

        let output = create_bit_array(input);

        assert_eq!(output[0], true, "0 should be accepted");
        assert_eq!(output[1], true, "1 should be accepted");
        assert_eq!(
            output[2], true,
            "61444 (one below threshold) should be accepted"
        );
        assert_eq!(
            output[3], false,
            "61445 (equal to threshold) should be rejected"
        );
        assert_eq!(output[4], false, "61446 should be rejected");
        assert_eq!(output[5], false, "65535 should be rejected");
        for i in 6..68 {
            assert_eq!(output[i], true, "chunk {i} (value 0) should be accepted");
        }
    }
}

#[test]
fn test_pad_vec_from_bit_array_last_bit_false_reads_final_slot() {
    // with bit_array[67] false, prefix reaches wt == 67 at i == 67, so the final slot
    // reads input[67] that goes out of bounds on a wt-length input
    let mut bit_array = [true; 68];
    bit_array[67] = false;
    let input: Vec<u16> = (0..68).map(|i| i as u16).collect();
    let output = pad_vec_from_bit_array(input, bit_array);
    assert_eq!(output[67], 67);
    for i in 0..67 {
        assert_eq!(output[i], i as u16);
    }
}
