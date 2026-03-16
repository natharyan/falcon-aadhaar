use core::alloc;

use nova_aadhaar_qr::util::{alloc_constant, conditionally_select, less_than, num_to_bits, alloc_num_equals_constant};
use bellpepper_core::{ConstraintSystem, LinearCombination, SynthesisError, boolean::Boolean, num::AllocatedNum};
use bellpepper::gadgets::Assignment;
use blstrs::Scalar;
use falcon_rust::{MODULUS, N, LOG_N, Polynomial, PublicKey};
use ff::PrimeFieldBits;

pub(crate) fn var_shift_left<CS, Scalar>(cs: &mut CS, input: &Vec<AllocatedNum<Scalar>>, shift: &AllocatedNum<Scalar>, n: usize, nbits: usize) -> Result<Vec<AllocatedNum<Scalar>>, SynthesisError> 
where
    Scalar: PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    assert_eq!(input.len(), n);

    let mut output: Vec<AllocatedNum<Scalar>> = input.clone();
    let shift_bits = num_to_bits(cs.namespace(|| "num_to_bits var_shift_left"), &shift, nbits)?;

    for j in 0..nbits {
        let mut next = Vec::with_capacity(n);
        for i in 0..n {
            let off = (i + (1 << j)) % n;
            let val = conditionally_select(cs.namespace(|| format!("conditionally_select var_shift_left_{}_{}",j,i)), &output[off], &output[i], &shift_bits[j])?;
            next.push(val);
        }
        output = next;
    }
    Ok(output)
}

pub(crate) fn var_subarray_from_zero_index<CS, Scalar>(cs: &mut CS, input: &Vec<AllocatedNum<Scalar>>, end: &AllocatedNum<Scalar>, n: usize, nbits: usize) -> Result<Vec<AllocatedNum<Scalar>>, SynthesisError>
where
    Scalar: PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    assert_eq!(input.len(), n);
    
    let mut output: Vec<AllocatedNum<Scalar>> = Vec::with_capacity(n);
    let zero = alloc_constant(cs.namespace(|| "alloc_constant var_subarray_from_zero_index"), Scalar::from(0u64))?;
    for i in 0..n {
        let i_const = alloc_constant(
            cs.namespace(|| format!("const_i_{i}")),
            Scalar::from(i as u64),
        )?;
        let lt = less_than(cs.namespace(|| format!("less_than_var_subarray_from_zero_index_{}", i)), &i_const, &end, nbits)?;
        output.push(conditionally_select(cs.namespace(|| format!("conditionally_select var_subarray_from_zero_index_{}",i)), &input[i], &zero, &lt)?);
    }
    Ok(output)
}

// 5,145 constraints without var_subarray_from_zero_index for n = 512
/// left shift input by offset end - start
pub(crate) fn var_subarray<CS, Scalar>(cs: &mut CS, input: Vec<AllocatedNum<Scalar>>, start: AllocatedNum<Scalar>, end: AllocatedNum<Scalar>, n: usize, nbits: usize) -> Result<Vec<AllocatedNum<Scalar>>, SynthesisError>
where
    Scalar: PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{

    // enforce start < end
    let lt = less_than(cs.namespace(|| "less_than var_subarray"), &start, &end, nbits)?;
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

// 18,836 constraints for input.len() == 512
/// output[i] = next subarray element if bit_array[i] == 1, 0 otherwise.
/// prefix[i] = number of 1s before index i
/// eg. bit_array = [1,0,1,0,1,1,1] then prefix = [0,1,1,2,2,3,4]
pub fn pad_vec_from_bit_array<CS, Scalar>(cs: &mut CS, input: Vec<AllocatedNum<Scalar>>, bit_array: Vec<Boolean>) -> Result<Vec<AllocatedNum<Scalar>>, SynthesisError>
where
    Scalar: PrimeFieldBits,
    CS: ConstraintSystem<Scalar>
{
    assert_eq!(bit_array.len(), 68);

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
            |lc| lc + prefix[i - 1].get_variable() 
                                            + &bit_array[i - 1].lc(CS::one(), Scalar::ONE),
        );

        prefix.push(next);
    }

    let mut output: Vec<AllocatedNum<Scalar>> = Vec::with_capacity(68);
    for i in 0..68 {
        let mut selected_lc = LinearCombination::<Scalar>::zero();
        let mut terms: Vec<AllocatedNum<Scalar>> = Vec::with_capacity(68);

        for j in 0..68 {
            // true if j == prefix[i]
            let eq = alloc_num_equals_constant(
                cs.namespace(|| format!("eq_{i}_{j}")),
                &prefix[i],
                Scalar::from(j as u64),
            )?;
            // term = input[j] if eq == true else 0
            let term = AllocatedNum::alloc(cs.namespace(|| format!("term_{i}_{j}")), || {
                if eq.get_value().unwrap_or(false) {
                    Ok(*input[j].get_value().get()?)
                } else {
                    Ok(Scalar::ZERO)
                }
            })?;

            cs.enforce(
                || format!("term constraint {i}_{j}"),
                |lc| lc + input[j].get_variable(),
                |_| eq.lc(CS::one(), Scalar::ONE),
                |lc| lc + term.get_variable(),
            );

            selected_lc = selected_lc + term.get_variable();
            terms.push(term);
        }

        // selected = sum_k term_k
        let selected = AllocatedNum::alloc(cs.namespace(|| format!("selected_{i}")), || {
            let mut acc = Scalar::ZERO;
            for t in &terms {
                acc += t.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            }
            Ok(acc)
        })?;

        cs.enforce(
            || format!("enforce selected sum {i}"),
            |lc| lc + CS::one(),
            |_| selected_lc,
            |lc| lc + selected.get_variable(),
        );

        // mask with bit_array
        // out_i = input[prefix[i]]*bit_array[i]
        let zero_const = alloc_constant(cs.namespace(|| format!("zero_out_{i}")),Scalar::ZERO)?;
        let out = conditionally_select(
            cs.namespace(|| format!("mask_output_{i}")),
            &selected,
            &zero_const,
            &bit_array[i],
        )?;

        output.push(out);

    }

    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use blstrs::Scalar as Fr;
    use rand::{rngs::StdRng, RngExt, SeedableRng};
    use ff::Field;

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

        let expected: Vec<_> = (0..n)
            .map(|i| input_vals[(i + 3) % n])
            .collect();

        let out_vals = get_vals(&out);

        assert_eq!(expected, out_vals);

        println!("number of constrainst for var_shift_left by 3: {}", cs.num_constraints());

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_var_subarray_from_zero_index_and_zero_tail() {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let n = N;
        let nbits = LOG_N;

        let input = alloc_input(&mut cs, n);

        let end = alloc_scalar(&mut cs, "end", 4);

        let out =
            var_subarray_from_zero_index(&mut cs, &input, &end, n, nbits).unwrap();

        let input_vals = get_vals(&input);

        let mut expected = vec![Fr::ZERO; n];
        for i in 0..4 {
            expected[i] = input_vals[i];
        }

        let out_vals = get_vals(&out);

        assert_eq!(expected, out_vals);

        println!("number constraints for var_subarray_from_zero_index by 4: {}", cs.num_constraints());

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

        println!("number of constraints for var_subarray: {}", cs.num_constraints());

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
    fn test_pad_vec_from_bit_array() {
        let mut cs = TestConstraintSystem::<Fr>::new();
        let mut rng = StdRng::seed_from_u64(999);

        let input_vars = alloc_input(&mut cs, 68);
        let input_vals = get_vals(&input_vars);

        let mut bit_vals = Vec::with_capacity(68);
        let mut bit_vars = Vec::with_capacity(68);

        for _ in 0..68 {
            let b: bool = rng.random::<bool>();
            bit_vals.push(b);
            bit_vars.push(Boolean::constant(b));
        }

        let output = pad_vec_from_bit_array(
            &mut cs.namespace(|| "pad_vec"),
            input_vars.clone(),
            bit_vars.clone(),
        )
        .unwrap();

        let mut expected = vec![Fr::ZERO; 68];
        let mut ptr = 0usize;

        for i in 0..68 {
            if bit_vals[i] {
                expected[i] = input_vals[ptr];
                ptr += 1;
            } else {
                expected[i] = Fr::ZERO;
            }
        }

        for i in 0..68 {
            assert_eq!(output[i].get_value().unwrap(), expected[i], "Mismatch at index {i}");
        }

        println!("number of constraints for pad_vec_bit_array: {}", cs.num_constraints());

        assert!(cs.is_satisfied());

    }
}