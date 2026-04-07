use std::alloc;

use crate::age_proof::NUM_COEFF_INDEX_BITS;
use crate::hash::shake256::SHAKE256_BLOCK_LENGTH_BYTES;
use bellpepper::gadgets::{multipack::bytes_to_bits,boolean::AllocatedBit,num::Num};
use bellpepper_core::boolean::{Boolean};

use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError, LinearCombination};
use blstrs::Scalar;
use clap::error;
use falcon_rust::{MODULUS, SIG_L2_BOUND, N, Polynomial, PublicKey};
use ff::{PrimeField, PrimeFieldBits};
use keccak::f1600;
use nova_aadhaar_qr::util::{alloc_constant, alloc_num_equals, check_decomposition, conditionally_select, num_to_bits};
use sha3::{
    Shake256,
    digest::{ExtendableOutput, Update, XofReader},
};
use num_bigint::BigUint;
use num_traits::ToPrimitive;

/// Convert bytes to little-endian bits
pub(crate) fn bytes_to_bits_le(bytes: &[u8]) -> Vec<bool> {
    bytes
        .iter()
        .flat_map(|byte| (0..8).map(move |i| (byte >> i) & 1 == 1))
        .collect()
}

/// Convert little-endian bits to bytes
pub(crate) fn bits_to_bytes_le(bits: &[bool]) -> Vec<u8> {
    bits.chunks(8)
        .map(|chunk| {
            chunk
                .iter()
                .enumerate()
                .fold(0u8, |acc, (i, &b)| acc | ((b as u8) << i))
        })
        .collect()
}

// Convert big-endian bits to bytes
pub(crate) fn bits_to_bytes(bits: &[bool]) -> Vec<u8> {
    bits.chunks(8)
        .map(|chunk| {
            chunk
                .iter()
                .enumerate()
                .fold(0u8, |acc, (i, &b)| acc | ((b as u8) << (7 - i)))
        })
        .collect()
}

pub(crate) fn vec_bool_to_arr_u64(input: &[bool]) -> [u64; 25] {
    let mut input_u64: [u64; 25] = [0; 25];
    for (i, chunk) in input.chunks(64).enumerate() {
        let mut word = 0u64;
        for (bit_idx, &bit) in chunk.iter().enumerate() {
            if bit {
                word |= 1u64 << bit_idx; // Little-endian bit order
            }
        }
        input_u64[i] = word;
    }

    input_u64
}

pub(crate) fn arr_u64_to_vec_bool(input: &[u64; 25]) -> [bool; 1600] {
    let vec: Vec<bool> = input
        .iter()
        .flat_map(|word| {
            (0..64).map(move |i| {
                (word >> i) & 1 == 1 // Extract each bit and convert to Boolean
            })
        })
        .collect();
    vec.try_into().expect("Expected exactly 1600 bits")
}

// referenced from https://github.com/zhenfeizhang/falcon.rs/blob/master/falcon-r1cs/src/gadgets/arithmetics.rs#L105
/// Generate the variable b = a mod 12289;
pub(crate) fn mod_q<Scalar, CS>(
    mut cs: CS,
    a: &AllocatedNum<Scalar>
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where 
    Scalar: PrimeField + ff::PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    // we want to prove that `b = a mod 12289`
    // that is
    // (1) a - t * 12289 = b
    // for some unknown t, with
    // (2) b < 12289
    //
    // Note that this implementation assumes the
    // native field's order is greater than 12289^2
    // so we do not have any overflows

    // rebuild the field elements
    let a_val:Scalar = a.get_value().unwrap_or(Scalar::ONE);

    let a_int: BigUint = BigUint::from_bytes_le(a_val.to_repr().as_ref());

    let modulus_int = BigUint::from(MODULUS as u64);
    let t_int = &a_int / &modulus_int;
    let b_int = &a_int % &modulus_int;

    // convert t_val's little-endian byte representation directly to a field element
    let t_val = {
        let t_bytes = t_int.to_bytes_le();
        let mut repr = <Scalar as PrimeField>::Repr::default();
        let repr_bytes = repr.as_mut();
        let copy_len = repr_bytes.len().min(t_bytes.len());
        repr_bytes[..copy_len].copy_from_slice(&t_bytes[..copy_len]);
        let ct_option = Scalar::from_repr(repr);
        let opt: Option<Scalar> = ct_option.into();
        opt.ok_or(SynthesisError::AssignmentMissing)?
    };
    let b_val = Scalar::from(b_int.to_u64().unwrap());

    let t_var = AllocatedNum::alloc(cs.namespace(|| "t"), || Ok(t_val))?;
    let b_var = AllocatedNum::alloc(cs.namespace(|| "b"), || Ok(b_val))?;

    // (1) a - b = t*12289
    cs.enforce(
        || "mod relation",
        |lc| lc + t_var.get_variable(),
        |lc| lc + (Scalar::from(MODULUS as u64), CS::one()),
        |lc| lc + a.get_variable() - b_var.get_variable(),
    );
    
    // (2) b < 12289
    enforce_less_than_q(cs.namespace(|| "enforce_less_than_q mod_q"),&b_var)?;

    Ok(b_var)
}

// referenced from https://github.com/zhenfeizhang/falcon.rs/blob/master/falcon-r1cs/src/gadgets/range_proofs.rs#L42
pub(crate) fn enforce_less_than_q<Scalar, CS>(
    mut cs: CS,
    a: &AllocatedNum<Scalar>,
) -> Result<(), SynthesisError>
where
    Scalar: PrimeField + ff::PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    let a_val = a.get_value().unwrap_or(Scalar::ONE);

    // Extract first 14 bits from witness (little-endian)
    let a_bytes = a_val.to_repr();
    let a_bytes_ref = a_bytes.as_ref();

    let mut a_bits_le = Vec::with_capacity(14);
    for i in 0..14 {
        let byte_idx = i / 8;
        let bit_idx = i % 8;
        let bit = if byte_idx < a_bytes_ref.len() {
            (a_bytes_ref[byte_idx] >> bit_idx) & 1 == 1
        } else {
            false
        };
        a_bits_le.push(bit);
    }

    // Allocate Boolean variables
    let a_bit_vars: Vec<Boolean> = a_bits_le
        .iter()
        .enumerate()
        .map(|(i, &bit)| {
            Ok(Boolean::from(AllocatedBit::alloc(
                cs.namespace(|| format!("bit {}", i)),
                Some(bit),
            )?))
        })
        .collect::<Result<Vec<Boolean>, SynthesisError>>()?;

    // Enforce decomposition: a = sum(2^i * bit_i)
    check_decomposition(
        cs.namespace(|| "enforce_decompose"),
        a,
        a_bit_vars.clone(),
    )?;

    // Compute OR(bits[0..11])
    let mut lower_bits_or = Boolean::Constant(false);
    for (i, bit) in a_bit_vars[0..12].iter().enumerate() {
        lower_bits_or = Boolean::or(
            cs.namespace(|| format!("or bits 0..{}", i)),
            &lower_bits_or,
            bit,
        )?;
    }

    let bits_0_to_11_all_zero = Boolean::not(&lower_bits_or);

    // bit12 == 0 ?
    let bit12_is_zero = Boolean::not(&a_bit_vars[12]);

    // bit13 == 0 ?
    let bit13_is_zero = Boolean::not(&a_bit_vars[13]);

    // bit12_is_zero OR bits_0_to_11_all_zero
    let inner_or = Boolean::or(
        cs.namespace(|| "bit12_zero OR lower_zero"),
        &bit12_is_zero,
        &bits_0_to_11_all_zero,
    )?;

    // bit13_is_zero OR inner_or
    let result = Boolean::or(
        cs.namespace(|| "bit13_zero OR inner"),
        &bit13_is_zero,
        &inner_or,
    )?;

    // Enforce result == true
    Boolean::enforce_equal(
        cs.namespace(|| "enforce less than q"),
        &result,
        &Boolean::Constant(true),
    )?;

    Ok(())
}



// Referenced from https://github.com/zhenfeizhang/falcon.rs/blob/master/falcon-r1cs/src/gadgets/arithmetics.rs#L157
/// Generate the variable c = a * b mod 12289;
/// with a guarantee that the inputs a and b satisfies:
/// * a < 12289
/// * b < 12289
/// Cost: 30 constraints
#[allow(dead_code)]
pub(crate) fn mul_mod<Scalar, CS>(
    mut cs: CS,
    a: &AllocatedNum<Scalar>,
    b: &AllocatedNum<Scalar>,
    modulus_var: &AllocatedNum<Scalar>,
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
    Scalar: PrimeField + ff::PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    // we want to prove that `c = a * b mod 12289`
    // that is
    // (1) a * b - t * 12289 = c
    // for some unknown t, with
    // (2) c < 12289
    //
    // Note that this implementation assumes the
    // native field's order is greater than 12289^2
    // so we do not have any overflows

    // rebuild the field elements
    let a_val:Scalar = a.get_value().unwrap_or(Scalar::ONE);
    let b_val:Scalar = b.get_value().unwrap_or(Scalar::ONE);

    let ab_val = a_val * b_val;
    let ab_int: BigUint = BigUint::from_bytes_le(ab_val.to_repr().as_ref());

    let modulus_int: BigUint = BigUint::from(MODULUS as u64);
    let t_int = &ab_int / &modulus_int;
    let c_int = &ab_int % &modulus_int;

    // cast the variables
    let t_val = Scalar::from(t_int.to_u64().unwrap());
    let c_val = Scalar::from(c_int.to_u64().unwrap());
    
    let t_var = AllocatedNum::alloc(cs.namespace(||"t"), || Ok(t_val))?;
    let c_var = AllocatedNum::alloc(cs.namespace(|| "c"), || Ok(c_val))?;

    // (1) a * b - t * 12289 = c
    // let ab_var = mul_alloc(cs.namespace(|| "a*b"), a, b)?;
    let ab_var = a.mul(cs.namespace(|| "a*b"), b)?;

    let tq = t_var.mul(cs.namespace(|| "t*q"), &modulus_var)?;
    // Enforce: a * b - t * 12289 = c (constraints for a < 12289 and b < 12289 are enforced in the main circuit body)
    cs.enforce(
        || "ab - tq = c",
        |lc| lc + ab_var.get_variable() - tq.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + c_var.get_variable(),
    );

    // (2) c < 12289
    enforce_less_than_q(cs.namespace(|| "enforce_less_than_q"), &c_var)?;
    
    Ok(c_var)
}

/// Indexed selection from an array via a binary mux tree using index bits
/// idx = b0 + 2*b1 + 2^2*b2 + ... + 2^(n-1)*bn to select the correct element in O(n), here n = 512
/// Interprets vec as a binary tree and uses the bits of idx to traverse up the tree
/// bit bi works as a selector at layer n-1
pub(crate) fn select_from_vector_512<Scalar, CS>(
    mut cs: CS,
    vec: &[AllocatedNum<Scalar>],
    idx: &AllocatedNum<Scalar>
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where 
    Scalar: PrimeField + ff::PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    // assert_eq!(vec.len(), 512, "select_from_vector_mux_512 only supports vectors of length 512");

    let idx_bits = num_to_bits(cs.namespace(||" coeff_index bits"), idx, NUM_COEFF_INDEX_BITS as usize)?;

    let mut layer = vec.to_vec();
    
    // binary mux tree with 9 levels
    for (_, bit) in idx_bits.iter().enumerate() {
        let mut next = Vec::with_capacity(layer.len() / 2);
        for j in 0..(layer.len() / 2) {
            let selected = conditionally_select(cs.namespace(|| "mux level"), &layer[2*j + 1],
                &layer[2*j],
                bit)?;
            next.push(selected);
        }
        // eliminate half of the elements in the current layer in each iteration
        layer = next;
    }
    assert!(layer.len() == 1, "After mux tree traversal, only one element should remain");
    Ok(layer[0].clone())
}

pub(crate) fn select_from_vec_linear<Scalar, CS>(
    mut cs: CS,
    input: &[AllocatedNum<Scalar>],
    idx: &AllocatedNum<Scalar>
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
    Scalar: PrimeField + ff::PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    let mut selected = AllocatedNum::alloc(cs.namespace(|| "selected"), || Ok(Scalar::ZERO))?;
    for (i, elem) in input.iter().enumerate() {
        let idx_i = AllocatedNum::alloc(cs.namespace(|| format!("idx_{}", i)), || Ok(Scalar::from(i as u64)))?;
        let is_selected = alloc_num_equals(cs.namespace(|| format!("is idx {i} selected")), &idx, &idx_i)?;
        selected = conditionally_select(cs.namespace(|| format!("select elem {}", i)), elem, &selected, &is_selected)?;
    }
    Ok(selected)
}

// Referenced from https://github.com/zhenfeizhang/falcon.rs/blob/master/falcon-r1cs/src/gadgets/arithmetics.rs#L34
/// Generate the variable c = <a \cdot b> mod 12289;
/// with a guarantee that the inputs a and b satisfies:
/// * a_i < 12289
/// * b_i < 12289
/// Cost: 29 + a.len() constraints
/// TODO: for inner product, keep buff_pk_poly as vec<vec<Scalar>> as table for each index i = 0..512 use select_from_vector_512 to select the correct vector for coeff_index
pub(crate) fn inner_product_mod<Scalar, CS>( // TODO
    mut cs: CS,
    a: &[AllocatedNum<Scalar>],
    b: &[AllocatedNum<Scalar>],
    modulus_var: &AllocatedNum<Scalar>,
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
    Scalar: PrimeField + ff::PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    if a.len() != b.len() || a.is_empty() {
        panic!("Invalid input length: a {} vs b {}", a.len(), b.len());
    }

    // we want to prove that `c = <a \cdot b> mod 12289`
    // that is
    // (1) a_0 * b_0 + a_1 * b_1 + ... + a_k * b_k - t * 12289 = c
    // for some unknown t, with
    // (2) c < 12289
    //
    // Note that this implementation assumes the
    // native field's order is greater than 12289^2
    // so we do not have any overflows
    //
    // also note that this method is slightly more efficient
    // than calling mul_mod iteratively

    let a_val = a.iter().map(|var| var.get_value().unwrap_or(Scalar::ONE)).collect::<Vec<Scalar>>();
    let b_val = b.iter().map(|var| var.get_value().unwrap_or(Scalar::ONE)).collect::<Vec<Scalar>>();

    let mut ab_val = a_val[0] * b_val[0];
    for (&a_i, &b_i) in a_val.iter().zip(b_val.iter()).skip(1) {
        ab_val += a_i*b_i;
    }
    let ab_int: BigUint = BigUint::from_bytes_le(ab_val.to_repr().as_ref());
    
    let modulus_int: BigUint = BigUint::from(MODULUS as u64);
    let t_int = &ab_int / &modulus_int;
    let c_int = &ab_int % &modulus_int;

    let t_val = Scalar::from(t_int.to_u64().unwrap());
    let c_val = Scalar::from(c_int.to_u64().unwrap());

    // cast the variables
    let t_var = AllocatedNum::alloc(cs.namespace(|| "t"), || Ok(t_val))?;
    let c_var = AllocatedNum::alloc(cs.namespace(|| "c"), || Ok(c_val))?;

    // (1) a_0 * b_0 + a_1 * b_1 + ... + a_k * b_k - t * 12289 = c
    let mut ab_var = a[0].mul(cs.namespace(|| "a[0]*b[0]"), &b[0])?;
    for (a_i, b_i) in a.iter().zip(b.iter()).skip(1) {
        let prod = a_i.mul(cs.namespace(|| "a[i]*b[i]"), b_i)?;
        ab_var = ab_var.add(cs.namespace(|| "ab_var = ab_var + a[i]*b[i]"), &prod)?;
    }

    let tq = t_var.mul(cs.namespace(|| "t*q"), modulus_var)?;

    // Enforce: a_0 * b_0 + a_1 * b_1 + ... + a_k * b_k - t * 12289 = c (constraints for a_i < 12289 and b_i < 12289 are enforced in the main circuit body)
    cs.enforce(
        || "inner product mod relation",
        |lc| lc + ab_var.get_variable() - tq.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + c_var.get_variable()
    );

    enforce_less_than_q(cs, &c_var)?;

    Ok(c_var)
}

pub(crate) fn num_to_alloc<Scalar, CS>(
    mut cs: CS,
    num: &Num<Scalar>,
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
    Scalar: PrimeField + PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    let num_var = AllocatedNum::alloc(
        cs.namespace(|| "num_to_alloc"),
        || num.get_value().ok_or(SynthesisError::AssignmentMissing),
    )?;
    cs.enforce(
        || "enforce num to allocnum",
        |lc| lc + &num.lc(Scalar::ONE),
        |lc| lc + CS::one(),
        |lc| lc + num_var.get_variable(),
    );
    Ok(num_var)
}

pub(crate) fn kary_or<Scalar, CS>(
    mut cs: CS,
    bits: &[Boolean],
) -> Result<Boolean, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    assert!(!bits.is_empty(), "kary_or requires at least one input");
    let mut acc = bits[0].clone();
    for (i, bit) in bits[1..].iter().enumerate() {
        acc = Boolean::or(cs.namespace(|| format!("kary_or_{}", i)), &acc, bit)?;
    }
    Ok(acc)
}

pub(crate) fn kary_and<Scalar, CS>(
   mut cs: CS,
    bits: &[Boolean],
) -> Result<Boolean, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    assert!(!bits.is_empty(), "kary_and requires at least one input");
    let mut acc = bits[0].clone();
    for (i, bit) in bits[1..].iter().enumerate() {
        acc = Boolean::and(cs.namespace(|| format!("kary_and_{}", i)), &acc, bit)?;
    }
    Ok(acc)
}

/// Constraint that the witness of a is smaller than 34034726
/// Cost: 47 constraints.
/// (This improves the range proof of 1264 constraints as in Arkworks.)    
pub(crate) fn enforce_less_than_norm_bound<CS, Scalar>(
    mut cs: CS,
    a: &AllocatedNum<Scalar>,
) -> Result<Boolean, SynthesisError> 
where 
CS: ConstraintSystem<Scalar>,
Scalar: PrimeField + PrimeFieldBits + PartialOrd,
{
    // the norm bound is 0b10000001110101010000100110 which is 26 bits, i.e.,
    // 2^25 + 2^18 + 2^17 + 2^16 + 2^14 + 2^ 12 + 2^10 + 2^5 + 2^2 + 2
    let a_val = a.get_value().unwrap_or(Scalar::ONE);

    // suppressing this check so that unit test can test
    // bad paths
    #[cfg(not(test))]
    if a_val >= Scalar::from(SIG_L2_BOUND) {
        panic!("Invalid input to enforce_less_than_norm_bound");
    }


    let a_bits = bytes_to_bits_le(a_val.to_repr().as_ref());
    // a_bit_vars is the least 26 bits of a
    // (we only care for the first 26 bits of a_bits)
    let a_bit_vars = a_bits
        .iter()
        .take(26)
        .enumerate()
        .map(|(i, &bit)| {
            Ok(Boolean::from(AllocatedBit::alloc(
                cs.namespace(|| format!("bit {}", i)),
                Some(bit),
            )?))
        })
        .collect::<Result<Vec<Boolean>, SynthesisError>>()?;

    // ensure that a_bits are the bit decomposition of a
    check_decomposition(cs.namespace(|| "check_decomposition enforce_less_than_norm_bound"), a, a_bit_vars.clone())?;

    let kary_or_19_24 = kary_or(cs.namespace(|| "kary_or_19_24"), &a_bit_vars[19..25])?.not();
    let kary_and_16_18 = kary_and(cs.namespace(|| "kary_and_16_18"), &a_bit_vars[16..19])?.not();
    let kary_or_6_9 = kary_or(cs.namespace(|| "kary_or_6_9"), &a_bit_vars[6..10])?.not();
    let kary_or_3_4 = kary_or(cs.namespace(|| "kary_or_3_4"), &a_bit_vars[3..5])?.not();
    let kary_and_1_2 = kary_and(cs.namespace(|| "kary_and_1_2"), &a_bit_vars[1..3])?.not();
    // argue that a < 0b10000001110101010000100110  via the following:
    // - a[25] == 0 or
    // - a[25] == 1 and a[19..24] == 0 and
    //    - either one of a[16..18] == 0
    //    - or a[16..18] == 1 and a[15] == 0 and
    //      - either a[14] == 0
    //      - or a[14] == 1 and a[13] == 0 and
    //          - either a[12] == 0
    //          - or a[12] == 1 and a[11] == 0 and
    //              - either a[10] == 0
    //              - or a[10] == 1 and a[6-9] == 0 and
    //                  - either a[5] == 0
    //                  - or a[5] == 1 and a[3] = a [4] == 0 and
    //                      - one of a[1] or a[2] == 0
    let and_3_4 = Boolean::and(cs.namespace(|| "and_3_4"), &kary_or_3_4, &kary_and_1_2)?; // - or a[5] == 1 and a[3] = a [4] == 0 and one of a[1] or a[2] == 0
    let or_5 = Boolean::or(cs.namespace(|| "or_5"), &a_bit_vars[5].not(), &and_3_4)?; // either a[5] == 0
    let and_6_9 = Boolean::and(cs.namespace(|| "and_6_9"), &kary_or_6_9, &or_5)?; // - or a[10] == 1 and a[6-9] == 0 and
    let or_10 = Boolean::or(cs.namespace(|| "or_10"), &a_bit_vars[10].not(), &and_6_9)?; // - either a[10] == 0
    let and_11 = Boolean::and(cs.namespace(|| "and_11"), &a_bit_vars[11].not(), &or_10)?; // - or a[12] == 1 and a[11] == 0 and
    let or_12 = Boolean::or(cs.namespace(|| "or_12"), &a_bit_vars[12].not(), &and_11)?; // - either a[12] == 0
    let and_13 = Boolean::and(cs.namespace(|| "and_13"), &a_bit_vars[13].not(), &or_12)?; // - or a[14] == 1 and a[13] == 0 and
    let or_14 = Boolean::or(cs.namespace(|| "or_14"), &a_bit_vars[14].not(), &and_13)?; // - either a[14] == 0
    let and_15 = Boolean::and(cs.namespace(|| "and_15"), &a_bit_vars[15].not(), &or_14)?; // - or a[16..18] == 1 and a[15] == 0 and
    let or_16_18 = Boolean::or(cs.namespace(|| "or_16_18"), &kary_and_16_18, &and_15)?; // - either one of a[16..18] == 0
    let and_19_24 = Boolean::and(cs.namespace(|| "and_19_24"), &kary_or_19_24, &or_16_18)?; // - a[25] == 1 and a[19..24] == 0 and
    let res = Boolean::or(cs.namespace(|| "or_25"), &a_bit_vars[25].not(), &and_19_24)?; // - a[25] == 0 or
    // Boolean::enforce_equal(cs.namespace(|| "enforce less than norm bound"), &res, &Boolean::Constant(true))?;

    Ok(res)
}

/// Return a variable indicating if the input is less than 6144 or not
/// Cost: 18 constraints.
/// (This improves the range proof of 1264 constraints as in Arkworks.)
pub(crate) fn is_less_than_6144<CS, Scalar>(
    cs: &mut CS,
    a: &AllocatedNum<Scalar>,
) -> Result<Boolean, SynthesisError> 
where
    CS: ConstraintSystem<Scalar>,
    Scalar: PrimeField + PrimeFieldBits + PartialOrd,
{
    // println!("< norm 6144 satisfied? {:?}", cs.is_satisfied());

    let a_val = a.get_value().unwrap_or(Scalar::ONE);

    // Note that the function returns a boolean and
    // the input a is allowed to be larger than 6144

    let a_bits = bytes_to_bits_le(a_val.to_repr().as_ref());
    // a_bit_vars is the least 14 bits of a
    // (we only care for the first 14 bits of a_bits)
    let a_bit_vars = a_bits
        .iter()
        .take(14)
        .enumerate()
        .map(|(i, &bit)| {
            Ok(Boolean::from(AllocatedBit::alloc(
                cs.namespace(|| format!("is_less_than_6144 bit {}", i)),
                Some(bit),
            )?))
        })
        .collect::<Result<Vec<Boolean>, SynthesisError>>()?;

    // ensure that a_bits are the bit decomposition of a
    check_decomposition(cs.namespace(|| "enforce_decomposition_is_less_than_6144"), a, a_bit_vars.clone())?;

    // argue that a < 6144 = 2^12 + 2^11 via the following:
    // - a[13] == 0 and
    // - either a[12] == 0 or a[11] == 0

    // a[13] == 0
    let bit13_is_zero = a_bit_vars[13].not();
    let bit12_is_zero = a_bit_vars[12].not();
    let bit11_is_zero = a_bit_vars[11].not();

    let inner_or = Boolean::or(
        cs.namespace(|| "lt6144 bit12_zero OR bit11_zero"),
        &bit12_is_zero,
        &bit11_is_zero,
    )?;

    let res = Boolean::and(
        cs.namespace(|| "lt6144 bit13_zero AND inner"),
        &bit13_is_zero,
        &inner_or,
    )?;

    Ok(res)
}

pub(crate) fn normalize_half_q<CS, Scalar>(
    cs: &mut CS,
    a: &AllocatedNum<Scalar>,
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
    CS: ConstraintSystem<Scalar>,
    Scalar: PrimeField + PrimeFieldBits + PartialOrd,
{
    let modulus_scalar = Scalar::from(MODULUS as u64);
    let modulus_var = alloc_constant(cs.namespace(|| "modulus"), modulus_scalar)?;

    let modulus_minus_a = AllocatedNum::alloc(cs.namespace(|| "modulus_minus_a"), || {
        let a_val = a
            .get_value()
            .ok_or(SynthesisError::AssignmentMissing)?;
        Ok(modulus_scalar - a_val)
    })?;
    cs.enforce(
        || "modulus_minus_a + a = modulus",
        |lc| lc + modulus_minus_a.get_variable() + a.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + modulus_var.get_variable(),
    );

    let flag_less_than_q = is_less_than_6144(cs, a)?;
    conditionally_select(
        cs.namespace(|| "normalize_half_q"),
        a,
        &modulus_minus_a,
        &flag_less_than_q,
    )
}

// normalize coefficient in [0,q] to the range [-q/2, q/2]
pub(crate) fn normalize_coeff(val: i64) -> u64 {
    let modulus = MODULUS as i64;
    let normalized = if val > modulus / 2 {
        (modulus - val) as u64
    } else {
        val as u64
    };
    normalized
}