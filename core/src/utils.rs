use crate::circuit::NUM_COEFF_INDEX_BITS;
use crate::shake256::SHAKE256_BLOCK_LENGTH_BYTES;
use bellpepper::gadgets::{multipack::bytes_to_bits,boolean::AllocatedBit};
use bellpepper_core::boolean::{Boolean};
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, SynthesisError, LinearCombination};
use blstrs::Scalar;
use clap::error;
use falcon_rust::{MODULUS, N, Polynomial, PublicKey};
use ff::{PrimeField, PrimeFieldBits};
use keccak::f1600;
use nova_aadhaar_qr::util::{check_decomposition, alloc_constant, conditionally_select, num_to_bits, conditionally_select_vec};
use sha3::{
    Shake256,
    digest::{ExtendableOutput, Update, XofReader},
};
use num_bigint::BigUint;
use num_traits::ToPrimitive;

/// Reference implementation of SHAKE256 using sha3 crate
pub(crate) fn shake_256(input: &[u8], d: usize) -> Vec<u8> {
    let mut hasher = Shake256::default();
    hasher.update(input);
    let mut reader = hasher.finalize_xof();
    let mut result = vec![0u8; d];
    XofReader::read(&mut reader, &mut result);
    result
}

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

/// One step of the absorption (flag = false) or squeezing phase (flag = true)
pub(crate) fn library_step_sponge(
    mut state: Vec<bool>,
    m_i: Option<Vec<bool>>,
    r: usize,
    flag: bool,
) -> [bool; 1600] {
    // absorption step
    if !flag {
        if let Some(m_i_bits) = m_i {
            for i in 0..r {
                state[i] ^= m_i_bits[i];
            }
        } else {
            assert!(false, "Absorption step requires input message block m_i");
        }
    }
    let mut input_arr_u64 = vec_bool_to_arr_u64(&state);
    f1600(&mut input_arr_u64);
    arr_u64_to_vec_bool(&input_arr_u64)
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

    let t_val = Scalar::from(t_int.to_u64().unwrap());
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
    assert_eq!(vec.len(), 512, "select_from_vector_mux_512 only supports vectors of length 512");

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