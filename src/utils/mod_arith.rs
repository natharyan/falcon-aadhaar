use falcon_rust::MODULUS;
use ff::{PrimeField, PrimeFieldBits};
use bellpepper_core::{ConstraintSystem, LinearCombination, SynthesisError};
use bellpepper_core::num::AllocatedNum;
use crate::utils::{alloc_constant, conditionally_select};
use num_bigint::BigUint;
use num_traits::ToPrimitive;
use crate::utils::{enforce_less_than_q, is_less_than_6144};

// referenced from https://github.com/zhenfeizhang/falcon.rs/blob/master/falcon-r1cs/src/gadgets/arithmetics.rs#L105
/// Generate the variable b = a mod 12289;
pub(crate) fn mod_q<Scalar, CS>(
    mut cs: CS,
    a: &AllocatedNum<Scalar>,
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
    let a_val: Scalar = a.get_value().unwrap_or(Scalar::ONE);

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
    enforce_less_than_q(cs.namespace(|| "enforce_less_than_q mod_q"), &b_var)?;

    Ok(b_var)
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
    let a_val: Scalar = a.get_value().unwrap_or(Scalar::ONE);
    let b_val: Scalar = b.get_value().unwrap_or(Scalar::ONE);

    let ab_val = a_val * b_val;
    let ab_int: BigUint = BigUint::from_bytes_le(ab_val.to_repr().as_ref());

    let modulus_int: BigUint = BigUint::from(MODULUS as u64);
    let t_int = &ab_int / &modulus_int;
    let c_int = &ab_int % &modulus_int;

    // cast the variables
    let t_val = Scalar::from(t_int.to_u64().unwrap());
    let c_val = Scalar::from(c_int.to_u64().unwrap());

    let t_var = AllocatedNum::alloc(cs.namespace(|| "t"), || Ok(t_val))?;
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

// Referenced from https://github.com/zhenfeizhang/falcon.rs/blob/master/falcon-r1cs/src/gadgets/arithmetics.rs#L34
/// Generate the variable c = <a \cdot b> mod 12289;
/// with a guarantee that the inputs a and b satisfies:
/// * a_i < 12289
/// * b_i < 12289
/// Cost: 29 + a.len() constraints
pub(crate) fn inner_product_mod<Scalar, CS>(
    // TODO
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

    let a_val = a
        .iter()
        .map(|var| var.get_value().unwrap_or(Scalar::ONE))
        .collect::<Vec<Scalar>>();
    let b_val = b
        .iter()
        .map(|var| var.get_value().unwrap_or(Scalar::ONE))
        .collect::<Vec<Scalar>>();

    let mut ab_val = a_val[0] * b_val[0];
    for (&a_i, &b_i) in a_val.iter().zip(b_val.iter()).skip(1) {
        ab_val += a_i * b_i;
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
        |lc| lc + c_var.get_variable(),
    );

    enforce_less_than_q(cs, &c_var)?;

    Ok(c_var)
}

// normalize to [-q/2,q/2] over unsigned representatives, if a >= 6144, return 12289 - a; otherwise return a
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
        let a_val = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
        Ok(modulus_scalar - a_val)
    })?;
    cs.enforce(
        || "modulus_minus_a + a = modulus",
        |lc| lc + modulus_minus_a.get_variable() + a.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + modulus_var.get_variable(),
    );

    let flag_less_than_half_q = is_less_than_6144(cs, a)?;
    conditionally_select(
        cs.namespace(|| "normalize_half_q"),
        a,
        &modulus_minus_a,
        &flag_less_than_half_q,
    )
}

// normalize coefficient in [0,q] to the range [-q/2, q/2] over unsigned representatives, if a >= 6144, return 12289 - a; otherwise return a
pub(crate) fn normalize_coeff(val: i64) -> u64 {
    let modulus = MODULUS as i64;
    let normalized = if val > modulus / 2 {
        (modulus - val) as u64
    } else {
        val as u64
    };
    normalized
}

