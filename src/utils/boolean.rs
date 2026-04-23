use ff::{PrimeField, PrimeFieldBits};
use bellpepper_core::{ConstraintSystem, LinearCombination, SynthesisError};
use bellpepper_core::boolean::Boolean;

pub(crate) fn kary_or<Scalar, CS>(mut cs: CS, bits: &[Boolean]) -> Result<Boolean, SynthesisError>
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

pub(crate) fn kary_and<Scalar, CS>(mut cs: CS, bits: &[Boolean]) -> Result<Boolean, SynthesisError>
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