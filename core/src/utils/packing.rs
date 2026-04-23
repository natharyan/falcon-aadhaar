use ff::{PrimeField, PrimeFieldBits};
use bellpepper_core::{ConstraintSystem, LinearCombination, SynthesisError};
use bellpepper_core::boolean::Boolean;
use bellpepper_core::num::AllocatedNum;
use bellpepper::gadgets::{num::Num};


/// Takes a sequence of booleans and exposes them as compact Nums per field-capacity chunk (little-endian)
pub(crate) fn pack_bits_scalars<Scalar, CS>(
    mut cs: CS,
    bits: &[Boolean],
) -> Result<Vec<AllocatedNum<Scalar>>, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    
    let mut packed = Vec::with_capacity(
        (bits.len() + (Scalar::CAPACITY as usize) - 1) / (Scalar::CAPACITY as usize),
    );

    for (chunk_idx, bit_group) in bits.chunks(Scalar::CAPACITY as usize).enumerate() {
        let mut num = Num::<Scalar>::zero();
        let mut coeff = Scalar::ONE;

        for bit in bit_group {
            num = num.add_bool_with_coeff(CS::one(), bit, coeff);
            coeff = coeff.double();
        }

        let alloc_num = AllocatedNum::alloc(cs.namespace(|| format!("input_{chunk_idx}")), || {
            num.get_value().ok_or(SynthesisError::AssignmentMissing)
        })?;

        // num * 1 = packed_chunk
        cs.enforce(
            || format!("packing constraint {chunk_idx}"),
            |_| num.lc(Scalar::ONE),
            |lc| lc + CS::one(),
            |lc| lc + alloc_num.get_variable(),
        );

        packed.push(alloc_num);
    }

    Ok(packed)
}

pub(crate) fn num_to_alloc<Scalar, CS>(
    mut cs: CS,
    num: &Num<Scalar>,
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
    Scalar: PrimeField + PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    let num_var = AllocatedNum::alloc(cs.namespace(|| "num_to_alloc"), || {
        num.get_value().ok_or(SynthesisError::AssignmentMissing)
    })?;
    cs.enforce(
        || "enforce num to allocnum",
        |lc| lc + &num.lc(Scalar::ONE),
        |lc| lc + CS::one(),
        |lc| lc + num_var.get_variable(),
    );
    Ok(num_var)
}