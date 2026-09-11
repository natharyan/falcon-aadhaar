use bellpepper::gadgets::num::Num;
use bellpepper_core::boolean::Boolean;
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::{ConstraintSystem, LinearCombination, SynthesisError};
use ff::{PrimeField, PrimeFieldBits};

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

// Pack a 16-bit sample from current SHAKE256 state into a single AllocatedNum, following shake_sample_u16's bit ordering
pub(crate) fn pack_shake_sample_u16<Scalar, CS>(
    mut cs: CS,
    bits: &[Boolean],
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
    Scalar: PrimeField,
    CS: ConstraintSystem<Scalar>,
{
    assert_eq!(
        bits.len(),
        16,
        "pack_shake_sample_u16 expects a 16-bit sample"
    );

    let mut num = Num::<Scalar>::zero();

    // (high byte) bits[0..8], little-endian within the byte
    let mut coeff = Scalar::from(256u64);
    for bit in bits[0..8].iter() {
        num = num.add_bool_with_coeff(CS::one(), bit, coeff);
        coeff = coeff.double();
    }
    // (low byte) bits[8..16], little-endian within the byte
    let mut coeff = Scalar::ONE;
    for bit in bits[8..16].iter() {
        num = num.add_bool_with_coeff(CS::one(), bit, coeff);
        coeff = coeff.double();
    }

    let alloc_num = AllocatedNum::alloc(cs.namespace(|| "shake sample"), || {
        num.get_value().ok_or(SynthesisError::AssignmentMissing)
    })?;
    // num * 1 = sample
    cs.enforce(
        || "packing constraint shake sample",
        |_| num.lc(Scalar::ONE),
        |lc| lc + CS::one(),
        |lc| lc + alloc_num.get_variable(),
    );

    Ok(alloc_num)
}

/// Takes a sequence of booleans and exposes them as compact Nums per field-capacity chunk (big-endian)
// pub(crate) fn pack_bits_scalars_be<Scalar, CS>(
//     mut cs: CS,
//     bits: &[Boolean],
// ) -> Result<Vec<AllocatedNum<Scalar>>, SynthesisError>
// where
//     Scalar: PrimeField,
//     CS: ConstraintSystem<Scalar>,
// {
//     let mut packed = Vec::with_capacity(
//         (bits.len() + (Scalar::CAPACITY as usize) - 1) / (Scalar::CAPACITY as usize),
//     );
//     for (chunk_idx, bit_group) in bits.chunks(Scalar::CAPACITY as usize).enumerate() {
//         let mut num = Num::<Scalar>::zero();
//         let mut coeff = Scalar::ONE;
//         for bit in bit_group.iter().rev() {
//             num = num.add_bool_with_coeff(CS::one(), bit, coeff);
//             coeff = coeff.double();
//         }
//         let alloc_num = AllocatedNum::alloc(cs.namespace(|| format!("input_{chunk_idx}")), || {
//             num.get_value().ok_or(SynthesisError::AssignmentMissing)
//         })?;
//         // num * 1 = packed_chunk
//         cs.enforce(
//             || format!("packing constraint {chunk_idx}"),
//             |_| num.lc(Scalar::ONE),
//             |lc| lc + CS::one(),
//             |lc| lc + alloc_num.get_variable(),
//         );
//         packed.push(alloc_num);
//     }
//     Ok(packed)
// }

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
