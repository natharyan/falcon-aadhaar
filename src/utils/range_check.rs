#[cfg(not(test))]
use falcon_rust::SIG_L2_BOUND;
use ff::{PrimeField, PrimeFieldBits};
use bellpepper_core::{ConstraintSystem, LinearCombination, SynthesisError,boolean::Boolean,num::AllocatedNum};
use bellpepper::gadgets::{boolean::AllocatedBit};
use crate::utils::check_decomposition;

use crate::utils::{bytes_to_bits_le, kary_and, kary_or};

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
    check_decomposition(cs.namespace(|| "enforce_decompose"), a, a_bit_vars.clone())?;

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

/// Return a variable indicating if the input is less than 6144 or not
/// Cost: 18 constraints.
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
    check_decomposition(
        cs.namespace(|| "enforce_decomposition_is_less_than_6144"),
        a,
        a_bit_vars.clone(),
    )?;

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

/// Constraint that the witness of a is smaller than 34034726
/// Cost: 47 constraints.
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
    check_decomposition(
        cs.namespace(|| "check_decomposition enforce_less_than_norm_bound"),
        a,
        a_bit_vars.clone(),
    )?;

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