use falcon_rust::MODULUS;
use ff::{PrimeField, PrimeFieldBits};
use bellpepper_core::{ConstraintSystem, LinearCombination, SynthesisError};
use bellpepper_core::num::AllocatedNum;
use nova_aadhaar_qr::util::{alloc_num_equals, conditionally_select, num_to_bits};

use crate::age_proof::NUM_COEFF_INDEX_BITS;

/// Indexed selection from an array via a binary mux tree using index bits
/// idx = b0 + 2*b1 + 2^2*b2 + ... + 2^(n-1)*bn to select the correct element in O(n), here n = 512
/// Interprets vec as a binary tree and uses the bits of idx to traverse up the tree
/// bit bi works as a selector at layer n-1
pub(crate) fn select_from_vector_512<Scalar, CS>(
    mut cs: CS,
    vec: &[AllocatedNum<Scalar>],
    idx: &AllocatedNum<Scalar>,
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
    Scalar: PrimeField + ff::PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    // assert_eq!(vec.len(), 512, "select_from_vector_mux_512 only supports vectors of length 512");

    let idx_bits = num_to_bits(
        cs.namespace(|| " coeff_index bits"),
        idx,
        NUM_COEFF_INDEX_BITS as usize,
    )?;

    let mut layer = vec.to_vec();

    // binary mux tree with 9 levels
    for (_, bit) in idx_bits.iter().enumerate() {
        let mut next = Vec::with_capacity(layer.len() / 2);
        for j in 0..(layer.len() / 2) {
            let selected = conditionally_select(
                cs.namespace(|| "mux level"),
                &layer[2 * j + 1],
                &layer[2 * j],
                bit,
            )?;
            next.push(selected);
        }
        // eliminate half of the elements in the current layer in each iteration
        layer = next;
    }
    assert!(
        layer.len() == 1,
        "After mux tree traversal, only one element should remain"
    );
    Ok(layer[0].clone())
}

pub(crate) fn select_from_vec_linear<Scalar, CS>(
    mut cs: CS,
    input: &[AllocatedNum<Scalar>],
    idx: &AllocatedNum<Scalar>,
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
    Scalar: PrimeField + ff::PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    let mut selected = AllocatedNum::alloc(cs.namespace(|| "selected"), || Ok(Scalar::ZERO))?;
    for (i, elem) in input.iter().enumerate() {
        let idx_i = AllocatedNum::alloc(cs.namespace(|| format!("idx_{}", i)), || {
            Ok(Scalar::from(i as u64))
        })?;
        let is_selected = alloc_num_equals(
            cs.namespace(|| format!("is idx {i} selected")),
            &idx,
            &idx_i,
        )?;
        selected = conditionally_select(
            cs.namespace(|| format!("select elem {}", i)),
            elem,
            &selected,
            &is_selected,
        )?;
    }
    Ok(selected)
}