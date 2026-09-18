use crate::{
    age_proof::latticefold::{AadhaarAgeProofCircuit, StepCircuit},
    latticefold_adapter::{
        ntt_pack::{check_field_relation, pack_z},
        shape_cs::{z_vector, BpMatrix, LatticefoldR1CS, ShapeCS},
        stark_field::StarkFq,
    },
};
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::test_cs::TestConstraintSystem;
use bellpepper_core::{Comparable, ConstraintSystem, Delta};
use std::time::Instant;

type C1 = AadhaarAgeProofCircuit<StarkFq>;

/// allocate z as public input. z0 is public, so R1CS::l == arity() and each lane's
/// x_ccs is its (opcode, io_hash). replacing the opcode with a 0..15 counter, so the
/// public vector carries no payload-dependent information, is the planned change and
/// is not made yet.
pub fn alloc_public_z<CS: ConstraintSystem<StarkFq>>(
    cs: &mut CS,
    z: &[StarkFq],
) -> Vec<AllocatedNum<StarkFq>> {
    z.iter()
        .enumerate()
        .map(|(i, v)| {
            AllocatedNum::alloc_input(cs.namespace(|| format!("z_{}", i)), || Ok(*v))
                .expect("alloc z")
        })
        .collect()
}

/// synthesize one step into a witness-bearing backend and return its z in
/// latticefold order together with the step's output.
///
/// ShapeCS cannot produce z: it never evaluates a value closure, which is exactly
/// what lets it run on a circuit with no valid witness. a second backend is
/// required, which is Nova's split (ShapeCS in setup, SatisfyingAssignment in
/// prove_step) with TestConstraintSystem in the witness role, as in
/// tests/shapecs_to_latticefold_r1cs.rs.
///
/// the returned TestConstraintSystem is dropped by the caller as soon as z is
/// taken: the k witness vectors are needed simultaneously to transpose, the k
/// constraint systems are not.
pub fn synthesize_step(
    step: &C1,
    z_in: &[StarkFq],
    index: usize,
    shape_cs: &ShapeCS,
) -> (Vec<StarkFq>, Vec<StarkFq>) {
    let mut cs = TestConstraintSystem::<StarkFq>::new();
    let z_alloc = alloc_public_z(&mut cs, z_in);

    let z_next_alloc = step
        .synthesize(&mut cs, &z_alloc)
        .expect("witness synthesis failed");

    if !cs.is_satisfied() {
        panic!(
            "Step {} FAILED: {}",
            index,
            cs.which_is_unsatisfied().unwrap_or("<unknown>")
        );
    }

    if index == 0 {
        match shape_cs.delta(&cs, false) {
            Delta::Equal => println!("ShapeCS == TestConstraintSystem (Delta::Equal)"),
            Delta::ConstraintMismatch(row, a, b) => panic!(
                "shape/witness passes diverge at row {}:\n  ShapeCS: {:?}\n  TestCS:  {:?}",
                row, a.3, b.3
            ),
            other => panic!("shape/witness passes diverge: {:?}", other),
        }
    }

    let z = z_vector(&cs.scalar_inputs(), &cs.scalar_aux());
    let z_out = z_next_alloc
        .iter()
        .map(|v| v.get_value().expect("z_out value missing"))
        .collect();

    println!("Step {} OK", index);
    (z, z_out)
}

/// pad to num_lanes() by replicating the last real step's witness.
///
/// padding lanes must satisfy the SAME R1CS, since the matrices are broadcast
/// across all slots and a lane of zeros or noise would fail. replicating an
/// existing satisfying witness is the cheapest valid choice: one clone per lane, no
/// extra synthesis. the last real step is used because it is already in the frozen
/// tail state (next_nullifier and ctx_absorb are conditionally_select'd on
/// flag_shake_active, so they stop advancing once SHAKE absorption is done), which
/// is what a genuine dummy step would produce anyway.
///
/// temporary, to be removed with the counter change: because z0 is public,
/// replicated lanes have identical x_ccs, which a verifier can see. once
/// cntr = 0..15 replaces the opcode in the public IO each padding lane needs its own
/// counter and therefore its own synthesis, and flag_last_step moves from
/// next_shake_opcode AND NOT flag_coeff to create_flag(cntr == 15) so only lane 15
/// emits nullifier_msg. until then every lane past the real steps reports
/// flag_last_step == true, harmless for the relation but not the intended semantics.
pub fn pad_lanes(z_lanes: &mut Vec<Vec<StarkFq>>, k: usize) -> usize {
    let real = z_lanes.len();
    let dummy = z_lanes[real - 1].clone();
    for _ in real..k {
        z_lanes.push(dummy.clone());
    }
    k - real
}

/// verify both sides of the Remark 4.1 equivalence.
///
/// the packed ring relation holds iff all k field relations hold. checking both
/// sides makes that observable rather than assumed, and the per-lane check names the
/// failing lane where the packed check reports only a row index.
pub fn verify_both_sides(
    extracted: &LatticefoldR1CS,
    matrices: (&BpMatrix, &BpMatrix, &BpMatrix),
    z_lanes: &[Vec<StarkFq>],
) {
    let (a_f, b_f, c_f) = matrices;

    let lane_timer = Instant::now();
    for (i, z) in z_lanes.iter().enumerate() {
        if let Some(row) = check_field_relation(a_f, b_f, c_f, z) {
            panic!(
                "lane {i} unsatisfied at row {row}: {}",
                extracted
                    .constraint_name(row)
                    .unwrap_or("<unnamed constraint>")
            );
        }
    }
    println!(
        "All {} lanes satisfy the field relation ({:?})",
        z_lanes.len(),
        lane_timer.elapsed()
    );

    let z_star = pack_z(z_lanes).expect("packing failed");
    let check_timer = Instant::now();
    match extracted.check_relation(&z_star) {
        Ok(()) => println!(
            "packed R1CS over StarkRingNTT: check_relation OK ({:?})",
            check_timer.elapsed()
        ),
        Err(msg) => panic!("packed R1CS rejects the packed witness:\n  {}", msg),
    }
}

/// corrupting one lane must break the packed relation and that lane's own field
/// relation, and must leave every other lane untouched. the last assertion is what
/// demonstrates slot independence: a packing that broadcast instead of transposing
/// would pass the first two.
pub fn negative_control(
    extracted: &LatticefoldR1CS,
    matrices: (&BpMatrix, &BpMatrix, &BpMatrix),
    z_lanes: &[Vec<StarkFq>],
    lane: usize,
) {
    let (a_f, b_f, c_f) = matrices;
    let mut z_broken = z_lanes.to_vec();
    let last = z_broken[lane].len() - 1;
    z_broken[lane][last] = z_broken[lane][last] + StarkFq::from(1u64);

    let z_star_broken = pack_z(&z_broken).expect("pack");
    assert!(
        extracted.check_relation(&z_star_broken).is_err(),
        "corrupting lane {lane} did not break the packed relation: the NTT slots are \
         not independent, or the packing is broadcasting instead of transposing"
    );
    assert!(
        check_field_relation(a_f, b_f, c_f, &z_broken[lane]).is_some(),
        "corrupting lane {lane} did not break its own field relation"
    );
    for (i, z) in z_broken.iter().enumerate() {
        if i != lane {
            assert_eq!(
                check_field_relation(a_f, b_f, c_f, z),
                None,
                "corrupting lane {lane} also broke lane {i}: slots are leaking into each other"
            );
        }
    }
    println!("corrupted lane {lane} detected, other lanes unaffected");
}
