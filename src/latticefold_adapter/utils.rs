use crate::{
    age_proof::latticefold::{AadhaarAgeProofCircuit, StepCircuit},
    latticefold_adapter::{
        // stark_field::StarkFq,
        goldilocks_field::GoldilocksFq,
        ntt_pack::{check_field_relation, pack_z},
        shape_cs::{z_vector, BpMatrix, LatticefoldR1CS, ShapeCS},
    },
};
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::test_cs::TestConstraintSystem;
use bellpepper_core::{Comparable, ConstraintSystem, Delta};
use std::time::Instant;

type C1 = AadhaarAgeProofCircuit<GoldilocksFq>;

/// allocate z as a vector of public inputs.
pub fn alloc_public_z<CS: ConstraintSystem<GoldilocksFq>>(
    cs: &mut CS,
    z: &[GoldilocksFq],
) -> Vec<AllocatedNum<GoldilocksFq>> {
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
pub fn synthesize_step(
    step: &C1,
    z_in: &[GoldilocksFq],
    index: usize,
    shape_cs: &ShapeCS,
) -> (Vec<GoldilocksFq>, Vec<GoldilocksFq>) {
    let mut cs = TestConstraintSystem::<GoldilocksFq>::new();
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

/// pad to num_lanes() to GoldilocksRingNTT.NTT_SLOTS
pub fn pad_lanes(z_lanes: &mut Vec<Vec<GoldilocksFq>>, k: usize) -> usize {
    let real = z_lanes.len();
    let dummy = z_lanes[real - 1].clone();
    for _ in real..k {
        z_lanes.push(dummy.clone());
    }
    k - real
}

/// verify all GoldilocksFq R1CS instances and the GoldilocksRingNTT R1CS instance.
pub fn verify_both_sides(
    extracted: &LatticefoldR1CS,
    matrices: (&BpMatrix, &BpMatrix, &BpMatrix),
    z_lanes: &[Vec<GoldilocksFq>],
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

/// confirm R1CS satisfaction upto NTT transform.
pub fn negative_control(
    extracted: &LatticefoldR1CS,
    matrices: (&BpMatrix, &BpMatrix, &BpMatrix),
    z_lanes: &[Vec<GoldilocksFq>],
    lane: usize,
) {
    let (a_f, b_f, c_f) = matrices;
    let mut z_broken = z_lanes.to_vec();
    let last = z_broken[lane].len() - 1;
    z_broken[lane][last] = z_broken[lane][last] + GoldilocksFq::from(1u64);

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
