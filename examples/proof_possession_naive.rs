use core::panic;
use std::time::Instant;

use bellpepper_core::num::AllocatedNum;
use bellpepper_core::test_cs::TestConstraintSystem;
use bellpepper_core::ConstraintSystem;
use clap::Command;
use falcon_aadhaar::{
    age_proof::OP_CODE_LAST, proof_possession_incremental::NaiveProofOfPossessionCircuit,
    qr::parse_aadhaar_qr_data,
};
use falcon_rust::{KeyPair, Polynomial, PublicKey};
use flate2::{write::ZlibEncoder, Compression};
use image::{self};
use nova_snark::traits::circuit::StepCircuit;
use nova_snark::{
    provider::{PallasEngine, VestaEngine},
    traits::{circuit::TrivialCircuit, snark::RelaxedR1CSSNARKTrait, Engine},
    CompressedSNARK, PublicParams, RecursiveSNARK,
};
use num_bigint::BigInt;
use zlib_rs::{
    inflate::{uncompress_slice, InflateConfig},
    ReturnCode,
};

type E1 = PallasEngine;
type E2 = VestaEngine;
type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<E1>;
type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<E2>;
type S1 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E1, EE1>;
type S2 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E2, EE2>;
type C1 = NaiveProofOfPossessionCircuit<<E1 as Engine>::Scalar>;
type C2 = TrivialCircuit<<E2 as Engine>::Scalar>;

fn main() {
    let keypair = KeyPair::keygen();
    let msg = "testing message";
    let sig = keypair
        .secret_key
        .sign_with_seed("test seed".as_ref(), msg.as_ref());
    assert!(keypair.public_key.verify(msg.as_ref(), &sig));
    let h: PublicKey = keypair.public_key;
    let s2: Polynomial = (&sig).into();
    let c: Polynomial = Polynomial::from_hash_of_message(msg.as_ref(), sig.nonce());

    let circuit_primary: C1 = NaiveProofOfPossessionCircuit::default(h, s2, c);
    let circuit_secondary: C2 = TrivialCircuit::default();

    let param_gen_timer = Instant::now();
    println!("Producing public parameters...");
    let pp = PublicParams::<E1, E2, C1, C2>::setup(
        &circuit_primary,
        &circuit_secondary,
        &*S1::ck_floor(),
        &*S2::ck_floor(),
    )
    .unwrap();

    let param_gen_time = param_gen_timer.elapsed();
    println!("PublicParams::setup, took {:?} ", param_gen_time);

    println!(
        "Number of constraints per step (primary circuit): {}",
        pp.num_constraints().0
    );
    println!(
        "Number of constraints per step (secondary circuit): {}",
        pp.num_constraints().1
    );
    println!(
        "Number of variables per step (primary circuit): {}",
        pp.num_variables().0
    );
    println!(
        "Number of variables per step (secondary circuit): {}",
        pp.num_variables().1
    );

    let primary_circuit_sequence =
        C1::new_state_sequence(&msg.as_bytes().to_vec(), &sig, keypair.public_key);

    let z0_primary = C1::calc_initial_primary_circuit_input(&msg.as_bytes().to_vec(), &sig);
    let z0_secondary = vec![<E2 as Engine>::Scalar::zero()];

    let proof_gen_timer = Instant::now();
    // produce a recursive SNARK
    println!("Generating a RecursiveSNARK...");
    let mut recursive_snark: RecursiveSNARK<E1, E2, C1, C2> =
        RecursiveSNARK::<E1, E2, C1, C2>::new(
            &pp,
            &primary_circuit_sequence[0],
            &circuit_secondary,
            &z0_primary,
            &z0_secondary,
        )
        .unwrap();

    // let mut z_current: Vec<<E1 as Engine>::Scalar> = z0_primary.clone();
    // for (i, circuit) in primary_circuit_sequence.iter().enumerate() {
    //     let mut cs = TestConstraintSystem::<<E1 as Engine>::Scalar>::new();

    //     let z_alloc: Vec<AllocatedNum<<E1 as Engine>::Scalar>> = z_current
    //         .iter()
    //         .enumerate()
    //         .map(|(j, val)| {
    //             AllocatedNum::alloc(cs.namespace(|| format!("z_{}", j)), || Ok(*val)).unwrap()
    //         })
    //         .collect();

    //     let z_next_alloc = circuit.synthesize(&mut cs, &z_alloc).unwrap();

    //     if !cs.is_satisfied() {
    //         println!("Step {} FAILED: {}", i, cs.which_is_unsatisfied().unwrap());
    //         panic!("Constraint system not satisfied at step {}", i);
    //     } else {
    //         println!("Step {} OK", i,);
    //     }

    //     z_current = z_next_alloc
    //         .iter()
    //         .map(|v| v.get_value().unwrap())
    //         .collect();
    // }

    let start = Instant::now();
    for (i, circuit_primary) in primary_circuit_sequence.iter().enumerate() {
        let step_start = Instant::now();
        let res = recursive_snark.prove_step(&pp, circuit_primary, &circuit_secondary);
        assert!(res.is_ok());
        println!(
            "RecursiveSNARK::prove_step {}: {:?}, took {:?}",
            i,
            res.is_ok(),
            step_start.elapsed()
        );
    }
    println!(
        "Total time taken by RecursiveSNARK::prove_steps: {:?}",
        start.elapsed()
    );

    let num_steps = primary_circuit_sequence.len();
    // verify the recursive SNARK
    println!("Verifying a RecursiveSNARK...");
    let start = Instant::now();
    let res = recursive_snark.verify(&pp, num_steps, &z0_primary, &z0_secondary);
    println!(
        "RecursiveSNARK::verify: {:?}, took {:?}",
        res.is_ok(),
        start.elapsed()
    );
    if let Err(e) = &res {
        println!("Verification failed with error: {:?}", e);
    }
    assert!(res.is_ok());

    // produce a compressed SNARK
    println!("Generating a CompressedSNARK using Spartan with IPA-PC...");
    let (pk, vk) = CompressedSNARK::<_, _, _, _, S1, S2>::setup(&pp).unwrap();

    let start = Instant::now();

    let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &pk, &recursive_snark);
    println!(
        "CompressedSNARK::prove: {:?}, took {:?}",
        res.is_ok(),
        start.elapsed()
    );
    assert!(res.is_ok());

    let proving_time = proof_gen_timer.elapsed();
    println!("Total proving time is {:?}", proving_time);

    let compressed_snark = res.unwrap();

    let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
    bincode::serialize_into(&mut encoder, &compressed_snark).unwrap();
    let compressed_snark_encoded = encoder.finish().unwrap();
    println!(
        "CompressedSNARK::len {:?} bytes",
        compressed_snark_encoded.len()
    );

    // verify the compressed SNARK
    println!("Verifying a CompressedSNARK...");
    let start = Instant::now();
    let res = compressed_snark.verify(&vk, num_steps, &z0_primary, &z0_secondary);
    let verification_time = start.elapsed();
    println!(
        "CompressedSNARK::verify: {:?}, took {:?}",
        res.is_ok(),
        verification_time,
    );
    assert!(res.is_ok());
    println!("=========================================================");
    println!("Number of constraints per step: {}", pp.num_constraints().0);
    println!("Public parameters generation time: {:?} ", param_gen_time);
    println!(
        "Total proving time (excl pp generation): {:?}",
        proving_time
    );
    println!("Compressed SNARK size: {:.1} KB", compressed_snark_encoded.len() as f64 / 1000.0);
    println!("Total verification time: {:?}", verification_time);

    println!("=========================================================");

    let final_outputs = res.unwrap().0;

    let final_coeff_index = final_outputs[1];
    assert_eq!(final_coeff_index, <E1 as Engine>::Scalar::from(512u64));

    println!("l2norm(s1,s2) = {:?}", final_outputs[0]);
}
