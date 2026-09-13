use bellpepper_core::num::AllocatedNum;
use bellpepper_core::test_cs::TestConstraintSystem;
use bellpepper_core::{Comparable, ConstraintSystem, Delta};
use cyclotomic_rings::rings::StarkRingNTT;
use falcon_aadhaar::{
    age_proof::latticefold::AadhaarAgeProofCircuit,
    age_proof::latticefold::StepCircuit,
    latticefold_adapter::shape_cs::{build_r1cs, ShapeCS},
    latticefold_adapter::stark_field::{to_ark_fq, StarkFq},
    qr::{parse_aadhaar_qr_data_falcon, AadhaarQRData},
};
use falcon_rust::{Polynomial, PublicKey};
use image::{self};
use num_bigint::BigInt;
use std::time::Instant;
use zlib_rs::{
    inflate::{uncompress_slice, InflateConfig},
    ReturnCode,
};

fn qr_image_path() -> String {
    std::env::var("FALCON_QR_IMAGE")
        .unwrap_or_else(|_| format!("{}/falcon_qr.png", env!("CARGO_MANIFEST_DIR")))
}

fn current_date_string() -> String {
    std::env::var("FALCON_CURRENT_DATE").unwrap_or_else(|_| "23-04-2026".to_string())
}

#[test]
fn latticefold_r1cs_matches_step_circuit_witness() {
    let fname = qr_image_path();
    let current_date_str = current_date_string();
    let current_date_bytes: &[u8; 10] = current_date_str.as_bytes().try_into().unwrap();

    let img = image::open(&fname).unwrap().to_luma8();
    let mut img = rqrr::PreparedImage::prepare(img);
    let grids = img.detect_grids();
    assert_eq!(grids.len(), 1);
    let (_, content) = grids[0].decode().unwrap();
    let content_bytes = content.as_bytes();
    let qr_int = BigInt::parse_bytes(content_bytes, 10).unwrap();
    let (_, qr_int_bytes) = qr_int.to_bytes_be();

    let mut output = [0; 1 << 13];
    let config = InflateConfig { window_bits: 31 };
    let (decompressed_qr_bytes, ret) = uncompress_slice(&mut output, &qr_int_bytes, config);
    assert_eq!(ret, ReturnCode::Ok);

    let fields: Vec<&[u8]> = decompressed_qr_bytes.split(|&b| b == 0xFF).collect();

    println!("=== Aadhaar QR Fields ===");

    for (i, field) in fields.iter().enumerate() {
        // Try to display as UTF-8 string, skip binary fields (photo)
        if let Ok(text) = std::str::from_utf8(field) {
            if !text.is_empty() && text.chars().all(|c| !c.is_control() || c == '\n') {
                println!("Field {}: {}", i, text);
            } else {
                println!("Field {}: [binary data, {} bytes]", i, field.len());
            }
        } else {
            println!("Field {}: [binary data, {} bytes]", i, field.len());
        }
    }

    // The step function circuit, instantiated over StarkFq
    type C1 = AadhaarAgeProofCircuit<StarkFq>;

    let res = parse_aadhaar_qr_data_falcon(decompressed_qr_bytes.to_vec());
    if !res.is_ok() {
        panic!("Error parsing Aadhaar QR code bytes")
    }

    // signed_data is the Falcon payload (AadhaarQR[0..n-256]); falcon_msg is nonce||signed_data.
    let aadhaar_qr_data: AadhaarQRData = res.unwrap();
    println!(
        "Number of bytes in QR code: {}",
        aadhaar_qr_data.signed_data.len() + aadhaar_qr_data.signature_bytes.len()
    );

    // no default circuit required for this test
    let _h: PublicKey = aadhaar_qr_data.pk;
    let _s2: Polynomial = (&aadhaar_qr_data.falcon_sig).into();

    let circuit_sequence = C1::new_state_sequence(
        &aadhaar_qr_data,
        &aadhaar_qr_data.falcon_sig,
        aadhaar_qr_data.pk,
    );

    let z0 = C1::calc_initial_primary_circuit_input(
        current_date_bytes,
        &aadhaar_qr_data.falcon_msg,
        &aadhaar_qr_data.falcon_sig,
    ); // initial_opcode, current_date_scalar
    assert_eq!(z0.len(), circuit_sequence[0].arity(), "z0 arity mismatch");
    println!("Number of steps: {}", circuit_sequence.len());

    let step = &circuit_sequence[0];

    let shape_timer = Instant::now();
    let mut shape_cs = ShapeCS::new();
    let z0_shape: Vec<AllocatedNum<StarkFq>> = z0
        .iter()
        .enumerate()
        .map(|(i, v)| {
            AllocatedNum::alloc_input(shape_cs.namespace(|| format!("z_{}", i)), || Ok(*v))
                .expect("alloc z0")
        })
        .collect();

    let _ = step
        .synthesize(&mut shape_cs, &z0_shape)
        .expect("shape synthesis failed");

    let shape_time = shape_timer.elapsed();

    println!(
        "Number of constraints per step: {}",
        shape_cs.num_constraints()
    );
    println!(
        "Number of variables per step: {} ({} public inputs + 1 constant + {} witness)",
        shape_cs.num_inputs() + shape_cs.num_aux(),
        shape_cs.num_inputs() - 1,
        shape_cs.num_aux()
    );
    println!("ShapeCS synthesis took {:?}", shape_time);

    let wit_timer = Instant::now();
    let mut test_cs = TestConstraintSystem::<StarkFq>::new();
    let z0_wit: Vec<AllocatedNum<StarkFq>> = z0
        .iter()
        .enumerate()
        .map(|(i, v)| {
            AllocatedNum::alloc_input(test_cs.namespace(|| format!("z_{}", i)), || Ok(*v))
                .expect("alloc z0")
        })
        .collect();
    let z_out = step
        .synthesize(&mut test_cs, &z0_wit)
        .expect("witness synthesis failed");
    println!(
        "TestConstraintSystem synthesis took {:?}",
        wit_timer.elapsed()
    );

    if !test_cs.is_satisfied() {
        panic!(
            "Step 0 FAILED: {}",
            test_cs.which_is_unsatisfied().unwrap_or("<unknown>")
        );
    }
    println!("Step 0 OK");

    match shape_cs.delta(&test_cs, false) {
        Delta::Equal => println!("ShapeCS == TestConstraintSystem (Delta::Equal)"),
        Delta::ConstraintMismatch(row, a, b) => panic!(
            "shape/witness passes diverge at row {}:\n  ShapeCS: {:?}\n  TestCS:  {:?}",
            row, a.3, b.3
        ),
        other => panic!("shape/witness passes diverge: {:?}", other),
    }

    let build_timer = Instant::now();
    let extracted = build_r1cs(&shape_cs);
    println!("build_r1cs took {:?}", build_timer.elapsed());

    let x_len = shape_cs.num_inputs() - 1;
    assert_eq!(
        extracted.r1cs.l, x_len,
        "R1CS::l must equal the public input count"
    );
    assert_eq!(extracted.r1cs.A.nrows, shape_cs.num_constraints());
    assert_eq!(
        extracted.r1cs.A.ncols,
        x_len + 1 + shape_cs.num_aux(),
        "ncols must be |x| + 1 + |w|"
    );

    let inputs = test_cs.scalar_inputs(); // [1, x_1, ..., x_l]
    let aux = test_cs.scalar_aux(); // [w_0, ...]

    assert_eq!(
        inputs.len(),
        shape_cs.num_inputs(),
        "input count differs between the two passes"
    );
    assert_eq!(
        aux.len(),
        shape_cs.num_aux(),
        "aux count differs between the two passes"
    );
    assert_eq!(
        inputs[0],
        StarkFq::from(1u64),
        "input 0 must be the constant 1"
    );

    let z_field: Vec<StarkFq> = inputs[1..]
        .iter()
        .chain(core::iter::once(&inputs[0])) // the constant, now at index l
        .chain(aux.iter())
        .copied()
        .collect();
    assert_eq!(z_field.len(), extracted.r1cs.A.ncols);

    let z: Vec<StarkRingNTT> = z_field
        .iter()
        .map(|v| StarkRingNTT::from(to_ark_fq(v)))
        .collect();

    let check_timer = Instant::now();
    match extracted.check_relation(&z) {
        Ok(()) => println!("R1CS::check_relation: OK ({:?})", check_timer.elapsed()),
        Err(msg) => panic!("extracted R1CS rejects the native witness:\n  {}", msg),
    }

    let mut z_bad = z.clone();
    let last = z_bad.len() - 1;
    z_bad[last] = z_bad[last] + StarkRingNTT::from(1u64);
    assert!(
        extracted.check_relation(&z_bad).is_err(),
        "a pertubed witness vector was accepted: the extracted R1CS constraints incorrect"
    );
    println!("corrupted witness correctly rejected");

    println!("Step 0 extraction works.");
    println!("constraints : {}", extracted.r1cs.A.nrows);
    println!("z length    : {}", extracted.r1cs.A.ncols);
    println!("public (l)  : {}", extracted.r1cs.l);
    println!("z_out arity : {}", z_out.len());
}
