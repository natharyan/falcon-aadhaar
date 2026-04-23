use bellpepper_core::num::AllocatedNum;
use bellpepper_core::test_cs::TestConstraintSystem;
use bellpepper_core::ConstraintSystem;
use clap::Command;
use falcon_aadhaar::{
    age_proof::AadhaarAgeProofCircuit,
    age_proof::OP_CODE_LAST,
    qr::{parse_aadhaar_qr_data, AadhaarQRData},
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
use std::fs::File;
use std::io::BufWriter;
use std::time::Instant;
use zlib_rs::{
    inflate::{uncompress_slice, InflateConfig},
    ReturnCode,
};

fn main() {
    let cmd = Command::new("Aadhaar-based Proof of 18+ Age")
        .bin_name("proveage")
        .arg(
            clap::Arg::new("aadhaar_qrcode_image")
                .value_name("Aadhaar QR code image file")
                .required(true),
        )
        .arg(
            clap::Arg::new("current_date")
                .value_name("Current date in DD-MM-YYYY format")
                .required(true),
        )
        .after_help("The proveage command proves that the Aadhaar holder is 18+");

    let m = cmd.get_matches();
    let fname = m.get_one::<String>("aadhaar_qrcode_image").unwrap();
    let current_date_str = m.get_one::<String>("current_date").unwrap();
    let current_date_bytes: &[u8; 10] = current_date_str.as_bytes().try_into().unwrap();

    let img = image::open(fname).unwrap().to_luma8();
    // Prepare for detection
    let mut img = rqrr::PreparedImage::prepare(img);
    // Search for grids, without decoding
    let grids = img.detect_grids();
    assert_eq!(grids.len(), 1);
    // Decode the grid
    let (_, content) = grids[0].decode().unwrap();
    // println!("Aadhaar QR code content: {}", content);
    let content_bytes = content.as_bytes();
    let qr_int = BigInt::parse_bytes(content_bytes, 10).unwrap();
    let (_, qr_int_bytes) = qr_int.to_bytes_be();

    let mut output = [0; 1 << 13];
    let config = InflateConfig { window_bits: 31 };
    let (decompressed_qr_bytes, ret) = uncompress_slice(&mut output, &qr_int_bytes, config);
    assert_eq!(ret, ReturnCode::Ok);

    // Split by 0xFF delimiter and print readable fields
    let fields: Vec<&[u8]> = decompressed_qr_bytes.split(|&b| b == 0xFF).collect();

    println!("=== Aadhaar QR Fields ===");
    
    // println!("\n=== DoB Parsing Debug ===");
    // let test_dob_index = {
    //     let mut num_delimiters_seen = 0;
    //     let mut i = 2;
    //     while i < decompressed_qr_bytes.len() && num_delimiters_seen < 4 {
    //         if decompressed_qr_bytes[i] == 0xFF {
    //             num_delimiters_seen += 1;
    //         }
    //         i += 1;
    //     }
    //     i
    // };
    // println!("Calculated dob_byte_index: {}", test_dob_index);
    // if test_dob_index + 10 <= decompressed_qr_bytes.len() {
    //     let dob_bytes = &decompressed_qr_bytes[test_dob_index..test_dob_index + 10];
    //     println!("DoB bytes (hex): {:02X?}", dob_bytes);
    //     if let Ok(dob_str) = std::str::from_utf8(dob_bytes) {
    //         println!("DoB as string: '{}'", dob_str);
    //     }
    //     println!("First byte: {} (should be 48-57 for '0'-'9')", dob_bytes[0]);
    //     println!("All bytes as chars: {}", dob_bytes.iter().map(|&b| format!("{}", b as char)).collect::<String>());
    // } else {
    //     println!("ERROR: dob_byte_index + 10 exceeds buffer length!");
    //     println!("Buffer length: {}, dob_byte_index: {}", decompressed_qr_bytes.len(), test_dob_index);
    // }
    // println!();
    
    for (i, field) in fields.iter().enumerate() {
        // Try to display as UTF-8 string, skip binary fields (photo/signature)
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
    // println!("{:?}", String::from_utf8_lossy(decompressed_qr_bytes));
    type E1 = PallasEngine;
    type E2 = VestaEngine;
    type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<E1>;
    type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<E2>;
    type S1 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E1, EE1>;
    type S2 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E2, EE2>;
    type C1 = AadhaarAgeProofCircuit<<E1 as Engine>::Scalar>;
    type C2 = TrivialCircuit<<E2 as Engine>::Scalar>;

    let res = parse_aadhaar_qr_data(decompressed_qr_bytes.to_vec());
    if !res.is_ok() {
        panic!("Error parsing Aadhaar QR code bytes")
    }
    
    // signed_data is the Falcon payload (AadhaarQR[0..n-256]); falcon_msg is nonce||signed_data.
    let aadhaar_qr_data: AadhaarQRData = res.unwrap();
    println!(
        "Number of bytes in QR code: {}",
        aadhaar_qr_data.signed_data.len() + aadhaar_qr_data.rsa_signature.len()
    );

    // println!("\n=== DoB Byte Index Debug ===");
    // println!("Actual dob_byte_index from aadhaar_qr_data: {}", aadhaar_qr_data.dob_byte_index);
    
    // if aadhaar_qr_data.dob_byte_index + 10 <= decompressed_qr_bytes.len() {
    //     let dob_bytes = &decompressed_qr_bytes[aadhaar_qr_data.dob_byte_index..aadhaar_qr_data.dob_byte_index + 10];
    //     println!("DoB bytes (hex): {:02X?}", dob_bytes);
    //     println!("DoB as string: '{}'", String::from_utf8_lossy(dob_bytes));
    //     println!("First byte: {} (should be 48-57 for digit)", dob_bytes[0]);
        
    //     // Also check what's in the first 136-byte block that gets passed to circuit
    //     println!("\nFirst 136 bytes of signed_data:");
    //     let msg_block = &aadhaar_qr_data.signed_data[0..std::cmp::min(136, aadhaar_qr_data.signed_data.len())];
    //     println!("Bytes 30-50 in first block:");
    //     for i in 30..std::cmp::min(50, msg_block.len()) {
    //         println!("  Index {}: 0x{:02X} = {}", i, msg_block[i], msg_block[i] as char);
    //     }
        
    //     println!("\nBytes at DoB position (indices {}-{}) in first block:", 
    //              aadhaar_qr_data.dob_byte_index, 
    //              aadhaar_qr_data.dob_byte_index + 9);
    //     for i in aadhaar_qr_data.dob_byte_index..std::cmp::min(aadhaar_qr_data.dob_byte_index + 10, msg_block.len()) {
    //         println!("  Index {}: 0x{:02X} = {}", i, msg_block[i], msg_block[i] as char);
    //     }
    // } else {
    //     println!("ERROR: dob_byte_index + 10 exceeds buffer!");
    //     println!("Buffer length: {}, dob_byte_index: {}", decompressed_qr_bytes.len(), aadhaar_qr_data.dob_byte_index);
    // }
    
    // println!("Number of bytes in QR code: {}",
    //     aadhaar_qr_data.signed_data.len() + aadhaar_qr_data.rsa_signature.len()
    // );


    // falcon signature on aadhaar_qr_data.signed_data
    let h: PublicKey = aadhaar_qr_data.pk;
    let s2: Polynomial = (&aadhaar_qr_data.falcon_sig).into();
    let c: Polynomial = aadhaar_qr_data.c;

    let circuit_primary: C1 = AadhaarAgeProofCircuit::default(h, s2, c);
    let circuit_secondary: C2 = TrivialCircuit::default();

    let param_gen_timer = Instant::now();
    println!("Producing public parameters...");
    // NOTE calls the synthesize function of AadhaarAgeProofCircuit to compute R1CS constraints
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

    
    let primary_circuit_sequence = C1::new_state_sequence(
        &aadhaar_qr_data,
        &aadhaar_qr_data.falcon_sig,
        aadhaar_qr_data.pk,
    );

    let z0_primary = C1::calc_initial_primary_circuit_input(
        current_date_bytes,
        &aadhaar_qr_data.falcon_msg,
        &aadhaar_qr_data.falcon_sig,
    ); // initial_opcode, current_date_scalar
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

    // save compress_snark in json file
    let file = File::create("compressed_snark.json").unwrap();
    let writer = BufWriter::new(file);
    serde_json::to_writer(writer, &compressed_snark).unwrap();

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
    println!("Public parameters generation time: {:?} ", param_gen_time);
    println!(
        "Total proving time (excl pp generation): {:?}",
        proving_time
    );
    println!("Total verification time: {:?}", verification_time);

    println!("=========================================================");

    let final_outputs = res.unwrap().0;

    let final_opcode = final_outputs[0];
    assert_eq!(final_opcode, <E1 as Engine>::Scalar::from(OP_CODE_LAST));

    println!("Nullifier = {:?}", final_outputs[3]);
}
