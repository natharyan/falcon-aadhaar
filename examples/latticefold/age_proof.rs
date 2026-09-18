// stops at R1CS::check_relation. no CCS, no Ajtai commitment, no folding
//
// reference: https://github.com/NethermindEth/latticefold
// reference: https://github.com/NethermindEth/folded-falcon (crates/folded-falcon/examples/usage.rs)
//

use clap::Command;

use falcon_aadhaar::{
    age_proof::latticefold::AadhaarAgeProofCircuit,
    age_proof::latticefold::StepCircuit,
    qr::{parse_aadhaar_qr_data_falcon, AadhaarQRData},
};

use falcon_aadhaar::latticefold_adapter::{
    goldilocks_field::GoldilocksFq,
    ntt_pack::check_field_relation,
    ntt_pack::{num_lanes, pack_z},
    shape_cs::{build_r1cs, get_matrices, ShapeCS},
    utils::{alloc_public_z, negative_control, pad_lanes, synthesize_step, verify_both_sides},
    // stark_field::StarkFq,
    // lf_prove::{prove, verify},
    // shape_cs::{z_vector, BpMatrix},
};

use falcon_rust::{Polynomial, PublicKey};
use image::{self};
use num_bigint::BigInt;
use std::time::Instant;
use zlib_rs::{
    inflate::{uncompress_slice, InflateConfig},
    ReturnCode,
};

type C1 = AadhaarAgeProofCircuit<GoldilocksFq>;

fn main() {
    let cmd = Command::new("Aadhaar-based Proof of 18+ Age (LatticeFold NTT packing)")
        .bin_name("latticefold_age_proof")
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
        .after_help(
            "Packs every step of the age-proof circuit into one R1CS instance over \
             StarkRingNTT and checks it against the natively computed witnesses.",
        );

    let m = cmd.get_matches();
    let fname = m.get_one::<String>("aadhaar_qrcode_image").unwrap();
    let current_date_str = m.get_one::<String>("current_date").unwrap();
    let current_date_bytes: &[u8; 10] = current_date_str.as_bytes().try_into().unwrap();

    let img = image::open(fname).unwrap().to_luma8();
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

    // Split by 0xFF delimiter and print readable fields
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

    let res = parse_aadhaar_qr_data_falcon(decompressed_qr_bytes.to_vec());
    if !res.is_ok() {
        panic!("Error parsing Aadhaar QR code bytes")
    }
    let aadhaar_qr_data = res.unwrap();

    println!(
        "Number of bytes in QR code: {}",
        aadhaar_qr_data.signed_data.len() + aadhaar_qr_data.signature_bytes.len()
    );

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

    let num_steps = circuit_sequence.len();
    let k = num_lanes();
    assert_eq!(z0.len(), circuit_sequence[0].arity(), "z0 arity mismatch");
    assert!(
        num_steps <= k,
        "num_steps = {num_steps} exceeds the {k} available NTT slots; a second packed \
         instance and a fold would be required"
    );
    println!("Number of steps: {num_steps} (packing into {k} NTT slots)");

    // shape, once. all steps run the same circuit, so the R1CS is extracted a single
    // time and reused for every lane. this is the structural saving over a monolithic
    // circuit: the constraint system stays at one step's size rather than num_steps
    // times it, and it is what makes the packed matrices correct with no packing work.
    let shape_timer = Instant::now();
    let mut shape_cs = ShapeCS::new();
    let z0_shape = alloc_public_z(&mut shape_cs, &z0);
    let _ = circuit_sequence[0]
        .synthesize(&mut shape_cs, &z0_shape)
        .expect("shape synthesis failed");

    let x_len = shape_cs.num_inputs() - 1;
    let ncols = x_len + 1 + shape_cs.num_aux();
    println!(
        "Number of constraints per step: {}",
        shape_cs.num_constraints()
    );
    println!(
        "Number of variables per step: {} ({} public inputs + 1 constant + {} witness)",
        ncols,
        x_len,
        shape_cs.num_aux()
    );
    println!("ShapeCS synthesis took {:?}", shape_timer.elapsed());

    // field-level matrices, for the per-lane cross-check. these are the A_i, B_i, C_i
    // of Remark 4.1, identical for every i.
    let (a_f, b_f, c_f) = get_matrices(&shape_cs);

    // witness per step, threading z_out -> z_in.
    let wit_timer = Instant::now();
    let mut z_lanes: Vec<Vec<GoldilocksFq>> = Vec::with_capacity(k);
    let mut z_current: Vec<GoldilocksFq> = z0.clone();

    for (i, circuit) in circuit_sequence.iter().enumerate() {
        let (z, z_out) = synthesize_step(circuit, &z_current, i, &shape_cs);
        assert_eq!(z.len(), ncols, "step {i} produced |z| = {}", z.len());
        z_lanes.push(z);
        z_current = z_out;
    }

    println!(
        "All {num_steps} witnesses generated in {:?}",
        wit_timer.elapsed()
    );

    let n_pad = pad_lanes(&mut z_lanes, k);
    println!("Padded {n_pad} lanes by replicating the final step's witness");

    let build_timer = Instant::now();
    let extracted = build_r1cs(&shape_cs);
    println!("build_r1cs took {:?}", build_timer.elapsed());
    assert_eq!(extracted.r1cs.l, x_len);
    assert_eq!(extracted.r1cs.A.nrows, shape_cs.num_constraints());
    assert_eq!(extracted.r1cs.A.ncols, ncols);

    let pack_timer = Instant::now();
    let z_star = pack_z(&z_lanes).expect("packing failed");
    assert_eq!(z_star.len(), ncols);
    println!(
        "Packed {k} lanes into |z*| = {} ring elements in {:?}",
        z_star.len(),
        pack_timer.elapsed()
    );

    verify_both_sides(&extracted, (&a_f, &b_f, &c_f), &z_lanes);
    negative_control(&extracted, (&a_f, &b_f, &c_f), &z_lanes, 3);
    extracted
        .check_relation(&z_star)
        .expect("packed R1CS check_relation failed");

    println!("Multi-step packing works.");
    println!("real steps       : {num_steps}");
    println!("padded lanes     : {n_pad}");
    println!("NTT slots        : {k}");
    println!("constraints      : {}", extracted.r1cs.A.nrows);
    println!("|z| per lane     : {ncols}");
    println!("|z*| (ring)      : {}", z_star.len());
    println!("public inputs (l): {}", extracted.r1cs.l);
}
