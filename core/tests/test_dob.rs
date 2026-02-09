/// Test to verify that DOB constraints pass with qr.png
use bellpepper::gadgets::multipack::bytes_to_bits;
use bellpepper_core::{
    ConstraintSystem,
    boolean::{AllocatedBit, Boolean},
    test_cs::TestConstraintSystem,
};
use falcon_rust::{KeyPair, Signature};
use image;
use num_bigint::BigInt;
use pasta_curves::Fp;
use zlib_rs::{
    ReturnCode,
    inflate::{InflateConfig, uncompress_slice},
};

use falcon_aadhaar::dob::{calculate_age_in_years, get_day_month_year_conditional};
use falcon_aadhaar::qr::{
    DATA_LENGTH_PER_STEP, DELIMITER, DOB_LENGTH_BYTES, NUM_DELIMITERS_BEFORE_DOB,
};
use nova_aadhaar_qr::util::{alloc_constant, boolean_implies, less_than_or_equal};

fn parse_qr_for_dob_test(qr_data: &[u8]) -> (Vec<u8>, usize) {
    let qr_data_len = qr_data.len();
    assert!(qr_data_len >= 256, "QR data too short");

    let mut num_delimiters_seen = 0;
    let mut i = 2;
    while i < DATA_LENGTH_PER_STEP {
        if qr_data[i] == DELIMITER {
            num_delimiters_seen += 1;
        }
        i += 1;
        if num_delimiters_seen == NUM_DELIMITERS_BEFORE_DOB {
            break;
        }
    }
    let dob_byte_index = i;
    assert!(
        dob_byte_index + DOB_LENGTH_BYTES - 1 < DATA_LENGTH_PER_STEP,
        "DOB not in first block"
    );

    let signed_data = qr_data[0..qr_data_len - 256].to_vec();
    (signed_data, dob_byte_index)
}

fn load_qr() -> (Vec<u8>, usize) {
    let img = image::open("qr.png").expect("Failed to open qr.png");
    let img = img.to_luma8();

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

    parse_qr_for_dob_test(decompressed_qr_bytes)
}

fn alloc_date_bits<CS: ConstraintSystem<Fp>>(mut cs: CS, date_bytes: &[u8]) -> Vec<Boolean> {
    assert_eq!(date_bytes.len(), 10);
    let date_bits_values = bytes_to_bits(date_bytes);
    date_bits_values
        .into_iter()
        .enumerate()
        .map(|(i, b)| {
            Boolean::from(
                AllocatedBit::alloc(cs.namespace(|| format!("alloc bit {i}")), Some(b)).unwrap(),
            )
        })
        .collect()
}

#[test]
fn test_age_calculation_with_qr_png() {
    let (signed_data, dob_byte_index) = load_qr();

    let dob_bytes = &signed_data[dob_byte_index..dob_byte_index + 10];
    println!("DOB from QR: {}", String::from_utf8_lossy(dob_bytes));

    let current_date_bytes = b"05-02-2026";
    println!(
        "Current date: {}",
        String::from_utf8_lossy(current_date_bytes)
    );

    let mut cs = TestConstraintSystem::<Fp>::new();

    let date_bits = alloc_date_bits(cs.namespace(|| "alloc dob bits"), dob_bytes);

    let curr_date_bits =
        alloc_date_bits(cs.namespace(|| "alloc curr_date bits"), current_date_bytes);

    let is_rsa_opcode_first_rsa = Boolean::Constant(true);

    let (day, month, year) = get_day_month_year_conditional(
        cs.namespace(|| "get birth day, month, year"),
        &date_bits,
        &is_rsa_opcode_first_rsa,
    )
    .unwrap();

    let (current_day, current_month, current_year) = get_day_month_year_conditional(
        cs.namespace(|| "get current day, month, year"),
        &curr_date_bits,
        &is_rsa_opcode_first_rsa,
    )
    .unwrap();

    println!(
        "DOB: day={:?}, month={:?}, year={:?}",
        day.get_value(),
        month.get_value(),
        year.get_value()
    );

    let age = calculate_age_in_years(
        cs.namespace(|| "calculate age"),
        &day,
        &month,
        &year,
        &current_day,
        &current_month,
        &current_year,
        &is_rsa_opcode_first_rsa,
    )
    .unwrap();

    println!("Calculated age: {:?}", age.get_value());

    let age18 = alloc_constant(cs.namespace(|| "alloc 18"), Fp::from(18u64)).unwrap();
    let age_gte_18 = less_than_or_equal(
        cs.namespace(|| "age >= 18"),
        &age18,
        &age,
        19, // In the first step, age will occupy 7 bits but in later steps it can occupy 19 bits
    )
    .unwrap();

    boolean_implies(
        cs.namespace(|| "if first SHA256 step then age must at least 18"),
        &is_rsa_opcode_first_rsa,
        &age_gte_18,
    )
    .unwrap();

    println!("Age >= 18: {:?}", age_gte_18.get_value());

    if !cs.is_satisfied() {
        println!("Unsatisfied constraint: {:?}", cs.which_is_unsatisfied());
    }
    assert!(cs.is_satisfied());

    println!("All DOB constraints PASSED!");
    println!("Number of constraints: {}", cs.num_constraints());

    // Test Falcon signature generation and verification
    // NOTE: Must run with falcon-512 feature due to hardcoded 512 in sig.rs unpack
    // Run with: cargo test --no-default-features --features falcon-512 -- --nocapture
    println!("\n=== Testing Falcon Signature ===");

    let keypair = KeyPair::keygen();
    let seed = "test seed".as_ref();
    let sig_message = &signed_data;
    let sig: Signature = keypair
        .secret_key
        .sign_with_seed(seed, sig_message);

    assert!(keypair.public_key.verify_rust(sig_message.as_ref(), &sig));
    println!("Falcon signature verification PASSED!");
}
