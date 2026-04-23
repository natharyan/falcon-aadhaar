use clap::Command;
use falcon_aadhaar::falcon_bytes::signature_as_bytes;
use falcon_aadhaar::qr::{
    parse_aadhaar_qr_data_falcon, parse_aadhaar_qr_data_rsa, AadhaarQRData,
};
use flate2::{write::ZlibEncoder, Compression};
use image::Luma;
use num_bigint::{BigInt, Sign};
use qrcode::QrCode;
use std::io::Write;
use zlib_rs::{
    inflate::{uncompress_slice, InflateConfig},
    ReturnCode,
};

fn decode_png_to_qr_bytes(input_png: &str) -> Vec<u8> {
    let img = image::open(input_png)
        .unwrap_or_else(|e| panic!("Failed to open input image {input_png}: {e}"))
        .to_luma8();

    let mut prepared = rqrr::PreparedImage::prepare(img);
    let grids = prepared.detect_grids();
    assert_eq!(grids.len(), 1, "Expected exactly one QR code in input image");

    let (_, content) = grids[0].decode().expect("Failed to decode QR grid");
    let qr_int = BigInt::parse_bytes(content.as_bytes(), 10)
        .expect("QR content is not a valid decimal-encoded big integer");
    let (_, qr_int_bytes) = qr_int.to_bytes_be();

    let mut output = [0u8; 1 << 15];
    let config = InflateConfig { window_bits: 31 };
    let (decompressed_qr_bytes, ret) = uncompress_slice(&mut output, &qr_int_bytes, config);
    assert_eq!(ret, ReturnCode::Ok, "Failed to decompress QR payload bytes");

    decompressed_qr_bytes.to_vec()
}

fn encode_qr_bytes_to_png(qr_bytes: &[u8], output_png: &str) {
    let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
    encoder
        .write_all(qr_bytes)
        .expect("Failed to zlib-compress Falcon QR bytes");
    let compressed = encoder
        .finish()
        .expect("Failed to finalize zlib-compression");

    let big = BigInt::from_bytes_be(Sign::Plus, &compressed);
    let qr_decimal = big.to_str_radix(10);

    let code = QrCode::new(qr_decimal.as_bytes()).expect("Failed to build QR matrix");
    let image = code
        .render::<Luma<u8>>()
        .min_dimensions(1024, 1024)
        .build();
    image
        .save(output_png)
        .unwrap_or_else(|e| panic!("Failed to save output PNG {output_png}: {e}"));
}

fn main() {
    let cmd = Command::new("Generate Falcon-signed Aadhaar QR")
        .bin_name("generate_falcon_qr")
        .arg(
            clap::Arg::new("input_aadhaar_qrcode_image")
                .value_name("Input Aadhaar QR image (legacy RSA-tail format)")
                .required(true),
        )
        .arg(
            clap::Arg::new("output_falcon_qrcode_image")
                .value_name("Output Falcon-signed Aadhaar QR image")
                .required(true),
        )
        .after_help(
            "Reads an Aadhaar QR PNG, signs its payload with UIDAI Falcon key, replaces the final signature field with raw Falcon signature bytes, and writes a new QR PNG.",
        );

    let matches = cmd.get_matches();
    let input_png = matches
        .get_one::<String>("input_aadhaar_qrcode_image")
        .unwrap();
    let output_png = matches
        .get_one::<String>("output_falcon_qrcode_image")
        .unwrap();

    let original_qr_bytes = decode_png_to_qr_bytes(input_png);
    let parsed_rsa: AadhaarQRData = parse_aadhaar_qr_data_rsa(original_qr_bytes)
        .expect("Failed to parse legacy RSA-tail Aadhaar QR payload");

    let mut falcon_qr_bytes = parsed_rsa.signed_data.clone();
    falcon_qr_bytes.extend_from_slice(signature_as_bytes(&parsed_rsa.falcon_sig));

    parse_aadhaar_qr_data_falcon(falcon_qr_bytes.clone())
        .expect("Generated Falcon-tail QR payload failed parser verification");

    encode_qr_bytes_to_png(&falcon_qr_bytes, output_png);

    println!("Generated Falcon-signed Aadhaar QR PNG: {output_png}");
    let sig_bytes = signature_as_bytes(&parsed_rsa.falcon_sig);
    println!(
        "Payload bytes: {}, signature bytes: {}, total bytes: {}",
        parsed_rsa.signed_data.len(),
        sig_bytes.len(),
        falcon_qr_bytes.len()
    );
}
