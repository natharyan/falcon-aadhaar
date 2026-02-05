// Referenced from nova-aadhaar-qr create, modified to include falcon signature

use bincode::config;
use falcon_rust::{KeyPair, Signature};
use std::io::Error;
pub const DELIMITER: u8 = 255;
const CHAR_V: u8 = 86; // Corresponds to "V"
const CHAR_2: u8 = 50; // Corresponds to "2"
const CHAR_4: u8 = 52; // Corresponds to "4"
const CHAR_5: u8 = 53; // Corresponds to "5"
pub const DOB_LENGTH_BYTES: usize = 10; // Date of birth is in DD-MM-YYYY format
pub const NUM_DELIMITERS_BEFORE_DOB: usize = 4; // Date of birth is the 4th field in the QR code data
pub const DATA_LENGTH_PER_STEP: usize = 136; // 136 bytes will be hashed per Nova step

pub struct AadhaarQRData {
    pub signed_data: Vec<u8>,
    pub rsa_signature: Vec<u8>,
    pub falcon_signature: Signature,
    pub dob_byte_index: usize,
}

// #[cfg(feature = "falcon-512")]
pub fn parse_aadhaar_qr_data(qr_data: Vec<u8>) -> Result<AadhaarQRData, Error> {
    let qr_data_len = qr_data.len();

    if qr_data_len < 256 {
        return Err(Error::other(
            "QR data is shorter than 2048-bit RSA signature",
        ));
    }

    if qr_data[0] != CHAR_V || !(qr_data[1] >= CHAR_2 && qr_data[1] <= CHAR_5) {
        return Err(Error::other(
            "Aadhaar QR code version must be V2, V3, V4, or V5",
        ));
    }

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
    if dob_byte_index + DOB_LENGTH_BYTES - 1 >= DATA_LENGTH_PER_STEP {
        // Circuit assumes that the date of birth is contained in the first 128 bytes
        // This requires the holder's Name to fit in 89 characters
        return Err(Error::other("Date of birth is not in first 128 bytes"));
    }

    let keypair = KeyPair::keygen();
    let sig_message = &qr_data[0..qr_data_len - 256];
    let sig: falcon_rust::Signature = keypair
        .secret_key
        .sign_with_seed("test seed".as_ref(), sig_message);

    assert!(keypair.public_key.verify_rust(sig_message.as_ref(), &sig));
    println!("Falcon signature verification PASSED!");

    Ok(AadhaarQRData {
        signed_data: qr_data[0..qr_data_len - 256].to_vec(), // All bytes except last 256 are signed
        rsa_signature: qr_data[qr_data_len - 256..].to_vec(), // Last 256 bytes have the RSA signature
        falcon_signature: sig, // falcon signature over all bytes except the last 256 bytes
        dob_byte_index,
    })
}
