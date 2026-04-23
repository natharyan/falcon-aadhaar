// Referenced from nova-aadhaar-qr crate, modified to include falcon signature on the qr code

use crate::falcon_bytes::{public_key_from_bytes, secret_key_from_bytes, signature_from_bytes};
use falcon_rust::{KeyPair, Polynomial, PublicKey, Signature, PK_LEN, SIG_LEN, SK_LEN};
use std::fs;
use std::io::Error;
use std::path::PathBuf;

pub const DELIMITER: u8 = 255;
const CHAR_V: u8 = 86; // Corresponds to "V"
const CHAR_2: u8 = 50; // Corresponds to "2"
const CHAR_4: u8 = 52; // Corresponds to "4"
const CHAR_5: u8 = 53; // Corresponds to "5"
pub const RSA_SIGNATURE_LENGTH_BYTES: usize = 256;
pub const DOB_LENGTH_BYTES: usize = 10; // Date of birth is in DD-MM-YYYY format
pub const NUM_DELIMITERS_BEFORE_DOB: usize = 4; // Date of birth is the 4th field in the QR code data
pub const DATA_LENGTH_PER_STEP: usize = 136; // 136 bytes will be hashed per Nova step
pub const NONCE_LENGTH_BYTES: usize = 40; // Falcon nonce length (signature bytes [1..41))
pub const FALCON_SIGNATURE_LENGTH_BYTES: usize = SIG_LEN;
const UIDAI_FALCON_SK_FILE: &str = "keys/uidai_falcon_sk.bin";
const UIDAI_FALCON_PK_FILE: &str = "keys/uidai_falcon_pk.bin";

pub struct AadhaarQRData {
    pub signed_data: Vec<u8>,
    pub falcon_msg: Vec<u8>,
    pub signature_bytes: Vec<u8>,
    pub dob_byte_index: usize,
    pub falcon_sig: Signature,
    pub c: Polynomial,
    pub pk: PublicKey,
}

fn key_fixture_path(relative: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(relative)
}

fn read_key_file<const N: usize>(relative: &str, label: &str) -> Result<[u8; N], Error> {
    let path = key_fixture_path(relative);
    let bytes = fs::read(&path).map_err(|e| {
        Error::other(format!("Failed to read UIDAI {label} key file {}: {e}", path.display()))
    })?;
    let arr: [u8; N] = bytes.try_into().map_err(|_| {
        Error::other(format!(
            "UIDAI {label} key in {} has invalid length: expected {N} bytes",
            path.display()
        ))
    })?;
    Ok(arr)
}

pub fn uidai_keypair() -> Result<KeyPair, Error> {
    let sk_bytes = read_key_file::<SK_LEN>(UIDAI_FALCON_SK_FILE, "secret")?;
    let pk_bytes = read_key_file::<PK_LEN>(UIDAI_FALCON_PK_FILE, "public")?;

    let secret_key = secret_key_from_bytes(sk_bytes);
    let public_key = public_key_from_bytes(pk_bytes);

    let derived_pk = secret_key.make_public_key();
    if derived_pk != public_key {
        return Err(Error::other(
            "UIDAI key fixture mismatch: public key does not match secret key",
        ));
    }

    Ok(KeyPair {
        public_key,
        secret_key,
    })
}

fn parse_dob_byte_index(payload: &[u8]) -> Result<usize, Error> {
    if payload.len() < DATA_LENGTH_PER_STEP {
        return Err(Error::other("QR payload is too short to locate date of birth"));
    }

    let mut num_delimiters_seen = 0;
    let mut i = 2;
    while i < DATA_LENGTH_PER_STEP {
        if payload[i] == DELIMITER {
            num_delimiters_seen += 1;
        }
        i += 1;
        if num_delimiters_seen == NUM_DELIMITERS_BEFORE_DOB {
            break;
        }
    }

    let dob_byte_index = i;
    let dob_byte_index_with_nonce = dob_byte_index + NONCE_LENGTH_BYTES;
    if dob_byte_index_with_nonce + DOB_LENGTH_BYTES - 1 >= DATA_LENGTH_PER_STEP {
        return Err(Error::other(
            "Date of birth is not in first SHAKE block after nonce prefix",
        ));
    }

    Ok(dob_byte_index_with_nonce)
}

pub fn parse_aadhaar_qr_data_rsa(qr_data: Vec<u8>) -> Result<AadhaarQRData, Error> {
    let qr_data_len = qr_data.len();

    if qr_data_len < RSA_SIGNATURE_LENGTH_BYTES {
        return Err(Error::other(
            "QR data is shorter than 2048-bit RSA signature",
        ));
    }

    if qr_data[0] != CHAR_V || !(qr_data[1] >= CHAR_2 && qr_data[1] <= CHAR_5) {
        return Err(Error::other(
            "Aadhaar QR code version must be V2, V3, V4, or V5",
        ));
    }

    let signed_data = qr_data[0..qr_data_len - RSA_SIGNATURE_LENGTH_BYTES].to_vec();
    let keypair = uidai_keypair()?;
    let sig_message = signed_data.as_slice();
    let sig = keypair.secret_key.sign(sig_message);
    let h: PublicKey = keypair.public_key;
    let c: Polynomial = Polynomial::from_hash_of_message(sig_message, sig.nonce());
    let mut falcon_msg = sig.nonce().to_vec();
    falcon_msg.extend_from_slice(sig_message);

    assert!(keypair.public_key.verify_rust(sig_message, &sig));
    println!("Falcon signature verification PASSED!");

    Ok(AadhaarQRData {
        signed_data,
        falcon_msg,
        signature_bytes: qr_data[qr_data_len - RSA_SIGNATURE_LENGTH_BYTES..].to_vec(),
        dob_byte_index: parse_dob_byte_index(&qr_data)?,
        falcon_sig: sig,
        c,
        pk: h,
    })
}

pub fn parse_aadhaar_qr_data_falcon(qr_data: Vec<u8>) -> Result<AadhaarQRData, Error> {
    let qr_data_len = qr_data.len();

    if qr_data_len < FALCON_SIGNATURE_LENGTH_BYTES {
        return Err(Error::other("QR data is shorter than Falcon signature length"));
    }

    if qr_data[0] != CHAR_V || !(qr_data[1] >= CHAR_2 && qr_data[1] <= CHAR_5) {
        return Err(Error::other(
            "Aadhaar QR code version must be V2, V3, V4, or V5",
        ));
    }

    let signed_data = qr_data[0..qr_data_len - FALCON_SIGNATURE_LENGTH_BYTES].to_vec();
    let signature_bytes: [u8; FALCON_SIGNATURE_LENGTH_BYTES] = qr_data
        [qr_data_len - FALCON_SIGNATURE_LENGTH_BYTES..]
        .try_into()
        .map_err(|_| Error::other("Unable to parse Falcon signature bytes"))?;
    let falcon_sig = signature_from_bytes(signature_bytes);
    let keypair = uidai_keypair()?;
    let c = Polynomial::from_hash_of_message(signed_data.as_slice(), falcon_sig.nonce());
    let mut falcon_msg = falcon_sig.nonce().to_vec();
    falcon_msg.extend_from_slice(&signed_data);
    let dob_byte_index = parse_dob_byte_index(&signed_data)?;

    if !keypair.public_key.verify_rust(signed_data.as_slice(), &falcon_sig) {
        return Err(Error::other("Falcon signature verification failed"));
    }

    Ok(AadhaarQRData {
        signed_data,
        falcon_msg,
        signature_bytes: signature_bytes.to_vec(),
        dob_byte_index,
        falcon_sig,
        c,
        pk: keypair.public_key,
    })
}

pub fn parse_aadhaar_qr_data(qr_data: Vec<u8>) -> Result<AadhaarQRData, Error> {
    parse_aadhaar_qr_data_rsa(qr_data)
}
