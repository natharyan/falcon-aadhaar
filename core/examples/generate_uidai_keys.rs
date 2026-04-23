use falcon_aadhaar::falcon_bytes::{public_key_as_bytes, secret_key_as_bytes};
use falcon_aadhaar::qr::{uidai_keypair, FALCON_SIGNATURE_LENGTH_BYTES};
use falcon_rust::{KeyPair, PK_LEN, SK_LEN};
use std::fs;
use std::path::PathBuf;

const UIDAI_SK_REL: &str = "keys/uidai_falcon_sk.bin";
const UIDAI_PK_REL: &str = "keys/uidai_falcon_pk.bin";
const UIDAI_SEED: &[u8] = b"UIDAI seed for fixtures";

fn key_path(relative: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(relative)
}

fn main() {
    let sk_path = key_path(UIDAI_SK_REL);
    let pk_path = key_path(UIDAI_PK_REL);

    if sk_path.exists() && pk_path.exists() {
        let kp = uidai_keypair().expect("existing UIDAI key fixtures must be valid");
        println!("UIDAI key fixtures already exist and are valid");
        println!("Secret key: {} ({} bytes)", sk_path.display(), SK_LEN);
        println!("Public key: {} ({} bytes)", pk_path.display(), PK_LEN);
        println!(
            "Falcon signature length for this build: {} bytes",
            FALCON_SIGNATURE_LENGTH_BYTES
        );
        println!("Public key checksum byte: {}", public_key_as_bytes(&kp.public_key)[0]);
        return;
    }

    let keypair = KeyPair::keygen_with_seed(UIDAI_SEED);

    if let Some(parent) = sk_path.parent() {
        fs::create_dir_all(parent).expect("failed to create keys directory");
    }

    fs::write(&sk_path, secret_key_as_bytes(&keypair.secret_key))
        .expect("failed to write UIDAI secret key");
    fs::write(&pk_path, public_key_as_bytes(&keypair.public_key))
        .expect("failed to write UIDAI public key");

    println!("Generated UIDAI Falcon key fixtures");
    println!("Secret key: {} ({} bytes)", sk_path.display(), SK_LEN);
    println!("Public key: {} ({} bytes)", pk_path.display(), PK_LEN);
    println!(
        "Falcon signature length for this build: {} bytes",
        FALCON_SIGNATURE_LENGTH_BYTES
    );
}
