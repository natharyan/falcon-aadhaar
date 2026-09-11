use falcon_aadhaar::falcon_bytes::{public_key_as_bytes, secret_key_as_bytes};
use falcon_aadhaar::qr::{uidai_keypair, FALCON_SIGNATURE_LENGTH_BYTES};
use falcon_rust::{KeyPair, PK_LEN, SK_LEN};
use std::fs;
use std::path::PathBuf;
use std::time::Instant;

const UIDAI_SK_REL: &str = "keys/uidai_falcon_sk.bin";
const UIDAI_PK_REL: &str = "keys/uidai_falcon_pk.bin";
const UIDAI_SEED: &[u8] = b"UIDAI seed for pair";

fn key_path(relative: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(relative)
}

fn main() {
    let total_start = Instant::now();
    let sk_path = key_path(UIDAI_SK_REL);
    let pk_path = key_path(UIDAI_PK_REL);

    if sk_path.exists() && pk_path.exists() {
        let validation_start = Instant::now();
        let kp = uidai_keypair().expect("existing UIDAI key pair must be valid");
        let validation_elapsed = validation_start.elapsed();
        println!("UIDAI key pair already exists and are valid");
        println!("Secret key: {} ({} bytes)", sk_path.display(), SK_LEN);
        println!("Public key: {} ({} bytes)", pk_path.display(), PK_LEN);
        println!(
            "Falcon signature length for this build: {} bytes",
            FALCON_SIGNATURE_LENGTH_BYTES
        );
        println!("Public key checksum byte: {}", public_key_as_bytes(&kp.public_key)[0]);
        println!("Validation time: {:.2?}", validation_elapsed);
        println!("Total runtime: {:.2?}", total_start.elapsed());
        return;
    }

    let keygen_start = Instant::now();
    let keypair = KeyPair::keygen_with_seed(UIDAI_SEED);
    let keygen_elapsed = keygen_start.elapsed();

    if let Some(parent) = sk_path.parent() {
        fs::create_dir_all(parent).expect("failed to create keys directory");
    }

    fs::write(&sk_path, secret_key_as_bytes(&keypair.secret_key))
        .expect("failed to write UIDAI secret key");
    fs::write(&pk_path, public_key_as_bytes(&keypair.public_key))
        .expect("failed to write UIDAI public key");

    println!("Generated UIDAI Falcon key pair");
    println!("Secret key: {} ({} bytes)", sk_path.display(), SK_LEN);
    println!("Public key: {} ({} bytes)", pk_path.display(), PK_LEN);
    println!(
        "Falcon signature length for this build: {} bytes",
        FALCON_SIGNATURE_LENGTH_BYTES
    );
    println!("Key pair generation time: {:.2?}", keygen_elapsed);
    println!("Total runtime: {:.2?}", total_start.elapsed());
}
