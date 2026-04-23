use falcon_rust::{PublicKey, SecretKey, Signature, PK_LEN, SIG_LEN, SK_LEN};

pub fn signature_from_bytes(bytes: [u8; SIG_LEN]) -> Signature {
    unsafe { std::mem::transmute::<[u8; SIG_LEN], Signature>(bytes) }
}

pub fn signature_as_bytes(sig: &Signature) -> &[u8; SIG_LEN] {
    unsafe { &*(sig as *const Signature as *const [u8; SIG_LEN]) }
}

pub fn public_key_from_bytes(bytes: [u8; PK_LEN]) -> PublicKey {
    unsafe { std::mem::transmute::<[u8; PK_LEN], PublicKey>(bytes) }
}

pub fn public_key_as_bytes(pk: &PublicKey) -> &[u8; PK_LEN] {
    unsafe { &*(pk as *const PublicKey as *const [u8; PK_LEN]) }
}

pub fn secret_key_from_bytes(bytes: [u8; SK_LEN]) -> SecretKey {
    unsafe { std::mem::transmute::<[u8; SK_LEN], SecretKey>(bytes) }
}

pub fn secret_key_as_bytes(sk: &SecretKey) -> &[u8; SK_LEN] {
    unsafe { &*(sk as *const SecretKey as *const [u8; SK_LEN]) }
}
