use bellpepper::gadgets::multipack::bytes_to_bits;
use bellpepper_core::boolean::Boolean;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use clap::error;
use ff::PrimeField;
use keccak::f1600;
use sha3::{Shake256, digest::{ExtendableOutput, Update, XofReader}};
use falcon_rust::{MODULUS, N, Polynomial, PublicKey};
use crate::shake256::{SHAKE256_BLOCK_LENGTH_BYTES};
use math::round::ceil;

/// Reference implementation of SHAKE256 using sha3 crate
pub(crate) fn shake_256(input: &[u8], d: usize) -> Vec<u8> {
    let mut hasher = Shake256::default();
    hasher.update(input);
    let mut reader = hasher.finalize_xof();
    let mut result = vec![0u8; d];
    XofReader::read(&mut reader, &mut result);
    result
}

/// Convert bytes to little-endian bits
pub(crate) fn bytes_to_bits_le(bytes: &[u8]) -> Vec<bool> {
    bytes
        .iter()
        .flat_map(|byte| (0..8).map(move |i| (byte >> i) & 1 == 1))
        .collect()
}

/// Convert little-endian bits to bytes
pub(crate) fn bits_to_bytes_le(bits: &[bool]) -> Vec<u8> {
    bits.chunks(8)
        .map(|chunk| {
            chunk
                .iter()
                .enumerate()
                .fold(0u8, |acc, (i, &b)| acc | ((b as u8) << i))
        })
        .collect()
}

// Convert big-endian bits to bytes
pub(crate) fn bits_to_bytes(bits: &[bool]) -> Vec<u8> {
    bits.chunks(8)
        .map(|chunk| {
            chunk.iter()
                .enumerate()
                .fold(0u8, |acc, (i, &b)| acc | ((b as u8) << (7 - i)))
        })
        .collect()
}

pub(crate) fn vec_bool_to_arr_u64(input: &[bool]) -> [u64; 25] {
    let mut input_u64: [u64; 25] = [0; 25];
    for (i, chunk) in input.chunks(64).enumerate() {
        let mut word = 0u64;
        for (bit_idx, &bit) in chunk.iter().enumerate() {
            if bit {
                word |= 1u64 << bit_idx; // Little-endian bit order
            }
        }
        input_u64[i] = word;
    }

    input_u64
}

pub(crate) fn arr_u64_to_vec_bool(input: &[u64; 25]) -> [bool; 1600] {
    let vec: Vec<bool> = input
        .iter()
        .flat_map(|word| {
            (0..64).map(move |i| {
                (word >> i) & 1 == 1 // Extract each bit and convert to Boolean
            })
        })
        .collect();
    vec.try_into().expect("Expected exactly 1600 bits")
}

/// One step of the absorption (flag = false) or squeezing phase (flag = true)
pub(crate) fn library_step_sponge(
    mut state: Vec<bool>,
    m_i: Option<Vec<bool>>,
    r: usize,
    flag: bool,
) -> [bool; 1600]
{
    // absorption step
    if !flag {
        if let Some(m_i_bits) = m_i {
            for i in 0..r {
                state[i] ^=  m_i_bits[i];
            }
        } else {
            assert!(false, "Absorption step requires input message block m_i");
        }
    }
    let mut input_arr_u64 = vec_bool_to_arr_u64(&state);
    f1600(&mut input_arr_u64);
    arr_u64_to_vec_bool(&input_arr_u64)
}

pub(crate) fn library_hashtocoeffs(
    ctx: [bool; 1600],
    q: u16,
    coeff_index: u64,
    s2: Polynomial,
    flag_coeff: bool,
    h_poly: Polynomial // TODO remove this as a paramater
) -> (u64, u16, [bool; 1600]) {
    let s2_h = s2 * h_poly;
    let k = ceil(2^16 / q);
    let sum_aggregated: u16 = 0;
    let ctx_pointer = 0;
    for i in 1..=68 {
        let t_bits = ctx[ctx_pointer..ctx_pointer+16];
        let mut t: u16 = 0;
        // evaluate using big-endian convention
        for &bit in t_bits {
            t = (t << 1) | (bit as u16);
        }
        let flag_success = t < k * q;
        let update_flag = flag_success && flag_coeff;
        let c = t % q;
        let s1_coeff = c - s2_h[coeff_index as usize];
        let sum_update: u64  = 0;
        if update_flag {
            sum_update = s1_coeff*s1_coeff + s2_h[coeff_index as usize]*s2_h[coeff_index as usize];
            coeff_index += 1;
        }
        sum_aggregated += sum_update;
        ctx_pointer += 16;
    }
    // apply shake256 permutation
    ctx_squeeze = library_step_sponge(ctx_squeeze, None, 1088, true);
    
    (coeff_index, sum_aggregated, ctx_squeeze)
}