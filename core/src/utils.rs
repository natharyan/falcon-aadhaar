use bellpepper_core::boolean::Boolean;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::PrimeField;
use keccak::f1600;
use sha3::{Shake256, digest::{ExtendableOutput, Update, XofReader}};

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

fn vec_bool_to_arr_u64(input: &[Boolean]) -> [u64; 25] {
    let mut input_u64: [u64; 25] = [0; 25];
    for (i, chunk) in input.chunks(64).enumerate() {
        let mut word = 0u64;
        for (bit_idx, bit) in chunk.iter().enumerate() {
            if bit.get_value().unwrap_or(false) {
                word |= 1u64 << bit_idx; // Little-endian bit order
            }
        }
        input_u64[i] = word;
    }

    input_u64
}

fn arr_u64_to_vec_bool(input: &[u64; 25]) -> Vec<Boolean> {
    input
        .iter()
        .flat_map(|word| {
            (0..64).map(move |i| {
                Boolean::Constant((word >> i) & 1 == 1) // Extract each bit and convert to Boolean
            })
        })
        .collect()
}

/// One step of the absorption (flag = false) or squeezing phase (flag = true)
pub fn library_step_sponge<E, CS>(
    mut cs: CS,
    mut state: Vec<Boolean>,
    m_i: Option<Vec<Boolean>>,
    r: usize,
    flag: bool,
) -> Result<Vec<Boolean>, SynthesisError>
where
    E: PrimeField,
    CS: ConstraintSystem<E>,
{
    if !flag {
        if let Some(m_i) = m_i {
            // Absorption step
            for i in 0..r {
                state[i] = Boolean::xor(cs.namespace(|| format!("absorb xor bit {}", i)), &state[i], &m_i[i])?;
            }
        } else {
            return Err(SynthesisError::AssignmentMissing);
        }
    }
    // Squeezing step: no m_i required, just apply f1600

    let mut input_arr_u64 = vec_bool_to_arr_u64(&state);
    f1600(&mut input_arr_u64);
    Ok(arr_u64_to_vec_bool(&input_arr_u64))
}