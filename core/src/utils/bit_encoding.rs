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
            chunk
                .iter()
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