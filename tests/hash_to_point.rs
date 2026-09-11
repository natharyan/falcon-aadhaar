use falcon_aadhaar::{
    hash::shake256::{library_shake256_inject, library_step_sponge},
    subarray::create_bit_array,
    utils::shake_sample_u16,
};
use falcon_rust::{Polynomial, MODULUS, MODULUS_THRESHOLD, N};

const SHAKE256_RATE_BITS: usize = 1088;
const SAMPLE_BITS: usize = 16;
const SAMPLES_PER_SQUEEZE: usize = SHAKE256_RATE_BITS / SAMPLE_BITS; // 68

struct Shake256PointSampler {
    state: [bool; 1600],
    rate_offset: usize,
    squeeze_rounds: usize,
}

impl Shake256PointSampler {
    fn new(state: [bool; 1600]) -> Self {
        Self {
            state,
            rate_offset: 0,
            squeeze_rounds: 0,
        }
    }

    fn squeeze(&mut self) {
        self.state = library_step_sponge(self.state.to_vec(), None, SHAKE256_RATE_BITS, true);
        self.rate_offset = 0;
        self.squeeze_rounds += 1;
    }

    /// Read the next 16-bit big-endian sample from the SHAKE256 XOR stream.
    fn next_u16_be(&mut self) -> u16 {
        if self.rate_offset + SAMPLE_BITS > SHAKE256_RATE_BITS {
            self.squeeze();
        }

        let w = shake_sample_u16(&self.state, self.rate_offset);
        self.rate_offset += SAMPLE_BITS;
        w
    }

    fn squeeze_rounds(&self) -> usize {
        self.squeeze_rounds
    }
}

/// Falcon `hash_to_point`: map (nonce, message) to the challenge polynomial `c`.
pub fn hash_to_point(message: &[u8], nonce: &[u8]) -> [u16; N] {
    let mut preimage = nonce.to_vec();
    preimage.extend_from_slice(message);

    let mut sampler = Shake256PointSampler::new(library_shake256_inject([false; 1600], preimage));

    let mut res = [0u16; N];
    let mut i = 0usize;
    while i < N {
        let w = sampler.next_u16_be();
        if w < MODULUS_THRESHOLD {
            res[i] = (w % MODULUS) as u16;
            i += 1;
        }
    }

    res
}

#[test]
fn hash_to_point_matches_falcon_rust() {
    let cases: Vec<(&[u8], &[u8])> = vec![
        (b"hello world", &[0u8; 40]),
        (b"", &[0u8; 40]),
        (b"The quick brown fox jumps over the lazy dog", &[1u8; 40]),
        (
            b"aadhaar age proof test message with some extra bytes",
            b"nonce-with-distinct-prefix-for-falcon-shake",
        ),
    ];

    for (message, nonce) in cases {
        let expected = Polynomial::from_hash_of_message(message, nonce);
        let got = hash_to_point(message, nonce);
        assert_eq!(
            got,
            *expected.coeff(),
            "mismatch for message={message:?}, nonce_len={}",
            nonce.len()
        );
    }
}

#[test]
fn hash_to_point_applies_squeeze_rounds_when_n_exceeds_rate() {
    // Falcon-512 has N=512 > 1088/16=68, so at least one squeeze round is required.
    assert!(
        N > SAMPLES_PER_SQUEEZE,
        "test assumes N > rate/16; got N={N}, samples_per_squeeze={SAMPLES_PER_SQUEEZE}"
    );

    let mut preimage = vec![0u8; 40];
    preimage.extend_from_slice(b"squeeze-round check");

    let mut sampler =
        Shake256PointSampler::new(library_shake256_inject([false; 1600], preimage.clone()));

    // Consume exactly one rate block worth of 16-bit samples.
    for _ in 0..SAMPLES_PER_SQUEEZE {
        sampler.next_u16_be();
    }
    assert_eq!(
        sampler.rate_offset, SHAKE256_RATE_BITS,
        "should have consumed the full 1088-bit rate before squeezing"
    );
    assert_eq!(
        sampler.squeeze_rounds, 0,
        "no squeeze yet while still within the first rate block"
    );

    // The next sample must trigger a squeeze permutation.
    sampler.next_u16_be();
    assert_eq!(
        sampler.squeeze_rounds, 1,
        "reading past the rate must apply one squeeze round"
    );

    // Full hash_to_point for N=512 must perform multiple squeeze rounds.
    let message = b"squeeze-round check";
    let nonce = &[0u8; 40];
    let mut full_preimage = nonce.to_vec();
    full_preimage.extend_from_slice(message);
    let mut full_sampler =
        Shake256PointSampler::new(library_shake256_inject([false; 1600], full_preimage));
    let mut collected = 0usize;
    while collected < N {
        let w = full_sampler.next_u16_be();
        if w < MODULUS_THRESHOLD {
            collected += 1;
        }
    }
    assert!(
        full_sampler.squeeze_rounds() >= 1,
        "collecting {N} coeffs must require at least one squeeze round"
    );
}

#[test]
fn sampling_threshold_constants_match_falcon() {
    assert_eq!(MODULUS, 12289);
    assert_eq!(MODULUS_THRESHOLD, 61445);
    assert_eq!(
        MODULUS_THRESHOLD,
        (65536u32 / MODULUS as u32 * MODULUS as u32) as u16
    );
    assert_eq!(SAMPLES_PER_SQUEEZE, 68);
}

fn create_bit_array_match_falcon_rejection() {
    let nonce = [0u8; 40];
    let message = b"aadhaar age proof sampling alignment";
    let mut preimage = nonce.to_vec();
    preimage.extend_from_slice(message);

    let mut state = library_shake256_inject([false; 1600], preimage);
    let expected = Polynomial::from_hash_of_message(message, &nonce);

    let mut coeffs = Vec::with_capacity(N);
    while coeffs.len() < N {
        let bit_array = create_bit_array(state);
        for k in 0..68 {
            let w = shake_sample_u16(&state, 16 * k);
            assert_eq!(
                bit_array[k],
                w < MODULUS_THRESHOLD,
                "bit_array mismatch at k={k}"
            );
            if bit_array[k] && coeffs.len() < N {
                coeffs.push(w % MODULUS);
            }
        }
        state = library_step_sponge(state.to_vec(), None, SHAKE256_RATE_BITS, true);
    }

    assert_eq!(coeffs.as_slice(), expected.coeff().as_slice());
}
