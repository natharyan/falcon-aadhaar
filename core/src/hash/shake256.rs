// referenced from lurk-lab/gadget/keccak (https://github.com/lurk-lab/bellpepper-gadgets/blob/main/crates/keccak/src/lib.rs)
// modified to include shake256, variable input length, and squeezing phase of the sponge construction of keccak for variable output length.
// Bellpepper implementation of https://github.com/natharyan/arkworks-keccak/blob/main/src/constraints.rs for shake256

use bellpepper::gadgets::multipack::bytes_to_bits;
use bellpepper_core::ConstraintSystem;
use bellpepper_core::SynthesisError;
use bellpepper_core::boolean::Boolean;
use proptest::bits;
use keccak::f1600;
use sha3::{
    Digest, Keccak256, Sha3_256, Shake128, Shake256,
    digest::{ExtendableOutput, Update, XofReader},
};

use crate::gadgets::bellpepper_uint64::UInt64;
use crate::utils::{
    arr_u64_to_vec_bool, bits_to_bytes_le, bytes_to_bits_le,
    vec_bool_to_arr_u64,
};
use ff::PrimeField;

pub(crate) const SHAKE256_BLOCK_LENGTH_BITS: usize = 1088;
pub(crate) const SHAKE256_BLOCK_LENGTH_BYTES: usize = 136;
pub(crate) const SHAKE256_DIGEST_LENGTH_BYTES: usize = 200;
pub(crate) const SHAKE256_DIGEST_LENGTH_BITS: usize = 1600;

// use bellpepper_uint64 as uint64;
// use uint64::UInt64;

#[rustfmt::skip]
const ROUND_CONSTANTS: [u64; 24] = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
    0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
];
const ROTR: [usize; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

pub fn library_shake_256(input: &[u8], d: usize) -> Vec<u8> {
    let mut hasher = Shake256::default();
    hasher.update(input);
    let mut reader = hasher.finalize_xof();
    let mut result = vec![0u8; d];
    XofReader::read(&mut reader, &mut result);
    result
}

/// One step of the absorption (flag = false) or squeezing phase (flag = true)
pub(crate) fn library_step_sponge(
    mut state: Vec<bool>,
    m_i: Option<Vec<bool>>,
    r: usize,
    flag: bool,
) -> [bool; 1600] {
    // absorption step
    if !flag {
        if let Some(m_i_bits) = m_i {
            for i in 0..r {
                state[i] ^= m_i_bits[i];
            }
        } else {
            assert!(false, "Absorption step requires input message block m_i");
        }
    }
    let mut input_arr_u64 = vec_bool_to_arr_u64(&state);
    f1600(&mut input_arr_u64);
    arr_u64_to_vec_bool(&input_arr_u64)
}

fn xor_2<E, CS>(mut cs: CS, a: &UInt64, b: &UInt64) -> Result<UInt64, SynthesisError>
where
    E: PrimeField,
    CS: ConstraintSystem<E>,
{
    // a ^ b
    a.xor(cs.namespace(|| "xor_2"), b)
}

fn xor_5<E, CS>(
    mut cs: CS,
    a: &UInt64,
    b: &UInt64,
    c: &UInt64,
    d: &UInt64,
    e: &UInt64,
) -> Result<UInt64, SynthesisError>
where
    E: PrimeField,
    CS: ConstraintSystem<E>,
{
    // a ^ b ^ c ^ d ^ e
    let ab = a.xor(cs.namespace(|| "xor_5 first"), b)?;
    let abc = ab.xor(cs.namespace(|| "xor_5 second"), c)?;
    let abcd = abc.xor(cs.namespace(|| "xor_5 third"), d)?;
    abcd.xor(cs.namespace(|| "xor_5 fourth"), e)
}

fn xor_not_and<E, CS>(
    mut cs: CS,
    a: &UInt64,
    b: &UInt64,
    c: &UInt64,
) -> Result<UInt64, SynthesisError>
where
    E: PrimeField,
    CS: ConstraintSystem<E>,
{
    // a ^ ((!b) & c)
    let nb = b.not();
    let nbc = nb.and(cs.namespace(|| "xor_not_and second"), c)?;
    a.xor(cs.namespace(|| "xor_not_and third"), &nbc)
}

fn round_1600<E, CS>(mut cs: CS, a: &[UInt64], rc: u64) -> Result<Vec<UInt64>, SynthesisError>
where
    E: PrimeField,
    CS: ConstraintSystem<E>,
{
    assert_eq!(a.len(), 25);

    // # θ step
    // C[x] = A[x,0] xor A[x,1] xor A[x,2] xor A[x,3] xor A[x,4],   for x in 0…4
    let mut c = Vec::new();
    for x in 0..5 {
        let cs = &mut cs.namespace(|| format!("omega c {}", x));

        c.push(xor_5(
            cs,
            &a[x],
            &a[x + 5usize],
            &a[x + 10usize],
            &a[x + 15usize],
            &a[x + 20usize],
        )?);
    }

    // panic!("c: {:?}", c);

    // D[x] = C[x-1] xor rot(C[x+1],1),                             for x in 0…4
    let mut d = Vec::new();
    for x in 0..5 {
        let cs = &mut cs.namespace(|| format!("omega d {}", x));

        d.push(xor_2(
            cs,
            &c[(x + 4usize) % 5usize],
            &c[(x + 1usize) % 5usize].rotl(1),
        )?);
    }

    // A[x,y] = A[x,y] xor D[x],                           for (x,y) in (0…4,0…4)
    let mut a_new1 = Vec::new();
    for y in 0..5 {
        for x in 0..5 {
            let cs = &mut cs.namespace(|| format!("omega {},{}", x, y));

            a_new1.push(xor_2(cs, &a[x + (y * 5usize)], &d[x])?);
        }
    }

    // # ρ and π steps
    // B[y,2*x+3*y] = rot(A[x,y], r[x,y]),                 for (x,y) in (0…4,0…4)
    let mut b = a_new1.clone();
    for y in 0..5 {
        for x in 0..5 {
            b[y + ((((2 * x) + (3 * y)) % 5) * 5usize)] =
                a_new1[x + (y * 5usize)].rotl(ROTR[x + (y * 5usize)]);
        }
    }

    let mut a_new2 = Vec::new();

    // # χ step
    // A[x,y] = B[x,y] xor ((not B[x+1,y]) and B[x+2,y]),  for (x,y) in (0…4,0…4)
    for y in 0..5 {
        for x in 0..5 {
            let cs = &mut cs.namespace(|| format!("chi {},{}", x, y));

            a_new2.push(xor_not_and(
                cs,
                &b[x + (y * 5usize)],
                &b[((x + 1usize) % 5usize) + (y * 5usize)],
                &b[((x + 2usize) % 5usize) + (y * 5usize)],
            )?);
        }
    }

    // // # ι step
    // // A[0,0] = A[0,0] xor RC
    let rc = UInt64::constant(rc);
    a_new2[0] = a_new2[0].xor(cs.namespace(|| "xor RC"), &rc)?;

    Ok(a_new2)
}

pub(crate) fn keccak_f_1600<E, CS>(mut cs: CS, input: &[Boolean]) -> Result<Vec<Boolean>, SynthesisError>
where
    E: PrimeField,
    CS: ConstraintSystem<E>,
{
    assert_eq!(input.len(), 1600);

    let mut a = input.chunks(64).map(UInt64::from_bits).collect::<Vec<_>>();

    for (i, round_constant) in ROUND_CONSTANTS.iter().enumerate() {
        let cs = &mut cs.namespace(|| format!("keccack round {}", i));

        a = round_1600(cs, &a, *round_constant)?;
    }

    let a_new = a.into_iter().flat_map(|e| e.into_bits()).collect();
    
    Ok(a_new)
}

pub fn pad101<E, CS>(_cs: CS, input: &[Boolean]) -> Result<Vec<Boolean>, SynthesisError>
where
    E: PrimeField,
    CS: ConstraintSystem<E>,
{
    let mut padded: Vec<Boolean> = input.to_vec();
    // append 1111 for domain separation for shake256 (https://keccak.team/files/Keccak-submission-3.pdf, section 2.1.2)
    padded.push(Boolean::Constant(true));
    padded.push(Boolean::Constant(true));
    padded.push(Boolean::Constant(true));
    padded.push(Boolean::Constant(true));
    // append a single 1 bit
    padded.push(Boolean::Constant(true));
    // append K '0' bits, where K is the minimum number >= 0 such that L + 1 + K  is a multiple of r = 1088
    while (padded.len() + 1) % 1088 != 0 {
        padded.push(Boolean::Constant(false));
    }
    padded.push(Boolean::Constant(true));
    Ok(padded)
}

pub fn split_to_blocks(input: &[Boolean]) -> Result<Vec<Vec<Boolean>>, SynthesisError> {
    assert!(input.len() % 1088 == 0, "Incorrect padding");
    let blocks = input
        .chunks(1088)
        .map(|chunk: &[Boolean]| chunk.to_vec())
        .collect();
    Ok(blocks)
}

pub fn truncate(input: &[Boolean], t: usize) -> Result<Vec<Boolean>, SynthesisError> {
    assert!(input.len() >= t, "Lesser than required squeezing rounds");

    Ok(input[..t].to_vec())
}

pub fn shake256_inject<E, CS>(
    mut cs: CS,
    mut state: Vec<Boolean>,
    padded_message: Vec<Boolean>,
    r: usize,
) -> Result<Vec<Boolean>, SynthesisError>
where
    E: PrimeField,
    CS: ConstraintSystem<E>,
{
    let m_blocks: Vec<Vec<Boolean>> = split_to_blocks(&padded_message)?;
    for m_i in m_blocks.iter() {
        // expected output for a single step of absorption phase
        let state_bools = state.iter().map(|b| b.get_value().unwrap()).collect();
        let m_i_bools = m_i.iter().map(|b| b.get_value().unwrap()).collect();
        let expected_state = library_step_sponge(state_bools, Some(m_i_bools), r, false);
        for i in 0..r {
            state[i] = Boolean::xor(
                cs.namespace(|| format!("absorb block bit {}", i)),
                &state[i],
                &m_i[i],
            )?;
        }
        let cs = &mut cs.namespace(|| format!("keccack round in absorption phase"));
        state = keccak_f_1600(cs, &state)?;
        for (o, &i) in state.iter().zip(expected_state.iter()) {
            assert_eq!(o.get_value().unwrap(), i, "keccak step mismatch!!");
        }
    }
    Ok(state)
}

// TODO: make state a pair of vec<boolean> and pointer which tracks how many bits have been extracted and use it to reset the state using the keccak permutation
pub fn shake256_extract<E, CS>(
    mut cs: CS,
    mut state: Vec<Boolean>,
    r: usize,
    d: usize,
) -> Result<Vec<Boolean>, SynthesisError>
where
    E: PrimeField,
    CS: ConstraintSystem<E>,
{
    let mut z: Vec<Boolean> = Vec::new();
    z.extend(truncate(&state, r)?);
    while z.len() < d {
        // expected output for single step of squeezing phase
        // let expected_state = library_step_sponge(cs, state.clone(), None, r, true)?;
        let cs = &mut cs.namespace(|| format!("keccack round in squeezing phase"));
        state = keccak_f_1600(cs, &state)?;
        // for (o, i) in state.iter().zip(expected_state.iter()) {
        //     assert_eq!(
        //         o.value().unwrap(),
        //         i.value().unwrap(),
        //         "keccak step mismatch!!"
        //     );
        // }
        z.extend(truncate(&state, r)?);
    }

    z = truncate(&z, d)?;

    Ok(z)
}

pub(crate) fn shake256_msg_blocks(input: Vec<u8>) -> Vec<[u8; SHAKE256_BLOCK_LENGTH_BYTES]> {
    let mut padded: Vec<bool> = bytes_to_bits_le(&input);
    // append 1111 for domain separation for shake256 (https://keccak.team/files/Keccak-submission-3.pdf, section 2.1.2)
    padded.push(true);
    padded.push(true);
    padded.push(true);
    padded.push(true);
    // append a single 1 bit
    padded.push(true);
    // append K '0' bits, where K is the minimum number >= 0 such that L + 1 + K  is a multiple of r = 1088
    while (padded.len() + 1) % 1088 != 0 {
        padded.push(false);
    }
    padded.push(true);
    let padded_bytes: Vec<u8> = bits_to_bytes_le(&padded);
    padded_bytes
        .chunks(SHAKE256_BLOCK_LENGTH_BYTES)
        .map(|chunk| chunk.try_into().unwrap())
        .collect()
}

pub fn shake256_gadget<E, CS>(
    mut cs: CS,
    preimage_bits: &[Boolean],
    d: usize,
) -> Result<Vec<Boolean>, SynthesisError>
where
    E: PrimeField,
    CS: ConstraintSystem<E>,
{
    let r: usize = 1088;
    let padded: Vec<Boolean> =
        pad101(&mut cs.namespace(|| "shake256 padding"), &preimage_bits).unwrap();
    assert!(padded.len() % r == 0, "Incorrect padding");

    // Absorbing phase
    // Initialization
    let mut state: Vec<Boolean> = vec![Boolean::Constant(false); 1600];
    state = shake256_inject(&mut cs.namespace(|| "shake256 injection"), state, padded, r)?;

    // Squeezing phase
    let z = shake256_extract(&mut cs.namespace(|| "shake256 extraction"), state, r, d)?;
    Ok(z)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::utils::{bits_to_bytes_le, shake_256};
    use bellpepper_core::boolean::AllocatedBit;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use pasta_curves::Fp;
    #[test]
    fn test_keccak_f_1600() {
        let mut cs = TestConstraintSystem::<Fp>::new();

        // dummy test input
        let input: Vec<Boolean> = (0..1600)
            .map(|i| {
                Boolean::from(
                    AllocatedBit::alloc(cs.namespace(|| format!("input bit {}", i)), Some(false))
                        .unwrap(),
                )
            })
            .collect();

        let _output = keccak_f_1600::<Fp, _>(cs.namespace(|| "keccak_f_1600"), &input).unwrap();

        if !cs.is_satisfied() {
            println!("Unsatisfied constraint: {:?}", cs.which_is_unsatisfied());
        }
        assert!(cs.is_satisfied(), "Constraint system is not satisfied!");

        println!("keccak_f_1600 constraints: {}", cs.num_constraints());
    }

    #[test]
    fn test_shake256_gadget() {
        let preimage: Vec<u8> = b"hello world".to_vec();
        let preimage_length = preimage.len();

        let d: usize = 16;

        // add 7 to get ceil of quotient
        let expected_bytes = shake_256(&preimage, (d + 7) / 8);
        let expected_bits = bytes_to_bits_le(&expected_bytes);

        let preimage_bits: Vec<bool> = bytes_to_bits_le(&preimage);

        println!(
            "Input length: {} bits ({} bytes)",
            preimage_bits.len(),
            preimage_length
        );
        println!("Output length: {} bits", d);

        let mut cs = TestConstraintSystem::<Fp>::new();

        let preimage_bools: Vec<Boolean> = preimage_bits
            .iter()
            .enumerate()
            .map(|(i, &bit)| {
                Boolean::from(
                    AllocatedBit::alloc(cs.namespace(|| format!("preimage bit {}", i)), Some(bit))
                        .unwrap(),
                )
            })
            .collect();

        let result = shake256_gadget(cs.namespace(|| "shake256"), &preimage_bools, d).unwrap();

        println!("Result length: {} bits", result.len());
        assert_eq!(result.len(), d, "Output size mismatch!");

        let result_bits: Vec<bool> = result.iter().map(|b| b.get_value().unwrap()).collect();
        let result_bytes = bits_to_bytes_le(&result_bits);

        let expected_truncated: Vec<bool> = expected_bits.iter().take(d).cloned().collect();

        println!("Expected hash: {:?}", hex::encode(&expected_bytes));
        println!("Actual hash: {:?}", hex::encode(&result_bytes));

        for (i, (r, e)) in result_bits
            .iter()
            .zip(expected_truncated.iter())
            .enumerate()
        {
            assert_eq!(r, e, "Mismatch at bit {}", i);
        }

        if !cs.is_satisfied() {
            println!("Unsatisfied constraint: {:?}", cs.which_is_unsatisfied());
        }
        assert!(cs.is_satisfied(), "Constraint system is not satisfied!");

        println!("SHAKE256 test PASSED!");
        println!("Number of constraints: {}", cs.num_constraints());
    }
}
