use core::hash;
use std::{ops::Mul,cmp::max};
use bellpepper::gadgets::multipack::{bytes_to_bits, compute_multipacking, pack_bits};
use bellpepper_core::{
    ConstraintSystem, LinearCombination, SynthesisError,
    boolean::{AllocatedBit, Boolean},
    num::AllocatedNum,
    test_cs::TestConstraintSystem,
};
use bellpepper_nonnative::{
    mp::bignat::{BigNat, nat_to_limbs},
    util::{bit::Bit, gadget::Gadget, num::Num},
};

use bitvec::vec;
use falcon_rust::{KeyPair, LOG_N, MODULUS, N, NTTPolynomial, Polynomial, PublicKey, SIG_L2_BOUND, Signature};
use ff::{PrimeField, PrimeFieldBits};
use nova_snark::traits::circuit::StepCircuit;
use num_bigint::{BigInt, Sign};
use sha2::{compress256, digest::generic_array::GenericArray};

use keccak::f1600;

use nova_aadhaar_qr::{
    poseidon::PoseidonHasher,
    util::{
        alloc_constant, alloc_num_equals, alloc_num_equals_constant, bignat_to_allocatednum_limbs,
        boolean_implies, check_decomposition, conditionally_select,
        conditionally_select_boolean_vec, conditionally_select_vec, less_than_or_equal,
        num_to_bits,less_than
    },
};

use crate::{
    dob::{
        DOB_INDEX_BIT_LENGTH, calculate_age_in_years,
        delimiter_count_before_and_within_dob_is_correct, get_day_month_year_conditional,
        left_shift_bytes,
    }, 
    hash::shake256::{
        SHAKE256_BLOCK_LENGTH_BITS, SHAKE256_BLOCK_LENGTH_BYTES, SHAKE256_DIGEST_LENGTH_BITS, SHAKE256_DIGEST_LENGTH_BYTES, keccak_f_1600, library_shake256_inject, library_step_sponge, shake256_gadget, shake256_inject, shake256_msg_blocks, shake256_pad101
    }, 
    ntt::{inv_ntt, inv_ntt_deferred_circuit, ntt, ntt_deferred_circuit, ntt_mult_const_p2}, 
    qr::{AadhaarQRData, parse_aadhaar_qr_data}, 
    subarray::var_shift_left, 
    utils::{bits_to_bytes_le, bytes_to_bits_le, enforce_less_than_norm_bound, 
        mod_q, normalize_coeff, normalize_half_q, num_to_alloc}
};

// pub const NUM_OPCODE_BITS: usize = 6; // 1 MSB for SHA256 + 5 LSBs for RSA
// pub const NUM_RSA_OPCODE_BITS: u64 = 5;
// pub const RSA_OPCODE_MASK: u64 = (1 << NUM_RSA_OPCODE_BITS) - 1;
// pub const OP_SHA256_ACTIVE: u64 = 0;
// pub const OP_SHA256_NOOP: u64 = 1;
// pub const OP_RSA_FIRST: u64 = 0;
// pub const OP_RSA_LAST: u64 = 16;
// pub const OP_CODE_LAST: u64 = (OP_SHA256_NOOP << NUM_RSA_OPCODE_BITS) + OP_RSA_LAST;

pub const NUM_OPCODE_BITS: usize = 10; // 1 MSB for SHAKE256 + 9 LSBs for COEFF_INDEX
pub const NUM_COEFF_INDEX_BITS: u64 = 9;
pub const COEFF_INDEX_MASK: u64 = (1 << NUM_COEFF_INDEX_BITS) - 1;
pub const OP_SHAKE256_ACTIVE: u64 = 0;
pub const OP_SHAKE256_NO_OP: u64 = 1;
pub const OP_COEFF_INDEX_FIRST: u64 = 0;
pub const OP_COEFF_INDEX_LAST: u64 = 511;
pub const OP_CODE_LAST: u64 = (OP_SHAKE256_NO_OP << NUM_COEFF_INDEX_BITS) + OP_COEFF_INDEX_LAST;
pub const L2_NORM_INIT: u64 = 0;

const DATE_LENGTH_BYTES: usize = 10;
const TIMESTAMP_START_BYTE_INDEX: usize = 9;
const NAME_START_BYTE_INDEX: usize = 27;

#[derive(Clone, Debug)]
pub struct AadhaarAgeProofCircuit<Scalar>
where
    Scalar: PrimeField,
{
    opcode: u64,
    next_opcode: u64,
    msg: [u8; SHAKE256_BLOCK_LENGTH_BYTES],
    dob_byte_index: usize,
    l2_norm_sum: u64,
    ctx_absorb: [bool; SHAKE256_DIGEST_LENGTH_BITS],
    ctx_inject: [bool; SHAKE256_DIGEST_LENGTH_BITS],
    shake_inject_m_block: Scalar,
    s2: Polynomial,
    c: Polynomial,
    hash_c: Scalar,
    h: Polynomial,
    current_nullifier: Scalar,
}

impl<Scalar> Default for AadhaarAgeProofCircuit<Scalar>
where
    Scalar: PrimeField,
{
    fn default() -> Self {
        Self {
            opcode: 0u64,
            next_opcode: 0u64,
            msg: [0u8; SHAKE256_BLOCK_LENGTH_BYTES],
            dob_byte_index: 0,
            l2_norm_sum: 0u64,
            ctx_absorb: [false; SHAKE256_DIGEST_LENGTH_BITS],
            ctx_inject: [false; SHAKE256_DIGEST_LENGTH_BITS],
            hash_c: Scalar::default(),
            shake_inject_m_block: Scalar::default(),
            c: Polynomial::default(),
            s2: Polynomial::default(),
            current_nullifier: Scalar::default(),
            h: Polynomial::default(),
        }
    }
}

impl<Scalar> AadhaarAgeProofCircuit<Scalar>
where
    Scalar: PrimeFieldBits,
{
    fn update_nullifier(prev_nullifier: Scalar, l2_norm_sum: u64, ctx_absorb: [bool; SHAKE256_DIGEST_LENGTH_BITS], msg_blocks: &Vec<[u8; 136]>) -> Scalar {
        let ctx_inject = library_shake256_inject([false; 1600], msg_blocks.iter().flatten().cloned().collect());
        let ctx_inject_scalars = ctx_inject.iter().map(|&b| if b {Scalar::from(1u64)} else {Scalar::from(0u64)}).collect::<Vec<Scalar>>();
        let ctx_absorb_scalars = ctx_absorb.iter().map(|&b| if b {Scalar::from(1u64)} else {Scalar::from(0u64)}).collect::<Vec<Scalar>>();
        let mut absorb_inject_norm_preimage = ctx_inject_scalars.clone();
        absorb_inject_norm_preimage.push(Scalar::from(l2_norm_sum));
        absorb_inject_norm_preimage.extend(ctx_absorb_scalars);
        absorb_inject_norm_preimage.push(prev_nullifier);
        let hasher_inject_norm = PoseidonHasher::<Scalar>::new(absorb_inject_norm_preimage.len() as u32);
        let next_nullifier = hasher_inject_norm.hash(&absorb_inject_norm_preimage);

        // let absorb_inject_norm_preimage_vars: Vec<AllocatedNum<Scalar>> = absorb_inject_norm_preimage.iter().enumerate().map(|(i, &x)| {
        //     AllocatedNum::alloc(cs.namespace(|| format!("absorb_inject_norm_preimage {}", i)), || Ok(x))
        // }).collect::<Result<Vec<AllocatedNum<Scalar>>, SynthesisError>>()?;
        // let hash_absorb_inject_norm = hasher_inject_norm.hash_in_circuit(
        //     &mut cs.namespace(|| "poseidon hash ctx_inject"),
        //     &absorb_inject_norm_preimage_vars,
        // )?;

        // let msg_blocks_bits = bytes_to_bits(msg_blocks);
        // let mut msg_block_scalars = compute_multipacking::<Scalar>(&msg_blocks_bits);
        // msg_block_scalars.insert(0, prev_nullifier);
        // let nullifier_hasher = PoseidonHasher::new(msg_block_scalars.len() as u32);
        // let next_nullifier = nullifier_hasher.hash(&msg_block_scalars);
        next_nullifier
    }

    pub fn calc_initial_primary_circuit_input(current_date_bytes: &[u8], msg: &Vec<u8>, sig: &Signature) -> Vec<Scalar> {
        let initial_opcode = Scalar::from((OP_SHAKE256_ACTIVE << NUM_OPCODE_BITS) + OP_COEFF_INDEX_FIRST);

        let padded_msg = shake256_pad101(msg);
        let padded_msg_bytes = bits_to_bytes_le(&padded_msg);
        
        let ctx_inject: [bool; 1600] = library_shake256_inject([false; 1600], msg.to_vec());
        // let ctx_inject_scalars = ctx_inject.iter().map(|&x| Scalar::from(x as u64)).collect::<Vec<Scalar>>();
        // let absorb_inject_norm_hasher = PoseidonHasher::<Scalar>::new(ctx_inject_scalars.len() as u32);
        // let mut inject_norm_preimage = ctx_inject_scalars.clone();
        // inject_norm_preimage.push(Scalar::from(0u64)); // initial l2 norm sum is 0
        // inject_norm_preimage.extend(vec![Scalar::from(0u64); 1600]); // initial ctx_absorb is [false; 1600]
        // let hash_absorb_inject_norm: Scalar = absorb_inject_norm_hasher.hash(&inject_norm_preimage);

        let shake_inject_m_scalars = compute_multipacking::<Scalar>(&ctx_inject);
        let current_date_bits = bytes_to_bits(current_date_bytes);
        let current_date_scalars = compute_multipacking::<Scalar>(&current_date_bits);
        assert_eq!(current_date_scalars.len(), 1);
        let current_date_scalar = current_date_scalars[0];

        let c: Vec<u16> = Polynomial::from_hash_of_message(msg.as_ref(), sig.nonce()).coeff().iter().map(|x| *x as u16).collect::<Vec<u16>>().try_into().unwrap();
        let c_scalars: Vec<Scalar> = c.iter().map(|&x| Scalar::from(x as u64)).collect();
        let c_hasher = PoseidonHasher::<Scalar>::new(c_scalars.len() as u32);
        let hash_c = c_hasher.hash(&c_scalars);
        // vec![initial_opcode, current_date_scalar]

        // The last scalar corresponds to the current date
        vec![initial_opcode, hash_c, shake_inject_m_scalars[0], current_date_scalar]
    }

    pub fn new_state_sequence(
        aadhaar_qr_data: &AadhaarQRData,
        sig: &Signature,
        pk: PublicKey,
    ) -> Vec<AadhaarAgeProofCircuit<Scalar>> {
            
        let mut aadhaar_steps = vec![];
        
        let msg = aadhaar_qr_data.signed_data.clone();
        let msg_blocks: Vec<[u8; 136]> = shake256_msg_blocks(&msg);

        let mut prev_nullifier = Scalar::ZERO;

        let first_opcode = (OP_SHAKE256_ACTIVE << NUM_OPCODE_BITS) + OP_COEFF_INDEX_FIRST;
        let first_next_opcode = if msg_blocks.len() == 1 {
            (OP_SHAKE256_NO_OP << NUM_OPCODE_BITS) + (OP_COEFF_INDEX_FIRST) + 64
        } else {
            first_opcode + 64
        };

        let s2: Polynomial = sig.into();
        let c: Polynomial = Polynomial::from_hash_of_message(msg.as_ref(), sig.nonce());
        let pk_poly: Polynomial = (&pk).into();

        let shake_inject_m = library_shake256_inject([false; 1600], msg.clone());
        let shake_inject_m_scalars = compute_multipacking::<Scalar>(&shake_inject_m);
        assert_eq!(shake_inject_m_scalars.len(), 7);

        let c_scalars: Vec<Scalar> = c.coeff().iter().map(|&x| Scalar::from(x as u64)).collect();
        let c_hasher = PoseidonHasher::<Scalar>::new(c_scalars.len() as u32);
        let hash_c = c_hasher.hash(&c_scalars);
        
        let mut coeff_index: u64 = 0;

        // TODO add consistency check between ctx_inject and shake_inject_m_block
        // option 1) use num_to_bits on shake_inject_m and convert bytes in ctx_inject to bits and compare using groups indexed using coeff_index/68
        // option 2) or use bellpepper::gadgets::pack_bits to convert ctx_inject bits to scalars
        let mut ctx_absorb = [false; 1600];
        let ctx_inject: [bool; SHAKE256_DIGEST_LENGTH_BITS] = shake_inject_m.clone();
        assert_eq!(ctx_inject.len(), SHAKE256_DIGEST_LENGTH_BITS as usize);
        let mut l2_norm_sum = 0u64;
        
        // First step
        aadhaar_steps.push(Self {
            opcode: first_opcode,
            next_opcode: first_next_opcode,
            msg: msg_blocks[0],
            dob_byte_index: aadhaar_qr_data.dob_byte_index,
            l2_norm_sum: l2_norm_sum,
            ctx_absorb: ctx_absorb.clone(),
            ctx_inject: ctx_inject.clone(),
            s2: s2.clone(),
            current_nullifier: prev_nullifier,
            h: pk_poly.clone(),
            hash_c: hash_c,
            shake_inject_m_block: shake_inject_m_scalars[0],
            c: c.clone(),
        });

        let msg_block_without_timestamp: [u8; SHAKE256_BLOCK_LENGTH_BYTES] = [
            &msg_blocks[0][0..TIMESTAMP_START_BYTE_INDEX],
            &[0u8; NAME_START_BYTE_INDEX - TIMESTAMP_START_BYTE_INDEX],
            &msg_blocks[0][NAME_START_BYTE_INDEX..],
        ]
        .concat()
        .try_into()
        .unwrap();

        prev_nullifier = Self::update_nullifier(prev_nullifier, l2_norm_sum, ctx_absorb, &msg_blocks);

        // compress256(
        //     &mut sha256_state,
        //     &[*GenericArray::from_slice(&sha256_msg_blocks[0])],
        // );
        // compress256(
        //     &mut sha256_state,
        //     &[*GenericArray::from_slice(&sha256_msg_blocks[1])],
        // );

        let num_blocks = msg_blocks.len();
        println!("Number of SHAKE256 blocks: {}", num_blocks);
        let num_steps = max(num_blocks, 8);

        let ntt_s2: NTTPolynomial = ntt(&s2);
        let ntt_h: NTTPolynomial = ntt(&pk_poly);
        let ntt_s2h: NTTPolynomial = ntt_s2.mul(ntt_h);
        let prod_s2h: Polynomial = inv_ntt(&ntt_s2h);

        let mut opcode = first_opcode + 64;
        for i in 1..num_steps {
            let mut sum_aggregated = 0u64;
            for k in 0..64 {
                let flag_coeff_c_less_2h = if c.coeff()[coeff_index as usize] < prod_s2h.coeff()[coeff_index as usize] {true} else {false};
                // coefficients of both c and prod_s2h are already modulo q.
                let c_lt_s2h = c.coeff()[coeff_index as usize] + MODULUS - prod_s2h.coeff()[coeff_index as usize];
                let s1_coeff = if flag_coeff_c_less_2h {c_lt_s2h} else {c.coeff()[coeff_index as usize] - prod_s2h.coeff()[coeff_index as usize]};
                let s1_normalized = normalize_coeff(s1_coeff as i64);
                let s2_normalized = normalize_coeff(s2.coeff()[coeff_index as usize] as i64);
                sum_aggregated = sum_aggregated + s1_normalized * s1_normalized + s2_normalized * s2_normalized;
                if sum_aggregated >= SIG_L2_BOUND {
                    panic!("L2 norm exceeded SIG_L2_BOUND at coeff {}: {}", coeff_index, sum_aggregated);
                }
                coeff_index = coeff_index + 1u64;
            }
            
            l2_norm_sum = l2_norm_sum + sum_aggregated;
            if l2_norm_sum >= SIG_L2_BOUND as u64 {
                panic!("L2 norm exceeded SIG_L2_BOUND at coeff {}: {}", i, l2_norm_sum);
            }
            
            ctx_absorb = library_step_sponge(ctx_absorb.to_vec(), Some(bytes_to_bits_le(&msg_blocks[i % num_blocks])), 1088, false);

            let next_opcode = if i < num_blocks - 1 {
                (OP_SHAKE256_ACTIVE << NUM_OPCODE_BITS) + coeff_index
            } else {
                (OP_SHAKE256_NO_OP << NUM_OPCODE_BITS) + coeff_index
            };

            aadhaar_steps.push(Self {
                opcode: opcode,
                next_opcode: next_opcode,
                msg: msg_blocks[i % num_blocks],
                dob_byte_index: aadhaar_qr_data.dob_byte_index,
                l2_norm_sum: l2_norm_sum,
                ctx_absorb: ctx_absorb.clone(),
                ctx_inject: ctx_inject.clone(),
                s2: s2.clone(),
                current_nullifier: prev_nullifier,
                h: pk_poly.clone(),
                hash_c: hash_c,
                c: c.clone(),
                shake_inject_m_block: shake_inject_m_scalars[i % shake_inject_m_scalars.len()],
            });

            opcode = next_opcode;
            
            prev_nullifier = Self::update_nullifier(prev_nullifier, l2_norm_sum, ctx_absorb, &msg_blocks);
            
        }

        aadhaar_steps
    }
}

impl<Scalar> StepCircuit<Scalar> for AadhaarAgeProofCircuit<Scalar>
where
    Scalar: PrimeFieldBits + PartialOrd,
{
    fn arity(&self) -> usize {
        4
    }

    fn synthesize<CS: ConstraintSystem<Scalar>>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<Scalar>],
    ) -> Result<Vec<AllocatedNum<Scalar>>, SynthesisError> {
        let opcode = &z[0];
        let hash_c = &z[1];
        let shake_inject_m_block = &z[2];
        let nullifier = &z[3];

        let msg = self.msg;
        let msg_bits = bytes_to_bits_le(&msg);
        let msg_vars: Vec<Boolean> = msg_bits
            .iter()
            .enumerate()
            .map(|(i, &b)| -> Result<Boolean, SynthesisError> {
                Ok(Boolean::from(AllocatedBit::alloc(
                    cs.namespace(|| format!("msg bit {i}")),
                    Some(b),
                )?))
            })
            .collect::<Result<Vec<Boolean>, SynthesisError>>()?;

        // allocate bit for next_shake_opcode using Boolean and self.next_shake_opcode
        let next_opcode = AllocatedNum::alloc(cs.namespace(|| "next opcode"), || Ok(Scalar::from(self.next_opcode)))?;
        let mut l2_norm_sum = AllocatedNum::alloc(cs.namespace(|| "L2 norm sum"), || Ok(Scalar::from(self.l2_norm_sum)))?;
        
        let next_opcode_bits_le = num_to_bits(cs.namespace(|| "Decompose next opcode"), &next_opcode, NUM_OPCODE_BITS)?;
        let next_shake_opcode = next_opcode_bits_le[NUM_COEFF_INDEX_BITS as usize].clone();

        // TODO add io_hash consistency check
        let ctx_inject = self.ctx_inject;
        let ctx_inject_scalars = ctx_inject.iter().map(|&b| if b {Scalar::from(1u64)} else {Scalar::from(0u64)}).collect::<Vec<Scalar>>();
        let ctx_inject_vars: Vec<Boolean> = ctx_inject
            .iter()
            .enumerate()
            .map(|(i, &b)| -> Result<Boolean, SynthesisError> {
                Ok(Boolean::from(AllocatedBit::alloc(
                    cs.namespace(|| format!("ctx_inject bit {i}")),
                    Some(b),
                )?))
            })
            .collect::<Result<Vec<Boolean>, SynthesisError>>()?;
        
        let ctx_absorb = self.ctx_absorb;
        let ctx_absorb_scalars = ctx_absorb.iter().map(|&b| if b {Scalar::from(1u64)} else {Scalar::from(0u64)}).collect::<Vec<Scalar>>();
        let mut ctx_absorb_vars: Vec<Boolean> = ctx_absorb
            .iter()
            .enumerate()
            .map(|(i, &b)| -> Result<Boolean, SynthesisError> {
                Ok(Boolean::from(AllocatedBit::alloc(
                    cs.namespace(|| format!("ctx_absorb bit {i}")),
                    Some(b),
                )?))
            })
            .collect::<Result<Vec<Boolean>, SynthesisError>>()?;
        
        let mut absorb_inject_norm_preimage = ctx_inject_scalars.clone();
        absorb_inject_norm_preimage.push(Scalar::from(self.l2_norm_sum));
        absorb_inject_norm_preimage.extend(ctx_absorb_scalars);
        absorb_inject_norm_preimage.push(self.current_nullifier);
        let hasher_inject_norm = PoseidonHasher::<Scalar>::new(absorb_inject_norm_preimage.len() as u32);
        // TODO Cannot directly allocate variables here without constraining them to already constrained variables: ctx_inject_vars, ctx_absorb_vars, the l2_norm_sum . Add allocatednum vec to Boolean vec consistency add
        let absorb_inject_norm_preimage_vars: Vec<AllocatedNum<Scalar>> = absorb_inject_norm_preimage.iter().enumerate().map(|(i, &x)| {
            AllocatedNum::alloc(cs.namespace(|| format!("absorb_inject_norm_preimage {}", i)), || Ok(x))
        }).collect::<Result<Vec<AllocatedNum<Scalar>>, SynthesisError>>()?;
        let hash_absorb_inject_norm = hasher_inject_norm.hash_in_circuit(
            &mut cs.namespace(|| "poseidon hash ctx_inject"),
            &absorb_inject_norm_preimage_vars,
        )?;

        // enforce equality between Hpos_inject_norm and hash_inject_norm if not in the 
        // cs.enforce(
        //     || "enforce hash of ctx_inject equals hash_inject",
        //     |lc| lc + hash_absorb_inject_norm.get_variable(),
        //     |lc| lc + CS::one(),
        //     |lc| lc + nullifier.get_variable(),
        // );

        let s2 = self.s2;
        let c = self.c;

        let s2_scalars = s2.coeff().iter().map(|&x| Scalar::from(x as u64)).collect::<Vec<Scalar>>();
        let c_scalars = c.coeff().iter().map(|&x| Scalar::from(x as u64)).collect::<Vec<Scalar>>();
        // let h_scalars = h.coeff().iter().map(|&x| Scalar::from(x as u64)).collect::<Vec<Scalar>>();
        
        let s2_vars = s2_scalars.iter().enumerate().map(|(i,&x)| {
            AllocatedNum::alloc(cs.namespace(|| format!("alloc s2 coefficient {}", i)), || {Ok(x)})
        }).collect::<Result<Vec<AllocatedNum<Scalar>>, SynthesisError>>()?;
        let c_vars = c_scalars.iter().enumerate().map(|(i,&x)| {
            AllocatedNum::alloc(cs.namespace(|| format!("alloc c coefficient {}", i)), || {Ok(x)})
        }).collect::<Result<Vec<AllocatedNum<Scalar>>, SynthesisError>>()?;
        
        // check that opcode fits in 10 bits
        let opcode_bits_le =
            num_to_bits(cs.namespace(|| "Decompose opcode"), opcode, NUM_OPCODE_BITS)?;
        let current_shake_opcode = opcode_bits_le[NUM_COEFF_INDEX_BITS as usize].clone();
        let coeff_index_bits_le = opcode_bits_le[..NUM_COEFF_INDEX_BITS as usize].to_vec();

        let mut coeff_index = AllocatedNum::alloc(cs.namespace(|| "RSA opcode"), || {
            Ok(Scalar::from(self.opcode & COEFF_INDEX_MASK))
        })?;

        // check allocated RSA opcode matches with input opcode bits
        check_decomposition(
            cs.namespace(|| "check RSA opcode allocation"),
            &coeff_index,
            coeff_index_bits_le,
        )?;

        // TODO add range and consistency checks for opcodes
        // // check that next opcode fits in 6 bits
        // let next_opcode_bits_le = num_to_bits(
        //     cs.namespace(|| "Decompose next opcode"),
        //     &next_opcode,
        //     NUM_OPCODE_BITS,
        // )?;
        // let next_sha256_opcode = next_opcode_bits_le[NUM_RSA_OPCODE_BITS as usize].clone();
        // let next_rsa_opcode_bits_le = next_opcode_bits_le[..NUM_RSA_OPCODE_BITS as usize].to_vec();

        // let next_rsa_opcode = AllocatedNum::alloc(cs.namespace(|| "next RSA opcode"), || {
        //     Ok(Scalar::from(self.next_opcode & RSA_OPCODE_MASK))
        // })?;

        // // check allocated next RSA opcode matches with input opcode bits
        // check_decomposition(
        //     cs.namespace(|| "check next RSA opcode allocation"),
        //     &next_rsa_opcode,
        //     next_rsa_opcode_bits_le,
        // )?;

        // // Constraints related to the opcode inputs
        // cs.enforce(
        //     || "next RSA opcode is always one more than current RSA opcode",
        //     |lc| lc + next_rsa_opcode.get_variable(),
        //     |lc| lc + CS::one(),
        //     |lc| lc + CS::one() + rsa_opcode.get_variable(),
        // );

        // once shake256_opcode is 1, next_shake_opcode must be 1 as well
        boolean_implies(
            cs.namespace(|| "next SHA256 opcode is identical or one more"),
            &current_shake_opcode,
            &next_shake_opcode,
        )?;

        let flag_first_step = alloc_num_equals_constant(
            cs.namespace(|| "first step flag"),
            &coeff_index,
            Scalar::from(OP_COEFF_INDEX_FIRST),
        )?;
        
        let flag_absorb_last_step = Boolean::and(
            cs.namespace(|| "absorb last step flag"),
            &current_shake_opcode.not(),
            &next_shake_opcode,
        )?;
        
        // enforce flag_first_step => l2_norm_sum = 0 and ctx_absorb = [0; 1600]
        let flag_l2norm_init = alloc_num_equals_constant(
            cs.namespace(|| "L2 norm init flag"),
            &l2_norm_sum,
            Scalar::from(L2_NORM_INIT),
        )?;

        let mut any_one = Boolean::Constant(false);
        for (i, b) in ctx_absorb_vars.iter().enumerate() {
            any_one = Boolean::or(cs.namespace(|| format!("ctx_absorb_any_one_{i}")), &any_one, b)?;
        }
        let flag_absorb_init = any_one.not();
        
        let is_init_absorb = Boolean::or(
            cs.namespace(|| "initial absorb step flag"),
            &flag_first_step.not(),
            &flag_absorb_init,
        )?;
        let is_init_norm = Boolean::or(
            cs.namespace(|| "initial norm step flag"),
            &flag_first_step.not(),
            &flag_l2norm_init,
        )?;
        
        let flag_is_initialized = Boolean::and(
            cs.namespace(|| "is initialized flag"),
            &is_init_absorb,
            &is_init_norm,
        )?;
        // enforce flag_absorb_init and flag_l2norm_init to be true if flag_first_step is true
        Boolean::enforce_equal(
            cs.namespace(|| "enforce is initialized"),
            &flag_is_initialized,
            &Boolean::Constant(true),
        )?;

        let c_hasher = PoseidonHasher::<Scalar>::new(c_vars.len() as u32);
        let hpos_c = c_hasher.hash_in_circuit(
            &mut cs.namespace(|| "poseidon hash c coefficients"),
            &c_vars,
        )?;
        cs.enforce(
            || "enforce hash of c equals hash_c",
            |lc| lc + hpos_c.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + hash_c.get_variable(),
        );

        let current_nullifier = AllocatedNum::alloc(cs.namespace(|| "current nullifier"), || Ok(self.current_nullifier))?;
        let nullifier_equal = alloc_num_equals(cs.namespace(|| "nullifier consistency check"), &current_nullifier, nullifier)?;
        boolean_implies(
            cs.namespace(|| "not first step implies nullifier consistency check"),
            &flag_first_step.not(),
            &nullifier_equal,
        )?;

        // No range check needed for c as it configured is a public input
        let s2_lshifted = var_shift_left(cs.namespace(|| "var_shift_left s2"), &s2_vars, &coeff_index, N, LOG_N)?;
        let c_lshifted = var_shift_left(cs.namespace(|| "var_shift_left c"), &c_vars, &coeff_index, N, LOG_N)?;
        let s2_subarray64 = s2_lshifted.iter().take(64).cloned().collect::<Vec<AllocatedNum<Scalar>>>();
        let c_subarray64 = c_lshifted.iter().take(64).cloned().collect::<Vec<AllocatedNum<Scalar>>>();

        let mut sum_aggregated = alloc_constant(cs.namespace(|| "alloc_constant sum_aggregated = 0"), Scalar::from(0u64))?;
        let ntt_s2 = ntt_deferred_circuit(cs.namespace(|| "ntt_deferred_circuit s2"), &s2_vars)?;
        let ntt_h = ntt(&self.h);
        let ntt_s2h = ntt_mult_const_p2(cs.namespace(|| "ntt_mult_const_p2"), ntt_s2, ntt_h)?;
        let prod_s2h = inv_ntt_deferred_circuit(cs.namespace(|| "inv_ntt_deferred_circuit s2h"), ntt_s2h)?;
        let prod_s2h = prod_s2h
            .iter().enumerate()
            .map(|(i, x)| num_to_alloc(cs.namespace(|| format!("alloc prod_s2h coeff {}", i)), &x))
            .collect::<Result<Vec<AllocatedNum<Scalar>>, SynthesisError>>()?;
        let prod_s2h_lshifted = var_shift_left(cs.namespace(|| "var_shift_left prod_s2h"), &prod_s2h, &coeff_index, N, LOG_N)?;
        let prod_s2h_subarray64 = prod_s2h_lshifted.iter().take(64).cloned().collect::<Vec<AllocatedNum<Scalar>>>();
        // reduce each coefficient mod q
        let prod_s2h_subarray64_modq = prod_s2h_subarray64.iter().enumerate().map(|(i, x)| {
            let reduced = mod_q(cs.namespace(|| format!("mod_q prod_s2h coeff_{}", i)), x)?;
            Ok(reduced)
        }).collect::<Result<Vec<AllocatedNum<Scalar>>, SynthesisError>>()?;

        let var1 = alloc_constant(cs.namespace(|| "alloc_constant 1"), Scalar::from(1u64))?;

        for k in 0..64 {
            // constraint s1_coeff
            let flag_coeff_c_less_s2h = less_than(
                cs.namespace(|| format!("flag_coeff_c_less_s2h_{}", k)),
                &c_subarray64[k],
                &prod_s2h_subarray64_modq[k],
                14,
            )?;
            let c_lt_s2h = AllocatedNum::alloc(cs.namespace(|| format!("c_lt_s2h_{}", k)), || {
                let c_coeff_val = c_subarray64[k]
                    .get_value()
                    .ok_or(SynthesisError::AssignmentMissing)?;
                let prod_s2h_coeff_val = prod_s2h_subarray64_modq[k]
                    .get_value()
                    .ok_or(SynthesisError::AssignmentMissing)?;
                Ok(c_coeff_val + Scalar::from(MODULUS as u64) - prod_s2h_coeff_val)
            })?;
            cs.enforce(
                || format!("c_lt_s2h = c_coeff + q - prod_s2h_coeff_{}", k),
                |lc| lc + c_lt_s2h.get_variable() + prod_s2h_subarray64_modq[k].get_variable(),
                |lc| lc + CS::one(),
                |lc| lc + c_subarray64[k].get_variable() + (Scalar::from(MODULUS as u64), CS::one()),
            );
            let c_minus_s2h = AllocatedNum::alloc(cs.namespace(|| format!("c_minus_s2h_{}", k)), || {
                let c_coeff_val = c_subarray64[k]
                    .get_value()
                    .ok_or(SynthesisError::AssignmentMissing)?;
                let prod_s2h_coeff_val = prod_s2h_subarray64_modq[k]
                    .get_value()
                    .ok_or(SynthesisError::AssignmentMissing)?;
                Ok(c_coeff_val - prod_s2h_coeff_val)
            })?;
            cs.enforce(
                || format!("c_minus_s2h = c_coeff - prod_s2h_coeff_{}", k),
                |lc| lc + c_minus_s2h.get_variable() + prod_s2h_subarray64_modq[k].get_variable(),
                |lc| lc + CS::one(),
                |lc| lc + c_subarray64[k].get_variable(),
            );
            let s1_coeff = conditionally_select(
                cs.namespace(|| format!("s1_coeff conditional select_{}", k)),
                &c_lt_s2h,
                &c_minus_s2h,
                &flag_coeff_c_less_s2h,
            )?;

            // normalize coefficients to [-q/2, q/2] before squaring
            let s2_normalized = normalize_half_q(&mut cs.namespace(|| format!("normalize s2_{}", k)), &s2_subarray64[k])?;
            let s2_coeff_sq = s2_normalized.mul(cs.namespace(|| format!("s2_normalized*s2_normalized_{}", k)), &s2_normalized)?;

            // no need to enforce modulo q range check on s1_coeff as both prod_s2h (through ntt multiplication) and c already have coefficients modulo q
            let s1_normalized = normalize_half_q(&mut cs.namespace(|| format!("normalize s1_{}", k)), &s1_coeff)?;
            let s1_coeff_sq = s1_normalized.mul(cs.namespace(|| format!("s1_normalized*s1_normalized_{}", k)), &s1_normalized)?;
            
            // update l2 norm sum and coeff index
            let sum_update = s1_coeff_sq.add(cs.namespace(|| format!("s1_coeff^2 + s2_coeff^2_{}", k)), &s2_coeff_sq)?;
            sum_aggregated = sum_aggregated.add(cs.namespace(|| format!("sum_aggregated = sum_aggregated + sum_update_{}", k)), &sum_update)?;
            coeff_index = coeff_index.add(cs.namespace(|| format!("coeff_index = coeff_index + 1_{}", k)), &var1)?;
        }
        
        l2_norm_sum = l2_norm_sum.add(cs.namespace(|| "l2_norm_sum = l2_norm_sum + sum_update"), &sum_aggregated)?;
        
        let var_512 = alloc_constant(cs.namespace(|| "alloc_constant 512"), Scalar::from(512u64))?;
        let flag_coeff = less_than(cs.namespace(|| "flag_coeff"), &coeff_index, &var_512, LOG_N + 1)?;
        
        // enforce norm bound once all 512 coefficients have been processed
        let flag_norm_bound = enforce_less_than_norm_bound(cs.namespace(|| "enforce_less_than_norm_bound naive_incremental"), &l2_norm_sum)?;
        let res = Boolean::or(cs.namespace(|| "boolean or flag_coeff flag_norm_bound"), &flag_coeff, &flag_norm_bound)?;
        Boolean::enforce_equal(cs.namespace(|| "enforce or result is true"), &res, &Boolean::Constant(true))?;

        ctx_absorb_vars = keccak_f_1600(
            cs.namespace(|| "SHA256 step sponge"),
            &ctx_absorb_vars,
        )?;

        let mut flag_final_absorb = Boolean::Constant(true);
        for (i, (absorb_bit, inject_bit)) in ctx_absorb_vars.iter().zip(ctx_inject_vars.iter()).enumerate() {
            let bits_equal = Boolean::xor(cs.namespace(|| format!("ctx_absorb_inject_bits_equal_{i}")), absorb_bit, inject_bit)?.not();
            flag_final_absorb = Boolean::and(cs.namespace(|| format!("ctx_absorb_final_{i}")), &flag_final_absorb, &bits_equal)?;
        }
        // enforce flag_absorb_last_step => each bit of ctx_absorb equals corresponding bit of ctx_inject
        boolean_implies(
            cs.namespace(|| "last step implies final absorb correctness"),
            &flag_absorb_last_step,
            &flag_final_absorb,
        )?;

        // TODO check if this needs to be constrained
        let msg_without_timestamp: Vec<u8> = [
            &self.msg[0..TIMESTAMP_START_BYTE_INDEX],
            &[0u8; NAME_START_BYTE_INDEX - TIMESTAMP_START_BYTE_INDEX],
            &self.msg[NAME_START_BYTE_INDEX..],
        ].concat()
        .try_into().unwrap();

        // let nullifier_hasher = PoseidonHasher::<Scalar>::new(1 +  msg_without_timestamp.len() as u32);
        // let mut temp_nullifier_1_preimage = msg_without_timestamp.iter().map(|&b| Scalar::from(b as u64)).collect::<Vec<Scalar>>();
        // temp_nullifier_1_preimage.insert(0, current_nullifier.clone());
        // let temp_nullifier_1_preimage_vars = temp_nullifier_1_preimage.iter().enumerate().map(|(i, &x)| {
        //     AllocatedNum::alloc(cs.namespace(|| format!("temp nullifier 1 preimage {}", i)), || Ok(x))
        // }).collect::<Result<Vec<AllocatedNum<Scalar>>, SynthesisError>>()?;
        // let mut temp_nullifier_2_preimage = self.msg.iter().map(|&b| Scalar::from(b as u64)).collect::<Vec<Scalar>>();
        // temp_nullifier_2_preimage.insert(0, current_nullifier.clone());
        // let temp_nullifier_2_preimage_vars = temp_nullifier_2_preimage.iter().enumerate().map(|(i, &x)| {
        //     AllocatedNum::alloc(cs.namespace(|| format!("temp nullifier 2 preimage {}", i)), || Ok(x))
        // }).collect::<Result<Vec<AllocatedNum<Scalar>>, SynthesisError>>()?;
        // let next_nullifier_preimage = conditionally_select_vec(
        //     cs.namespace(|| "nullifier preimage selection"),
        //     &temp_nullifier_1_preimage_vars,
        //     &temp_nullifier_2_preimage_vars,
        //     &flag_first_step,
        // )?;
        // let next_nullifier = nullifier_hasher.hash_in_circuit(
        //     &mut cs.namespace(|| "hash nullifier preimage"),
        //     &next_nullifier_preimage,
        // )?;

        // enforce age > 18
        let dob_byte_index =
            AllocatedNum::alloc_infallible(cs.namespace(|| "alloc DoB byte index"), || {
                Scalar::from(self.dob_byte_index as u64)
            });

        let mut shift_bits =
            dob_byte_index.to_bits_le(cs.namespace(|| "decompose DoB byte index"))?;
        shift_bits.truncate(DOB_INDEX_BIT_LENGTH);
        
        let delimiter_count_correct = delimiter_count_before_and_within_dob_is_correct(
            cs.namespace(|| "check if delimiter count before DoB is correct"),
            &msg_vars,
            &dob_byte_index,
        )?;
        boolean_implies(
            cs.namespace(|| "if first SHA256 step then delimiter count must be correct"),
            &flag_first_step,
            &delimiter_count_correct,
        )?;

        let mut msg_vars_for_shift = msg_vars.clone();
        let shift_input_len = 1usize << (DOB_INDEX_BIT_LENGTH + 3);
        msg_vars_for_shift.resize(shift_input_len, Boolean::Constant(false));
        
        // let shifted_msg = left_shift_bytes(
        //     cs.namespace(|| "left shift to bring DoB bytes to the beginning"),
        //     &msg_vars,
        //     &shift_bits,
        // )?;
        let shifted_msg = left_shift_bytes(
            cs.namespace(|| "left shift to bring DoB bytes to the beginning"),
            &msg_vars_for_shift,
            &shift_bits,
            )?;
        let (day, month, year) = get_day_month_year_conditional(
            cs.namespace(|| "get birth day, month, year"),
            &shifted_msg[0..DATE_LENGTH_BYTES * 8],
            &flag_first_step,
        )?;

        let mut current_date_bits = z[3].to_bits_le(cs.namespace(|| "alloc current date bits"))?;
        current_date_bits.truncate(DATE_LENGTH_BYTES * 8);

        let (current_day, current_month, current_year) = get_day_month_year_conditional(
            cs.namespace(|| "get current birth day, month, year"),
            &current_date_bits,
            &flag_first_step,
        )?;

        let age = calculate_age_in_years(
            cs.namespace(|| "calculate age"),
            &day,
            &month,
            &year,
            &current_day,
            &current_month,
            &current_year,
            &flag_first_step,
        )?;
        let age18 = alloc_constant(cs.namespace(|| "alloc 18"), Scalar::from(18u64))?;
        let age_gte_18 = less_than_or_equal(
            cs.namespace(|| "age <= 18"),
            &age18,
            &age,
            19, // In the first step, age will occupy 7 bits but in later steps it can occupy 19 bits
        )?;
        boolean_implies(
            cs.namespace(|| "if first SHA256 step then age must at least 18"),
            &flag_first_step,
            &age_gte_18,
        )?;

        let var512 = alloc_constant(cs.namespace(|| "512 constant"), Scalar::from(512))?;
        let flag_coeff = less_than(
            cs.namespace(|| "coeff index less than 512 flag"),
            &coeff_index,
            &var512,
            LOG_N
        )?;

        let flag_final_step = Boolean::and(
            cs.namespace(|| "final step flag"),
            &flag_absorb_last_step,
            &flag_coeff.not(),
        )?;

        let inject_norm_absorb_nullifier_preimage = ctx_inject_scalars.clone();
        let mut inject_norm_absorb_nullifier_vars = inject_norm_absorb_nullifier_preimage.iter().enumerate().map(|(i, &x)| {
            AllocatedNum::alloc(cs.namespace(|| format!("inject_norm_absorb_nullifier_preimage {}", i)), || Ok(x))
        }).collect::<Result<Vec<AllocatedNum<Scalar>>, SynthesisError>>()?;
        inject_norm_absorb_nullifier_vars.push(l2_norm_sum);
        // TODO cannot freshly allocate here without constraining.
        let absorb_as_allocated: Vec<AllocatedNum<Scalar>> = ctx_absorb_vars
            .iter()
            .enumerate()
            .map(|(i, v)| {
                AllocatedNum::alloc(cs.namespace(|| format!("ctx_absorb_to_scalar_{}", i)), || {
                    Ok(if v.get_value().unwrap_or(false) { Scalar::ONE } else { Scalar::ZERO })
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        inject_norm_absorb_nullifier_vars.extend(absorb_as_allocated);
        inject_norm_absorb_nullifier_vars.push(nullifier.clone());
        let inject_norm_absorb_hasher = PoseidonHasher::<Scalar>::new(inject_norm_absorb_nullifier_vars.len() as u32);
        let next_nullifier = inject_norm_absorb_hasher.hash_in_circuit(&mut cs.namespace(|| "hash inject norm"), &inject_norm_absorb_nullifier_vars)?;
        
        // TODO replace this with constrainted ctx_inject instead.
        let next_shake_inject_m_block = AllocatedNum::alloc(cs.namespace(|| "next shake inject m block"), || Ok(self.shake_inject_m_block))?;
        let last_z_out = vec![next_opcode.clone(), hash_c.clone(), next_shake_inject_m_block.clone(), next_nullifier.clone()];

        // let z_out = conditionally_select_vec(
        //     cs.namespace(|| "Choose between outputs of last opcode and others"),
        //     &last_z_out,
        //     &[next_opcode, hash_c.clone(), next_shake_inject_m_block, next_nullifier],
        //     &flag_final_step,
        // )?;
        let z_out = last_z_out;

        Ok(z_out)
    }
}
