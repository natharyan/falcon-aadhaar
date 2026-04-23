use crate::{
    dob::{
        DOB_INDEX_BIT_LENGTH, calculate_age_in_years, delimiter_count_before_and_within_dob_is_correct, get_day_month_year_conditional, left_shift_bytes
    },
    hash::shake256::{
        SHAKE256_BLOCK_LENGTH_BITS, SHAKE256_BLOCK_LENGTH_BYTES, SHAKE256_DIGEST_LENGTH_BITS, SHAKE256_DIGEST_LENGTH_BYTES, keccak_f_1600, library_shake256_inject, library_step_sponge, shake256_gadget, shake256_inject, shake256_msg_blocks, shake256_pad101
    },
    ntt::{inv_ntt, inv_ntt_deferred_circuit, ntt, ntt_deferred_circuit, ntt_mult_const_p2},
    qr::{AadhaarQRData, NONCE_LENGTH_BYTES},
    subarray::var_shift_left,
    utils::{
        bits_to_bytes_le, bytes_to_bits_le, enforce_less_than_norm_bound, mod_q, normalize_coeff,
        normalize_half_q, num_to_alloc, pack_bits_scalars, select_from_vec_linear,
    },
    hash::poseidon::PoseidonHasher,
};
use bellpepper::gadgets::multipack::{bytes_to_bits, compute_multipacking, pack_bits};
use bellpepper_core::{
    ConstraintSystem, LinearCombination, SynthesisError, boolean::{self, AllocatedBit, Boolean}, num::AllocatedNum, test_cs::TestConstraintSystem
};
use bellpepper_nonnative::{
    mp::bignat::{nat_to_limbs, BigNat},
    util::{bit::Bit, gadget::Gadget, num::Num},
};
use bitvec::vec;
use core::hash;
use falcon_rust::{
    KeyPair, NTTPolynomial, Polynomial, PublicKey, Signature, LOG_N, MODULUS, N, SIG_L2_BOUND,
};
use ff::{PrimeField, PrimeFieldBits};
use keccak::f1600;
use crate::{
    utils::{
        alloc_constant, alloc_num_equals, alloc_num_equals_constant,
        boolean_implies, check_decomposition, conditionally_select,
        conditionally_select_boolean_vec, conditionally_select_vec, less_than, less_than_or_equal,
        num_to_bits,
    },
};
use nova_snark::traits::circuit::StepCircuit;
use num_bigint::{BigInt, Sign};
use sha2::{compress256, digest::generic_array::GenericArray};
use std::{cmp::max, ops::Mul};

pub const NUM_OPCODE_BITS: usize = 11; // 1 MSB for SHAKE256 + 10 LSBs for COEFF_INDEX
pub const NUM_COEFF_INDEX_BITS: u64 = 10; // COEFF_INDEX <= 512
pub const COEFF_INDEX_MASK: u64 = (1 << NUM_COEFF_INDEX_BITS) - 1;
pub const OP_SHAKE256_ACTIVE: u64 = 0;
pub const OP_SHAKE256_NO_OP: u64 = 1;
pub const OP_COEFF_INDEX_FIRST: u64 = 0;
pub const OP_COEFF_INDEX_LAST: u64 = 512;
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
    coeff_index: u64,
    l2_norm_sum: u64,
    msg: [u8; SHAKE256_BLOCK_LENGTH_BYTES],
    s2: Polynomial,
    c: Polynomial,
    h: PublicKey,
    ctx_inject_packed: [Scalar; 7],
    ctx_absorb: [bool; SHAKE256_DIGEST_LENGTH_BITS],
    dob_byte_index: usize,
    prev_nullifier: Scalar,
}

impl<Scalar> AadhaarAgeProofCircuit<Scalar>
where
    Scalar: PrimeFieldBits,
{
    pub fn default(h: PublicKey, s2: Polynomial, c: Polynomial) -> Self {
        Self {
            opcode: 0u64,
            next_opcode: 0u64,
            coeff_index: 0u64,
            l2_norm_sum: 0u64,
            msg: [0u8; SHAKE256_BLOCK_LENGTH_BYTES],
            s2: s2,
            c: c,
            h: h,
            ctx_inject_packed: [Scalar::ZERO; 7],
            ctx_absorb: [false; SHAKE256_DIGEST_LENGTH_BITS],
            dob_byte_index: 0,
            prev_nullifier: Scalar::default(),
        }
    }

    // fn update_nullifier(
    //     prev_nullifier: Scalar,
    //     l2_norm_sum: u64,
    //     ctx_absorb: [bool; SHAKE256_DIGEST_LENGTH_BITS],
    //     msg: &Vec<u8>,
    // ) -> Scalar {
    //     let ctx_inject: [bool; 1600] = library_shake256_inject(
    //         [false; 1600],
    //         msg.clone(),
    //     );
    //     let ctx_inject_packed = compute_multipacking::<Scalar>(&ctx_inject);
    //     assert!(ctx_inject_packed.len() == 7);
    //     let ctx_absorb_packed = compute_multipacking::<Scalar>(&ctx_absorb);
    //     let mut nullifier_preimage = ctx_inject_packed.clone();
    //     nullifier_preimage.push(Scalar::from(l2_norm_sum));
    //     nullifier_preimage.extend(ctx_absorb_packed);
    //     nullifier_preimage.push(prev_nullifier);
    //     let hasher_nullifier =
    //         PoseidonHasher::<Scalar>::new(nullifier_preimage.len() as u32);
    //     let next_nullifier = hasher_nullifier.hash(&nullifier_preimage);

    //     next_nullifier
    // }
    fn update_nullifier(
        prev_nullifier: Scalar,
        msg: &[u8],
        is_first: bool,
    ) -> Scalar {
        let mut block;
        if is_first {
            // Remove the first 40 bytes corresponding to the Falcon nonce
            block = msg[NONCE_LENGTH_BYTES..].to_vec();
            // Mask timestamp bytes
            for j in TIMESTAMP_START_BYTE_INDEX..NAME_START_BYTE_INDEX {
                block[j] = 0;
            }
        } else {
            block = msg.to_vec();
        }

        let block_bits: Vec<bool> = bytes_to_bits_le(&block);
        let block_packed: Vec<Scalar> = compute_multipacking::<Scalar>(&block_bits);
        let mut preimage = vec![prev_nullifier];
        preimage.extend(block_packed);
        let hasher = PoseidonHasher::<Scalar>::new(preimage.len() as u32);
        hasher.hash(&preimage)
    }

    pub fn calc_initial_primary_circuit_input(
        current_date_bytes: &[u8],
        msg: &Vec<u8>,
        sig: &Signature,
    ) -> Vec<Scalar> {
        let initial_opcode = Scalar::from((OP_SHAKE256_ACTIVE << NUM_COEFF_INDEX_BITS) + OP_COEFF_INDEX_FIRST);

        assert!(
            msg.len() >= NONCE_LENGTH_BYTES,
            "Expected nonce-prefixed Falcon message"
        );

        let msg_blocks: Vec<[u8; 136]> = shake256_msg_blocks(&msg);

        let ctx_inject: [bool; 1600] = library_shake256_inject(
            [false; 1600],
            msg.to_vec(),
        );
        let ctx_inject_bits = ctx_inject.to_vec();
        // 254 bools per scalar for multipacking
        let ctx_inject_packed: Vec<Scalar> = compute_multipacking::<Scalar>(&ctx_inject_bits);
        // println!("ctx_inject_packed len: {}", ctx_inject_packed.len());
        let inject_hasher = PoseidonHasher::<Scalar>::new(ctx_inject_packed.len() as u32);

        let c_msg = &msg[NONCE_LENGTH_BYTES..];
        let c: Polynomial = Polynomial::from_hash_of_message(c_msg, sig.nonce());
        let c_scalars: Vec<Scalar> = c.coeff().iter().map(|&x| Scalar::from(x as u64)).collect();
        let c_hasher = PoseidonHasher::<Scalar>::new(c_scalars.len() as u32);
        let hash_c = c_hasher.hash(&c_scalars);
        
        let current_date_bits = bytes_to_bits(current_date_bytes);
        let current_date_scalars = compute_multipacking::<Scalar>(&current_date_bits);
        assert_eq!(current_date_scalars.len(), 1);
        let current_date_scalar = current_date_scalars[0];

        vec![
            initial_opcode,
            hash_c,
            ctx_inject_packed[0],
            current_date_scalar,
        ]
    }

    pub fn new_state_sequence(
        aadhaar_qr_data: &AadhaarQRData,
        sig: &Signature,
        pk: PublicKey,
    ) -> Vec<AadhaarAgeProofCircuit<Scalar>> {
        let mut aadhaar_steps: Vec<AadhaarAgeProofCircuit<Scalar>> = vec![];

        let falcon_msg: Vec<u8> = aadhaar_qr_data.falcon_msg.clone();
        let msg_blocks: Vec<[u8; 136]> = shake256_msg_blocks(&falcon_msg);
        let signed_msg: Vec<u8> = falcon_msg[NONCE_LENGTH_BYTES..].to_vec();

        let s2: Polynomial = sig.into();
        let c: Polynomial = Polynomial::from_hash_of_message(&signed_msg, sig.nonce());
        let pk_poly: Polynomial = (&pk).into();

        let mut prev_nullifier = Scalar::ZERO; // App_ID set as 0 for now

        let mut opcode = (OP_SHAKE256_ACTIVE << NUM_COEFF_INDEX_BITS) + OP_COEFF_INDEX_FIRST;
        let mut next_opcode = if msg_blocks.len() == 1 {
            (OP_SHAKE256_NO_OP << NUM_COEFF_INDEX_BITS) + (OP_COEFF_INDEX_FIRST) + 64
        } else {
            opcode + 64
        };
        let mut coeff_index: u64 = OP_COEFF_INDEX_FIRST;

        let ctx_inject: [bool; 1600] = library_shake256_inject(
            [false; 1600],
            falcon_msg.clone(),
        );
        let ctx_inject_bits = ctx_inject.to_vec();
        // 254 bools per scalar for multipacking
        let ctx_inject_packed: Vec<Scalar> = compute_multipacking::<Scalar>(&ctx_inject_bits);
        assert!(ctx_inject_packed.len() == 7);
        let inject_hasher = PoseidonHasher::<Scalar>::new(ctx_inject_packed.len() as u32);

        let c_scalars: Vec<Scalar> = c.coeff().iter().map(|&x| Scalar::from(x as u64)).collect();
        let c_hasher = PoseidonHasher::<Scalar>::new(c_scalars.len() as u32);

        let mut ctx_absorb = [false; 1600];
        let mut l2_norm_sum = 0u64;

        // First step
        aadhaar_steps.push(Self {
            opcode: opcode,
            coeff_index: coeff_index,
            next_opcode: next_opcode,
            msg: msg_blocks[0],
            dob_byte_index: aadhaar_qr_data.dob_byte_index,
            l2_norm_sum: l2_norm_sum,
            ctx_absorb: ctx_absorb.clone(),
            ctx_inject_packed: ctx_inject_packed.clone().try_into().unwrap(),
            s2: s2.clone(),
            prev_nullifier: prev_nullifier,
            h: pk.clone(),
            c: c.clone(),
        });

        // prev_nullifier = Self::update_nullifier(prev_nullifier, l2_norm_sum, ctx_absorb, &falcon_msg);
        prev_nullifier = Self::update_nullifier(prev_nullifier, &msg_blocks[0], true);

        let num_blocks = msg_blocks.len();
        println!("Number of SHAKE256.inject steps: {}", num_blocks);
        let num_steps = max(num_blocks, 8);
        println!("Number of steps: {}", num_steps);

        // compute s2*h modulo q
        let ntt_s2: NTTPolynomial = ntt(&s2);
        let ntt_h: NTTPolynomial = ntt(&pk_poly);
        let ntt_s2h: NTTPolynomial = ntt_s2.mul(ntt_h);
        let prod_s2h: Polynomial = inv_ntt(&ntt_s2h);
        for i in 1..num_steps {
            let coeff_index_init = coeff_index;
            let mut sum_aggregated = 0u64;
            for k in 0..64 {
                let idx = ((coeff_index_init + k as u64) % (N as u64)) as usize;
                let flag_coeff_c_less_2h =
                    if c.coeff()[idx] < prod_s2h.coeff()[idx] {
                        true
                    } else {
                        false
                    };
                // coefficients of both c and prod_s2h are already modulo q.
                let c_lt_s2h = c.coeff()[idx] + MODULUS - prod_s2h.coeff()[idx];
                let s1_coeff = if flag_coeff_c_less_2h {
                    c_lt_s2h
                } else {
                    c.coeff()[idx] - prod_s2h.coeff()[idx]
                };
                let s1_normalized = normalize_coeff(s1_coeff as i64);
                let s2_normalized = normalize_coeff(s2.coeff()[idx] as i64);
                sum_aggregated = sum_aggregated + s1_normalized * s1_normalized + s2_normalized * s2_normalized;
            }

            let coeff_index_next = coeff_index_init + 64;  // Compute END position
            if coeff_index_next <= OP_COEFF_INDEX_LAST {
                l2_norm_sum = l2_norm_sum + sum_aggregated;
            }
            
            coeff_index = coeff_index_next.min(OP_COEFF_INDEX_LAST);  // Cap at 512 for next step
            
            if l2_norm_sum >= SIG_L2_BOUND {
                panic!(
                    "L2 norm exceeded SIG_L2_BOUND at coeff {}: {}",
                    i, l2_norm_sum
                );
            }

            ctx_absorb = library_step_sponge(
                ctx_absorb.to_vec(),
                Some(bytes_to_bits_le(&msg_blocks[(i - 1) % num_blocks])),
                1088,
                false,
            );

            opcode = next_opcode;
            let temp_next_opcode = next_opcode;

            // next step's coeff_index_init = current init + 64, capped at 512
            let cur_coeff_init = opcode & COEFF_INDEX_MASK;
            let next_coeff = (cur_coeff_init + 64).min(OP_COEFF_INDEX_LAST);

            next_opcode = if i < num_blocks - 1 {
                (OP_SHAKE256_ACTIVE << NUM_COEFF_INDEX_BITS) + next_coeff
            } else {
                (OP_SHAKE256_NO_OP << NUM_COEFF_INDEX_BITS) + next_coeff
            };

            // once coeff_index > 512, next_opcode remains the same.
            if coeff_index > OP_COEFF_INDEX_LAST {
                next_opcode = temp_next_opcode;
                coeff_index = OP_COEFF_INDEX_LAST;
            }
            
            aadhaar_steps.push(Self {
                opcode: opcode,
                coeff_index: coeff_index,
                next_opcode: next_opcode,
                msg: msg_blocks[i % num_blocks],
                dob_byte_index: aadhaar_qr_data.dob_byte_index,
                l2_norm_sum: l2_norm_sum,
                ctx_absorb: ctx_absorb.clone(),
                ctx_inject_packed: ctx_inject_packed.clone().try_into().unwrap(),
                s2: s2.clone(),
                prev_nullifier: prev_nullifier,
                h: pk.clone(),
                c: c.clone(),
            });
            
            // prev_nullifier = Self::update_nullifier(prev_nullifier, l2_norm_sum, ctx_absorb, &falcon_msg);
            prev_nullifier = Self::update_nullifier(prev_nullifier, &msg_blocks[i % num_blocks], false);
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
        let cur_shake_block = &z[2];
        let io_hash = &z[3];

        let s2_vars = self
            .s2
            .coeff()
            .iter()
            .enumerate()
            .map(|(i, &x)| AllocatedNum::alloc(cs.namespace(|| format!("s2 coeff {}", i)), || Ok(Scalar::from(x as u64))))
            .collect::<Result<Vec<AllocatedNum<Scalar>>, SynthesisError>>()?;
        let c_vars = self
            .c
            .coeff()
            .iter()
            .enumerate()
            .map(|(i, &x)| AllocatedNum::alloc(cs.namespace(|| format!("c coeff {}", i)), || Ok(Scalar::from(x as u64))))
            .collect::<Result<Vec<AllocatedNum<Scalar>>, SynthesisError>>()?;

        let ctx_inject_packed_vars = self.ctx_inject_packed
            .iter()
            .enumerate()
            .map(|(i, &x)| {
                AllocatedNum::alloc(cs.namespace(|| format!("ctx_inject_packed_{i}")), || Ok(x))
            })
            .collect::<Result<Vec<_>, _>>()?;

        let next_opcode = AllocatedNum::alloc(cs.namespace(|| "next opcode"), || {
            Ok(Scalar::from(self.next_opcode))
        })?;

        let mut l2_norm_sum_var = AllocatedNum::alloc(cs.namespace(|| "l2_norm_sum"), || Ok(Scalar::from(self.l2_norm_sum)))?;
        let prev_nullifier_var = AllocatedNum::alloc(cs.namespace(|| "prev_nullifier"), || Ok(self.prev_nullifier))?;
        
        let mut ctx_absorb_vars: Vec<Boolean> = vec![];
        
        // enforce consistency of ctx_inject, l2_norm_sum, ctx_absorb
        let mut io_hash_preimage: Vec<AllocatedNum<Scalar>> = ctx_inject_packed_vars.to_vec();
        io_hash_preimage.push(l2_norm_sum_var.clone());
        for (i, &b) in self.ctx_absorb.iter().enumerate() {
            let ctx_absorb_bit = Boolean::from(AllocatedBit::alloc(
                cs.namespace(|| format!("ctx_absorb bit {i}")),
                Some(b),
            )?);
            ctx_absorb_vars.push(ctx_absorb_bit.clone());
        }
        // pack [Boolean; 1600] into 7 scalars
        let ctx_absorb_packed = pack_bits_scalars(
            cs.namespace(|| "pack_bits_scalars ctx_absorb"),
            &ctx_absorb_vars,
        )?;
        for (i, ctx_absorb_packed_scalar) in ctx_absorb_packed.iter().enumerate() {
            io_hash_preimage.push(ctx_absorb_packed_scalar.clone());
        }
        io_hash_preimage.push(prev_nullifier_var.clone());
        
        let io_hasher = PoseidonHasher::<Scalar>::new(io_hash_preimage.len() as u32);
        let io_hash_calculated = io_hasher.hash_in_circuit(
            &mut cs.namespace(|| "poseidon hash nullifier preimage nullifier_calculated"),
            &io_hash_preimage,
        )?;

        let msg: [u8; 136] = self.msg;
        let msg_bits: Vec<bool> = bytes_to_bits_le(&msg);
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

        // range check on opcode and next_opcode for 10 bits
        let opcode_bits_le = num_to_bits(cs.namespace(|| "Decompose opcode"), opcode, NUM_OPCODE_BITS)?;
        let current_shake_opcode = opcode_bits_le[NUM_COEFF_INDEX_BITS as usize].clone();
        let current_coeff_index_bits_le = opcode_bits_le[..NUM_COEFF_INDEX_BITS as usize].to_vec();
        let next_opcode_bits_le = num_to_bits(cs.namespace(|| "Decompose next opcode"),&next_opcode,NUM_OPCODE_BITS,        )?;
        let next_shake_opcode = next_opcode_bits_le[NUM_COEFF_INDEX_BITS as usize].clone();
        let next_coeff_index_bits_le = next_opcode_bits_le[..NUM_COEFF_INDEX_BITS as usize].to_vec();
        
        // constrain coeff_index and next_coeff_index
        let mut coeff_index = AllocatedNum::alloc(cs.namespace(|| "coeff_index"), || {
            Ok(Scalar::from(self.opcode & COEFF_INDEX_MASK))
        })?;
        check_decomposition(
            cs.namespace(|| "check coeff_index opcode allocation"),
            &coeff_index,
            current_coeff_index_bits_le,
        )?;
        let coeff_index_init = coeff_index.clone();
        let next_coeff_index = AllocatedNum::alloc(cs.namespace(|| "next coeff_index"), || {
            Ok(Scalar::from(self.next_opcode & COEFF_INDEX_MASK))
        })?;
        check_decomposition(
            cs.namespace(|| "check next coeff_index allocation"),
            &next_coeff_index,
            next_coeff_index_bits_le,
        )?;
        
        // once shake256_opcode is 1, next_shake_opcode must be 1 as well
        boolean_implies(
            cs.namespace(|| "next SHA256 opcode is identical or one more"),
            &current_shake_opcode,
            &next_shake_opcode,
        )?;

        let flag_absorb_last_step = Boolean::and(
            cs.namespace(|| "absorb last step flag"),
            &current_shake_opcode.not(),
            &next_shake_opcode,
        )?;

        // enforce flag_first_step => l2_norm_sum = 0 and ctx_absorb = [0; 1600]
        let flag_first_step = alloc_num_equals_constant(
            cs.namespace(|| "first step flag"),
            &coeff_index,
            Scalar::from(OP_COEFF_INDEX_FIRST),
        )?;

        let flag_l2norm_init = alloc_num_equals_constant(
            cs.namespace(|| "L2 norm init flag"),
            &l2_norm_sum_var,
            Scalar::from(L2_NORM_INIT),
        )?;

        let mut any_one = Boolean::Constant(false);
        for (i, b) in ctx_absorb_vars.iter().enumerate() {
            any_one = Boolean::or(
                cs.namespace(|| format!("ctx_absorb_any_one_{i}")),
                &any_one,
                b,
            )?;
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

        let nullifier_equal = alloc_num_equals(
            cs.namespace(|| "nullifier consistency check"),
            &io_hash_calculated,
            io_hash,
        )?;
        boolean_implies(
            cs.namespace(|| "not first step implies nullifier consistency check"),
            &flag_first_step.not(),
            &nullifier_equal,
        )?;

        // No range check needed for c as it configured is a public input
        let s2_lshifted = var_shift_left(
            cs.namespace(|| "var_shift_left s2"),
            &s2_vars,
            &coeff_index,
            N,
            LOG_N,
        )?;
        let c_lshifted = var_shift_left(
            cs.namespace(|| "var_shift_left c"),
            &c_vars,
            &coeff_index,
            N,
            LOG_N,
        )?;
        let s2_subarray64 = s2_lshifted
            .iter()
            .take(64)
            .cloned()
            .collect::<Vec<AllocatedNum<Scalar>>>();
        let c_subarray64 = c_lshifted
            .iter()
            .take(64)
            .cloned()
            .collect::<Vec<AllocatedNum<Scalar>>>();

        let mut sum_aggregated = alloc_constant(
            cs.namespace(|| "alloc_constant sum_aggregated = 0"),
            Scalar::from(0u64),
        )?;
        let ntt_s2 = ntt_deferred_circuit(cs.namespace(|| "ntt_deferred_circuit s2"), &s2_vars)?;
        let pk_poly = (&self.h).into();
        let ntt_h = ntt(&pk_poly);
        let ntt_s2h = ntt_mult_const_p2(cs.namespace(|| "ntt_mult_const_p2"), ntt_s2, ntt_h)?;
        let prod_s2h =
            inv_ntt_deferred_circuit(cs.namespace(|| "inv_ntt_deferred_circuit s2h"), ntt_s2h)?;
        let prod_s2h = prod_s2h
            .iter()
            .enumerate()
            .map(|(i, x)| num_to_alloc(cs.namespace(|| format!("alloc prod_s2h coeff {}", i)), &x))
            .collect::<Result<Vec<AllocatedNum<Scalar>>, SynthesisError>>()?;
        let prod_s2h_lshifted = var_shift_left(
            cs.namespace(|| "var_shift_left prod_s2h"),
            &prod_s2h,
            &coeff_index,
            N,
            LOG_N,
        )?;
        let prod_s2h_subarray64 = prod_s2h_lshifted
            .iter()
            .take(64)
            .cloned()
            .collect::<Vec<AllocatedNum<Scalar>>>();
        // reduce each coefficient mod q
        let prod_s2h_subarray64_modq = prod_s2h_subarray64
            .iter()
            .enumerate()
            .map(|(i, x)| {
                let reduced = mod_q(cs.namespace(|| format!("mod_q prod_s2h coeff_{}", i)), x)?;
                Ok(reduced)
            })
            .collect::<Result<Vec<AllocatedNum<Scalar>>, SynthesisError>>()?;

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
                |lc| {
                    lc + c_subarray64[k].get_variable() + (Scalar::from(MODULUS as u64), CS::one())
                },
            );
            let c_minus_s2h =
                AllocatedNum::alloc(cs.namespace(|| format!("c_minus_s2h_{}", k)), || {
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
            let s2_normalized = normalize_half_q(
                &mut cs.namespace(|| format!("normalize s2_{}", k)),
                &s2_subarray64[k],
            )?;
            let s2_coeff_sq = s2_normalized.mul(
                cs.namespace(|| format!("s2_normalized*s2_normalized_{}", k)),
                &s2_normalized,
            )?;

            // no need to enforce modulo q range check on s1_coeff as both prod_s2h (through ntt multiplication) and c already have coefficients modulo q
            let s1_normalized = normalize_half_q(
                &mut cs.namespace(|| format!("normalize s1_{}", k)),
                &s1_coeff,
            )?;
            let s1_coeff_sq = s1_normalized.mul(
                cs.namespace(|| format!("s1_normalized*s1_normalized_{}", k)),
                &s1_normalized,
            )?;

            // update l2 norm sum and coeff index
            let sum_update = s1_coeff_sq.add(
                cs.namespace(|| format!("s1_coeff^2 + s2_coeff^2_{}", k)),
                &s2_coeff_sq,
            )?;
            sum_aggregated = sum_aggregated.add(
                cs.namespace(|| format!("sum_aggregated = sum_aggregated + sum_update_{}", k)),
                &sum_update,
            )?;
            // coeff_index = coeff_index.add(
            //     cs.namespace(|| format!("coeff_index = coeff_index + 1_{}", k)),
            //     &var1,
            // )?;
        }

        let var_64 = alloc_constant(cs.namespace(|| "const_64"), Scalar::from(64u64))?;

        let coeff_index_after = coeff_index_init.add(
            cs.namespace(|| "coeff_index + 64"),
            &var_64,
        )?;

        // XOR message block with keccak state
        let mut absorb_xor_msg = msg_vars
            .iter()
            .enumerate()
            .map(|(i, b)| {
                Boolean::xor(
                    cs.namespace(|| format!("absorb_xor_msg_{}", i)),
                    b,
                    &ctx_absorb_vars[i],
                )
            })
            .collect::<Result<Vec<Boolean>, SynthesisError>>()?;
        absorb_xor_msg.extend(ctx_absorb_vars[SHAKE256_BLOCK_LENGTH_BITS..].iter().cloned());

        // apply keccak round permuation
        ctx_absorb_vars = keccak_f_1600(cs.namespace(|| "SHA256 step sponge"), &absorb_xor_msg)?;

        let var_512 = alloc_constant(cs.namespace(|| "alloc_constant 512"), Scalar::from(512u64))?;
        let flag_coeff = less_than_or_equal(
            cs.namespace(|| "flag_coeff"),
            &coeff_index_after,
            &var_512,
            LOG_N + 1,
        )?;

        let min_512_coeff_index = conditionally_select(
            cs.namespace(|| "next_coeff_index conditional select"),
            &coeff_index_after,
            &var_512,
            &flag_coeff,
        )?;

        // Enforce next_coeff_index = min(coeff_index, 512)
        cs.enforce(
            || "enforce next_coeff_index = min(coeff_index, 512)",
            |lc| lc + next_coeff_index.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + min_512_coeff_index.get_variable(),
        );

        let l2_norm_sum_inc = l2_norm_sum_var.add(
            cs.namespace(|| "l2_norm_sum = l2_norm_sum + sum_update"),
            &sum_aggregated,
        )?;
        // Skip l2_norm_sum update if coeff_index > 512
        l2_norm_sum_var = conditionally_select(
            cs.namespace(|| "l2_norm_sum conditional select"),
            &l2_norm_sum_inc,
            &l2_norm_sum_var,
            &flag_coeff,
        )?;

        // enforce norm bound once all 512 coefficients have been processed
        let flag_norm_bound = enforce_less_than_norm_bound(
            cs.namespace(|| "enforce_less_than_norm_bound naive_incremental"),
            &l2_norm_sum_var,
        )?;
        
        Boolean::enforce_equal(
            cs.namespace(|| "enforce norm bound"),
            &flag_norm_bound,
            &Boolean::Constant(true),
        )?;

        let mut flag_final_absorb = Boolean::Constant(true);
        
        let ctx_absorb_packed_vars = pack_bits_scalars(
            cs.namespace(|| "pack_bits_scalars ctx_absorb_vars"),
            &ctx_absorb_vars,
        )?;
        for (i, (inject_packed, absorb_packed)) in ctx_inject_packed_vars
            .iter()
            .zip(ctx_absorb_packed_vars.iter())
            .enumerate()
        {
            let packed_equal = alloc_num_equals(
                cs.namespace(|| format!("ctx_absorb_inject_packed_equal_{}", i)),
                inject_packed,
                absorb_packed,
            )?;
            flag_final_absorb = Boolean::and(
                cs.namespace(|| format!("ctx_absorb_final_{}", i)),
                &flag_final_absorb,
                &packed_equal,
            )?;
        }
        // enforce flag_absorb_last_step => each bit of ctx_absorb equals corresponding bit of ctx_inject
        boolean_implies(
            cs.namespace(|| "last step implies final absorb correctness"),
            &flag_absorb_last_step,
            &flag_final_absorb,
        )?;

        let step_i_val = (self.coeff_index / 64) % 7;
        let step_i = AllocatedNum::alloc(
            cs.namespace(|| "step_i"),
            || Ok(Scalar::from(step_i_val)),
        )?;

        // q = (coeff_index/64) / 7  =>  0 for coeff_index < 448, 1 for >= 448
        let q_val = (self.coeff_index / 64) / 7;
        let q = AllocatedNum::alloc(
            cs.namespace(|| "step_i_q"),
            || Ok(Scalar::from(q_val)),
        )?;

        // 1-bit range check for q
        let _ = num_to_bits(cs.namespace(|| "q_bits"), &q, 1)?;

        // 3-bit range check for step_i
        let _ = num_to_bits(cs.namespace(|| "step_i_bits"), &step_i, 3)?;

        // coeff_index = 64*step_i + 448*q   (448 = 7*64)
        cs.enforce(
            || "64 * step_i + 448 * q = coeff_index_init",
            |lc| lc
                + (Scalar::from(64u64),  step_i.get_variable())
                + (Scalar::from(448u64), q.get_variable()),
            |lc| lc + CS::one(),
            |lc| lc + coeff_index_init.get_variable(),
        );

        // cur_shake_block must equal ctx_inject_packed[step_i]
        let cur_expected = select_from_vec_linear(
            cs.namespace(|| "sel_cur_shake"),
            &ctx_inject_packed_vars,
            &step_i,
        )?;
        cs.enforce(
            || "cur_shake_block == ctx_inject_packed[step_i]",
            |lc| lc + cur_expected.get_variable() - cur_shake_block.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc,
        );

        let flag_at_max = alloc_num_equals_constant(
            cs.namespace(|| "coeff_index_init == 512"),
            &coeff_index_init,
            Scalar::from(512u64),
        )?;

        // next_idx = (step_i + 1) % 7
        let const_zero = alloc_constant(cs.namespace(|| "const_0"), Scalar::ZERO)?;
        let step_plus1 = step_i.add(cs.namespace(|| "step_plus1"), &var1)?;
        let step_plus1_eq_7 = alloc_num_equals_constant(
            cs.namespace(|| "step_plus1_eq_7"),
            &step_plus1,
            Scalar::from(7u64),
        )?;
        let next_idx = conditionally_select(
            cs.namespace(|| "next_idx = step_plus1==7 ? 0 : step_plus1"),
            &const_zero,
            &step_plus1,
            &step_plus1_eq_7,
        )?;

        let shake_block_next_normal = select_from_vec_linear(
            cs.namespace(|| "sel_next_shake"),
            &ctx_inject_packed_vars,
            &next_idx,
        )?;

        // If coeff_index==512, freeze block index else increment
        let shake_block_next = conditionally_select(
            cs.namespace(|| "freeze shake_block if at max"),
            cur_shake_block,
            &shake_block_next_normal,
            &flag_at_max,
        )?;

        // remove nonce bytes, then mask timestamp bytes.
        let mut msg_without_timestamp_nonce: Vec<Boolean> =
            msg_vars[NONCE_LENGTH_BYTES * 8..].to_vec();
        for byte_idx in TIMESTAMP_START_BYTE_INDEX..NAME_START_BYTE_INDEX {
            let base = byte_idx * 8;
            for bit_idx in 0..8 {
                msg_without_timestamp_nonce[base + bit_idx] = Boolean::Constant(false);
            }
        }

        let mut temp_nullifier_1_preimage = vec![prev_nullifier_var.clone()];
        temp_nullifier_1_preimage.extend(
            pack_bits_scalars(cs.namespace(|| "pack msg_m"), &msg_without_timestamp_nonce)?
        );
        let temp_nullifier_1_hasher = PoseidonHasher::<Scalar>::new(temp_nullifier_1_preimage.len() as u32);
        let temp_nullifier_1 = temp_nullifier_1_hasher.hash_in_circuit(
            &mut cs.namespace(|| "hash temp nullifier 1"), &temp_nullifier_1_preimage)?;

        let mut temp_nullifier_2_preimage = vec![prev_nullifier_var.clone()];
        temp_nullifier_2_preimage.extend(
            pack_bits_scalars(cs.namespace(|| "pack msg_r"), msg_vars.as_ref())?
        );
        let temp_nullifier_2_hasher = PoseidonHasher::<Scalar>::new(temp_nullifier_2_preimage.len() as u32);
        let temp_nullifier_2 = temp_nullifier_2_hasher.hash_in_circuit(
            &mut cs.namespace(|| "hash temp nullifier 2"), &temp_nullifier_2_preimage)?;
        
        // constrain the next nullifier
        let next_nullifier = conditionally_select(
            cs.namespace(|| "next_nullifier conditional select"),
            &temp_nullifier_1,
            &temp_nullifier_2,
            &flag_first_step,
        )?;

        let mut next_io_hash_preimage: Vec<AllocatedNum<Scalar>> = ctx_inject_packed_vars.to_vec();
        next_io_hash_preimage.push(l2_norm_sum_var);
        next_io_hash_preimage.extend(ctx_absorb_packed_vars);
        next_io_hash_preimage.push(next_nullifier.clone());
        
        let next_io_hasher = PoseidonHasher::<Scalar>::new(next_io_hash_preimage.len() as u32);
        let next_io_hash = next_io_hasher.hash_in_circuit(
            &mut cs.namespace(|| "poseidon hash nullifier preimage next_nullifier"),
            &next_io_hash_preimage,
        )?;

        // enforce age > 18
        let dob_byte_index =
            AllocatedNum::alloc_infallible(cs.namespace(|| "alloc DoB byte index"), || {
                Scalar::from(self.dob_byte_index as u64)
            });

        let delimiter_count_correct = delimiter_count_before_and_within_dob_is_correct(
            cs.namespace(|| "check if delimiter count before DoB is correct"),
            &msg_vars,
            &dob_byte_index,
        )?;
        boolean_implies(
            cs.namespace(|| "if first SHAKE256 step then delimiter count must be correct"),
            &flag_first_step,
            &delimiter_count_correct,
        )?;

        let mut shift_bits =
            dob_byte_index.to_bits_le(cs.namespace(|| "decompose DoB byte index"))?;
        shift_bits.truncate(DOB_INDEX_BIT_LENGTH);

        let shifted_msg_blocks = left_shift_bytes(
            cs.namespace(|| "left shift to bring DoB bytes to the beginning"),
            &msg_vars,
            &shift_bits,
        )?;
        
        // Convert shifted bits from LE to BE for character extraction
        let mut shifted_msg_blocks_be = vec![];
        for byte_idx in 0..(shifted_msg_blocks.len() / 8) {
            let byte_bits = &shifted_msg_blocks[byte_idx * 8..(byte_idx + 1) * 8];
            for bit in byte_bits.iter().rev() {
                shifted_msg_blocks_be.push(bit.clone());
            }
        }

        let (day, month, year) = get_day_month_year_conditional(
            cs.namespace(|| "get birth day, month, year"),
            &shifted_msg_blocks_be[0..DATE_LENGTH_BYTES * 8],
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
            cs.namespace(|| "if first SHAKE256 step then age must at least 18"),
            &flag_first_step,
            &age_gte_18,
        )?;
        
        let flag_last_step = Boolean::and(
            cs.namespace(|| "final step flag"),
            &flag_absorb_last_step,
            &flag_coeff.not(),
        )?;
        
        let last_z_out = vec![
            next_opcode.clone(),
            hash_c.clone(),
            shake_block_next.clone(),
            next_nullifier.clone(),
        ];

        let z_out = conditionally_select_vec(
            cs.namespace(|| "Choose between outputs of last opcode and others"),
            &last_z_out,
            &vec![
                    next_opcode.clone(),
                    hash_c.clone(),
                    shake_block_next.clone(),
                    next_io_hash.clone(),
                ],
            &flag_last_step,
        )?;

        Ok(z_out)
    }
}
