use std::ops::Mul;
use std::{alloc::alloc, ops::Add};

use crate::gadgets::{bellpepper_uint64::UInt64, ntt_mult::*};
use crate::shake256::{SHAKE256_BLOCK_LENGTH_BYTES, SHAKE256_DIGEST_LENGTH_BITS, keccak_f_1600, library_step_sponge};
use crate::utils::{bits_to_bytes_le, bytes_to_bits_le, enforce_less_than_q, enforce_less_than_norm_bound, inner_product_mod, mod_q, normalize_half_q, num_to_alloc, select_from_vec_linear};
use crate::ntt_mult::{ntt_deferred_circuit, inv_ntt_deferred_circuit, ntt, ntt_mult_const_p2};
use crate::circuit::{COEFF_INDEX_MASK, OP_COEFF_INDEX_FIRST, OP_COEFF_INDEX_LAST, OP_SHAKE256_ACTIVE, OP_SHAKE256_NO_OP, NUM_OPCODE_BITS};

use bellpepper::gadgets::multipack;
use bellpepper_core::{boolean::Boolean, num::AllocatedNum, ConstraintSystem, SynthesisError};
use blstrs::Scalar;
use falcon_rust::{LOG_N, MODULUS, N, Polynomial, PublicKey, Signature, SIG_L2_BOUND};
use ff::PrimeFieldBits;
use nova_aadhaar_qr::poseidon::PoseidonHasher;
use nova_aadhaar_qr::util::{alloc_constant, alloc_num_equals, alloc_num_equals_constant, boolean_implies, conditionally_select, less_than, num_to_bits};
use crate::shake256::library_shake_256;
use nova_snark::traits::circuit::StepCircuit;
use num_bigint::{BigInt,Sign};
use std::array::from_fn;

#[derive(Clone, Debug)]
pub struct NaiveProofOfPossessionCircuit<Scalar>
where 
    Scalar: PrimeFieldBits + PartialOrd,
{
    // TODO: check whether to keep l2_norm_sum as public input or not.
    pub l2_norm_sum: u64,
    pub coeff_index: u16,
    pub hash_c: Scalar,
    pub hash_s2: Scalar,
    pub shake_inject_m: Scalar,
    pub s2: Polynomial,
    pub c: [u16; N],
    pub h: Polynomial,
}

impl<Scalar> Default for NaiveProofOfPossessionCircuit<Scalar> 
where 
    Scalar: PrimeFieldBits + PartialOrd,
{
    fn default() -> Self {
        Self {
            l2_norm_sum: 0u64,
            coeff_index: 0u16,
            hash_c: Scalar::ZERO,
            hash_s2: Scalar::ZERO,
            shake_inject_m: Scalar::ZERO,
            s2: Polynomial::default(),
            c: [0u16; N],
            h: Polynomial::default(),
        }
    }
}

impl<Scalar> NaiveProofOfPossessionCircuit<Scalar>
where
    Scalar: PrimeFieldBits + PartialOrd,
{
    // calculate z_0
    pub fn calc_initial_primary_circuit_input(msg: &Vec<u8>, sig: &Signature) -> Vec<Scalar> {
        let initial_l2_norm_sum = Scalar::from(0u64);
        let intial_coeff_index = Scalar::from(0u64);
        
        // pack byte array into a field element for shake_inject_m
        let shake_inject_m_bytes: [u8; 16] = library_shake_256(msg, SHAKE256_DIGEST_LENGTH_BITS / 8)[..16].try_into().unwrap();
        let shake_inject_m_bits = multipack::bytes_to_bits(&shake_inject_m_bytes);
        let shake_inject_m_scalars = multipack::compute_multipacking::<Scalar>(&shake_inject_m_bits);
        assert_eq!(shake_inject_m_scalars.len(), 1);
        let shake_inject_m = shake_inject_m_scalars[0];

        // Decompress returns polynomial with signed integers as coefficients
        let s2_poly: Polynomial = sig.into();
        let s2_scalars: Vec<Scalar> = s2_poly.coeff().iter().map(|&x| {
            let signed = x as i16;
            let modq: u16 = if signed < 0 {
                (signed as i32 + MODULUS as i32) as u16
            } else {
                signed as u16
            };
            Scalar::from(modq as u64)
        }).collect();
        let c: Vec<u16> = Polynomial::from_hash_of_message(msg.as_ref(), sig.nonce()).coeff().iter().map(|x| *x as u16).collect::<Vec<u16>>().try_into().unwrap();
        
        // calculate hash_c and hash_s2
        let c_scalars: Vec<Scalar> = c.iter().map(|&x| Scalar::from(x as u64)).collect();
        // let s2_scalars: Vec<Scalar> = s2.iter().map(|&x| Scalar::from(x as u64)).collect();
        let c_hasher = PoseidonHasher::<Scalar>::new(c_scalars.len() as u32);
        let hash_c = c_hasher.hash(&c_scalars);
        let s2_hasher = PoseidonHasher::<Scalar>::new(s2_scalars.len() as u32);
        let hash_s2 = s2_hasher.hash(&s2_scalars);

        // The last scalar corresponds to the current date
        vec![initial_l2_norm_sum, intial_coeff_index, hash_c, hash_s2, shake_inject_m]
    }

    // calculate NaiveProofOfPossessionCircuit for all steps
    pub fn new_state_sequence(
        msg: &Vec<u8>,
        sig: &Signature,
        pk: PublicKey,
    ) -> Vec<NaiveProofOfPossessionCircuit<Scalar>> {
        
        let mut naive_incremental_falcon: Vec<NaiveProofOfPossessionCircuit<Scalar>> = vec![];

        let [_, _, hash_c, hash_s2, shake_inject_m]: [Scalar; 5] = Self::calc_initial_primary_circuit_input(msg, &sig).try_into().unwrap();
        let s2_raw: Polynomial = sig.into();
        let s2_modq: [u16; N] = from_fn(|i| {
            let signed = s2_raw.coeff()[i] as i16;
            if signed < 0 {
                (signed as i32 + MODULUS as i32) as u16
            } else {
                signed as u16
            }
        });
        let s2 = Polynomial(s2_modq);
        let c: Vec<u16> = Polynomial::from_hash_of_message(msg.as_ref(), sig.nonce()).coeff().iter().map(|x| *x as u16).collect::<Vec<u16>>().try_into().unwrap();
        let pk_poly: Polynomial = (&pk).into();
        let mut l2_norm_sum = 0u64;
        let mut coeff_index = OP_COEFF_INDEX_FIRST;

        // First step
        naive_incremental_falcon.push(Self {
            l2_norm_sum: l2_norm_sum,
            coeff_index: coeff_index,
            hash_c: hash_c,
            hash_s2: hash_s2,
            shake_inject_m: shake_inject_m,
            s2: s2,
            c: c.clone().try_into().unwrap(),
            h: pk_poly,
        });

        let normalize_coeff_host = |val: i64| -> u64 {
            let modulus = MODULUS as i64;
            let mut residue = val % modulus;
            if residue < 0 {
                residue += modulus;
            }
            if residue > modulus / 2 {
                (modulus - residue) as u64
            } else {
                residue as u64
            }
        };

        for i in 1..512 {
            coeff_index = coeff_index + 1;
            let ntt_s2 = ntt(&s2);
            let ntt_h = ntt(&pk_poly);
            let ntt_s2h = ntt_s2.mul(ntt_h);
            let prod_s2h = inv_ntt(&ntt_s2h);
            let prod_s2h_coeff = prod_s2h.coeff()[i];
            let s1_coeff = (c[i] + MODULUS - prod_s2h_coeff as u16) % MODULUS as u16;
            let s1_norm = normalize_coeff_host(s1_coeff as i64);
            let s2_norm = normalize_coeff_host(s2.coeff()[i] as i64);
            l2_norm_sum = l2_norm_sum + s1_norm * s1_norm + s2_norm * s2_norm;
            if l2_norm_sum >= SIG_L2_BOUND as u64 {
                panic!("L2 norm exceeded SIG_L2_BOUND at coeff {}: {}", i, l2_norm_sum);
            }

            naive_incremental_falcon.push(Self {
                l2_norm_sum: l2_norm_sum,
                coeff_index: coeff_index,
                hash_c: hash_c,
                hash_s2: hash_s2,
                shake_inject_m: shake_inject_m,
                s2: s2.clone(),
                c: c.clone().try_into().unwrap(),
                h: pk_poly,
            });
        }

        naive_incremental_falcon
    }
}

impl<Scalar> StepCircuit<Scalar> for NaiveProofOfPossessionCircuit<Scalar>
where
    Scalar: PrimeFieldBits + PartialOrd,
{
    fn arity(&self) -> usize {
        5
    }

    fn synthesize<CS>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<Scalar>],
    ) -> Result<Vec<AllocatedNum<Scalar>>, SynthesisError>
    where
        CS: ConstraintSystem<Scalar>
    {
        let zero_var = alloc_constant(cs.namespace(|| "alloc_constant zero"), Scalar::from(0u64))?;
        cs.enforce(
            || "enforce zero_var = 0",
            |lc| lc + zero_var.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc,
        );

        let l2_norm_sum = z[0].clone();
        let coeff_index = z[1].clone();
        let hash_c = z[2].clone();
        let hash_s2 = z[3].clone();
        let shake_inject_m = z[4].clone();

        // create witnesses using AllocatedNum::alloc for each coefficient of c and s2
        let c_vars = self.c.iter().enumerate().map(|(i,&x)| {
            AllocatedNum::alloc(cs.namespace(|| format!("alloc c coefficient {}", i)), || {Ok(Scalar::from(x as u64))})
        }).collect::<Result<Vec<AllocatedNum<Scalar>>, SynthesisError>>()?;
        
        // no range check enforced on s2 coefficients as if any s2[i] > q then s2[i]^2 > 12289^2 > SIG_L2_BOUND = 34034726
        let s2_vars = self.s2.coeff().iter().enumerate().map(|(i,&x)| {
            AllocatedNum::alloc(cs.namespace(|| format!("alloc s2 coefficient {}", i)), || {Ok(Scalar::from(x as u64))})
        }).collect::<Result<Vec<AllocatedNum<Scalar>>, SynthesisError>>()?;

        // enforce H_pos(c) = Hash_c
        let c_hasher = PoseidonHasher::<Scalar>::new(c_vars.len() as u32);
        let hpos_c = c_hasher.hash_in_circuit(
            &mut cs.namespace(|| "poseidon hash c coefficients"),
            &c_vars,
        )?;
        cs.enforce(
            || "enforce H_pos(c) == hash_c",
            |lc| lc + hpos_c.get_variable() - hash_c.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc,
        );
        // enforce H_pos(s2) = Hash_s2
        let s2_hasher = PoseidonHasher::<Scalar>::new(s2_vars.len() as u32);
        let hpos_s2 = s2_hasher.hash_in_circuit(
            &mut cs.namespace(|| "poseidon hash s2 coefficients"),
            &s2_vars,
        )?;
        cs.enforce(
            || "enforce H_pos(s2) == hash_s2",
            |lc| lc + hpos_s2.get_variable() - hash_s2.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc,
        );

        let s2_coeff = select_from_vec_linear(cs.namespace(|| "s2_coeff"), &s2_vars, &coeff_index)?;
        let c_coeff = select_from_vec_linear(cs.namespace(|| "c_coeff"), &c_vars, &coeff_index)?;
        
        // No range check needed for c as it is a public input
        // enforce_less_than_q(cs.namespace(|| "enforce_less_than_q naive_incremental"), &c_coeff)?;

        let var_511 = alloc_constant(cs.namespace(|| "alloc_constant 512"), Scalar::from(511u64))?;
        let flag_coeff = less_than(cs.namespace(|| "flag_coeff"), &coeff_index, &var_511, LOG_N)?;
        
        let ntt_s2 = ntt_deferred_circuit(cs.namespace(|| "ntt_deferred_circuit s2"), &s2_vars)?;
        let ntt_h = ntt(&self.h);
        let ntt_s2h = ntt_mult_const_p2(cs.namespace(|| "ntt_mult_const_p2"), ntt_s2, ntt_h)?;
        let prod_s2h = inv_ntt_deferred_circuit(cs.namespace(|| "inv_ntt_deferred_circuit s2h"), ntt_s2h)?;
        let prod_s2h = prod_s2h
            .iter().enumerate()
            .map(|(i, x)| num_to_alloc(cs.namespace(|| format!("alloc prod_s2h coeff {}", i)), &x))
            .collect::<Result<Vec<AllocatedNum<Scalar>>, SynthesisError>>()?;
        let prod_s2h_coeff = select_from_vec_linear(cs.namespace(|| "select_from_vec_linear prod_s2h_coeff"), &prod_s2h, &coeff_index)?;
        let prod_s2h_coeff = mod_q(cs.namespace(|| "mod_q prod_s2h_coeff"), &prod_s2h_coeff)?;

        // calculate s1_coeff
        let flag_coeff_c_less_s2h = less_than(
            cs.namespace(|| "flag_coeff_c_less_s2h"),
            &c_coeff,
            &prod_s2h_coeff,
            14,
        )?;
        let c_lt_s2h = AllocatedNum::alloc(cs.namespace(|| "c_lt_s2h"), || {
            let c_coeff_val = c_coeff
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            let prod_s2h_coeff_val = prod_s2h_coeff
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            Ok(c_coeff_val + Scalar::from(MODULUS as u64) - prod_s2h_coeff_val)
        })?;
        cs.enforce(
            || "c_lt_s2h = c_coeff + q - prod_s2h_coeff",
            |lc| lc + c_lt_s2h.get_variable() + prod_s2h_coeff.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + c_coeff.get_variable() + (Scalar::from(MODULUS as u64), CS::one()),
        );
        let c_minus_s2h = AllocatedNum::alloc(cs.namespace(|| "c_minus_s2h"), || {
            let c_coeff_val = c_coeff
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            let prod_s2h_coeff_val = prod_s2h_coeff
                .get_value()
                .ok_or(SynthesisError::AssignmentMissing)?;
            Ok(c_coeff_val - prod_s2h_coeff_val)
        })?;
        cs.enforce(
            || "c_minus_s2h = c_coeff - prod_s2h_coeff",
            |lc| lc + c_minus_s2h.get_variable() + prod_s2h_coeff.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + c_coeff.get_variable(),
        );
        let s1_coeff = conditionally_select(
            cs.namespace(|| "s1_coeff conditional select"),
            &c_lt_s2h,
            &c_minus_s2h,
            &flag_coeff_c_less_s2h,
        )?;

        // normalize coefficients to [-q/2, q/2] before squaring
        let s2_normalized = normalize_half_q(&mut cs.namespace(|| "normalize s2"), &s2_coeff)?;
        let s2_coeff_sq = s2_normalized.mul(cs.namespace(|| "s2_normalized*s2_normalized"), &s2_normalized)?;

        // TODO: check if need to impose range check on coefficients of s1
        let s1_normalized = normalize_half_q(&mut cs.namespace(|| "normalize s1"), &s1_coeff)?;
        let s1_coeff_sq = s1_normalized.mul(cs.namespace(|| "s1_normalized*s1_normalized"), &s1_normalized)?;

        let sum_update = s1_coeff_sq.add(cs.namespace(|| "s1_coeff^2 + s2_coeff^2"), &s2_coeff_sq)?;
        
        // update sum_aggregated
        let var1 = alloc_constant(cs.namespace(|| "alloc_constant 1"), Scalar::from(1u64))?;
        let coeff_index = coeff_index.add(cs.namespace(||"coeff_index + 1 naive_incremental"), &var1)?;
        let l2_norm_sum = l2_norm_sum.add(
            cs.namespace(|| "l2_norm_sum update"),
            &sum_update
        )?;
        
        // enforce norm bound once coeff_index = 511
        let flag_norm_bound = enforce_less_than_norm_bound(cs.namespace(|| "enforce_less_than_norm_bound naive_incremental"), &l2_norm_sum)?;
        Boolean::or(cs.namespace(|| "boolean or flag_coeff flag_norm_bound"), &flag_coeff, &flag_norm_bound)?;

        let z_out = vec![l2_norm_sum, coeff_index, hash_c, hash_s2, shake_inject_m];
        Ok(z_out)
    }
}