use std::ops::Mul;
use std::{alloc::alloc, ops::Add};

use crate::gadgets::{bellpepper_uint64::UInt64, ntt::*};
use crate::hash::shake256::{SHAKE256_BLOCK_LENGTH_BYTES, SHAKE256_DIGEST_LENGTH_BITS, 
                            SHAKE256_DIGEST_LENGTH_BYTES, SHAKE256_RATE_BYTES, 
                            keccak_f_1600, library_step_sponge, shake256_pad101};
use crate::subarray::var_shift_left;
use crate::utils::{normalize_coeff, bits_to_bytes_le, bytes_to_bits_le, enforce_less_than_q, 
                    enforce_less_than_norm_bound, inner_product_mod, mod_q, normalize_half_q, 
                    num_to_alloc, select_from_vec_linear};
use crate::ntt::{ntt_deferred_circuit, inv_ntt_deferred_circuit, ntt, ntt_mult_const_p2};
use crate::age_proof::{COEFF_INDEX_MASK, OP_COEFF_INDEX_FIRST, 
                        OP_COEFF_INDEX_LAST, OP_SHAKE256_ACTIVE, OP_SHAKE256_NO_OP, NUM_OPCODE_BITS};

use bellpepper::gadgets::multipack::{bytes_to_bits, compute_multipacking};
use bellpepper_core::{boolean::Boolean, num::AllocatedNum, ConstraintSystem, SynthesisError};
use blstrs::Scalar;
use falcon_rust::{LOG_N, MODULUS, N, Polynomial, PublicKey, Signature, SIG_L2_BOUND};
use ff::{PrimeFieldBits,PrimeField};
use nova_aadhaar_qr::poseidon::PoseidonHasher;
use nova_aadhaar_qr::util::{alloc_constant, alloc_num_equals, alloc_num_equals_constant, 
                            boolean_implies, conditionally_select, less_than, num_to_bits};
use crate::hash::shake256::shake_256;
use nova_snark::traits::circuit::StepCircuit;
use num_bigint::{BigInt,Sign};

#[derive(Clone, Debug)]
pub struct AggregatedProofOfPossessionCircuit<Scalar>
where 
    Scalar: PrimeField + PartialOrd,
{
    // TODO: check whether to keep l2_norm_sum as public input or not.
    coeff_index: u64,
    l2_norm_sum: u64,
    hash_c: Scalar,
    hash_s2: Scalar,
    shake_inject_m_block: Scalar,
    // io_hash: Scalar,
    s2: Polynomial,
    c: Polynomial,
    h: Polynomial,
}

impl<Scalar> Default for AggregatedProofOfPossessionCircuit<Scalar> 
where 
    Scalar: PrimeField + PartialOrd,
{
    fn default() -> Self {
        Self {
            coeff_index: 0u64,
            l2_norm_sum: 0u64,
            hash_c: Scalar::ZERO,
            hash_s2: Scalar::ZERO,
            shake_inject_m_block: Scalar::ZERO,
            // io_hash: Scalar::ZERO,
            s2: Polynomial::default(),
            c: Polynomial::default(),
            h: Polynomial::default(),
        }
    }
}

impl<Scalar> AggregatedProofOfPossessionCircuit<Scalar>
where
    Scalar: PrimeFieldBits + PartialOrd,
{
    // calculate z_0
    pub fn calc_initial_primary_circuit_input(msg: &Vec<u8>, sig: &Signature) -> Vec<Scalar> {
        let initial_l2_norm_sum = Scalar::from(0u64);
        let intial_coeff_index = Scalar::from(0u64);

        let msg_bits = shake256_pad101(msg);
        let padded_msg: Vec<u8> = bits_to_bytes_le(&msg_bits).try_into().unwrap();
        let shake_inject_m_bytes: [u8; SHAKE256_DIGEST_LENGTH_BYTES] =
            shake_256(&padded_msg, SHAKE256_DIGEST_LENGTH_BYTES).try_into().unwrap();
        let shake_inject_m_bits = bytes_to_bits(&shake_inject_m_bytes);
        let shake_inject_m: Vec<Scalar> = compute_multipacking::<Scalar>(&shake_inject_m_bits);
        assert_eq!(shake_inject_m.len(), 7);
        // pack byte array into a field elements for shake_inject_m
        // println!("length of shake_inject_m: {}", shake_inject_m.len());
        let c: Polynomial = Polynomial::from_hash_of_message(msg.as_ref(), sig.nonce());

        // calculate hash_c and hash_s2
        let c_scalars: Vec<Scalar> = c.coeff().iter().map(|&x| Scalar::from(x as u64)).collect();
        let c_hasher = PoseidonHasher::<Scalar>::new(c_scalars.len() as u32);
        let hash_c = c_hasher.hash(&c_scalars);
        // io_hash
        // let io_hash_scalars = [c_scalars, s2_scalars, vec![initial_l2_norm_sum, intial_coeff_index]].concat();
        // let io_hash_scalars = [c_scalars, s2_scalars, vec![intial_coeff_index]].concat();
        // let hasher = PoseidonHasher::<Scalar>::new(io_hash_scalars.len() as u32);
        // let io_hash = hasher.hash(&io_hash_scalars);
        // The last scalar corresponds to the current date
        vec![initial_l2_norm_sum, intial_coeff_index, hash_c, shake_inject_m[0]]
    }

    // calculate AggregatedProofOfPossessionCircuit for all steps
    pub fn new_state_sequence(
        msg: &Vec<u8>,
        sig: &Signature,
        pk: PublicKey,
    ) -> Vec<AggregatedProofOfPossessionCircuit<Scalar>> {
        
        let mut aggregated_incremental_falcon: Vec<AggregatedProofOfPossessionCircuit<Scalar>> = vec![];
        
        let s2: Polynomial = sig.into();
        let c: Polynomial = Polynomial::from_hash_of_message(msg.as_ref(), sig.nonce());
        let pk_poly: Polynomial = (&pk).into();
        let mut l2_norm_sum = 0u64;
        let mut coeff_index = OP_COEFF_INDEX_FIRST;
        let c_scalars = c.coeff().iter().map(|&x| Scalar::from(x as u64)).collect::<Vec<Scalar>>();
        let s2_scalars = s2.coeff().iter().map(|&x| Scalar::from(x as u64)).collect::<Vec<Scalar>>();
        let c_hasher = PoseidonHasher::<Scalar>::new(c_scalars.len() as u32);
        let hash_c = c_hasher.hash(&c_scalars);
        let s2_hasher = PoseidonHasher::<Scalar>::new(s2_scalars.len() as u32);
        let hash_s2 = s2_hasher.hash(&s2_scalars);

        let msg_bits = shake256_pad101(msg);
        let padded_msg: Vec<u8> = bits_to_bytes_le(&msg_bits).try_into().unwrap();
        let shake_inject_m_bytes: [u8; SHAKE256_DIGEST_LENGTH_BYTES] =
            shake_256(&padded_msg, SHAKE256_DIGEST_LENGTH_BYTES).try_into().unwrap();
        let shake_inject_m_bits = bytes_to_bits(&shake_inject_m_bytes);
        let shake_inject_m: Vec<Scalar> = compute_multipacking::<Scalar>(&shake_inject_m_bits);
        assert_eq!(shake_inject_m.len(), 7);

        aggregated_incremental_falcon.push(Self {
            l2_norm_sum: l2_norm_sum,
            coeff_index: coeff_index,
            hash_c: hash_c,
            hash_s2: hash_s2,
            shake_inject_m_block: shake_inject_m[0],
            s2: s2.clone(),
            c: c.clone().try_into().unwrap(),
            h: pk_poly.clone(),
        });
        
        // compute s2*h modulo q
        let ntt_s2 = ntt(&s2);
        let ntt_h = ntt(&pk_poly);
        let ntt_s2h = ntt_s2.mul(ntt_h);
        let prod_s2h = inv_ntt(&ntt_s2h);
        for i in 1..8 {
            // let s2_subarray64 = s2.coeff()[coeff_index as usize..(coeff_index + 64u64) as usize].to_vec();
            // let c_subarray64 = c.coeff()[coeff_index as usize..(coeff_index + 64u64) as usize].to_vec();
            // let prod_s2h_subarray64 = prod_s2h.coeff()[coeff_index as usize..(coeff_index + 64u64) as usize].to_vec();
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

            aggregated_incremental_falcon.push(Self {
                l2_norm_sum: l2_norm_sum,
                coeff_index: coeff_index,
                hash_c: hash_c,
                hash_s2: hash_s2,
                shake_inject_m_block: shake_inject_m[i % shake_inject_m.len()],
                s2: s2.clone(),
                c: c.clone().try_into().unwrap(),
                h: pk_poly,
            });
        }

        aggregated_incremental_falcon
    }
}

impl<Scalar> StepCircuit<Scalar> for AggregatedProofOfPossessionCircuit<Scalar>
where
    Scalar: PrimeFieldBits + PartialOrd,
{
    fn arity(&self) -> usize {
        4
    }

    fn synthesize<CS>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<Scalar>],
    ) -> Result<Vec<AllocatedNum<Scalar>>, SynthesisError>
    where
        CS: ConstraintSystem<Scalar>
    {   
        let mut l2_norm_sum_var = z[0].clone();
        let mut coeff_index_var = z[1].clone();
        let hash_c = z[2].clone();
        let cur_shake_inject_m_block = z[3].clone();
        // let shake_inject_m = AllocatedNum::alloc(
        //     cs.namespace(|| "shake_inject_m alloc"),
        //     || Ok(self.shake_inject_m_block),
        // )?;

        let c_scalars = self.c.coeff().iter().map(|&x| Scalar::from(x as u64)).collect::<Vec<Scalar>>();
        let s2_scalars = self.s2.coeff().iter().map(|&x| Scalar::from(x as u64)).collect::<Vec<Scalar>>();
        let c_vars = c_scalars.iter().enumerate().map(|(i,&x)| {
            AllocatedNum::alloc(cs.namespace(|| format!("alloc c coefficient {}", i)), || {Ok(x)})
        }).collect::<Result<Vec<AllocatedNum<Scalar>>, SynthesisError>>()?;
        // no range check enforced on s2 coefficients as if any s2[i] > q then s2[i]^2 > 12289^2 > SIG_L2_BOUND = 34034726
        let s2_vars = s2_scalars.iter().enumerate().map(|(i,&x)| {
            AllocatedNum::alloc(cs.namespace(|| format!("alloc s2 coefficient {}", i)), || {Ok(x)})
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

        // no need to enforce hash match for s2 as in each step more than coefficient is used.
        // let s2_hasher = PoseidonHasher::<Scalar>::new(s2_vars.len() as u32);
        // let hpos_s2 = s2_hasher.hash_in_circuit(
        //     &mut cs.namespace(|| "poseidon hash s2 coefficients"),
        //     &s2_vars,
        // )?;
        // cs.enforce(
        //     || "enforce H_pos(s2) == hash_s2",
        //     |lc| lc + hpos_s2.get_variable() - hash_s2.get_variable(),
        //     |lc| lc + CS::one(),
        //     |lc| lc,
        // );

        // No range check needed for c as it configured is a public input
        
        let s2_lshifted = var_shift_left(cs.namespace(|| "var_shift_left s2"), &s2_vars, &coeff_index_var, N, LOG_N)?;
        let c_lshifted = var_shift_left(cs.namespace(|| "var_shift_left c"), &c_vars, &coeff_index_var, N, LOG_N)?;
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
        let prod_s2h_lshifted = var_shift_left(cs.namespace(|| "var_shift_left prod_s2h"), &prod_s2h, &coeff_index_var, N, LOG_N)?;
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
            coeff_index_var = coeff_index_var.add(cs.namespace(|| format!("coeff_index = coeff_index + 1_{}", k)), &var1)?;
        }
        
        l2_norm_sum_var = l2_norm_sum_var.add(cs.namespace(|| "l2_norm_sum = l2_norm_sum + sum_update"), &sum_aggregated)?;
        
        let var_512 = alloc_constant(cs.namespace(|| "alloc_constant 512"), Scalar::from(512u64))?;
        let flag_coeff = less_than(cs.namespace(|| "flag_coeff"), &coeff_index_var, &var_512, LOG_N + 1)?;
        
        // enforce norm bound once all 512 coefficients have been processed
        let flag_norm_bound = enforce_less_than_norm_bound(cs.namespace(|| "enforce_less_than_norm_bound naive_incremental"), &l2_norm_sum_var)?;
        let res = Boolean::or(cs.namespace(|| "boolean or flag_coeff flag_norm_bound"), &flag_coeff, &flag_norm_bound)?;
        Boolean::enforce_equal(cs.namespace(|| "enforce or result is true"), &res, &Boolean::Constant(true))?;

        let z_out = vec![l2_norm_sum_var, coeff_index_var, hash_c, cur_shake_inject_m_block];
        Ok(z_out)
    }
}