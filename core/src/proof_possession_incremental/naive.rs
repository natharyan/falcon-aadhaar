use std::ops::Mul;
use std::{alloc::alloc, ops::Add};

use crate::gadgets::ntt::*;
use crate::hash::shake256::{SHAKE256_BLOCK_LENGTH_BYTES, SHAKE256_DIGEST_LENGTH_BITS, SHAKE256_DIGEST_LENGTH_BYTES, SHAKE256_RATE_BYTES, keccak_f_1600, library_step_sponge, shake256_pad101};
use crate::utils::{bits_to_bytes_le, bytes_to_bits_le, enforce_less_than_q, enforce_less_than_norm_bound, inner_product_mod, mod_q, normalize_half_q, num_to_alloc, select_from_vec_linear};
use crate::ntt::{ntt_deferred_circuit, inv_ntt_deferred_circuit, ntt, ntt_mult_const_p2};
use crate::age_proof::{COEFF_INDEX_MASK, OP_COEFF_INDEX_FIRST, OP_COEFF_INDEX_LAST, OP_SHAKE256_ACTIVE, OP_SHAKE256_NO_OP, NUM_OPCODE_BITS};

use bellpepper::gadgets::multipack::{bytes_to_bits, compute_multipacking};
use bellpepper_core::{boolean::Boolean, num::AllocatedNum, ConstraintSystem, SynthesisError};
use blstrs::Scalar;
use falcon_rust::{LOG_N, MODULUS, N, Polynomial, PublicKey, Signature, SIG_L2_BOUND};
use ff::PrimeFieldBits;
use nova_aadhaar_qr::poseidon::PoseidonHasher;
use nova_aadhaar_qr::util::{alloc_constant, alloc_num_equals, alloc_num_equals_constant, boolean_implies, conditionally_select, less_than, num_to_bits};
use crate::hash::shake256::shake_256;
use nova_snark::traits::circuit::StepCircuit;
use num_bigint::{BigInt,Sign};

#[derive(Clone, Debug)]
pub struct NaiveProofOfPossessionCircuit<Scalar>
where 
    Scalar: PrimeFieldBits + PartialOrd,
{
    // TODO: check whether to keep l2_norm_sum as public input or not.
    coeff_index: Scalar,
    l2_norm_sum: u64,
    hash_c: Scalar,
    hash_s2: Scalar,
    shake_inject_m: Scalar,
    // pub io_hash: Scalar,
    s2: Polynomial,
    c: [u16; N],
    h: Polynomial,
}

impl<Scalar> Default for NaiveProofOfPossessionCircuit<Scalar> 
where 
    Scalar: PrimeFieldBits + PartialOrd,
{
    fn default() -> Self {
        Self {
            coeff_index: Scalar::ZERO,
            l2_norm_sum: 0u64,
            hash_c: Scalar::ZERO,
            hash_s2: Scalar::ZERO,
            shake_inject_m: Scalar::ZERO,
            // io_hash: Scalar::ZERO,
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

        let msg_bits = shake256_pad101(msg);
        let padded_msg: Vec<u8> = bits_to_bytes_le(&msg_bits).try_into().unwrap();
        let shake_inject_m_bytes: [u8; SHAKE256_DIGEST_LENGTH_BYTES] =
            shake_256(&padded_msg, SHAKE256_DIGEST_LENGTH_BYTES).try_into().unwrap();
        let shake_inject_m_bits = bytes_to_bits(&shake_inject_m_bytes);
        let shake_inject_m = compute_multipacking::<Scalar>(&shake_inject_m_bits);
        assert_eq!(shake_inject_m.len(), 7);

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

    // calculate NaiveProofOfPossessionCircuit for all steps
    pub fn new_state_sequence(
        msg: &Vec<u8>,
        sig: &Signature,
        pk: PublicKey,
    ) -> Vec<NaiveProofOfPossessionCircuit<Scalar>> {
        
        let mut naive_incremental_falcon: Vec<NaiveProofOfPossessionCircuit<Scalar>> = vec![];
        
        let s2: Polynomial = sig.into();
        let c: Vec<u16> = Polynomial::from_hash_of_message(msg.as_ref(), sig.nonce()).coeff().iter().map(|x| *x as u16).collect::<Vec<u16>>().try_into().unwrap();
        let pk_poly: Polynomial = (&pk).into();
        let mut l2_norm_sum = 0u64;
        let mut coeff_index = Scalar::from(OP_COEFF_INDEX_FIRST as u64);
        let c_scalars = c.iter().map(|&x| Scalar::from(x as u64)).collect::<Vec<Scalar>>();
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
        let shake_inject_m = compute_multipacking::<Scalar>(&shake_inject_m_bits);
        assert_eq!(shake_inject_m.len(), 7);
        // let io_hash_scalars = [c_scalars.clone(), s2_scalars.clone(), vec![l2_norm_sum.into(), coeff_index.into()]].concat();
        // let io_hash_scalars = [c_scalars.clone(), s2_scalars.clone(), vec![coeff_index.into()]].concat();
        // let hasher = PoseidonHasher::<Scalar>::new(io_hash_scalars.len() as u32);
        // let io_hash = hasher.hash(&io_hash_scalars);

        // First step
        naive_incremental_falcon.push(Self {
            l2_norm_sum: l2_norm_sum,
            coeff_index: coeff_index,
            hash_c: hash_c,
            hash_s2: hash_s2,
            shake_inject_m: shake_inject_m[0],
            s2: s2,
            c: c.clone().try_into().unwrap(),
            h: pk_poly,
        });

        let normalize_coeff = |val: i64| -> u64 {
            let modulus = MODULUS as i64;
            if val > modulus / 2 {
                (modulus - val) as u64
            } else {
                val as u64
            }
        };

        for i in 1..512 {
            coeff_index = coeff_index + Scalar::from(1u64);
            // compute s2*h modulo q
            let ntt_s2 = ntt(&s2);
            let ntt_h = ntt(&pk_poly);
            let ntt_s2h = ntt_s2.mul(ntt_h);
            let prod_s2h = inv_ntt(&ntt_s2h);
            let prod_s2h_coeff = prod_s2h.coeff()[i];
            let s1_coeff = (c[i] + MODULUS - prod_s2h_coeff as u16) % MODULUS as u16;
            let s1_norm = normalize_coeff(s1_coeff as i64);
            let s2_norm = normalize_coeff(s2.coeff()[i] as i64);
            l2_norm_sum = l2_norm_sum + s1_norm * s1_norm + s2_norm * s2_norm;
            if l2_norm_sum >= SIG_L2_BOUND as u64 {
                panic!("L2 norm exceeded SIG_L2_BOUND at coeff {}: {}", i, l2_norm_sum);
            }
            // let io_hash_scalars = [c_scalars.clone(), s2_scalars.clone(), vec![l2_norm_sum.into(), coeff_index.into()]].concat();
            // let io_hash_scalars = [c_scalars.clone(), s2_scalars.clone(), vec![coeff_index.into()]].concat();
            // let io_hash = hasher.hash(&io_hash_scalars);

            naive_incremental_falcon.push(Self {
                l2_norm_sum: l2_norm_sum,
                coeff_index: coeff_index,
                hash_c: hash_c,
                hash_s2: hash_s2,
                shake_inject_m: shake_inject_m[i % shake_inject_m.len()],
                s2: s2.clone(),
                c: c.clone().try_into().unwrap(),
                h: pk_poly,
                // io_hash: io_hash,
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
        let l2_norm_sum_var = z[0].clone();
        let coeff_index_var = z[1].clone();
        let hash_c = z[2].clone();
        let shake_inject_m = z[3].clone();

        let next_shake_inject_m = AllocatedNum::alloc(
            cs.namespace(|| "next_shake_inject_m alloc"),
            || Ok(self.shake_inject_m),
        )?;

        let c_scalars = self.c.iter().map(|&x| Scalar::from(x as u64)).collect::<Vec<Scalar>>();
        let s2_scalars = self.s2.coeff().iter().map(|&x| Scalar::from(x as u64)).collect::<Vec<Scalar>>();
        let c_vars = c_scalars.iter().enumerate().map(|(i,&x)| {
            AllocatedNum::alloc(cs.namespace(|| format!("alloc c coefficient {}", i)), || {Ok(x)})
        }).collect::<Result<Vec<AllocatedNum<Scalar>>, SynthesisError>>()?;
        // no range check enforced on s2 coefficients as if any s2[i] > q then s2[i]^2 > 12289^2 > SIG_L2_BOUND = 34034726
        let s2_vars = s2_scalars.iter().enumerate().map(|(i,&x)| {
            AllocatedNum::alloc(cs.namespace(|| format!("alloc s2 coefficient {}", i)), || {Ok(x)})
        }).collect::<Result<Vec<AllocatedNum<Scalar>>, SynthesisError>>()?;

        // let io_hash_vars = [c_vars.clone(), s2_vars.clone(), vec![l2_norm_sum_var.clone(), coeff_index_var.clone()]].concat();
        // let io_hash_vars = [c_vars.clone(), s2_vars.clone(), vec![coeff_index_var.clone()]].concat();
        // let io_hash_hasher = PoseidonHasher::<Scalar>::new(io_hash_vars.len() as u32);
        // let io_hash_calculated = io_hash_hasher.hash_in_circuit(
        //     &mut cs.namespace(|| "calculate io_hash in circuit"),
        //     &io_hash_vars,
        // )?;
        // cs.enforce(
        //     || "enforce io_hash consistency",
        //     |lc| lc + io_hash_cur.get_variable(),
        //     |lc| lc + CS::one(),
        //     |lc| lc + io_hash_calculated.get_variable(),
        // );

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
        // no need to enforce hash match for s2 as > 0 number of coefficients are used in each step
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

        let s2_coeff = select_from_vec_linear(cs.namespace(|| "s2_coeff"), &s2_vars, &coeff_index_var)?;
        let c_coeff = select_from_vec_linear(cs.namespace(|| "c_coeff"), &c_vars, &coeff_index_var)?;
        
        // No range check needed for c as it is configured to be a public input
        
        let ntt_s2 = ntt_deferred_circuit(cs.namespace(|| "ntt_deferred_circuit s2"), &s2_vars)?;
        let ntt_h = ntt(&self.h);
        let ntt_s2h = ntt_mult_const_p2(cs.namespace(|| "ntt_mult_const_p2"), ntt_s2, ntt_h)?;
        let prod_s2h = inv_ntt_deferred_circuit(cs.namespace(|| "inv_ntt_deferred_circuit s2h"), ntt_s2h)?;
        let prod_s2h = prod_s2h
            .iter().enumerate()
            .map(|(i, x)| num_to_alloc(cs.namespace(|| format!("alloc prod_s2h coeff {}", i)), &x))
            .collect::<Result<Vec<AllocatedNum<Scalar>>, SynthesisError>>()?;
        let prod_s2h_coeff = select_from_vec_linear(cs.namespace(|| "select_from_vec_linear prod_s2h_coeff"), &prod_s2h, &coeff_index_var)?;
        let prod_s2h_coeff = mod_q(cs.namespace(|| "mod_q prod_s2h_coeff"), &prod_s2h_coeff)?;

        // constraint s1_coeff
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

        // update l2 norm sum and coeff index
        let sum_update = s1_coeff_sq.add(cs.namespace(|| "s1_coeff^2 + s2_coeff^2"), &s2_coeff_sq)?;
        let var1 = alloc_constant(cs.namespace(|| "alloc_constant 1"), Scalar::from(1u64))?;
        let coeff_index_var = coeff_index_var.add(cs.namespace(|| "coeff_index = coeff_index + 1"), &var1)?;
        let l2_norm_sum_var = l2_norm_sum_var.add(cs.namespace(|| "l2_norm_sum = l2_norm_sum + sum_update"), &sum_update)?;
        
        let var_512 = alloc_constant(cs.namespace(|| "alloc_constant 512"), Scalar::from(512u64))?;
        let flag_coeff = less_than(cs.namespace(|| "flag_coeff"), &coeff_index_var, &var_512, LOG_N + 1)?;

        // let io_hash_next_inputs = [c_vars, s2_vars, vec![l2_norm_sum_var.clone(), coeff_index_var.clone()]].concat();
        // let io_hash_next_inputs = [c_vars, s2_vars, vec![coeff_index_var.clone()]].concat();
        // let io_hash_next = io_hash_hasher.hash_in_circuit(
        //     &mut cs.namespace(|| "calculate next io_hash in circuit"),
        //     &io_hash_next_inputs,
        // )?;

        // enforce norm bound once all 512 coefficients have been processed
        let flag_norm_bound = enforce_less_than_norm_bound(cs.namespace(|| "enforce_less_than_norm_bound naive_incremental"), &l2_norm_sum_var)?;
        let res = Boolean::or(cs.namespace(|| "boolean or flag_coeff flag_norm_bound"), &flag_coeff, &flag_norm_bound)?;
        Boolean::enforce_equal(cs.namespace(|| "enforce or result is true"), &res, &Boolean::Constant(true))?;

        let z_out = vec![l2_norm_sum_var, coeff_index_var, hash_c, next_shake_inject_m];
        Ok(z_out)
    }
}