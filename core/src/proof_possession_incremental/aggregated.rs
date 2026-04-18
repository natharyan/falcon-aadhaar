use std::alloc;
use std::ops::Mul;
use std::{
    alloc::alloc,
    ops::{Add, Div},
};

// use crate::gadgets::{bellpepper_uint64::UInt64};
use crate::age_proof::{
    COEFF_INDEX_MASK, NUM_OPCODE_BITS, OP_COEFF_INDEX_FIRST, OP_COEFF_INDEX_LAST,
    OP_SHAKE256_ACTIVE, OP_SHAKE256_NO_OP,
};
use crate::hash::shake256::{
    keccak_f_1600, library_shake256_inject, library_step_sponge, shake256_msg_blocks,
    shake256_pad101, SHAKE256_BLOCK_LENGTH_BYTES, SHAKE256_DIGEST_LENGTH_BITS,
    SHAKE256_DIGEST_LENGTH_BYTES, SHAKE256_RATE_BYTES,
};
use crate::ntt::*;
use crate::ntt::{inv_ntt_deferred_circuit, ntt, ntt_deferred_circuit, ntt_mult_const_p2};
use crate::subarray::var_shift_left;
use crate::utils::{
    bits_to_bytes_le, bytes_to_bits_le, enforce_less_than_norm_bound, enforce_less_than_q,
    inner_product_mod, mod_q, normalize_coeff, normalize_half_q, num_to_alloc,
    select_from_vec_linear,
};

use crate::hash::shake256::shake_256;
use bellpepper::gadgets::multipack::{bytes_to_bits, compute_multipacking, pack_bits};
use bellpepper_core::{boolean::Boolean, num::AllocatedNum, ConstraintSystem, SynthesisError};
use blstrs::Scalar;
use falcon_rust::{Polynomial, PublicKey, Signature, LOG_N, MODULUS, N, SIG_L2_BOUND};
use ff::{PrimeField, PrimeFieldBits};
use nova_aadhaar_qr::poseidon::PoseidonHasher;
use nova_aadhaar_qr::util::{
    alloc_constant, alloc_num_equals, alloc_num_equals_constant, boolean_implies,
    conditionally_select, less_than, num_to_bits,
};
use nova_snark::traits::circuit::StepCircuit;
use num_bigint::{BigInt, Sign};

#[derive(Clone, Debug)]
pub struct AggregatedProofOfPossessionCircuit<Scalar>
where
    Scalar: PrimeField + PartialOrd,
{
    coeff_index: u64,
    l2_norm_sum: u64,
    hash_c: Scalar,
    hash_inject: Scalar,
    ctx_inject_packed: [Scalar; 7],
    s2: Polynomial,
    c: Polynomial,
    h: PublicKey,
}

// impl<Scalar> Default for AggregatedProofOfPossessionCircuit<Scalar>
// where
//     Scalar: PrimeField + PartialOrd,
// {
//     fn default() -> Self {
//         Self {
//             coeff_index: 0u64,
//             l2_norm_sum: 0u64,
//             hash_c: Scalar::ZERO,
//             hash_inject: Scalar::ZERO,
//             ctx_inject_packed: [Scalar::ZERO; 7],
//             s2: Polynomial::default(),
//             c: Polynomial::default(),
//             h: Polynomial::default(),
//         }
//     }
// }

impl<Scalar> AggregatedProofOfPossessionCircuit<Scalar>
where
    Scalar: PrimeFieldBits + PartialOrd,
{
    pub fn default(h: PublicKey, s2: Polynomial, c: Polynomial) -> Self {
        Self {
            coeff_index: 0u64,
            l2_norm_sum: 0u64,
            hash_c: Scalar::ZERO,
            hash_inject: Scalar::ZERO,
            ctx_inject_packed: [Scalar::ZERO; 7],
            s2: s2,
            c: c,
            h: h,
        }
    }

    // calculate z_0
    pub fn calc_initial_primary_circuit_input(msg: &Vec<u8>, sig: &Signature) -> Vec<Scalar> {
        let initial_l2_norm_sum = Scalar::from(0u64);
        let intial_coeff_index = Scalar::from(0u64);

        let msg_blocks: Vec<[u8; 136]> = shake256_msg_blocks(&msg);
        let ctx_inject: [bool; 1600] = library_shake256_inject(
            [false; 1600],
            msg_blocks.iter().flatten().cloned().collect(),
        );
        let ctx_inject_bits = ctx_inject.to_vec();
        // 254 bools per scalar for multipacking
        let ctx_inject_packed: Vec<Scalar> = compute_multipacking::<Scalar>(&ctx_inject_bits);
        // println!("ctx_inject_packed len: {}", ctx_inject_packed.len());
        let inject_hasher = PoseidonHasher::<Scalar>::new(ctx_inject_packed.len() as u32);
        let hash_inject = inject_hasher.hash(&ctx_inject_packed);

        let c: Polynomial = Polynomial::from_hash_of_message(msg.as_ref(), sig.nonce());
        let c_scalars: Vec<Scalar> = c.coeff().iter().map(|&x| Scalar::from(x as u64)).collect();
        let c_hasher = PoseidonHasher::<Scalar>::new(c_scalars.len() as u32);
        let hash_c = c_hasher.hash(&c_scalars);

        vec![
            initial_l2_norm_sum,
            intial_coeff_index,
            hash_c,
            ctx_inject_packed[0],
            hash_inject,
        ]
    }

    // calculate AggregatedProofOfPossessionCircuit for all steps
    pub fn new_state_sequence(
        msg: &Vec<u8>,
        sig: &Signature,
        pk: PublicKey,
    ) -> Vec<AggregatedProofOfPossessionCircuit<Scalar>> {
        let mut aggregated_incremental_falcon: Vec<AggregatedProofOfPossessionCircuit<Scalar>> =
            vec![];

        let s2: Polynomial = sig.into();
        let c: Polynomial = Polynomial::from_hash_of_message(msg.as_ref(), sig.nonce());
        let pk_poly: Polynomial = (&pk).into();
        let mut l2_norm_sum = 0u64;
        let mut coeff_index = OP_COEFF_INDEX_FIRST;
        let c_scalars = c
            .coeff()
            .iter()
            .map(|&x| Scalar::from(x as u64))
            .collect::<Vec<Scalar>>();
        let c_hasher = PoseidonHasher::<Scalar>::new(c_scalars.len() as u32);
        let hash_c = c_hasher.hash(&c_scalars);
        let msg_blocks: Vec<[u8; 136]> = shake256_msg_blocks(&msg);
        let ctx_inject: [bool; 1600] = library_shake256_inject(
            [false; 1600],
            msg_blocks.iter().flatten().cloned().collect(),
        );
        let ctx_inject_bits = ctx_inject.to_vec();
        let ctx_inject_packed: Vec<Scalar> = compute_multipacking::<Scalar>(&ctx_inject_bits);
        let inject_hasher = PoseidonHasher::<Scalar>::new(ctx_inject_packed.len() as u32);
        let hash_inject = inject_hasher.hash(&ctx_inject_packed);

        // First step
        aggregated_incremental_falcon.push(Self {
            l2_norm_sum: l2_norm_sum,
            coeff_index: coeff_index,
            hash_c: hash_c,
            ctx_inject_packed: ctx_inject_packed.clone().try_into().unwrap(),
            hash_inject: hash_inject,
            s2: s2.clone(),
            c: c.clone().try_into().unwrap(),
            h: pk.clone(),
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
                let flag_coeff_c_less_2h =
                    if c.coeff()[coeff_index as usize] < prod_s2h.coeff()[coeff_index as usize] {
                        true
                    } else {
                        false
                    };
                // coefficients of both c and prod_s2h are already modulo q.
                let c_lt_s2h = c.coeff()[coeff_index as usize] + MODULUS
                    - prod_s2h.coeff()[coeff_index as usize];
                let s1_coeff = if flag_coeff_c_less_2h {
                    c_lt_s2h
                } else {
                    c.coeff()[coeff_index as usize] - prod_s2h.coeff()[coeff_index as usize]
                };
                let s1_normalized = normalize_coeff(s1_coeff as i64);
                let s2_normalized = normalize_coeff(s2.coeff()[coeff_index as usize] as i64);
                sum_aggregated =
                    sum_aggregated + s1_normalized * s1_normalized + s2_normalized * s2_normalized;
                if sum_aggregated >= SIG_L2_BOUND {
                    panic!(
                        "L2 norm exceeded SIG_L2_BOUND at coeff {}: {}",
                        coeff_index, sum_aggregated
                    );
                }
                coeff_index = coeff_index + 1u64;
            }

            l2_norm_sum = l2_norm_sum + sum_aggregated;
            if l2_norm_sum >= SIG_L2_BOUND as u64 {
                panic!(
                    "L2 norm exceeded SIG_L2_BOUND at coeff {}: {}",
                    i, l2_norm_sum
                );
            }

            aggregated_incremental_falcon.push(Self {
                l2_norm_sum: l2_norm_sum,
                coeff_index: coeff_index,
                hash_c: hash_c,
                ctx_inject_packed: ctx_inject_packed.clone().try_into().unwrap(),
                hash_inject: hash_inject,
                s2: s2.clone(),
                c: c.clone().try_into().unwrap(),
                h: pk.clone(),
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
        5
    }

    fn synthesize<CS>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<Scalar>],
    ) -> Result<Vec<AllocatedNum<Scalar>>, SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
    {
        let mut l2_norm_sum_var = z[0].clone();
        let coeff_index_init = z[1].clone();
        let mut coeff_index_var = z[1].clone();
        let hash_c = z[2].clone();
        let cur_shake_block = z[3].clone();
        let hash_inject = z[4].clone();

        let ctx_inject_packed_vars = self
            .ctx_inject_packed
            .iter()
            .enumerate()
            .map(|(i, &x)| {
                AllocatedNum::alloc(cs.namespace(|| format!("ctx_inject_packed_{i}")), || Ok(x))
            })
            .collect::<Result<Vec<_>, _>>()?;

        // Bind ctx_inject_packed witnesses to hash_inject (z[4]).
        let inject_hasher = PoseidonHasher::<Scalar>::new(ctx_inject_packed_vars.len() as u32);
        let hpos_ctx_inject = inject_hasher.hash_in_circuit(
            &mut cs.namespace(|| "poseidon_ctx_inject"),
            &ctx_inject_packed_vars,
        )?;
        cs.enforce(
            || "H_pos(ctx_inject) == hash_inject",
            |lc| lc + hpos_ctx_inject.get_variable() - hash_inject.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc,
        );

        let c_scalars: Vec<Scalar> = self
            .c
            .coeff()
            .iter()
            .map(|&x| Scalar::from(x as u64))
            .collect();
        let s2_scalars: Vec<Scalar> = self
            .s2
            .coeff()
            .iter()
            .map(|&x| Scalar::from(x as u64))
            .collect();

        // No range check on c coefficient as it is publicly verifiable
        let c_vars = c_scalars
            .iter()
            .enumerate()
            .map(|(i, &x)| AllocatedNum::alloc(cs.namespace(|| format!("c_{i}")), || Ok(x)))
            .collect::<Result<Vec<_>, _>>()?;

        // No range check enforced on s2 coefficients as if any s2[i] > q then s2[i]^2 > 12289^2 > SIG_L2_BOUND = 34034726
        let s2_vars = s2_scalars
            .iter()
            .enumerate()
            .map(|(i, &x)| AllocatedNum::alloc(cs.namespace(|| format!("s2_{i}")), || Ok(x)))
            .collect::<Result<Vec<_>, _>>()?;

        // Bind c witness to hash_c (z[2]) so same c is used across all steps.
        let c_hasher = PoseidonHasher::<Scalar>::new(c_vars.len() as u32);
        let hpos_c = c_hasher.hash_in_circuit(&mut cs.namespace(|| "poseidon_c"), &c_vars)?;
        cs.enforce(
            || "H_pos(c) == hash_c",
            |lc| lc + hpos_c.get_variable() - hash_c.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc,
        );

        // No need to enforce hash match for s2 as in each step more than coefficient is used and coeff_index is incremented accordingly.

        let s2_lshifted = var_shift_left(
            cs.namespace(|| "vsl_s2"),
            &s2_vars,
            &coeff_index_init,
            N,
            LOG_N,
        )?;
        let c_lshifted = var_shift_left(
            cs.namespace(|| "vsl_c"),
            &c_vars,
            &coeff_index_init,
            N,
            LOG_N,
        )?;
        let s2_subarray64: Vec<_> = s2_lshifted.iter().take(64).cloned().collect();
        let c_subarray64: Vec<_> = c_lshifted.iter().take(64).cloned().collect();

        // inv_ntt(ntt(s2)*ntt(h)) over mod q
        let mut sum_aggregated = alloc_constant(cs.namespace(|| "sum_agg_init"), Scalar::ZERO)?;
        let ntt_s2 = ntt_deferred_circuit(cs.namespace(|| "ntt_s2"), &s2_vars)?;
        let pk_poly: Polynomial = (&self.h).into();
        let ntt_h = ntt(&pk_poly);
        let ntt_s2h = ntt_mult_const_p2(cs.namespace(|| "ntt_s2h"), ntt_s2, ntt_h)?;
        let prod_s2h = inv_ntt_deferred_circuit(cs.namespace(|| "inv_ntt_s2h"), ntt_s2h)?;
        let prod_s2h = prod_s2h
            .iter()
            .enumerate()
            .map(|(i, x)| num_to_alloc(cs.namespace(|| format!("alloc_s2h_{i}")), x))
            .collect::<Result<Vec<_>, _>>()?;
        // Use coeff_index_init here too — same reason as above.
        let prod_s2h_lshifted = var_shift_left(
            cs.namespace(|| "vsl_s2h"),
            &prod_s2h,
            &coeff_index_init,
            N,
            LOG_N,
        )?;
        let prod_s2h_sub64: Vec<_> = prod_s2h_lshifted.iter().take(64).cloned().collect();
        // Reduce each coefficient mod q
        let prod_s2h_sub64_modq = prod_s2h_sub64
            .iter()
            .enumerate()
            .map(|(i, x)| mod_q(cs.namespace(|| format!("modq_s2h_{i}")), x))
            .collect::<Result<Vec<_>, _>>()?;

        let var1 = alloc_constant(cs.namespace(|| "const_1"), Scalar::ONE)?;

        for k in 0..64 {
            // Constraint s1_coeff
            let flag_c_lt = less_than(
                cs.namespace(|| format!("c_lt_s2h_{k}")),
                &c_subarray64[k],
                &prod_s2h_sub64_modq[k],
                14,
            )?;

            // Candidate: c[k] + q - s2h[k]  (when c < s2h)
            let c_pq_s2h =
                AllocatedNum::alloc(cs.namespace(|| format!("c_pq_s2h_{k} alloc")), || {
                    let cv = c_subarray64[k]
                        .get_value()
                        .ok_or(SynthesisError::AssignmentMissing)?;
                    let sv = prod_s2h_sub64_modq[k]
                        .get_value()
                        .ok_or(SynthesisError::AssignmentMissing)?;
                    Ok(cv + Scalar::from(MODULUS as u64) - sv)
                })?;
            cs.enforce(
                || format!("c_pq_s2h_{k} enforce"),
                |lc| lc + c_pq_s2h.get_variable() + prod_s2h_sub64_modq[k].get_variable(),
                |lc| lc + CS::one(),
                |lc| {
                    lc + c_subarray64[k].get_variable() + (Scalar::from(MODULUS as u64), CS::one())
                },
            );

            // Candidate: c[k] - s2h[k]  (when c >= s2h)
            let c_m_s2h =
                AllocatedNum::alloc(cs.namespace(|| format!("c_m_s2h_{k} alloc")), || {
                    let cv = c_subarray64[k]
                        .get_value()
                        .ok_or(SynthesisError::AssignmentMissing)?;
                    let sv = prod_s2h_sub64_modq[k]
                        .get_value()
                        .ok_or(SynthesisError::AssignmentMissing)?;
                    Ok(cv - sv)
                })?;
            cs.enforce(
                || format!("c_m_s2h_{k} enforce"),
                |lc| lc + c_m_s2h.get_variable() + prod_s2h_sub64_modq[k].get_variable(),
                |lc| lc + CS::one(),
                |lc| lc + c_subarray64[k].get_variable(),
            );

            let s1_coeff = conditionally_select(
                cs.namespace(|| format!("s1_sel_{k}")),
                &c_pq_s2h,
                &c_m_s2h,
                &flag_c_lt,
            )?;

            // Normalize coefficients to [-q/2, q/2] using unsigned representatives before squaring
            let s2_norm: AllocatedNum<Scalar> = normalize_half_q(
                &mut cs.namespace(|| format!("norm_s2_{k}")),
                &s2_subarray64[k],
            )?;
            let s2_sq: AllocatedNum<Scalar> =
                s2_norm.mul(cs.namespace(|| format!("s2_sq_{k}")), &s2_norm)?;

            // No need to enforce modulo q range check on s1_coeff as both prod_s2h (through ntt multiplication) and c already have coefficients modulo q
            let s1_norm: AllocatedNum<Scalar> =
                normalize_half_q(&mut cs.namespace(|| format!("norm_s1_{k}")), &s1_coeff)?;
            let s1_sq: AllocatedNum<Scalar> =
                s1_norm.mul(cs.namespace(|| format!("s1_sq_{k}")), &s1_norm)?;

            let coeff_sum: AllocatedNum<Scalar> =
                s1_sq.add(cs.namespace(|| format!("sq_sum_{k}")), &s2_sq)?;
            sum_aggregated =
                sum_aggregated.add(cs.namespace(|| format!("agg_upd_{k}")), &coeff_sum)?;
            coeff_index_var = coeff_index_var.add(cs.namespace(|| format!("ci_inc_{k}")), &var1)?;
        }

        l2_norm_sum_var = l2_norm_sum_var.add(cs.namespace(|| "l2_update"), &sum_aggregated)?;

        let step_i_val = self.coeff_index / 64;
        let step_i =
            AllocatedNum::alloc(cs.namespace(|| "step_i"), || Ok(Scalar::from(step_i_val)))?;

        // Enforce: step_i * 64 = coeff_index_init
        cs.enforce(
            || "step_i * 64 = coeff_index_init",
            |lc| lc + step_i.get_variable(),
            |lc| lc + (Scalar::from(64u64), CS::one()),
            |lc| lc + coeff_index_init.get_variable(),
        );
        // 3-bit range check: step_i in {0, 1, ..., 6}, prevent the prover from choosing an arbitrary step_i that satisfies step_i * 64 = coeff_index_init
        let _ = num_to_bits(cs.namespace(|| "step_i_bits"), &step_i, 3)?;

        // step_i in {0..6} = step_i (identity)
        // step_i = 7 = 0 (wrap)
        let const_zero = alloc_constant(cs.namespace(|| "const_0"), Scalar::ZERO)?;
        let const_seven = alloc_constant(cs.namespace(|| "const_7"), Scalar::from(7u64))?;

        let step_eq_7: Boolean =
            alloc_num_equals_constant(cs.namespace(|| "step_eq_7"), &step_i, Scalar::from(7u64))?;
        // If step_i == 7 select 0, otherwise select step_i.
        let step_i_mod7 = conditionally_select(
            cs.namespace(|| "step_i_mod7"),
            &const_zero,
            &step_i,
            &step_eq_7,
        )?;

        // Constrain cur_shake_block == ctx_inject_packed[step_i_mod7]
        let cur_expected = select_from_vec_linear(
            cs.namespace(|| "sel_cur_shake"),
            &ctx_inject_packed_vars,
            &step_i_mod7,
        )?;
        cs.enforce(
            || "cur_shake_block == ctx_inject_packed[step_i_mod7]",
            |lc| lc + cur_expected.get_variable() - cur_shake_block.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc,
        );

        // Compute next_idx = (step_i_mod7 + 1) % 7 in-circuit
        // If result == 7 wrap to 0, otherwise keep.
        let step_plus1 = step_i_mod7.add(cs.namespace(|| "step_plus1"), &var1)?;

        let step_plus1_eq_7: Boolean = alloc_num_equals_constant(
            cs.namespace(|| "step_plus1_eq_7"),
            &step_plus1,
            Scalar::from(7u64),
        )?;
        let next_idx = conditionally_select(
            cs.namespace(|| "next_idx"),
            &const_zero,
            &step_plus1,
            &step_plus1_eq_7,
        )?;

        let shake_block_next = select_from_vec_linear(
            cs.namespace(|| "sel_next_shake"),
            &ctx_inject_packed_vars,
            &next_idx,
        )?;

        // Norm bound check
        let var_512 = alloc_constant(cs.namespace(|| "const_512"), Scalar::from(512u64))?;
        let flag_coeff: Boolean = less_than(
            cs.namespace(|| "coeff_lt_512"),
            &coeff_index_var,
            &var_512,
            LOG_N + 1,
        )?;
        let flag_norm_bound: Boolean =
            enforce_less_than_norm_bound(cs.namespace(|| "norm_bound"), &l2_norm_sum_var)?;
        let res: Boolean = Boolean::or(cs.namespace(|| "flag_or"), &flag_coeff, &flag_norm_bound)?;
        Boolean::enforce_equal(
            cs.namespace(|| "or_is_true"),
            &res,
            &Boolean::Constant(true),
        )?;

        Ok(vec![
            l2_norm_sum_var,
            coeff_index_var,
            hash_c,
            shake_block_next,
            hash_inject,
        ])
    }
}
