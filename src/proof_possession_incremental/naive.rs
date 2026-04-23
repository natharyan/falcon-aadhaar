use std::ops::Mul;
use std::{alloc::alloc, ops::Add};

use crate::age_proof::{
    COEFF_INDEX_MASK, NUM_OPCODE_BITS, OP_COEFF_INDEX_FIRST, OP_COEFF_INDEX_LAST,
    OP_SHAKE256_ACTIVE, OP_SHAKE256_NO_OP,
};
use crate::hash::shake256::{
    keccak_f_1600, library_shake256_inject, library_step_sponge, shake256_msg_blocks,
    shake256_pad101, SHAKE256_BLOCK_LENGTH_BYTES, SHAKE256_DIGEST_LENGTH_BITS,
    SHAKE256_DIGEST_LENGTH_BYTES, SHAKE256_RATE_BYTES,
};
use crate::hash::poseidon::PoseidonHasher;
use crate::ntt::*;
use crate::ntt::{inv_ntt_deferred_circuit, ntt, ntt_deferred_circuit, ntt_mult_const_p2};
use crate::utils::{
    bits_to_bytes_le, bytes_to_bits_le, enforce_less_than_norm_bound, enforce_less_than_q,
    inner_product_mod, mod_q, normalize_coeff, normalize_half_q, num_to_alloc,
    select_from_vec_linear,
};

use crate::hash::shake256::shake_256;
use bellpepper::gadgets::multipack::{bytes_to_bits, compute_multipacking};
use bellpepper_core::{boolean::Boolean, num::AllocatedNum, ConstraintSystem, SynthesisError};
use blstrs::Scalar;
use falcon_rust::{Polynomial, PublicKey, Signature, LOG_N, MODULUS, N, SIG_L2_BOUND};
use ff::{PrimeField, PrimeFieldBits};
use crate::utils::{
    alloc_constant, alloc_num_equals, alloc_num_equals_constant, boolean_implies,
    conditionally_select, less_than, num_to_bits,
};
use nova_snark::traits::circuit::StepCircuit;
use num_bigint::{BigInt, Sign};

#[derive(Clone, Debug)]
pub struct NaiveProofOfPossessionCircuit<Scalar>
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

// impl<Scalar> Default for NaiveProofOfPossessionCircuit<Scalar>
// where
//     Scalar: PrimeFieldBits + PartialOrd,
// {
//     fn default() -> Self {
//         Self {
//             coeff_index: Scalar::ZERO,
//             l2_norm_sum: 0u64,
//             hash_c: Scalar::ZERO,
//             hash_s2: Scalar::ZERO,
//             shake_inject_m: Scalar::ZERO,
//             // io_hash: Scalar::ZERO,
//             s2: Polynomial::default(),
//             c: [0u16; N],
//             h: Polynomial::default(),
//         }
//     }
// }

impl<Scalar> NaiveProofOfPossessionCircuit<Scalar>
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

    // calculate NaiveProofOfPossessionCircuit for all steps
    pub fn new_state_sequence(
        msg: &Vec<u8>,
        sig: &Signature,
        pk: PublicKey,
    ) -> Vec<NaiveProofOfPossessionCircuit<Scalar>> {
        let mut naive_incremental_falcon: Vec<NaiveProofOfPossessionCircuit<Scalar>> = vec![];

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
        naive_incremental_falcon.push(Self {
            l2_norm_sum: l2_norm_sum,
            coeff_index: coeff_index,
            hash_c: hash_c,
            ctx_inject_packed: ctx_inject_packed.clone().try_into().unwrap(),
            hash_inject: hash_inject,
            s2: s2.clone(),
            c: c.clone().try_into().unwrap(),
            h: pk.clone(),
        });

        // s2*h
        let mut prod_s2h = vec![0i64; N];
        for i in 0..N {
            for j in 0..N {
                let idx = (i + j) % N;
                let term = (s2.coeff()[i] as i64) * (pk_poly.coeff()[j] as i64);

                if i + j < N {
                    prod_s2h[idx] += term;
                } else {
                    prod_s2h[idx] -= term; // x^N ≡ -1
                }
            }
        }
        for i in 1..512 {
            coeff_index = coeff_index + 1u64;
            // reduce mod q
            let prod_coeff_mod_q =
                ((prod_s2h[i] % MODULUS as i64) + MODULUS as i64) % MODULUS as i64;
            let s1_coeff =
                (c.coeff()[i] as i64 + MODULUS as i64 - prod_coeff_mod_q) % MODULUS as i64;
            let s1_norm = normalize_coeff(s1_coeff as i64);
            let s2_norm = normalize_coeff(s2.coeff()[i] as i64);
            l2_norm_sum = l2_norm_sum + s1_norm * s1_norm + s2_norm * s2_norm;
            if l2_norm_sum >= SIG_L2_BOUND as u64 {
                panic!(
                    "L2 norm exceeded SIG_L2_BOUND at coeff {}: {}",
                    i, l2_norm_sum
                );
            }
            naive_incremental_falcon.push(Self {
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

        let s2_coeff =
            select_from_vec_linear(cs.namespace(|| "s2_coeff"), &s2_vars, &coeff_index_var)?;
        let c_coeff =
            select_from_vec_linear(cs.namespace(|| "c_coeff"), &c_vars, &coeff_index_var)?;

        // No range check needed for c as it is configured to be a public input

        // s2*h
        // let pk_poly: Polynomial = (&self.h).into();
        // let pk_coeffs: Vec<Scalar> = pk_poly
        //     .coeff()
        //     .iter()
        //     .map(|&x| Scalar::from(x as u64))
        //     .collect();

        // // Build buffer = [-pk[0], ..., -pk[N-1], pk[0], ..., pk[N-1]] for x^N ≡ -1 negacyclic convolution
        // let mut buf_poly_coeffs: Vec<Scalar> = pk_coeffs
        //     .iter()
        //     .map(|x| -*x)
        //     .collect();
        // buf_poly_coeffs.extend(pk_coeffs.iter().cloned());
        // buf_poly_coeffs.reverse();

        // // Compute raw negacyclic convolution without modulo reduction
        // let prod_s2h: Vec<AllocatedNum<Scalar>> = (0..N)
        //     .map(|k| {
        //         let buf_slice = &buf_poly_coeffs[N - 1 - k..2 * N - 1 - k];

        //         let prod_k = AllocatedNum::alloc(cs.namespace(|| format!("prod_s2h_{k}")), || {
        //             let mut acc = Scalar::ZERO;
        //             for i in 0..N {
        //                 let s2_i = s2_vars[i]
        //                     .get_value()
        //                     .ok_or(SynthesisError::AssignmentMissing)?;
        //                 acc += s2_i * buf_slice[i];
        //             }
        //             Ok(acc)
        //         })?;

        //         cs.enforce(
        //             || format!("prod_s2h_raw_{k}"),
        //             |lc| lc + CS::one(),
        //             |lc| {
        //                 let mut sum_lc = lc;
        //                 for i in 0..N {
        //                     sum_lc = sum_lc + (buf_slice[i], s2_vars[i].get_variable());
        //                 }
        //                 sum_lc
        //             },
        //             |lc| lc + prod_k.get_variable(),
        //         );

        //         Ok(prod_k)
        //     })
        //     .collect::<Result<Vec<_>, SynthesisError>>()?;
        // TODO: change this to schoolbook multiplication
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

        let prod_s2h_coeff = select_from_vec_linear(
            cs.namespace(|| "select_from_vec_linear prod_s2h_coeff"),
            &prod_s2h,
            &coeff_index_var,
        )?;
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
        let s2_coeff_sq = s2_normalized.mul(
            cs.namespace(|| "s2_normalized*s2_normalized"),
            &s2_normalized,
        )?;

        // no range check needed for s1_coeff as if s1_coeff > q or if s1_coeff < -q  then s1_coeff^2 > 12289^2 > SIG_L2_BOUND = 34034726
        let s1_normalized = normalize_half_q(&mut cs.namespace(|| "normalize s1"), &s1_coeff)?;
        let s1_coeff_sq = s1_normalized.mul(
            cs.namespace(|| "s1_normalized*s1_normalized"),
            &s1_normalized,
        )?;

        // update l2 norm sum and coeff index
        let sum_update =
            s1_coeff_sq.add(cs.namespace(|| "s1_coeff^2 + s2_coeff^2"), &s2_coeff_sq)?;
        let var1 = alloc_constant(cs.namespace(|| "alloc_constant 1"), Scalar::from(1u64))?;
        coeff_index_var =
            coeff_index_var.add(cs.namespace(|| "coeff_index = coeff_index + 1"), &var1)?;
        l2_norm_sum_var = l2_norm_sum_var.add(
            cs.namespace(|| "l2_norm_sum = l2_norm_sum + sum_update"),
            &sum_update,
        )?;

        let step_i = coeff_index_init.clone();

        // range check: coeff_index <= 512
        let _ = num_to_bits(cs.namespace(|| "coeff_index_bits"), &step_i, LOG_N + 1)?;

        // compute step_i mod 7 through repeated subtraction
        let const_zero = alloc_constant(cs.namespace(|| "const_0"), Scalar::ZERO)?;
        let const_seven = alloc_constant(cs.namespace(|| "const_7"), Scalar::from(7u64))?;
        // step_i_mod7 = step_i % 7
        let mut step_i_mod7 = step_i.clone();
        for j in 0..73 {
            // check step_i_mod7 < 7
            let lt_7 = less_than(
                cs.namespace(|| format!("lt_check_{j}")),
                &step_i_mod7,
                &const_seven,
                10,
            )?;

            // tmp = step_i_mod7 - 7
            let tmp = AllocatedNum::alloc(cs.namespace(|| format!("sub7_alloc_{j}")), || {
                let val = step_i_mod7
                    .get_value()
                    .ok_or(SynthesisError::AssignmentMissing)?;
                Ok(val - Scalar::from(7u64))
            })?;

            cs.enforce(
                || format!("sub7_constraint_{j}"),
                |lc| lc + tmp.get_variable() + (Scalar::from(7u64), CS::one()),
                |lc| lc + CS::one(),
                |lc| lc + step_i_mod7.get_variable(),
            );

            // if >= 7 subtract, else keep
            step_i_mod7 = conditionally_select(
                cs.namespace(|| format!("cond_sub7_{j}")),
                &step_i_mod7, // if lt_7 == true keep
                &tmp,         // else subtract
                &lt_7,
            )?;
        }

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

        // Compute next_idx = (step_i_mod7 + 1) % 7
        let var1 = alloc_constant(cs.namespace(|| "const_1"), Scalar::ONE)?;
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
        // let var_512 = alloc_constant(cs.namespace(|| "const_512"), Scalar::from(512u64))?;
        // let flag_coeff: Boolean = less_than(
        //     cs.namespace(|| "coeff_lt_512"),
        //     &coeff_index_var,
        //     &var_512,
        //     LOG_N + 1,
        // )?;
        let flag_norm_bound: Boolean =
            enforce_less_than_norm_bound(cs.namespace(|| "norm_bound"), &l2_norm_sum_var)?;
        // let res: Boolean = Boolean::or(cs.namespace(|| "flag_or"), &flag_coeff, &flag_norm_bound)?;
        Boolean::enforce_equal(
            cs.namespace(|| "or_is_true"),
            &flag_norm_bound,
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
