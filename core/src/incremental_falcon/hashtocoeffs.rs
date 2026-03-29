// // TODO

// use std::ops::Add;

// use crate::{
//     gadgets::bellpepper_uint64::UInt64,
//     hash::shake256::{SHAKE256_BLOCK_LENGTH_BYTES, SHAKE256_DIGEST_LENGTH_BITS, keccak_f_1600, library_step_sponge},
//     utils::{bits_to_bytes_le, bytes_to_bits_le, mod_q, inner_product_mod},
//     gadgets::ntt_poly_mult::*,
// };
// use bellpepper::gadgets::multipack;
// use bellpepper_core::{boolean::Boolean, num::AllocatedNum, ConstraintSystem, SynthesisError};
// use blstrs::Scalar;
// use falcon_rust::{MODULUS, N, Polynomial, PublicKey};
// use ff::PrimeFieldBits;
// use nova_aadhaar_qr::util::{alloc_constant, less_than, num_to_bits, conditionally_select};

// pub(crate) fn library_hashtocoeffs(
//     mut ctx: [bool; 1600],
//     q: u16,
//     mut coeff_index: u64,
//     s2: Polynomial,
//     flag_coeff: bool,
//     h_poly: Polynomial, // TODO remove this as a paramater
// ) -> (u64, u16, [bool; 1600]) {
//     let s2_h = s2 * h_poly;
//     // k = ceil(2^16/N)
//     let k = (((1u32 << 16) + q as u32 - 1) / q as u32) as u16;
//     let mut sum_aggregated: u16 = 0;
//     let mut ctx_pointer = 0;
//     for i in 1..=68 {
//         let t_bits = &ctx[ctx_pointer..ctx_pointer + 16];
//         let mut t: u16 = 0;
//         // evaluate using big-endian convention
//         for &bit in t_bits {
//             t = (t << 1) | (bit as u16);
//         }
//         let flag_success = t < k * q;
//         let update_flag = flag_success && flag_coeff;
//         let c = t % q;
//         let s1_coeff = c - s2_h.coeff()[coeff_index as usize]; // TODO: use mod_q here
//         let mut sum_update: u16 = 0;
//         if update_flag {
//             sum_update =
//                 s1_coeff * s1_coeff + s2_h.coeff()[coeff_index as usize] * s2_h.coeff()[coeff_index as usize];
//             coeff_index += 1;
//         }
//         sum_aggregated += sum_update;
//         ctx_pointer += 16;
//     }
//     // apply shake256 permutation
//     ctx = library_step_sponge(ctx.to_vec(), None, 1088, true);

//     (coeff_index, sum_aggregated, ctx)
// }

// pub(crate) fn hashtocoeffs<Scalar, CS>(
//     mut cs: CS,
//     mut ctx: &[Boolean; SHAKE256_DIGEST_LENGTH_BITS],
//     mut coeff_index: AllocatedNum<Scalar>,
//     s2: &Vec<AllocatedNum<Scalar>>,
//     flag_coeff: &Boolean,
//     h_poly: &Vec<AllocatedNum<Scalar>>,
// ) -> Result<(AllocatedNum<Scalar>, AllocatedNum<Scalar>, [Boolean; 1600]), SynthesisError>
// where
//     Scalar: PrimeFieldBits,
//     CS: ConstraintSystem<Scalar>,
// {
//     assert!(ctx.len() == 1600, "Context length should be 1600 bits");
//     // assign k = ceil(2^16/N) as a bellpepper constant using AllocatedNum
//     let k = ((1u64 << 16) + MODULUS as u64 - 1) / MODULUS as u64;
//     let kq: AllocatedNum<Scalar> = alloc_constant(cs.namespace(|| "k constant in hashtocoeffs"), Scalar::from(k * MODULUS as u64))?;
//     let sum_aggregated: AllocatedNum<Scalar> = alloc_constant(cs.namespace(|| "sum_aggregated init in hashtocoeffs"), Scalar::from(0u64))?;
//     let mut extract_ctr: usize = 0;

//     let modulus_var = alloc_constant(cs.namespace(|| "modulus_var in hashtocoeffs"), Scalar::from(MODULUS as u64))?;

//     let s2_h: Vec<AllocatedNum<Scalar>> = ntt_mult(cs.namespace(|| "ntt mult"), s2, h_poly)?; // TODO
//     // sampling with rejection corresponding to no update in coeff_index and sum_aggregated
//     for i in 1..=68 {
//         let t_bits: Vec<Boolean> = ctx[extract_ctr..extract_ctr + 16].to_vec();
        
//         // evaluate using big-endian bits to u16
//         let mut t_reverse: Vec<Boolean> = Vec::with_capacity(16);
//         for j in 0..16 {
//             t_reverse.push(t_bits[15 - j].clone());
//         }
//         let t: AllocatedNum<Scalar> = multipack::pack_bits(cs.namespace(|| "pack bits"), &t_reverse)?;

//         let flag_success = less_than(cs.namespace(|| "flag success"), &t, &kq, 16)?;
//         let update_flag = Boolean::and(cs.namespace(|| "update flag"), &flag_success, flag_coeff)?;
//         let c = mod_q(cs.namespace(|| "c = t mod q"), &t)?;

        

//         let s1_coeff: AllocatedNum<Scalar> = select_from_vector_512(cs, s2_h, &coeff_index)?;
//         let s2_coeff_index = select_from_vector_512(cs.namespace(||"select_from_vector"), s2, &coeff_index)?;

//         let zero_alloc = alloc_constant(cs, Scalar::from(0u64))?;
//         let one_alloc = alloc_constant(cs, Scalar::from(1u64))?;

//         let sum_update = conditionally_select(cs.namespace(|| "sum_update conditionally_select"), &(s1_coeff.mul(cs.namespace(|| "s1_coeff*s1_coeff"), &s1_coeff) + s2_coeff_index.mul(cs.namespace(|| "s2_coeff_index*s2_coeff_index"), &s2_coeff_index)), &zero_alloc, &update_flag)?;

//         sum_aggregated = sum_aggregated.add(cs.namespace(|| "update sum_aggregated"), &sum_update)?;
//         let coeff_index_plus_1 = coeff_index.add(cs.namespace(|| "coeff_index + 1"),&one_alloc)?;
//         coeff_index = conditionally_select(cs.namespace(|| "coeff_index update"), &coeff_index_plus_1, &coeff_index, &update_flag)?;
//         extract_ctr += 16;
//     }
//     let ctx_vec = keccak_f_1600(cs.namespace(|| "HashToCoeffs keccak_permute"), ctx)?;
//     let ctx_array: [Boolean; 1600] = ctx_vec.try_into().map_err(|_| SynthesisError::AssignmentMissing)?;
//     ctx = &ctx_array;
    
//     Ok((coeff_index.clone(), sum_aggregated, ctx.clone()))
// }
