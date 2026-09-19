//! Poseidon over Goldilocks, bridged to Plonky2's native implementation (qp-plonky2-core).

use bellpepper_core::{num::AllocatedNum, ConstraintSystem, LinearCombination, SynthesisError};
use ff::{Field, PrimeFieldBits};

use crate::latticefold_adapter::goldilocks_field::{to_canonical_u64, GoldilocksFq as F};

use qp_plonky2_core::config::Hasher;
use qp_plonky2_core::field::goldilocks_field::GoldilocksField as GlF;
use qp_plonky2_core::field::types::{Field as _, PrimeField64 as _};
use qp_plonky2_core::hash_types::{HashOut, NUM_HASH_OUT_ELTS};
use qp_plonky2_core::poseidon::{
    Poseidon, PoseidonHash, ALL_ROUND_CONSTANTS, HALF_N_FULL_ROUNDS, N_PARTIAL_ROUNDS, N_ROUNDS,
    SPONGE_RATE, SPONGE_WIDTH,
};

pub const WIDTH: usize = SPONGE_WIDTH; // 12
pub const RATE: usize = SPONGE_RATE; // 8
pub const HASH_OUT: usize = NUM_HASH_OUT_ELTS; // 4

#[inline]
fn fq_to_gl(x: &F) -> GlF {
    GlF::from_canonical_u64(to_canonical_u64(x))
}

#[inline]
fn gl_to_fq(g: GlF) -> F {
    F::from(g.to_canonical_u64())
}

#[inline]
fn fu(x: u64) -> F {
    // constants are all < p, so the derived ff From<u64> needs no reduction.
    F::from(x)
}

//-- Native implementation, bridge from GoldilocksFq to Plonky2's GoldilocksField. --//

/// Plonky2's poseidon, bridged to GoldilocksFq.
pub fn permute(state: [F; WIDTH]) -> [F; WIDTH] {
    let gl: [GlF; WIDTH] = core::array::from_fn(|i| fq_to_gl(&state[i]));
    let out = <GlF as Poseidon>::poseidon(gl);
    core::array::from_fn(|i| gl_to_fq(out[i]))
}

/// Plonky2's PoseidonHash::hash_no_pad, bridged to GoldilocksFq.
pub fn hash_no_pad(inputs: &[F]) -> [F; HASH_OUT] {
    let gl: Vec<GlF> = inputs.iter().map(fq_to_gl).collect();
    let h: HashOut<GlF> = <PoseidonHash as Hasher<GlF>>::hash_no_pad(&gl);
    core::array::from_fn(|i| gl_to_fq(h.elements[i]))
}

//-- CIRCUIT --//

#[inline]
fn rc(i: usize, round: usize) -> F {
    fu(ALL_ROUND_CONSTANTS[i + WIDTH * round])
}

/// x^7 of an affine input s given as (LinearCombination, value).
/// Mirrors Plonky2's sbox_monomial (poseidon.rs): x2=s*s, x4=x2*x2, x3=s*x2, out=x3*x4.
fn pow7_affine<CS: ConstraintSystem<F>>(
    cs: &mut CS,
    s_lc: &LinearCombination<F>,
    s_val: Option<F>,
) -> Result<AllocatedNum<F>, SynthesisError> {
    let x2v = s_val.map(|s| s * s);
    let x4v = x2v.map(|t| t * t);
    let x3v = match (s_val, x2v) {
        (Some(s), Some(t)) => Some(s * t),
        _ => None,
    };
    let outv = match (x3v, x4v) {
        (Some(a), Some(b)) => Some(a * b),
        _ => None,
    };

    let x2 = AllocatedNum::alloc(cs.namespace(|| "x2"), || {
        x2v.ok_or(SynthesisError::AssignmentMissing)
    })?;
    let x4 = AllocatedNum::alloc(cs.namespace(|| "x4"), || {
        x4v.ok_or(SynthesisError::AssignmentMissing)
    })?;
    let x3 = AllocatedNum::alloc(cs.namespace(|| "x3"), || {
        x3v.ok_or(SynthesisError::AssignmentMissing)
    })?;
    let out = AllocatedNum::alloc(cs.namespace(|| "x7"), || {
        outv.ok_or(SynthesisError::AssignmentMissing)
    })?;

    cs.enforce(
        || "x2=s*s",
        |lc| lc + s_lc,
        |lc| lc + s_lc,
        |lc| lc + x2.get_variable(),
    );
    cs.enforce(
        || "x4=x2*x2",
        |lc| lc + x2.get_variable(),
        |lc| lc + x2.get_variable(),
        |lc| lc + x4.get_variable(),
    );
    cs.enforce(
        || "x3=s*x2",
        |lc| lc + s_lc,
        |lc| lc + x2.get_variable(),
        |lc| lc + x3.get_variable(),
    );
    cs.enforce(
        || "x7=x3*x4",
        |lc| lc + x3.get_variable(),
        |lc| lc + x4.get_variable(),
        |lc| lc + out.get_variable(),
    );
    Ok(out)
}

fn alloc_eq_lc<CS: ConstraintSystem<F>>(
    cs: &mut CS,
    name: &'static str,
    lc: LinearCombination<F>,
    val: Option<F>,
) -> Result<AllocatedNum<F>, SynthesisError> {
    let out = AllocatedNum::alloc(cs.namespace(|| name), || {
        val.ok_or(SynthesisError::AssignmentMissing)
    })?;
    cs.enforce(
        || format!("{name} bind"),
        |l| l + out.get_variable(),
        |l| l + CS::one(),
        |_| lc,
    );
    Ok(out)
}

/// MDS layer: out[r] = sum_i CIRC[i]*y[(i+r)%12] + DIAG[r]*y[r] (Plonky2 poseidon.rs).
/// CIRC/DIAG are Plonky2's trait constants.
fn mds_circuit<CS: ConstraintSystem<F>>(
    cs: &mut CS,
    y: &[AllocatedNum<F>; WIDTH],
) -> Result<[AllocatedNum<F>; WIDTH], SynthesisError> {
    let circ = <GlF as Poseidon>::MDS_MATRIX_CIRC;
    let diag = <GlF as Poseidon>::MDS_MATRIX_DIAG;
    let mut out: Vec<AllocatedNum<F>> = Vec::with_capacity(WIDTH);
    for r in 0..WIDTH {
        let mut lc = LinearCombination::<F>::zero();
        let mut val = Some(F::ZERO);
        for i in 0..WIDTH {
            let src = (i + r) % WIDTH;
            let c = fu(circ[i]);
            lc = lc + (c, y[src].get_variable());
            val = match (val, y[src].get_value()) {
                (Some(a), Some(v)) => Some(a + c * v),
                _ => None,
            };
        }
        if diag[r] != 0 {
            let cd = fu(diag[r]);
            lc = lc + (cd, y[r].get_variable());
            val = match (val, y[r].get_value()) {
                (Some(a), Some(v)) => Some(a + cd * v),
                _ => None,
            };
        }
        out.push(alloc_eq_lc(
            &mut cs.namespace(|| format!("mds {r}")),
            "out",
            lc,
            val,
        )?);
    }
    out.try_into().map_err(|_| SynthesisError::Unsatisfiable)
}

/// (state[i] + round_constant(i,round)) as (LinearCombination, value).
fn affine<CS: ConstraintSystem<F>>(
    state_i: &AllocatedNum<F>,
    round: usize,
    i: usize,
) -> (LinearCombination<F>, Option<F>) {
    let lc = LinearCombination::<F>::zero() + state_i.get_variable() + (rc(i, round), CS::one());
    let val = state_i.get_value().map(|v| v + rc(i, round));
    (lc, val)
}

// full round: const + sbox(all 12) + mds
fn full_round_circuit<CS: ConstraintSystem<F>>(
    cs: &mut CS,
    state: &[AllocatedNum<F>; WIDTH],
    round: usize,
) -> Result<[AllocatedNum<F>; WIDTH], SynthesisError> {
    let mut y: Vec<AllocatedNum<F>> = Vec::with_capacity(WIDTH);
    for i in 0..WIDTH {
        let (lc, val) = affine::<CS>(&state[i], round, i);
        y.push(pow7_affine(
            &mut cs.namespace(|| format!("full sbox {i}")),
            &lc,
            val,
        )?);
    }
    let y: [AllocatedNum<F>; WIDTH] = y.try_into().map_err(|_| SynthesisError::Unsatisfiable)?;
    mds_circuit(&mut cs.namespace(|| "full mds"), &y)
}

// partial round: const(all) + sbox(lane 0) + mds (poseidon.rs:781)
fn partial_round_circuit<CS: ConstraintSystem<F>>(
    cs: &mut CS,
    state: &[AllocatedNum<F>; WIDTH],
    round: usize,
) -> Result<[AllocatedNum<F>; WIDTH], SynthesisError> {
    let mut y: Vec<AllocatedNum<F>> = Vec::with_capacity(WIDTH);
    let (lc0, val0) = affine::<CS>(&state[0], round, 0);
    y.push(pow7_affine(
        &mut cs.namespace(|| "partial sbox 0"),
        &lc0,
        val0,
    )?);
    for i in 1..WIDTH {
        let (lc, val) = affine::<CS>(&state[i], round, i);
        y.push(alloc_eq_lc(
            &mut cs.namespace(|| format!("partial pass {i}")),
            "pass",
            lc,
            val,
        )?);
    }
    let y: [AllocatedNum<F>; WIDTH] = y.try_into().map_err(|_| SynthesisError::Unsatisfiable)?;
    mds_circuit(&mut cs.namespace(|| "partial mds"), &y)
}

/// The Poseidon-GL permutation in-circuit; equals the native permute.
pub fn permute_circuit<CS: ConstraintSystem<F>>(
    cs: &mut CS,
    mut state: [AllocatedNum<F>; WIDTH],
) -> Result<[AllocatedNum<F>; WIDTH], SynthesisError> {
    let mut round_ctr = 0usize;
    for _ in 0..HALF_N_FULL_ROUNDS {
        state = full_round_circuit(
            &mut cs.namespace(|| format!("full {round_ctr}")),
            &state,
            round_ctr,
        )?;
        round_ctr += 1;
    }
    for _ in 0..N_PARTIAL_ROUNDS {
        state = partial_round_circuit(
            &mut cs.namespace(|| format!("partial {round_ctr}")),
            &state,
            round_ctr,
        )?;
        round_ctr += 1;
    }
    for _ in 0..HALF_N_FULL_ROUNDS {
        state = full_round_circuit(
            &mut cs.namespace(|| format!("full {round_ctr}")),
            &state,
            round_ctr,
        )?;
        round_ctr += 1;
    }
    debug_assert_eq!(round_ctr, N_ROUNDS);
    Ok(state)
}

/// The Poseidon-GL sponge in-circuit; equals the native hash_no_pad.
/// Returns 4 elements (do not truncate).
pub fn hash_in_circuit<CS: ConstraintSystem<F>>(
    cs: &mut CS,
    inputs: &[AllocatedNum<F>],
) -> Result<[AllocatedNum<F>; HASH_OUT], SynthesisError> {
    let zero = AllocatedNum::alloc(cs.namespace(|| "zero"), || Ok(F::ZERO))?;
    cs.enforce(
        || "zero=0",
        |lc| lc + zero.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc,
    );
    let mut state: Vec<AllocatedNum<F>> = vec![zero; WIDTH];

    for (chunk_idx, chunk) in inputs.chunks(RATE).enumerate() {
        for (i, x) in chunk.iter().enumerate() {
            state[i] = x.clone(); // overwrite (matches native set_from_slice)
        }
        let arr: [AllocatedNum<F>; WIDTH] = state
            .clone()
            .try_into()
            .map_err(|_| SynthesisError::Unsatisfiable)?;
        let permuted = permute_circuit(&mut cs.namespace(|| format!("perm {chunk_idx}")), arr)?;
        state = permuted.to_vec();
    }

    Ok([
        state[0].clone(),
        state[1].clone(),
        state[2].clone(),
        state[3].clone(),
    ])
}

/// Thin wrapper mirroring the old PoseidonHasher surface (output is now [_; 4]).
pub struct PoseidonHasherGl;
impl PoseidonHasherGl {
    pub fn new(_num_absorbs: u32) -> Self {
        Self
    }
    pub fn hash(&self, values: &[F]) -> [F; HASH_OUT] {
        hash_no_pad(values)
    }
    pub fn hash_in_circuit<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        values: &[AllocatedNum<F>],
    ) -> Result<[AllocatedNum<F>; HASH_OUT], SynthesisError> {
        hash_in_circuit(cs, values)
    }
}

/// IVC hash abstraction for the running io_hash / nullifier commitment. `DIGEST` is the
/// number of field elements in one digest. For Goldilocks it is 4 (Plonky2 `PoseidonHash`,
/// 256-bit / 128-bit collision resistance); a 1-element digest would be only ~32-bit
/// collision resistant over a 64-bit field. The Nova/Stark path keeps its own hashing and
/// does not implement this trait, so it is unaffected.
pub trait IvcHash: PrimeFieldBits {
    const DIGEST: usize;
    fn ivc_hash(values: &[Self]) -> Vec<Self>;
    fn ivc_hash_in_circuit<CS: ConstraintSystem<Self>>(
        cs: &mut CS,
        values: &[AllocatedNum<Self>],
    ) -> Result<Vec<AllocatedNum<Self>>, SynthesisError>;
}

impl IvcHash for F {
    const DIGEST: usize = HASH_OUT; // 4
    fn ivc_hash(values: &[Self]) -> Vec<Self> {
        hash_no_pad(values).to_vec()
    }
    fn ivc_hash_in_circuit<CS: ConstraintSystem<Self>>(
        cs: &mut CS,
        values: &[AllocatedNum<Self>],
    ) -> Result<Vec<AllocatedNum<Self>>, SynthesisError> {
        Ok(hash_in_circuit(cs, values)?.to_vec())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bellpepper_core::test_cs::TestConstraintSystem;

    fn arr(v: [u64; WIDTH]) -> [F; WIDTH] {
        core::array::from_fn(|i| fu(v[i]))
    }

    #[test]
    fn native_bridge_matches_plonky2_kats() {
        // poseidon_goldilocks.rs:466 test_vectors12. Because `permute` delegates to
        // Plonky2, this asserts the dependency resolves to the standard instance AND the
        // GoldilocksFq<->GoldilocksField bridge preserves every value.
        let zero_out = [
            0x3c18a9786cb0b359,
            0xc4055e3364a246c3,
            0x7953db0ab48808f4,
            0xc71603f33a1144ca,
            0xd7709673896996dc,
            0x46a84e87642f44ed,
            0xd032648251ee0b3c,
            0x1c687363b207df62,
            0xdf8565563e8045fe,
            0x40f5b37ff4254dae,
            0xd070f637b431067c,
            0x1792b1c4342109d7,
        ];
        assert_eq!(permute(arr([0; WIDTH])), arr(zero_out));

        let range_out = [
            0xd64e1e3efc5b8e9e,
            0x53666633020aaa47,
            0xd40285597c6a8825,
            0x613a4f81e81231d2,
            0x414754bfebd051f0,
            0xcb1f8980294a023f,
            0x6eb2a9e4d54a9d0f,
            0x1902bc3af467e056,
            0xf045d5eafdc6021f,
            0xe4150f77caaa3be5,
            0xc9bfd01d39b50cce,
            0x5c0a27fcb0e1459b,
        ];
        assert_eq!(
            permute(arr([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])),
            arr(range_out)
        );
    }

    #[test]
    fn circuit_permutation_equals_native() {
        let input: [u64; WIDTH] = [11, 9, 7, 5, 3, 1, 2, 4, 6, 8, 10, 12];
        let native = permute(arr(input));

        let mut cs = TestConstraintSystem::<F>::new();
        let alloc: Vec<AllocatedNum<F>> = input
            .iter()
            .enumerate()
            .map(|(i, &v)| {
                AllocatedNum::alloc(cs.namespace(|| format!("in{i}")), || Ok(fu(v))).unwrap()
            })
            .collect();
        let state: [AllocatedNum<F>; WIDTH] = alloc.try_into().unwrap();
        let out = permute_circuit(&mut cs, state).unwrap();
        assert!(cs.is_satisfied(), "circuit unsatisfied");
        for i in 0..WIDTH {
            assert_eq!(out[i].get_value().unwrap(), native[i], "lane {i}");
        }
    }

    #[test]
    fn circuit_sponge_equals_native() {
        let msg: Vec<F> = (0..20u64).map(fu).collect(); // 20 elems -> 3 blocks (8,8,4)
        let native = hash_no_pad(&msg);

        let mut cs = TestConstraintSystem::<F>::new();
        let alloc: Vec<AllocatedNum<F>> = msg
            .iter()
            .enumerate()
            .map(|(i, &v)| AllocatedNum::alloc(cs.namespace(|| format!("m{i}")), || Ok(v)).unwrap())
            .collect();
        let out = hash_in_circuit(&mut cs, &alloc).unwrap();
        assert!(cs.is_satisfied());
        for i in 0..HASH_OUT {
            assert_eq!(out[i].get_value().unwrap(), native[i], "digest lane {i}");
        }
    }
}
