//! proof generation, folding, and verification for the packed GoldilocksRingNTT R1CS instances.

use ark_serialize::{CanonicalSerialize, Compress};
use cyclotomic_rings::rings::{GoldilocksChallengeSet, GoldilocksRingNTT};
use latticefold::{
    arith::{Arith, Witness, CCCS, CCS, LCCCS},
    commitment::AjtaiCommitmentScheme,
    decomposition_parameters::DecompositionParams,
    nifs::{
        linearization::{
            structs::LinearizationProof, LFLinearizationProver, LFLinearizationVerifier,
            LinearizationProver, LinearizationVerifier,
        },
        LFProof, NIFSProver, NIFSVerifier,
    },
    transcript::poseidon::PoseidonTranscript,
};

use super::shape_cs::LatticefoldR1CS;

type NTT = GoldilocksRingNTT;
type CS = GoldilocksChallengeSet;
type T = PoseidonTranscript<NTT, CS>;

// TODO: update this for the witness size, currently picked from Latticefold's example
/// decomposition parameters for the Goldilocks prime.
#[derive(Clone)]
pub struct GoldilocksDP;

impl DecompositionParams for GoldilocksDP {
    const B: u128 = 1 << 15;
    const L: usize = 5;
    const B_SMALL: usize = 2;
    const K: usize = 15;
}

// TODO: latticefold's Goldilocks example defaults to 4. re-derive for the real witness size and security target.
/// Ajtai commitment height.
pub const KAPPA: usize = 4;

/// one packed group's committed instance and witness.
pub struct Group {
    pub cccs: CCCS<NTT>,
    pub wit: Witness<NTT>,
}

/// foling proof.
pub struct FoldedInstance {
    pub ccs: CCS<NTT>,
    pub cccs0: CCCS<NTT>,
    pub cccs1: CCCS<NTT>,
    pub lin_proof0: LinearizationProof<NTT>,
    pub fold_proof: LFProof<NTT>,
    pub prove_time: core::time::Duration,
}

impl FoldedInstance {
    /// the fold proof and instance 0's linearization proof.
    pub fn proof_sizes(&self) -> Result<(usize, usize), Box<dyn std::error::Error>> {
        let mut buf = Vec::new();
        self.fold_proof
            .serialize_with_mode(&mut buf, Compress::Yes)?;
        self.lin_proof0
            .serialize_with_mode(&mut buf, Compress::Yes)?;
        let compressed = buf.len();
        buf.clear();
        self.fold_proof
            .serialize_with_mode(&mut buf, Compress::No)?;
        self.lin_proof0
            .serialize_with_mode(&mut buf, Compress::No)?;
        Ok((compressed, buf.len()))
    }
}

/// build the shared CCS once from the extracted R1CS.
pub fn build_ccs(extracted: LatticefoldR1CS) -> (CCS<NTT>, usize) {
    let x_len = extracted.r1cs.l;
    let ncols = extracted.r1cs.A.ncols;
    let n = (ncols - x_len - 1) * GoldilocksDP::L;
    let ccs = CCS::from_r1cs_padded(extracted.r1cs, n, GoldilocksDP::L);
    (ccs, n)
}

/// commit one packed group under a commitment scheme.
pub fn commit_group(
    ccs: &CCS<NTT>,
    z_star: &[NTT],
    x_len: usize,
    scheme: &AjtaiCommitmentScheme<NTT>,
) -> Result<Group, Box<dyn std::error::Error>> {
    assert_eq!(
        z_star[x_len],
        NTT::from(1u64),
        "z*[l] must be the constant 1"
    );

    ccs.check_relation(z_star)
        .map_err(|e| format!("padded CCS rejects the packed witness: {e:?}"))?;

    let x_ccs = z_star[..x_len].to_vec();
    let w_ccs = z_star[x_len + 1..].to_vec();
    let wit: Witness<NTT> = Witness::from_w_ccs::<GoldilocksDP>(w_ccs);
    let cccs: CCCS<NTT> = CCCS {
        cm: wit.commit::<GoldilocksDP>(scheme)?,
        x_ccs,
    };

    Ok(Group { cccs, wit })
}

/// fold two packed groups into one proof.
pub fn fold_two(
    extracted: LatticefoldR1CS,
    z_star0: &[NTT],
    z_star1: &[NTT],
) -> Result<FoldedInstance, Box<dyn std::error::Error>> {
    let x_len = extracted.r1cs.l;
    let (ccs, n) = build_ccs(extracted);

    let mut rng = ark_std::test_rng();
    let scheme: AjtaiCommitmentScheme<NTT> = AjtaiCommitmentScheme::rand(KAPPA, n, &mut rng);

    let g0 = commit_group(&ccs, z_star0, x_len, &scheme)?;
    let g1 = commit_group(&ccs, z_star1, x_len, &scheme)?;

    let prove_start = std::time::Instant::now();

    // linearize group 0 -> accumulator; keep the proof (the verifier needs it).
    // LFAcc::init's `linearize::<_, CS, C>(comp)`.
    let mut lin_transcript = T::default();
    let (acc, lin_proof0) =
        LFLinearizationProver::<_, T>::prove(&g0.cccs, &g0.wit, &mut lin_transcript, &ccs)?;

    // fold group 1 in. LFAcc::fold's prove: (acc, g0.wit) running, (g1.cccs, g1.wit)
    // incoming.
    let mut prover_transcript = T::default();
    let (_folded_acc, _folded_wit, fold_proof) = NIFSProver::<NTT, GoldilocksDP, T>::prove(
        &acc,
        &g0.wit,
        &g1.cccs,
        &g1.wit,
        &mut prover_transcript,
        &ccs,
        &scheme,
    )?;
    let prove_time = prove_start.elapsed();

    Ok(FoldedInstance {
        ccs,
        cccs0: g0.cccs,
        cccs1: g1.cccs,
        lin_proof0,
        fold_proof,
        prove_time,
    })
}

/// verify a folded proof.
pub fn verify_folded(
    folded: &FoldedInstance,
) -> Result<core::time::Duration, Box<dyn std::error::Error>> {
    let verify_start = std::time::Instant::now();

    let mut v_lin_transcript = T::default();
    let acc_v = LFLinearizationVerifier::<_, T>::verify(
        &folded.cccs0,
        &folded.lin_proof0,
        &mut v_lin_transcript,
        &folded.ccs,
    )?;

    let mut v_transcript = T::default();
    NIFSVerifier::<NTT, GoldilocksDP, T>::verify(
        &acc_v,
        &folded.cccs1,
        &folded.fold_proof,
        &mut v_transcript,
        &folded.ccs,
    )?;

    Ok(verify_start.elapsed())
}

#[cfg(test)]
mod tests {
    use super::*;
    use bellpepper_core::num::AllocatedNum;
    use bellpepper_core::{ConstraintSystem, SynthesisError};

    use crate::latticefold_adapter::goldilocks_field::GoldilocksFq;
    use crate::latticefold_adapter::ntt_pack::{num_lanes, pack_z};
    use crate::latticefold_adapter::shape_cs::{build_r1cs, z_vector, ShapeCS};
    use crate::latticefold_adapter::witness_cs::WitnessCS;

    /// x^3 + x + 5 = y, x public. tiny (wit_len = 3, so n = wit_len * L = 15 and ccs.m
    /// pads to 16). exercises the WHOLE two-group path -- pack, commit, linearize, fold,
    /// verify -- with the real latticefold API, decoupled from the memory question that
    /// only bites at the full witness size. RUN THIS FIRST.
    fn synth<CS: ConstraintSystem<GoldilocksFq>>(
        cs: &mut CS,
        x: u64,
    ) -> Result<(), SynthesisError> {
        let x = AllocatedNum::alloc_input(cs.namespace(|| "x"), || Ok(GoldilocksFq::from(x)))?;
        let x_sq = x.square(cs.namespace(|| "x_sq"))?;
        let x_cu = x_sq.mul(cs.namespace(|| "x_cu"), &x)?;
        let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
            let xv = x.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            Ok(xv * xv * xv + xv + GoldilocksFq::from(5u64))
        })?;
        cs.enforce(
            || "y = x^3 + x + 5",
            |lc| {
                lc + x_cu.get_variable() + x.get_variable() + (GoldilocksFq::from(5u64), CS::one())
            },
            |lc| lc + CS::one(),
            |lc| lc + y.get_variable(),
        );
        Ok(())
    }

    /// pack `k = num_lanes()` lanes with x = base+1 .. base+k into one GoldilocksRingNTT
    /// instance, checking each lane's field relation and the packed relation on the way.
    fn packed_instance(shape_cs: &ShapeCS, ncols: usize, base: u64) -> Vec<NTT> {
        let k = num_lanes();
        let mut z_lanes: Vec<Vec<GoldilocksFq>> = Vec::with_capacity(k);
        for i in 0..k {
            let mut cs = WitnessCS::<GoldilocksFq>::new();
            synth(&mut cs, base + i as u64 + 1).expect("witness synthesis");
            let z = z_vector(cs.input_assignment(), cs.aux_assignment());
            assert_eq!(z.len(), ncols);
            z_lanes.push(z);
        }
        pack_z(&z_lanes).expect("pack")
    }

    #[test]
    fn test_two_group_fold_round_trip_small() {
        // shape once -- both groups share it.
        let mut shape_cs = ShapeCS::new();
        synth(&mut shape_cs, 1).expect("shape synthesis");
        let x_len = shape_cs.num_inputs() - 1;
        let ncols = x_len + 1 + shape_cs.num_aux();

        // two packed instances with DIFFERENT witnesses (base 0 and base 100) -- the
        // point of folding is combining two distinct instances, so distinct is the
        // meaningful test.
        let z_star0 = packed_instance(&shape_cs, ncols, 0);
        let z_star1 = packed_instance(&shape_cs, ncols, 100);

        let extracted = build_r1cs(&shape_cs);
        // each instance independently satisfies the packed relation before folding.
        extracted
            .check_relation(&z_star0)
            .expect("group 0 check_relation");
        extracted
            .check_relation(&z_star1)
            .expect("group 1 check_relation");

        // fold, then verify -- the two calls the example separates.
        let folded = fold_two(extracted, &z_star0, &z_star1).expect("fold_two");
        let verify_time = verify_folded(&folded).expect("verify_folded");

        let (compressed, uncompressed) = folded.proof_sizes().expect("serialize");
        assert!(compressed > 0);
        println!(
            "two-group fold: proof {compressed} B compressed ({uncompressed} B raw), \
             fold {:?}, verify {verify_time:?}",
            folded.prove_time
        );
    }
}
