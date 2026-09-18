//! packing k R1CS instances over StarkFq into one instance over StarkRingNTT.
//! this is Remark 4.1 of the LatticeFold paper, specialized to the case where all
//! k instances share one circuit.
//!
//! StarkRingNTT = Z_q[X]/(X^16 + 1) with q the Starknet prime. since 32 | q - 1 the
//! cyclotomic splits into 16 linear factors (CRT_FIELD_EXTENSION_DEGREE = 1), so
//! the NTT is a ring isomorphism NTT: R -> F^16, NTT(e) = (e_1, ..., e_16),
//! preserving addition and mapping multiplication to the slot-wise Hadamard
//! product. Remark 4.1 sets every entry so its NTT image is that entry across the
//! k instances:
//!
//!     A*[r,c] = NTT^-1( A_1[r,c], ..., A_k[r,c] )
//!     z*[j]   = NTT^-1( z_1[j],   ..., z_k[j]   )
//!     c_m*    = NTT^-1( c_{1,m},  ..., c_{k,m}  )
//!
//! the isomorphism then distributes through the matrix-vector product, so
//!
//!     NTT( (M* z*)[r] )_i = sum_c M_i[r,c] * z_i[c] = <M_i[r,.], z_i>
//!
//! i.e. slot i of the packed relation is exactly instance i's field relation, and
//! the packed R1CS holds iff all k field relations hold.
//!
//! no NTT is actually computed here, for two reasons read off stark-rings
//! crates/ring/src/cyclotomic_ring/ntt_form.rs:
//!
//! - line 25, CyclotomicPolyRingNTTGeneral([C::BaseCRTField; D]) stores the *NTT
//!   components* directly (the constructor at line 37 is from_array(ntt_coeffs)),
//!   so From<Vec<Fq>> at line 699 specifies a ring element by its NTT image. that
//!   is NTT^-1 by definition; the coefficient form is never materialized.
//! - line 689, from_scalar(v) = from_array([v; D]) with the upstream comment
//!   NTT([v, 0, ..., 0]) = ([v, ..., v]).
//!
//! the second fact is why the *matrices* need no work here. all lanes run the same
//! circuit, so A_1[r,c] = ... = A_k[r,c] = v and the entry Remark 4.1 asks for is
//! NTT^-1(v, ..., v), the constant polynomial, which is exactly what
//! shape_cs::to_sparse_matrix already emits via from_scalar. the same holds for the
//! CCS gate scalars c_m, so CCS::from_r1cs_padded needs no change either. only z
//! genuinely differs per lane.
//!
//! precedent: latticefold's own get_test_z_ntt does exactly this transpose -- build
//! R::dimension() field witnesses, then for each coordinate j collect the j-th
//! element of every witness and call R::from(vec).
//!
//! reference: https://github.com/NethermindEth/latticefold  (crates/latticefold/src/arith/r1cs.rs)
//! reference: https://github.com/NethermindEth/stark-rings  (crates/ring/src/cyclotomic_ring/ntt_form.rs)
//! reference: https://github.com/NethermindEth/folded-falcon  (crates/folded-falcon/examples/usage.rs)

use std::collections::BTreeMap;

use ark_ff::{BigInteger, PrimeField as ArkPrimeField};
use cyclotomic_rings::rings::StarkRingNTT;
use ff::PrimeField;
use stark_rings::{cyclotomic_ring::ICRT, PolyRing};

use super::shape_cs::BpMatrix;
use super::stark_field::{to_ark_fq, StarkFq};

/// number of independent NTT slots, i.e. how many field instances pack into one
/// ring instance. PolyRing::dimension() returns the const parameter D, which for
/// RqNTT = CyclotomicPolyRingNTTGeneral<StarkRingConfig, 4, { ntt::N }> is
/// ntt::N = 16. read at runtime rather than hardcoded so swapping the ring (Frog
/// would give 4, Goldilocks 8) is a type change and not a silent bug.
// reference: stark-rings ntt_form.rs, PolyRing::dimension returns the const D
pub fn num_lanes() -> usize {
    StarkRingNTT::dimension()
}

/// errors that can only mean a caller mistake, never a proof failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PackError {
    LaneCount {
        expected: usize,
        got: usize,
    },
    /// lanes disagree on |z|. every lane runs the same circuit, so every witness
    /// must have the same length; a mismatch means the lanes were not all
    /// synthesized from the same shape.
    LengthMismatch {
        lane: usize,
        expected: usize,
        got: usize,
    },
    Empty,
}

impl core::fmt::Display for PackError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            PackError::LaneCount { expected, got } => write!(
                f,
                "expected exactly {expected} lanes (StarkRingNTT::dimension()), got {got}"
            ),
            PackError::LengthMismatch {
                lane,
                expected,
                got,
            } => write!(
                f,
                "lane {lane} has |z| = {got}, expected {expected}; all lanes must share one shape"
            ),
            PackError::Empty => write!(f, "no lanes supplied"),
        }
    }
}

/// pack k = num_lanes() field witnesses into one ring witness.
/// z_lanes[i] is instance i's z in (x || 1 || w) order, all of length nc. returns
/// z* of length nc with z*[j] = NTT^-1(z_0[j], ..., z_{k-1}[j]). lane order is
/// preserved: lane i of the output corresponds to z_lanes[i].
// reference: latticefold arith/r1cs.rs get_test_z_ntt, which performs the same
// transpose over its own test witnesses
pub fn pack_z(z_lanes: &[Vec<StarkFq>]) -> Result<Vec<StarkRingNTT>, PackError> {
    let k = num_lanes();
    if z_lanes.is_empty() {
        return Err(PackError::Empty);
    }
    if z_lanes.len() != k {
        return Err(PackError::LaneCount {
            expected: k,
            got: z_lanes.len(),
        });
    }

    let nc = z_lanes[0].len();
    for (i, lane) in z_lanes.iter().enumerate() {
        if lane.len() != nc {
            return Err(PackError::LengthMismatch {
                lane: i,
                expected: nc,
                got: lane.len(),
            });
        }
    }

    // the transpose. for each coordinate j gather that coordinate across all k
    // lanes and declare the ring element with that NTT image. same shape as
    // latticefold's get_test_z_ntt.
    let mut z_star = Vec::with_capacity(nc);
    for j in 0..nc {
        let slots: Vec<_> = z_lanes.iter().map(|lane| to_ark_fq(&lane[j])).collect();
        // From<Vec<Fq>> stores these AS the NTT components, so this is NTT^-1.
        z_star.push(StarkRingNTT::from(slots));
    }

    Ok(z_star)
}

/// check one lane's field R1CS directly: (Az) o (Bz) == Cz. returns the index of
/// the first unsatisfied row, or None.
///
/// this exists to make the Remark 4.1 equivalence observable rather than assumed:
/// running it on every lane and comparing against
/// LatticefoldR1CS::check_relation(&z_star) shows that the packed ring relation
/// holds iff all k field relations hold. it is also the better diagnostic, since
/// the packed check reports one row index for the whole instance while this names
/// the lane.
// reference: latticefold arith/r1cs.rs R1CS::check_relation, the field-level analogue
// of what this checks per lane
pub fn check_field_relation(
    a: &BpMatrix,
    b: &BpMatrix,
    c: &BpMatrix,
    z: &[StarkFq],
) -> Option<usize> {
    let dot = |row: &Vec<(StarkFq, usize)>| -> StarkFq {
        row.iter().fold(StarkFq::from(0u64), |acc, (coeff, col)| {
            acc + *coeff * z[*col]
        })
    };

    (0..a.len()).find(|&r| dot(&a[r]) * dot(&b[r]) != dot(&c[r]))
}

/// measure the witness norm.
///
/// this decides two parameters that everything downstream depends on, so it should be
/// measured rather than assumed:
///
///   - latticefold's `DecompositionParams::L`, set by `B^L > q` only because the
///     *committed* vector must be short for Ajtai/SIS binding. if the witness is
///     already short, a much smaller L may be sound.
///   - LaBRADOR's `PrincipalRelation::Index::norm_bound_squared`, an L2 bound on the
///     witness concatenation. both implemented reductions in that codebase
///     (`binary_r1cs`, and the `Z64` path) exist to satisfy it.
///
/// the expectation for this circuit is that most of the 244k variables are Booleans
/// (keccak_f_1600, ctx_absorb/ctx_squeeze at 1600 bits each, msg_vars at 1088,
/// bit_array) with Falcon coefficients at 14 bits, and only a few hundred full-width
/// values (Poseidon internals, io_hash, prev_nullifier, packed scalars). the histogram
/// below is what confirms or refutes that.
pub struct NormReport {
    /// bit-length of the centred representative -> how many entries have it.
    pub histogram: BTreeMap<u64, usize>,
    /// upper bound on the sum of squares of centred representatives, as log2.
    pub norm_sq_bound_bits: f64,
    /// largest centred |value|, as a bit-length.
    pub max_bits: u64,
    pub total_entries: usize,
}

impl NormReport {
    /// does every value fit in a 64-bit prime field?
    ///
    /// Goldilocks is 2^64 - 2^32 + 1, so a centred value needs <= 63 bits to be
    /// representable with room for the sign. this is the decision the whole
    /// Goldilocks migration turns on: if false, the circuit produces values that a
    /// 64-bit field cannot hold and the migration is off regardless of the NTT fix.
    pub fn fits_in_goldilocks(&self) -> bool {
        self.max_bits <= 63
    }
}

impl core::fmt::Display for NormReport {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        writeln!(f, "entries      : {}", self.total_entries)?;
        writeln!(f, "max |value|  : 2^{}", self.max_bits)?;
        writeln!(f, "norm^2 bound : < 2^{:.1}", self.norm_sq_bound_bits)?;
        writeln!(
            f,
            "fits in Goldilocks (<= 63 bits centred): {}",
            if self.fits_in_goldilocks() {
                "YES"
            } else {
                "NO"
            }
        )?;
        writeln!(f, "bit-length histogram:")?;
        for (bits, count) in &self.histogram {
            let pct = 100.0 * (*count as f64) / (self.total_entries as f64);
            writeln!(f, "  {bits:>3} bits : {count:>10}  ({pct:5.1}%)")?;
        }
        Ok(())
    }
}

/// bit-length of a canonical little-endian byte representation.
/// 0 for zero, otherwise floor(log2(v)) + 1.
fn bitlen_le(bytes: &[u8]) -> u64 {
    for (i, b) in bytes.iter().enumerate().rev() {
        if *b != 0 {
            return (i as u64) * 8 + (8 - b.leading_zeros() as u64);
        }
    }
    0
}

/// bit-length of the CENTRED representative of a field element.
///
/// lattice norms are defined on the lift to [-(p-1)/2, (p-1)/2], not on the canonical
/// [0, p) one -- `p - 1` is a norm-1 element, not a norm-p element, and using the
/// canonical representative would inflate the measured norm by ~2^252.
///
/// no big-integer arithmetic is needed: `p - v` is exactly `-v` in the field, so the
/// field performs the 252-bit subtraction and we just take whichever of the two has
/// fewer bits.
fn centred_bits(v: &StarkFq) -> u64 {
    let pos = bitlen_le(v.to_repr().as_ref());
    let neg = bitlen_le((-*v).to_repr().as_ref());
    pos.min(neg)
}

/// same, for the arkworks-side base field (used on the coefficient representation).
fn centred_bits_ark(v: &<StarkRingNTT as PolyRing>::BaseRing) -> u64 {
    let pos = bitlen_le(&v.into_bigint().to_bytes_le());
    let neg = bitlen_le(&(-*v).into_bigint().to_bytes_le());
    pos.min(neg)
}

fn report_from<I: Iterator<Item = u64>>(bit_lengths: I) -> NormReport {
    let mut histogram: BTreeMap<u64, usize> = BTreeMap::new();
    let mut norm_sq_bound = 0f64;
    let mut max_bits = 0u64;
    let mut total_entries = 0usize;

    for bits in bit_lengths {
        *histogram.entry(bits).or_insert(0) += 1;
        max_bits = max_bits.max(bits);
        // |v| < 2^bits, so |v|^2 < 2^(2*bits). summing the bound rather than the exact
        // square keeps this in f64 (range reaches 2^1024, we need ~2^524) and gives an
        // upper bound, which is what a norm bound wants.
        if bits > 0 {
            norm_sq_bound += (2f64).powi(2 * bits as i32);
        }
        total_entries += 1;
    }

    NormReport {
        histogram,
        norm_sq_bound_bits: if norm_sq_bound > 0.0 {
            norm_sq_bound.log2()
        } else {
            0.0
        },
        max_bits,
        total_entries,
    }
}

/// field-level report over the per-lane witnesses, before packing.
///
/// this is the DIAGNOSTIC: it tells you which values are large and how many, so you
/// know what would need limb decomposition. it is not the number a lattice prover
/// checks -- see `coefficient_norm_report` for that.
pub fn field_norm_report(z_lanes: &[Vec<StarkFq>]) -> NormReport {
    report_from(
        z_lanes
            .iter()
            .flat_map(|lane| lane.iter())
            .map(centred_bits),
    )
}

/// coefficient-level report over the packed witness. THIS is the quantity lattice
/// provers bound.
///
/// norms are defined on the coefficient representation `RqPoly`, not on the NTT slots.
/// for a fully-splitting ring the slots are independent field elements, but the
/// coefficient form is their inverse NTT, which mixes all 16 -- so a witness that looks
/// small lane-wise can have large coefficients. `icrt()` performs that inverse
/// transform; `coeffs()` then reads the 16 coefficients of each element.
///
/// expect this to be larger than the field-level report. if the gap is big, that is
/// the real obstacle rather than the raw witness.
pub fn coefficient_norm_report(z_star: &[StarkRingNTT]) -> NormReport {
    let mut bits = Vec::with_capacity(z_star.len() * num_lanes());
    for e in z_star {
        let poly = (*e).icrt(); // NTT form -> coefficient form
        for c in poly.coeffs() {
            bits.push(centred_bits_ark(c));
        }
    }
    report_from(bits.into_iter())
}

#[cfg(test)]
mod tests {
    use super::*;
    use stark_rings::Ring;

    /// a uniform pack must equal the scalar lift, since NTT^-1(v, ..., v) is the
    /// constant polynomial. this is the identity to_sparse_matrix relies on.
    #[test]
    fn test_uniform_pack_equals_scalar_lift() {
        let k = num_lanes();
        assert_eq!(k, 16, "StarkRingNTT should expose 16 NTT slots");

        let v = StarkFq::from(12289u64);
        let lanes: Vec<Vec<StarkFq>> = (0..k).map(|_| vec![v]).collect();
        let packed = pack_z(&lanes).expect("pack");

        assert_eq!(packed.len(), 1);
        assert_eq!(packed[0], StarkRingNTT::from_scalar(to_ark_fq(&v)));
    }

    /// distinct per-lane values must not collapse to a scalar ring element. if
    /// they did, pack_z would be broadcasting instead of transposing and
    /// every lane would carry the same witness.
    #[test]
    fn test_distinct_lanes_are_not_scalar() {
        let k = num_lanes();
        let lanes: Vec<Vec<StarkFq>> = (0..k).map(|i| vec![StarkFq::from(i as u64)]).collect();
        let packed = pack_z(&lanes).expect("pack");

        assert_ne!(
            packed[0],
            StarkRingNTT::from_scalar(to_ark_fq(&StarkFq::from(0u64))),
            "lanes collapsed: pack_z is broadcasting, not transposing"
        );
    }

    /// slot i must carry lane i's value, in order.
    #[test]
    fn test_slot_order_matches_lane_order() {
        let k = num_lanes();
        let lanes: Vec<Vec<StarkFq>> = (0..k).map(|i| vec![StarkFq::from(i as u64 + 7)]).collect();
        let packed = pack_z(&lanes).expect("pack");

        let slots = packed[0].into_coeffs();
        for (i, lane) in lanes.iter().enumerate() {
            assert_eq!(
                slots[i],
                to_ark_fq(&lane[0]),
                "slot {i} does not carry lane {i}'s value"
            );
        }
    }

    #[test]
    fn test_lane_count_is_enforced() {
        let lanes: Vec<Vec<StarkFq>> = (0..3).map(|_| vec![StarkFq::from(1u64)]).collect();
        assert_eq!(
            pack_z(&lanes),
            Err(PackError::LaneCount {
                expected: num_lanes(),
                got: 3
            })
        );
    }

    #[test]
    fn test_length_mismatch_is_caught() {
        let k = num_lanes();
        let mut lanes: Vec<Vec<StarkFq>> = (0..k).map(|_| vec![StarkFq::from(1u64); 4]).collect();
        lanes[7].push(StarkFq::from(1u64));
        assert_eq!(
            pack_z(&lanes),
            Err(PackError::LengthMismatch {
                lane: 7,
                expected: 4,
                got: 5
            })
        );
    }

    /// end to end on x^3 + x + 5 = y with a different witness per lane, using
    /// latticefold's own variable layout from
    /// test_r1cs_example_from_constraint_system: z = (x, 1, y, x^2, x^3, x^3 + x).
    /// the matrices are identical across lanes, which is the whole point: one
    /// shape, k witnesses.
    #[test]
    fn test_sixteen_distinct_lanes_verify_per_lane() {
        let k = num_lanes();

        let lane_z = |x: u64| -> Vec<StarkFq> {
            vec![
                StarkFq::from(x),
                StarkFq::from(1u64),
                StarkFq::from(x * x * x + x + 5),
                StarkFq::from(x * x),
                StarkFq::from(x * x * x),
                StarkFq::from(x * x * x + x),
            ]
        };

        let one = StarkFq::from(1u64);
        let five = StarkFq::from(5u64);
        let a: BpMatrix = vec![
            vec![(one, 0)],
            vec![(one, 3)],
            vec![(one, 0), (one, 4)],
            vec![(five, 1), (one, 5)],
        ];
        let b: BpMatrix = vec![
            vec![(one, 0)],
            vec![(one, 0)],
            vec![(one, 1)],
            vec![(one, 1)],
        ];
        let c: BpMatrix = vec![
            vec![(one, 3)],
            vec![(one, 4)],
            vec![(one, 5)],
            vec![(one, 2)],
        ];

        let lanes: Vec<Vec<StarkFq>> = (0..k as u64).map(lane_z).collect();
        for (i, z) in lanes.iter().enumerate() {
            assert_eq!(
                check_field_relation(&a, &b, &c, z),
                None,
                "lane {i} is unsatisfied before packing"
            );
        }

        let z_star = pack_z(&lanes).expect("pack");
        assert_eq!(z_star.len(), 6);

        // corrupting one lane must break that lane only.
        let mut bad = lanes.clone();
        bad[11][2] = bad[11][2] + StarkFq::from(1u64);
        assert!(
            check_field_relation(&a, &b, &c, &bad[11]).is_some(),
            "corrupting lane 11 did not break its relation"
        );
        for (i, z) in bad.iter().enumerate() {
            if i != 11 {
                assert_eq!(
                    check_field_relation(&a, &b, &c, z),
                    None,
                    "corrupting lane 11 also broke lane {i}"
                );
            }
        }
    }
}
