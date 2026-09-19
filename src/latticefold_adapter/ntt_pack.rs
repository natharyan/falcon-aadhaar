//! packing k R1CS instances over GoldilocksFq into one R1CS instance over GoldilocksRingNTT (Remark 4.1 of the LatticeFold paper).
//! for a uniform IVC (matrices A,B,C are the same for each step).

use std::collections::BTreeMap;

use super::shape_cs::{BpMatrix, ShapeCS};
// use super::stark_field::{to_ark_fq, GoldilocksFq};
use super::goldilocks_field::{embed_slot, GoldilocksFq};
use ark_ff::{BigInteger, PrimeField as ArkPrimeField};
use bellpepper_core::Index;
use cyclotomic_rings::rings::GoldilocksRingNTT;
use ff::PrimeField;
use stark_rings::{cyclotomic_ring::ICRT, PolyRing};

/// number of NTT slots
pub fn num_lanes() -> usize {
    GoldilocksRingNTT::dimension()
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PackError {
    LaneCount {
        expected: usize,
        got: usize,
    },
    LengthMismatch {
        lane: usize,
        expected: usize,
        got: usize,
    },
    BatchRemainder {
        lanes: usize,
        k: usize,
    },
    Empty,
}

impl core::fmt::Display for PackError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            PackError::LaneCount { expected, got } => write!(
                f,
                "expected exactly {expected} lanes (GoldilocksRingNTT::dimension()), got {got}"
            ),
            PackError::LengthMismatch {
                lane,
                expected,
                got,
            } => write!(
                f,
                "lane {lane} has |z| = {got}, expected {expected}; all lanes must share one shape"
            ),
            PackError::BatchRemainder { lanes, k } => write!(
                f,
                "{lanes} lanes is not a multiple of {k} (GoldilocksRingNTT::dimension()); pad first"
            ),
            PackError::Empty => write!(f, "no lanes supplied"),
        }
    }
}

/// pack k = num_lanes() field elements into one vector of ring elements using the NTT transform.
/// z_star[j] = NTT^-1(z_0[j], ..., z_{k-1}[j]) for each coordinate j.
pub fn pack_z(z_lanes: &[Vec<GoldilocksFq>]) -> Result<Vec<GoldilocksRingNTT>, PackError> {
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
    // lanes and declare the ring element with that NTT image.
    let mut z_star = Vec::with_capacity(nc);
    for j in 0..nc {
        let slots: Vec<_> = z_lanes.iter().map(|lane| embed_slot(&lane[j])).collect();
        // From<Vec<Fq>> stores these AS the NTT components, so this is NTT^-1.
        z_star.push(GoldilocksRingNTT::from(slots));
    }

    Ok(z_star)
}

/// pack N = m * num_lanes() field lanes into m ring R1CS instances
pub fn pack_z_batched(
    z_lanes: &[Vec<GoldilocksFq>],
) -> Result<Vec<Vec<GoldilocksRingNTT>>, PackError> {
    let k = num_lanes();
    if z_lanes.is_empty() {
        return Err(PackError::Empty);
    }
    if z_lanes.len() % k != 0 {
        return Err(PackError::BatchRemainder {
            lanes: z_lanes.len(),
            k,
        });
    }
    // Each chunk of k R1CS instances over GoldilocksFq becomes is the NTT transform of a single R1CS instance in GoldilocksRingNTT.
    z_lanes.chunks(k).map(pack_z).collect()
}

/// check the R1CS relation (Az) o (Bz) == Cz for a single lane.
// reference: latticefold arith/r1cs.rs R1CS::check_relation
pub fn check_field_relation(
    a: &BpMatrix,
    b: &BpMatrix,
    c: &BpMatrix,
    z: &[GoldilocksFq],
) -> Option<usize> {
    let dot = |row: &Vec<(GoldilocksFq, usize)>| -> GoldilocksFq {
        row.iter()
            .fold(GoldilocksFq::from(0u64), |acc, (coeff, col)| {
                acc + *coeff * z[*col]
            })
    };

    (0..a.len()).find(|&r| dot(&a[r]) * dot(&b[r]) != dot(&c[r]))
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
        assert_eq!(k, 8, "GoldilocksRingNTT should expose 8 NTT slots");

        let v = GoldilocksFq::from(12289u64);
        let lanes: Vec<Vec<GoldilocksFq>> = (0..k).map(|_| vec![v]).collect();
        let packed = pack_z(&lanes).expect("pack");

        assert_eq!(packed.len(), 1);
        assert_eq!(packed[0], GoldilocksRingNTT::from(embed_slot(&v)));
    }

    /// distinct per-lane values must not collapse to a scalar ring element. if
    /// they did, pack_z would be broadcasting instead of transposing and
    /// every lane would carry the same witness.
    #[test]
    fn test_distinct_lanes_are_not_scalar() {
        let k = num_lanes();
        let lanes: Vec<Vec<GoldilocksFq>> =
            (0..k).map(|i| vec![GoldilocksFq::from(i as u64)]).collect();
        let packed = pack_z(&lanes).expect("pack");

        assert_ne!(
            packed[0],
            GoldilocksRingNTT::from(embed_slot(&GoldilocksFq::from(0u64))),
            "lanes collapsed: pack_z is broadcasting, not transposing"
        );
    }

    /// slot i must carry lane i's value, in order.
    #[test]
    fn test_slot_order_matches_lane_order() {
        let k = num_lanes();
        let lanes: Vec<Vec<GoldilocksFq>> = (0..k)
            .map(|i| vec![GoldilocksFq::from(i as u64 + 7)])
            .collect();
        let packed = pack_z(&lanes).expect("pack");

        let slots = packed[0].into_coeffs();
        for (i, lane) in lanes.iter().enumerate() {
            assert_eq!(
                slots[i],
                embed_slot(&lane[0]),
                "slot {i} does not carry lane {i}'s value"
            );
        }
    }

    #[test]
    fn test_batched_pack_splits_into_instances() {
        let k = num_lanes();
        let lanes: Vec<Vec<GoldilocksFq>> = (0..(2 * k) as u64)
            .map(|i| {
                vec![
                    GoldilocksFq::from(i),
                    GoldilocksFq::from(i + 1),
                    GoldilocksFq::from(i + 2),
                ]
            })
            .collect();

        let instances = pack_z_batched(&lanes).expect("batched pack");
        assert_eq!(instances.len(), 2, "expected two packed ring instances");
        for inst in &instances {
            assert_eq!(
                inst.len(),
                3,
                "each instance has one ring element per coordinate"
            );
        }

        assert_eq!(instances[0], pack_z(&lanes[..k]).unwrap());
        assert_eq!(instances[1], pack_z(&lanes[k..]).unwrap());
    }

    #[test]
    fn test_batched_pack_rejects_non_multiple() {
        let k = num_lanes();
        let lanes: Vec<Vec<GoldilocksFq>> = (0..(k + 1) as u64)
            .map(|_| vec![GoldilocksFq::from(1u64)])
            .collect();
        assert_eq!(
            pack_z_batched(&lanes),
            Err(PackError::BatchRemainder { lanes: k + 1, k })
        );
    }

    #[test]
    fn test_lane_count_is_enforced() {
        let lanes: Vec<Vec<GoldilocksFq>> =
            (0..3).map(|_| vec![GoldilocksFq::from(1u64)]).collect();
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
        let mut lanes: Vec<Vec<GoldilocksFq>> =
            (0..k).map(|_| vec![GoldilocksFq::from(1u64); 4]).collect();
        lanes[7].push(GoldilocksFq::from(1u64));
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
    /// latticefold's ordering for z
    fn test_sixteen_distinct_lanes_verify_per_lane() {
        let k = num_lanes();

        let lane_z = |x: u64| -> Vec<GoldilocksFq> {
            vec![
                GoldilocksFq::from(x),
                GoldilocksFq::from(1u64),
                GoldilocksFq::from(x * x * x + x + 5),
                GoldilocksFq::from(x * x),
                GoldilocksFq::from(x * x * x),
                GoldilocksFq::from(x * x * x + x),
            ]
        };

        let one = GoldilocksFq::from(1u64);
        let five = GoldilocksFq::from(5u64);
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

        let lanes: Vec<Vec<GoldilocksFq>> = (0..k as u64).map(lane_z).collect();
        for (i, z) in lanes.iter().enumerate() {
            assert_eq!(
                check_field_relation(&a, &b, &c, z),
                None,
                "lane {i} is unsatisfied before packing"
            );
        }

        let z_star = pack_z(&lanes).expect("pack");
        assert_eq!(z_star.len(), 6);

        let mut bad = lanes.clone();
        bad[11][2] = bad[11][2] + GoldilocksFq::from(1u64);
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
