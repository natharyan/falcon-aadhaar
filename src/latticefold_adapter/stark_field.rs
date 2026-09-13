//! StarkFq: an ff::PrimeField implemenation of stark_rings Fq which is based on ark_ff.
//!
//! bellpepper_core::ConstraintSystem<Scalar> requires Scalar: ff::PrimeField
//! (the zkcrypto ff crate). latticefold uses stark_rings which has base field
//!    pub type Fq = Fp256<MontBackend<FqConfig, 4>>;   // ark_ff::PrimeField.
//!
//! Fq cannot be used as Scalar directly because it does not implement ff::PrimeField, StarkFq is ff:Primefield with same modulus
//! as Fq, which enables conversion between the two types.
//!
//! reference: stark-rings/crates/ring/src/cyclotomic_ring/models/stark_prime/mod.rs:
//! #[modulus = "3618502788666131213697322783095070105623107215331596699973092056135872020481"]
//! #[generator = "3"]
//!

use ark_ff::PrimeField as ArkPrimeField;
use ff::PrimeField;
use stark_rings::cyclotomic_ring::models::stark_prime::Fq as ArkFq;

// define StarkFq to implement ff::Primefield with same modulus as stark_rings::Fq (ark_ff::PrimeField)
#[derive(PrimeField)]
#[PrimeFieldModulus = "3618502788666131213697322783095070105623107215331596699973092056135872020481"]
#[PrimeFieldGenerator = "3"]
#[PrimeFieldReprEndianness = "little"]
pub struct StarkFq([u64; 4]);

/// StarkFq (bellpepper) -> Fq (stark-rings)
pub fn to_ark_fq(v: &StarkFq) -> ArkFq {
    ArkFq::from_le_bytes_mod_order(v.to_repr().as_ref())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ff::{Field, PrimeFieldBits};

    #[test]
    fn test_moduli_agree() {
        let neg_one_ff = StarkFq::ZERO - StarkFq::ONE;
        let neg_one_ark = -ArkFq::from(1u64);
        assert_eq!(
            to_ark_fq(&neg_one_ff),
            neg_one_ark,
            "StarkFq and stark_rings::Fq do not share a modulus -- every \
             downstream matrix coefficient would be silently wrong"
        );
    }

    #[test]
    fn test_small_values_round_trip() {
        for v in [0u64, 1, 2, 5, 12289, 61445, 999_999] {
            assert_eq!(
                to_ark_fq(&StarkFq::from(v)),
                ArkFq::from(v),
                "mismatch at {v}"
            );
        }
    }

    #[test]
    fn test_satisfies_step_circuit_bounds() {
        fn assert_step_circuit_scalar<Scalar: PrimeFieldBits + PartialOrd>() {}
        assert_step_circuit_scalar::<StarkFq>();

        fn assert_ord<T: Ord>() {}
        assert_ord::<StarkFq>();
    }

    #[test]
    fn test_ord_is_canonical() {
        // Basic monotonicity.
        assert!(StarkFq::ZERO < StarkFq::ONE);
        assert!(StarkFq::from(1u64) < StarkFq::from(2u64));

        // Straddles a byte boundary, catches a reversed comparison order.
        assert!(StarkFq::from(255u64) < StarkFq::from(256u64));
        // ...and a 64-bit limb boundary.
        assert!(StarkFq::from(u64::MAX) < StarkFq::from(u64::MAX) + StarkFq::ONE);

        // Falcon's modulus.
        assert!(StarkFq::from(12288u64) < StarkFq::from(12289u64));

        // The exact comparison enforce_less_than_norm_bound performs.
        const SIG_L2_BOUND: u64 = 34034726;
        assert!(StarkFq::from(SIG_L2_BOUND - 1) < StarkFq::from(SIG_L2_BOUND));
        assert!(StarkFq::from(SIG_L2_BOUND) >= StarkFq::from(SIG_L2_BOUND));
        assert!(StarkFq::from(SIG_L2_BOUND + 1) > StarkFq::from(SIG_L2_BOUND));

        let max = StarkFq::ZERO - StarkFq::ONE;
        assert!(StarkFq::from(u64::MAX) < max);
        assert!(StarkFq::ZERO < max);
        assert_eq!(max.cmp(&max), core::cmp::Ordering::Equal);

        let a = StarkFq::from(7u64);
        let b = StarkFq::from(9u64);
        assert_eq!(a.partial_cmp(&b), Some(a.cmp(&b)));
        assert_eq!(a.cmp(&b), core::cmp::Ordering::Less);
    }

    #[test]
    fn test_ord_agrees_across_the_bridge() {
        let pairs = [
            (0u64, 1u64),
            (255, 256),
            (12288, 12289),
            (34034725, 34034726),
        ];
        for (lo, hi) in pairs {
            let (lo_ff, hi_ff) = (StarkFq::from(lo), StarkFq::from(hi));
            assert!(lo_ff < hi_ff, "StarkFq ordering wrong at ({lo}, {hi})");
            assert!(
                to_ark_fq(&lo_ff) < to_ark_fq(&hi_ff),
                "ordering not preserved across to_ark_fq at ({lo}, {hi})"
            );
        }
    }
}
