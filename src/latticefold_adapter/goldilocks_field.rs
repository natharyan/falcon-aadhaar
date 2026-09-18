//! GoldilocksFq: an ff::PrimeField implementation of stark_rings' of Goldilocks base-field -> Fq3 subfield embedding required for the inverse
//! formally: NTT(poly \in GoldilocksRingNTT) \in  GoldilocksFq[X]/(X^3 - X - 1).
//! latticefold's Goldilocks ring has base prime field in ark_ff
//! (refer to: stark-rings crates/ring/src/cyclotomic_ring/models/goldilocks/mod.rs).
//!
//! # NTT components = 8, each is a degree-3 extension of the base field

use ark_ff::{Field as ArkField, PrimeField as ArkPrimeField};
use ff::PrimeField;
use stark_rings::cyclotomic_ring::models::goldilocks::{Fq as ArkFqG, Fq3};

#[derive(PrimeField)]
#[PrimeFieldModulus = "18446744069414584321"]
#[PrimeFieldGenerator = "7"]
#[PrimeFieldReprEndianness = "little"]
pub struct GoldilocksFq([u64; 2]);

/// GoldilocksFq (bellpepper) -> Fq (stark-rings goldilocks base field).
pub fn to_ark_fq(v: &GoldilocksFq) -> ArkFqG {
    ArkFqG::from_le_bytes_mod_order(v.to_repr().as_ref())
}

/// Fq -> Fq3 (v |-> v + 0*u + 0*u^2).
#[inline]
pub fn embed_slot(v: &GoldilocksFq) -> Fq3 {
    Fq3::from_base_prime_field(to_ark_fq(v))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ff::{Field, PrimeFieldBits};

    #[test]
    fn test_moduli_agree() {
        let neg_one_ff = GoldilocksFq::ZERO - GoldilocksFq::ONE;
        let neg_one_ark = -ArkFqG::from(1u64);
        assert_eq!(
            to_ark_fq(&neg_one_ff),
            neg_one_ark,
            "GoldilocksFq and stark_rings goldilocks::Fq do not share a modulus -- \
             every downstream matrix coefficient would be silently wrong"
        );
    }

    #[test]
    fn test_small_values_round_trip() {
        for v in [0u64, 1, 2, 5, 12289, 61445, 999_999, u32::MAX as u64] {
            assert_eq!(
                to_ark_fq(&GoldilocksFq::from(v)),
                ArkFqG::from(v),
                "mismatch at {v}"
            );
        }
    }

    #[test]
    fn test_capacity_is_63() {
        // 1600 sponge bits then pack by CAPACITY: Goldilocks gives 26, not Stark's 7.
        // This is what forces ctx_inject_packed and the io_hash preimage to grow.
        assert_eq!(GoldilocksFq::NUM_BITS, 64);
        assert_eq!(GoldilocksFq::CAPACITY, 63);
        let chunks = (1600 + GoldilocksFq::CAPACITY as usize - 1) / GoldilocksFq::CAPACITY as usize;
        assert_eq!(chunks, 26);
    }

    #[test]
    fn test_embed_is_a_ring_hom() {
        // (a+b) and (a*b) must embed to the sum/product in Fq3. This is exactly the
        // property the Remark 4.1 soundness argument uses.
        let a = GoldilocksFq::from(12289u64);
        let b = GoldilocksFq::from(777u64);
        assert_eq!(embed_slot(&(a + b)), embed_slot(&a) + embed_slot(&b));
        assert_eq!(embed_slot(&(a * b)), embed_slot(&a) * embed_slot(&b));
        assert_eq!(embed_slot(&GoldilocksFq::ONE), Fq3::ONE);
        assert_eq!(embed_slot(&GoldilocksFq::ZERO), Fq3::ZERO);
    }

    #[test]
    fn test_embed_is_constant_in_slot() {
        // The embedded value must live purely in the degree-0 coordinate; the u and
        // u^2 coordinates must be zero, or the "wastes 2/3 of the slot" reasoning --
        // and the icrt-is-a-constant-polynomial claim for matrices -- would be false.
        let e = embed_slot(&GoldilocksFq::from(42u64));
        assert_eq!(e, Fq3::from_base_prime_field(ArkFqG::from(42u64)));
    }

    #[test]
    fn test_satisfies_step_circuit_bounds() {
        fn assert_step_circuit_scalar<S: PrimeFieldBits + PartialOrd>() {}
        assert_step_circuit_scalar::<GoldilocksFq>();
        fn assert_ord<T: Ord>() {}
        assert_ord::<GoldilocksFq>();
    }
}
