//! `StarkFq`: an `ff::PrimeField` twin of `stark_rings`' `Fq`.
//!
//! `bellpepper_core::ConstraintSystem<Scalar>` requires `Scalar: ff::PrimeField`
//! (the zkcrypto `ff` crate). `stark_rings`' base field is
//!
//!     pub type Fq = Fp256<MontBackend<FqConfig, 4>>;   // ark_ff
//!
//! i.e. `ark_ff::PrimeField`. These are two unrelated traits from two unrelated
//! ecosystems, and stark-rings depends on `ark-ff` only -- no `ff` impl exists
//! anywhere in it. We also cannot add one: orphan rule, both the trait and the
//! type are foreign. So `Fq` can never be a bellpepper `Scalar`, and the circuit
//! cannot be synthesized over it directly.
//!
//! `StarkFq` is the bridge: an `ff`-derived field at the identical modulus, so
//! converting between the two is a byte-level repr reformat rather than a
//! reduction into a different field.
//!
//! Modulus and generator copied verbatim from
//! stark-rings/crates/ring/src/cyclotomic_ring/models/stark_prime/mod.rs:
//!
//!     #[modulus = "3618502788666131213697322783095070105623107215331596699973092056135872020481"]
//!     #[generator = "3"]
//!
//! (Starknet prime, 2^251 + 17*2^192 + 1. `test_moduli_agree` below checks the
//! two definitions coincide at runtime)

use ark_ff::PrimeField as ArkPrimeField;
use ff::PrimeField;
use stark_rings::cyclotomic_ring::models::stark_prime::Fq as ArkFq;

#[derive(PrimeField)]
#[PrimeFieldModulus = "3618502788666131213697322783095070105623107215331596699973092056135872020481"]
#[PrimeFieldGenerator = "3"]
#[PrimeFieldReprEndianness = "little"]
pub struct StarkFq([u64; 4]);

/// `StarkFq` (bellpepper side) -> `Fq` (stark-rings side).
///
/// `to_repr()` gives little-endian bytes (per `PrimeFieldReprEndianness` above),
/// and `from_le_bytes_mod_order` reads little-endian. The `mod_order` in the name
/// is a no-op here: the input is already reduced and both types share a modulus.
/// If it ever does reduce, the moduli have drifted and `test_moduli_agree`
/// should be failing.
pub fn to_ark_fq(v: &StarkFq) -> ArkFq {
    ArkFq::from_le_bytes_mod_order(v.to_repr().as_ref())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ff::Field;

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
}
