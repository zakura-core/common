//! Standalone Orchard commitment, nullifier, and diversification primitives.
//!
//! Hash domains and the diversification fallback follow the primitive
//! [cache ownership](crate::primitives#lazy-data-and-ownership) policy, as do
//! the fixed-generator tables and Sinsemilla affine vector used by these calls.

use super::cache::Cache as OnceBox;
use alloc::boxed::Box;
use subtle::CtOption;

use super::{
    Fp, Fq, NonIdentityPallasPoint, generators::FixedGenerator, leos2bsp, pallas,
    sinsemilla::HashDomain,
};

const BASE_BITS: usize = Fp::NUM_BITS as usize;
const IVK_DOMAIN: &str = "z.cash:Orchard-CommitIvk-M";
const NOTE_DOMAIN: &str = "z.cash:Orchard-NoteCommit-M";
const DIVERSIFY_DOMAIN: &str = "z.cash:Orchard-gd";
static IVK: OnceBox<HashDomain> = OnceBox::new();
static NOTE: OnceBox<HashDomain> = OnceBox::new();

/// The x-coordinate of a point, with the identity mapped to zero.
pub fn extract(point: pallas::Point) -> Fp {
    point.to_affine().raw_coordinates().0
}

/// Embeds a canonical Pallas base-field integer in the larger scalar field.
pub fn base_to_scalar(value: Fp) -> Fq {
    Fq::from_native(
        udon::field::Fq::from_canonical_uint(value.native().to_canonical_uint())
            .expect("the Pallas base modulus is smaller than the scalar modulus"),
    )
}

/// Orchard's incoming viewing-key commitment, including Sinsemilla failure.
pub fn commit_ivk(ak: Fp, nk: Fp, randomness: Fq) -> CtOption<Fp> {
    IVK.get_or_init(|| Box::new(HashDomain::new(IVK_DOMAIN)))
        .hash_to_point(
            leos2bsp(ak.to_bytes())
                .take(BASE_BITS)
                .chain(leos2bsp(nk.to_bytes()).take(BASE_BITS)),
        )
        .map(|point| extract(point + FixedGenerator::CommitIvkR.multiply(&randomness)))
}

/// Orchard's note commitment. Point encodings are produced only for the
/// protocol's Sinsemilla message; arithmetic retains native points.
pub fn note_commitment(
    diversified_base: NonIdentityPallasPoint,
    transmission_key: NonIdentityPallasPoint,
    value: u64,
    rho: Fp,
    psi: Fp,
    randomness: Fq,
) -> CtOption<pallas::Point> {
    NOTE.get_or_init(|| Box::new(HashDomain::new(NOTE_DOMAIN)))
        .hash_to_point(
            leos2bsp(diversified_base.to_bytes())
                .chain(leos2bsp(transmission_key.to_bytes()))
                .chain(leos2bsp(value.to_le_bytes()))
                .chain(leos2bsp(rho.to_bytes()).take(BASE_BITS))
                .chain(leos2bsp(psi.to_bytes()).take(BASE_BITS)),
        )
        .map(|point| point + FixedGenerator::NoteCommitR.multiply(&randomness))
}

/// Orchard's nullifier derivation, using the width-three Poseidon parameters.
pub fn nullifier(key: Fp, rho: Fp, psi: Fp, commitment: pallas::Point) -> Fp {
    extract(
        FixedGenerator::NullifierK
            .multiply(&base_to_scalar(super::poseidon::hash([key, rho]) + psi))
            + commitment,
    )
}

/// A signed value commitment. `magnitude` is the absolute value and `negative`
/// selects its sign; both zero signs yield the same commitment.
pub fn value_commitment(magnitude: u64, negative: bool, randomness: Fq) -> pallas::Point {
    let value = Fq::from(magnitude);
    FixedGenerator::ValueCommitV.multiply(&(if negative { -value } else { value }))
        + FixedGenerator::ValueCommitR.multiply(&randomness)
}

/// Orchard's diversification hash, including the specified identity fallback.
pub fn diversify_hash(diversifier: &[u8; 11]) -> NonIdentityPallasPoint {
    let hasher = pallas::Point::hash_to_curve(DIVERSIFY_DOMAIN);
    let point = hasher(diversifier).native().to_point();
    if point.is_identity() {
        static FALLBACK: OnceBox<udon::curve::PallasAffine> = OnceBox::new();
        return NonIdentityPallasPoint::from_native(*FALLBACK.get_or_init(|| {
            Box::new(
                *hasher(&[])
                    .native()
                    .to_point()
                    .as_affine()
                    .expect("nonidentity diversification fallback"),
            )
        }));
    }
    NonIdentityPallasPoint::from_native(
        *point
            .as_affine()
            .expect("nonidentity diversification point"),
    )
}
