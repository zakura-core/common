//! Curve cycles and the fixed parameters a proof system binds to them.
//!
//! A cycle pairs two curves whose scalar and base fields interchange. [`Cycle`]
//! names both fields and both curves through the field and curve traits,
//! together with the fixed generators and Poseidon instances a protocol uses
//! over them, so a proof system holds one type parameter and reaches every
//! parameter it needs. A cycle also names its recursion [`Profile`], what a
//! proof carries beyond the base recursion, so one type parameter fixes the
//! proof's shape too. [`Pasta`] is the cycle of Pallas and Vesta, in the
//! [`Standard`] profile unless another is named.
//! This module requires the `poseidon` feature, which also enables `traits`.
//!
//! Generator derivation is not part of this crate. Generators are public
//! points with unknown discrete logarithm relationships, derived by the
//! parameter owner, typically by hash-to-curve, and supplied as borrowed
//! static slices. Construction rejects identity points and a blinding
//! generator that repeats a vector generator; [`Generators::are_distinct`]
//! additionally checks the vector generators against each other. Poseidon
//! instances come from [`crate::poseidon`]. The consuming protocol combines
//! these generators and scalars into its commitments using curve arithmetic.
//!
//! This example uses known multiples to demonstrate the parameter API and
//! arithmetic. These generator choices are insecure for cryptographic
//! commitments.
//!
//! ```
//! use zakura_udon::{
//!     curve::{PallasPoint, VestaPoint, Projective},
//!     cycle::{Cycle, FixedGenerators, Generators, Pasta, PastaParams, Standard},
//!     field::{Fp, Fq, FieldAdapter, PallasScalar},
//! };
//!
//! // The parameter owner keeps derived generators alive for the program's
//! // lifetime; a leaked vector stands in for embedded or baked points here.
//! let multiple = |k| PallasPoint::GENERATOR.mul_projective(&Fq::from_u64(k)).to_point();
//! let pallas: &'static [PallasPoint] = Vec::leak(vec![multiple(1), multiple(2)]);
//! static VESTA: [VestaPoint; 1] = [VestaPoint::GENERATOR];
//! let params = PastaParams::new(
//!     Generators::new(pallas, multiple(3)),
//!     Generators::new(&VESTA, VestaPoint::GENERATOR.mul_projective(&Fp::from_u64(2)).to_point()),
//! );
//! let generators = Pasta::<Standard>::nested_generators(&params);
//! assert!(generators.are_distinct());
//! // g[0] * 2 + h * 3 = 2G + 9G
//! type Scalar = FieldAdapter<PallasScalar>;
//! let commitment =
//!     (generators.g()[0] * Scalar::from(2) + *generators.h() * Scalar::from(3)).to_affine();
//! assert_eq!(commitment.into_inner(), multiple(11));
//! ```

use crate::{curve::EndomorphismAffine, field::Field, poseidon::PoseidonPermutation};

mod generators;
mod pasta;
mod profile;

pub use generators::{FixedGenerators, Generators, PallasGenerators, VestaGenerators};
pub use pasta::{Pasta, PastaParams};
pub use profile::{Profile, Standard};

#[cfg(test)]
mod tests;

/// A cycle of two curves, each defined over the other's scalar field.
///
/// This proof-system interface requires radix-2 FFTs, deferred products, and
/// compatible order-three curve endomorphisms. The latter are required by
/// [`EndomorphismAffine`], beyond the basic [`crate::curve::Affine`] contract.
///
/// Implementations are zero-sized markers. Parameters that exist at runtime,
/// such as generators, live in [`Params`](Self::Params) and are reached
/// through the accessor functions.
pub trait Cycle: Copy + Default + Send + Sync + 'static {
    /// The field circuits are written over: the scalar field of the
    /// [`HostCurve`](Self::HostCurve) and the coordinate field of the
    /// [`NestedCurve`](Self::NestedCurve).
    type CircuitField: Field;

    /// The scalar field of the [`NestedCurve`](Self::NestedCurve) and the
    /// coordinate field of the [`HostCurve`](Self::HostCurve).
    type ScalarField: Field;

    /// The curve applications use for keys, signatures, and other primitives
    /// whose arithmetic circuits express over the
    /// [`CircuitField`](Self::CircuitField).
    type NestedCurve: EndomorphismAffine<Scalar = Self::ScalarField, Base = Self::CircuitField>;

    /// The curve the proof system commits with when proving circuits over the
    /// [`CircuitField`](Self::CircuitField).
    type HostCurve: EndomorphismAffine<Scalar = Self::CircuitField, Base = Self::ScalarField>;

    /// Fixed generators of the [`NestedCurve`](Self::NestedCurve).
    type NestedGenerators: FixedGenerators<Self::NestedCurve>;

    /// Fixed generators of the [`HostCurve`](Self::HostCurve).
    type HostGenerators: FixedGenerators<Self::HostCurve>;

    /// The Poseidon instance over the [`CircuitField`](Self::CircuitField).
    type CircuitPoseidon: PoseidonPermutation<Self::CircuitField>;

    /// The Poseidon instance over the [`ScalarField`](Self::ScalarField).
    type ScalarPoseidon: PoseidonPermutation<Self::ScalarField>;

    /// Runtime parameters: the generators, and whatever else the cycle needs.
    type Params: Send + Sync + 'static;

    /// The recursion profile: what a proof over this cycle carries beyond
    /// the base recursion.
    type Profile: Profile;

    /// Returns the fixed generators of the [`NestedCurve`](Self::NestedCurve).
    fn nested_generators(params: &Self::Params) -> &Self::NestedGenerators;

    /// Returns the fixed generators of the [`HostCurve`](Self::HostCurve).
    fn host_generators(params: &Self::Params) -> &Self::HostGenerators;

    /// Returns the Poseidon instance over the
    /// [`CircuitField`](Self::CircuitField).
    fn circuit_poseidon(params: &Self::Params) -> &Self::CircuitPoseidon;

    /// Returns the Poseidon instance over the
    /// [`ScalarField`](Self::ScalarField).
    fn scalar_poseidon(params: &Self::Params) -> &Self::ScalarPoseidon;
}
