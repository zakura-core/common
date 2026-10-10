//! Curve contracts and Pasta arithmetic with caller-owned tables and scratch.
//!
//! Both curves have equation `y² = x³ + 5`, generator `(-1, 2)`, and prime
//! order. [`Pallas`] uses [`crate::field::Fp`] coordinates and
//! [`crate::field::Fq`] scalars; [`Vesta`] reverses that pairing.
//! [`AffinePoint`] stores a nonidentity point, [`Point`] also represents
//! identity, and [`ProjectivePoint`] avoids inversions during addition and doubling.
//! Use [`batch_normalize`] to share an inversion across projective results and
//! [`EisensteinTable`] or [`FixedBaseTable`] to prepare a base for repeated
//! scalar multiplication. [`glv_decompose`] and point endomorphisms are also
//! available to callers implementing their own scalar algorithms.
//! [`EisensteinScalar`] retains joint digits for compact tables, and
//! [`EisensteinTableBatch`] prepares or multiplies several bases together.
//! [`batch_mul_same_scalar`] multiplies projective inputs in place when no
//! retained tables are needed, accepting identity points and caller-owned
//! scratch sized by [`same_scalar_scratch`].
//! [`msm`](crate::msm) sums dense or indexed scalar/base terms with caller-owned
//! scratch and execution. Native point arithmetic uses explicit methods. The
//! unstable `traits` feature adds the `AffineAdapter` and `ProjectiveAdapter`
//! wrappers with operators, implementing `Affine`, `Projective`, and their
//! endomorphism capabilities through the same native arithmetic.
//!
//! Affine coordinates use [`crate::field::Reduced`] field elements;
//! projective coordinates and scalars may use loose residues. Constructors
//! establish the field and curve invariants, which trusted POD storage preserves
//! byte for byte.
//! Operations are variable-time and provide no constant-time guarantee for
//! secret inputs, including bases, scalars, and table contents. Setup and
//! execution require neither allocation nor a feature flag.
//!
//! ```
//! use zakura_udon::{curve::PallasPoint, field::Fq};
//! let generator = PallasPoint::GENERATOR;
//! assert_eq!(generator.mul_projective(&Fq::from_u64(2)),
//!            generator.double());
//! assert!(generator.add(&generator.neg()).is_identity());
//! assert_eq!(PallasPoint::from_bytes(generator.to_bytes()), Some(generator));
//! ```

#[cfg(feature = "traits")]
mod consumer;
pub(crate) mod pasta;

#[cfg(feature = "traits")]
pub use consumer::{
    Affine, AffineAdapter, EndomorphismAffine, EndomorphismProjective, Projective,
    ProjectiveAdapter,
};
pub use pasta::{
    AffinePoint, CurveError, CurveTableEntry, CurveTableRequirements, EisensteinScalar,
    EisensteinTable, EisensteinTableBatch, FixedBaseDescription, FixedBaseTable,
    IncompleteDoubleAndAdd, Pallas, PallasAffine, PallasPoint, PallasProjective, PastaCurve, Point,
    PreparedAffinePoint, ProjectivePoint, RotatedAffinePoint, Vesta, VestaAffine, VestaPoint,
    VestaProjective, batch_mul_same_scalar, batch_mul_same_scalar_prepared, batch_normalize,
    glv_decompose, same_scalar_scratch,
};
