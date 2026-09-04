//! This module contains the `Curve`/`CurveAffine` abstractions that allow us to
//! write code that generalizes over a pair of groups.

#[cfg(feature = "alloc")]
use group::prime::{PrimeCurve, PrimeCurveAffine};
#[cfg(feature = "alloc")]
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

#[cfg(feature = "alloc")]
use alloc::boxed::Box;
#[cfg(feature = "alloc")]
use core::ops::{Add, Mul, Sub};

/// This trait is a common interface for dealing with elements of an elliptic
/// curve group in a "projective" form, where that arithmetic is usually more
/// efficient.
///
/// Requires the `alloc` feature flag because of `hash_to_curve`.
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub trait CurveExt:
    PrimeCurve
    + group::Curve<Affine = <Self as CurveExt>::AffineExt>
    + group::Group<Scalar = <Self as CurveExt>::ScalarExt>
    + Default
    + ConditionallySelectable
    + ConstantTimeEq
    + From<<Self as group::Curve>::Affine>
{
    /// The scalar field of this elliptic curve.
    type ScalarExt: ff::WithSmallOrderMulGroup<3>;
    /// The base field over which this elliptic curve is constructed.
    type Base: ff::WithSmallOrderMulGroup<3>;
    /// The affine version of the curve
    type AffineExt: CurveAffine<CurveExt = Self, ScalarExt = <Self as CurveExt>::ScalarExt>
        + Mul<Self::ScalarExt, Output = Self>
        + for<'r> Mul<Self::ScalarExt, Output = Self>;

    /// CURVE_ID used for hash-to-curve.
    const CURVE_ID: &'static str;

    /// Apply the curve endomorphism by multiplying the x-coordinate
    /// by an element of multiplicative order 3.
    fn endo(&self) -> Self;

    /// Return the Jacobian coordinates of this point.
    fn jacobian_coordinates(&self) -> (Self::Base, Self::Base, Self::Base);

    /// Requests a hasher that accepts messages and returns near-uniformly
    /// distributed elements in the group, given domain prefix `domain_prefix`.
    ///
    /// This method is suitable for use as a random oracle.
    ///
    /// # Example
    ///
    /// ```
    /// use pasta_curves::arithmetic::CurveExt;
    /// fn pedersen_commitment<C: CurveExt>(
    ///     x: C::ScalarExt,
    ///     r: C::ScalarExt,
    /// ) -> C::Affine {
    ///     let hasher = C::hash_to_curve("z.cash:example_pedersen_commitment");
    ///     let g = hasher(b"g");
    ///     let h = hasher(b"h");
    ///     (g * x + &(h * r)).to_affine()
    /// }
    /// ```
    #[allow(clippy::type_complexity)]
    fn hash_to_curve<'a>(domain_prefix: &'a str) -> Box<dyn Fn(&[u8]) -> Self + 'a>;

    /// Returns whether or not this element is on the curve; should
    /// always be true unless an "unchecked" API was used.
    fn is_on_curve(&self) -> Choice;

    /// Returns the curve constant a.
    fn a() -> Self::Base;

    /// Returns the curve constant b.
    fn b() -> Self::Base;

    /// Obtains a point given Jacobian coordinates $X : Y : Z$, failing
    /// if the coordinates are not on the curve.
    fn new_jacobian(x: Self::Base, y: Self::Base, z: Self::Base) -> CtOption<Self>;

    /// Multiplies every point in `points` by the same `scalar`, writing the
    /// corresponding products to `output`.
    ///
    /// The default implementation performs the native scalar multiplication
    /// independently for each point. Implementations may batch work shared by
    /// these component-wise scalar multiplications.
    ///
    /// # Security
    ///
    /// This method may run in variable time with respect to `scalar`. **The
    /// scalar must be public.** Do not use this method with secret scalar
    /// material.
    ///
    /// # Panics
    ///
    /// Panics if `points` and `output` have different lengths.
    fn batch_mul_same_scalar_vartime(
        points: &[Self::AffineExt],
        scalar: &Self::ScalarExt,
        output: &mut [Self],
    ) {
        assert_eq!(points.len(), output.len());
        for (point, output) in points.iter().zip(output.iter_mut()) {
            *output = *point * scalar;
        }
    }

    /// Attempts an optimized variable-time multiscalar multiplication.
    ///
    /// Implementations own the backend and tuning decisions. Implementations
    /// without a specialized backend return `None`.
    ///
    /// # Security
    ///
    /// This method may run in variable time with respect to `scalars`. **Every
    /// scalar must be public.** Do not use this method with secret scalar
    /// material.
    ///
    /// # Panics
    ///
    /// Implementations may panic if `scalars` and `bases` have different
    /// lengths.
    fn try_multiexp_vartime(
        _scalars: &[Self::ScalarExt],
        _bases: &[Self::AffineExt],
    ) -> Option<Self> {
        None
    }

    /// Attempts an optimized variable-time identity test for a multiscalar
    /// multiplication whose nonzero scalars are expected to be random-like
    /// and full-width.
    ///
    /// The full-width profile is a performance hint only. The result must be
    /// exact for every scalar value, including zero and sparse or small
    /// nonzero scalars. [`Some(true)`](Some) means the multiscalar
    /// multiplication is the identity, [`Some(false)`](Some) means it is not,
    /// and [`None`] means that this implementation declined the optimization.
    /// Implementations without a specialized backend return [`None`].
    ///
    /// # Security
    ///
    /// This method may run in variable time with respect to `scalars` and
    /// `bases`. Inputs should be public unless the caller explicitly accepts
    /// timing leakage from secret material.
    ///
    /// # Panics
    ///
    /// Implementations may panic if `scalars` and `bases` have different
    /// lengths.
    fn try_multiexp_full_width_is_identity_vartime(
        _scalars: &[Self::ScalarExt],
        _bases: &[Self::AffineExt],
    ) -> Option<bool> {
        None
    }

    /// Attempts an affine, variable-time FFT specialized for this curve.
    ///
    /// `input` and `output` must have the same power-of-two length, equal to
    /// `2^log_n`. The transform is unnormalized. Implementations return
    /// `true` after writing the transform to `output`; the default returns
    /// `false` without modifying `output`.
    ///
    /// # Security
    ///
    /// This method may run in variable time with respect to the points and
    /// `omega`. Both must be public.
    fn fft_vartime(
        input: &[Self],
        output: &mut [Self::AffineExt],
        omega: Self::ScalarExt,
        log_n: u32,
    ) -> bool {
        let _ = (input, output, omega, log_n);
        false
    }

    /// Attempts to build a reusable prepared zero-check over fixed `bases`
    /// (see [`PreparedZeroCheck`]). Implementations without a prepared
    /// backend return `None`, and implementations may also decline —
    /// the Pasta backend returns `None` when its prepared table for this
    /// many bases would exceed its internal table-footprint budget.
    /// Preparation can cost hundreds of milliseconds and tens of mebibytes
    /// for a few thousand bases, so callers should invoke this once and
    /// reuse the handle across checks.
    ///
    /// # Security
    ///
    /// The returned handle runs in variable time with respect to scalars and
    /// points. Inputs to its zero-check methods must be public. Callers using
    /// [`PreparedZeroCheck::multiexp_with_terms_vartime`] with secret scalars
    /// must explicitly accept the timing side channel of a variable-time MSM.
    #[cfg(any(feature = "multicore", feature = "orbits"))]
    #[cfg_attr(docsrs, doc(cfg(any(feature = "multicore", feature = "orbits"))))]
    fn try_prepare_zero_check(
        bases: &[Self::AffineExt],
    ) -> Option<Box<dyn PreparedZeroCheck<Self>>> {
        let _ = bases;
        None
    }
}

/// An object-safe handle to a prepared fixed-base multiscalar zero-check:
/// whether $\sum_i \[k_i\] P_i + \sum_j \[s_j\] Q_j$ is the group identity,
/// for the fixed bases $P_i$ captured at preparation plus per-check
/// `extra` terms $(s_j, Q_j)$. Obtained from
/// [`CurveExt::try_prepare_zero_check`]; the Pasta curves implement it
/// with an internal prepared codebook backend, and the check is exact — it
/// accepts iff the sum is the identity.
#[cfg(any(feature = "multicore", feature = "orbits"))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "multicore", feature = "orbits"))))]
pub trait PreparedZeroCheck<C: CurveExt>: core::fmt::Debug + Send + Sync {
    /// The number of fixed bases this preparation covers; `scalars` below
    /// must have exactly this length.
    fn terms(&self) -> usize;

    /// Whether $\sum_i \[k_i\] P_i + \sum_j \[s_j\] Q_j$ is the identity.
    ///
    /// # Security
    ///
    /// Variable-time in everything; all inputs must be public.
    ///
    /// # Panics
    ///
    /// Panics if `scalars.len()` differs from [`Self::terms`].
    fn is_zero_with_terms_vartime(
        &self,
        scalars: &[C::ScalarExt],
        extra: &[(C::ScalarExt, C::AffineExt)],
    ) -> bool;

    /// The exact multiscalar multiplication
    /// $\sum_i \[k_i\] P_i + \sum_j \[s_j\] Q_j$ — the same evaluation the
    /// zero-check runs, with the group element returned instead of compared
    /// against the identity. A polynomial commitment over the prepared
    /// bases is exactly this call with the coefficients as the fixed
    /// scalars.
    ///
    /// # Security
    ///
    /// Variable-time in everything; callers committing to secret data must
    /// already accept a variable-time multiexp (as halo2's prover does).
    ///
    /// # Panics
    ///
    /// Panics if `scalars.len()` differs from [`Self::terms`].
    fn multiexp_with_terms_vartime(
        &self,
        scalars: &[C::ScalarExt],
        extra: &[(C::ScalarExt, C::AffineExt)],
    ) -> C;

    /// The same exact multiscalar multiplication as
    /// [`Self::multiexp_with_terms_vartime`], with the fixed-base scalars
    /// supplied as two consecutive slices. `prefix` is paired with the first
    /// fixed bases and `suffix` with the remaining fixed bases.
    ///
    /// The default implementation joins the slices in an owned buffer.
    /// Backends can override this method to consume both slices directly.
    ///
    /// # Security
    ///
    /// Variable-time in everything; callers committing to secret data must
    /// already accept a variable-time multiexp.
    ///
    /// # Panics
    ///
    /// Panics unless the combined slice length equals [`Self::terms`].
    fn multiexp_with_prefix_and_suffix(
        &self,
        prefix: &[C::ScalarExt],
        suffix: &[C::ScalarExt],
        extra: &[(C::ScalarExt, C::AffineExt)],
    ) -> C {
        let terms = prefix
            .len()
            .checked_add(suffix.len())
            .expect("fixed scalar count overflow");
        assert_eq!(terms, self.terms(), "one scalar per prepared base");

        let mut scalars = alloc::vec::Vec::with_capacity(terms);
        scalars.extend_from_slice(prefix);
        scalars.extend_from_slice(suffix);
        self.multiexp_with_terms_vartime(&scalars, extra)
    }
}

/// Internal construction for coordinates produced by trusted curve formulas.
#[cfg(feature = "alloc")]
pub(crate) trait CurveExtUnchecked: CurveExt {
    /// Constructs a point without validating that the coordinates are on the
    /// curve.
    ///
    /// Callers must ensure that the coordinates satisfy the curve equation or
    /// represent the identity.
    fn new_jacobian_unchecked(x: Self::Base, y: Self::Base, z: Self::Base) -> Self;
}

/// This trait is the affine counterpart to `Curve` and is used for
/// serialization, storage in memory, and inspection of $x$ and $y$ coordinates.
///
/// Requires the `alloc` feature flag because of `hash_to_curve` on [`CurveExt`].
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub trait CurveAffine:
    PrimeCurveAffine
    + group::CurveAffine<
        Scalar = <Self as CurveAffine>::ScalarExt,
        Curve = <Self as CurveAffine>::CurveExt,
    > + Default
    + Add<Output = <Self as group::CurveAffine>::Curve>
    + Sub<Output = <Self as group::CurveAffine>::Curve>
    + ConditionallySelectable
    + ConstantTimeEq
    + From<<Self as group::CurveAffine>::Curve>
{
    /// The scalar field of this elliptic curve.
    type ScalarExt: ff::WithSmallOrderMulGroup<3> + Ord;
    /// The base field over which this elliptic curve is constructed.
    type Base: ff::WithSmallOrderMulGroup<3> + Ord;
    /// The projective form of the curve
    type CurveExt: CurveExt<AffineExt = Self, ScalarExt = <Self as CurveAffine>::ScalarExt>;

    /// Gets the coordinates of this point.
    ///
    /// Returns None if this is the identity.
    fn coordinates(&self) -> CtOption<Coordinates<Self>>;

    /// Obtains a point given $(x, y)$, failing if it is not on the
    /// curve.
    fn from_xy(x: Self::Base, y: Self::Base) -> CtOption<Self>;

    /// Returns whether or not this element is on the curve; should
    /// always be true unless an "unchecked" API was used.
    fn is_on_curve(&self) -> Choice;

    /// Returns the curve constant $a$.
    fn a() -> Self::Base;

    /// Returns the curve constant $b$.
    fn b() -> Self::Base;
}

/// The affine coordinates of a point on an elliptic curve.
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
#[derive(Clone, Copy, Debug, Default)]
pub struct Coordinates<C: CurveAffine> {
    pub(crate) x: C::Base,
    pub(crate) y: C::Base,
}

#[cfg(feature = "alloc")]
impl<C: CurveAffine> Coordinates<C> {
    /// Obtains a `Coordinates` value given $(x, y)$, failing if it is not on the curve.
    pub fn from_xy(x: C::Base, y: C::Base) -> CtOption<Self> {
        // We use CurveAffine::from_xy to validate the coordinates.
        C::from_xy(x, y).map(|_| Coordinates { x, y })
    }
    /// Returns the x-coordinate.
    ///
    /// Equivalent to `Coordinates::u`.
    pub fn x(&self) -> &C::Base {
        &self.x
    }

    /// Returns the y-coordinate.
    ///
    /// Equivalent to `Coordinates::v`.
    pub fn y(&self) -> &C::Base {
        &self.y
    }

    /// Returns the u-coordinate.
    ///
    /// Equivalent to `Coordinates::x`.
    pub fn u(&self) -> &C::Base {
        &self.x
    }

    /// Returns the v-coordinate.
    ///
    /// Equivalent to `Coordinates::y`.
    pub fn v(&self) -> &C::Base {
        &self.y
    }
}

#[cfg(feature = "alloc")]
impl<C: CurveAffine> ConditionallySelectable for Coordinates<C> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Coordinates {
            x: C::Base::conditional_select(&a.x, &b.x, choice),
            y: C::Base::conditional_select(&a.y, &b.y, choice),
        }
    }
}

#[cfg(all(test, feature = "alloc"))]
mod tests {
    use super::*;
    use crate::{pallas, vesta};
    use ff::{Field, PrimeField, WithSmallOrderMulGroup};
    use group::CurveAffine as _;

    // Sizes 33 and up cross the GLV batch-affine threshold of 32 live points
    // (the identity injected at size/2 keeps one lane inert, so size 32 stays
    // just below it), exercising the batched kernel end-to-end through this
    // entry point at several sizes up to 513.
    const BATCH_SIZES: [usize; 16] = [0, 1, 2, 3, 7, 8, 15, 16, 17, 31, 32, 33, 127, 128, 129, 513];

    fn batch_mul_same_scalar_matches_native<C: CurveExt>() {
        let full_width = (C::ScalarExt::from(0x9E37_79B9_7F4A_7C15u64).square()
            + C::ScalarExt::from(0x0123_4567_89AB_CDEFu64))
        .square();
        let scalars = [
            C::ScalarExt::ZERO,
            C::ScalarExt::ONE,
            -C::ScalarExt::ONE,
            C::ScalarExt::from(2),
            C::ScalarExt::ZETA,
            -C::ScalarExt::ZETA,
            C::ScalarExt::ZETA + C::ScalarExt::ONE,
            C::ScalarExt::from(u64::MAX),
            C::ScalarExt::from_u128((1u128 << 127) - 1),
            C::ScalarExt::from_u128(1u128 << 127),
            full_width,
        ];

        for size in BATCH_SIZES {
            let projective: alloc::vec::Vec<C> = (0..size)
                .map(|i| {
                    if size > 2 && i == size / 2 {
                        C::identity()
                    } else {
                        C::generator()
                            * (C::ScalarExt::from(i as u64 + 1).square()
                                + C::ScalarExt::from(0xDEAD_BEEFu64))
                    }
                })
                .collect();
            let points: alloc::vec::Vec<C::AffineExt> =
                projective.iter().copied().map(C::AffineExt::from).collect();
            let mut output = alloc::vec![C::identity(); size];

            for scalar in scalars {
                C::batch_mul_same_scalar_vartime(&points, &scalar, &mut output);
                for ((point, output), expected) in
                    points.iter().zip(output.iter()).zip(projective.iter())
                {
                    assert_eq!(*output, *point * scalar);
                    assert_eq!(*output, *expected * scalar);
                }
            }
        }
    }

    #[test]
    fn batch_mul_same_scalar_pallas() {
        batch_mul_same_scalar_matches_native::<pallas::Point>();
    }

    #[test]
    fn batch_mul_same_scalar_vesta() {
        batch_mul_same_scalar_matches_native::<vesta::Point>();
    }

    #[test]
    #[should_panic]
    fn batch_mul_same_scalar_length_mismatch_panics() {
        let points = [pallas::Affine::generator()];
        let mut output = [];
        pallas::Point::batch_mul_same_scalar_vartime(&points, &pallas::Scalar::ONE, &mut output);
    }
}
