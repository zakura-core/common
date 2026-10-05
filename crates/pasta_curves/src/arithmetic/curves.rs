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

    /// Attempts several fixed-base multiscalar multiplications that share
    /// `scalars`.
    ///
    /// `output.len()` is the number of independent lanes. The number of
    /// prepared odd multiples per base is inferred from the slice lengths and
    /// must be a supported power of two. `prepared_odd_multiples` is laid out
    /// by scalar, odd multiple, then lane. Its entry
    /// `(scalar, multiple, lane)` is
    /// $(2 \mathit{multiple} + 1) P_{\mathit{scalar}, \mathit{lane}}$. A
    /// successful implementation writes
    /// $\sum_i \mathit{scalars}_i P_{i, \mathit{lane}}$ to each output lane.
    ///
    /// Implementations return `false` without modifying `output` when this
    /// operation is unsupported or the input shape is invalid.
    ///
    /// # Correctness
    ///
    /// Callers must supply odd multiples in the documented layout.
    /// Implementations need not validate the semantic contents of a
    /// shape-valid table; malformed entries can produce an incorrect group
    /// result even when this method returns `true`.
    ///
    /// # Security
    ///
    /// This method may run in variable time with respect to `scalars`.
    /// **The scalars must be public.** Do not use this method with secret
    /// scalar material.
    fn try_batch_multiexp_shared_scalars_vartime(
        _prepared_odd_multiples: &[Self::AffineExt],
        _scalars: &[Self::ScalarExt],
        _output: &mut [Self],
    ) -> bool {
        false
    }

    /// Attempts an optimized variable-time multiscalar multiplication.
    ///
    /// Implementations own the backend and tuning decisions. Implementations
    /// without a specialized backend return `None`.
    ///
    /// # Security
    ///
    /// This method may run in variable time with respect to `scalars`. Inputs
    /// should be public unless the caller explicitly accepts timing leakage
    /// from secret scalar material.
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

    /// The same exact multiscalar multiplication as
    /// [`Self::multiexp_with_terms_vartime`], with `scalars` paired with the
    /// contiguous prepared bases beginning at `base_offset`. Prepared bases
    /// outside that range have implicit zero scalars.
    ///
    /// The default implementation materializes the implicit zero scalars.
    /// Backends can override this method to evaluate only the selected range.
    ///
    /// # Security
    ///
    /// Variable-time in everything; callers committing to secret data must
    /// already accept a variable-time multiexp.
    ///
    /// # Panics
    ///
    /// Panics if the selected range extends past [`Self::terms`].
    fn multiexp_with_base_offset_vartime(
        &self,
        base_offset: usize,
        scalars: &[C::ScalarExt],
        extra: &[(C::ScalarExt, C::AffineExt)],
    ) -> C {
        let range_end = base_offset
            .checked_add(scalars.len())
            .expect("prepared base range overflow");
        assert!(range_end <= self.terms(), "prepared base range in bounds");

        let mut full_scalars = alloc::vec![<C::ScalarExt as ff::Field>::ZERO; self.terms()];
        full_scalars[base_offset..range_end].copy_from_slice(scalars);
        self.multiexp_with_terms_vartime(&full_scalars, extra)
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

/// Attempts to decode eight affine encodings with a shared SIMD backend.
///
/// Each result has the same validity and point value as
/// [`group::GroupEncoding::from_bytes`], including the encoded identity. The
/// outer `None` means the curve, enabled features, or CPU are unsupported;
/// in that case no encodings are decoded and callers can use scalar decoding.
/// An invalid encoding instead produces a per-lane empty [`CtOption`].
///
/// This currently accelerates only the concrete Pallas and Vesta affine types
/// with `glv`, `sqrt-table`, and `x86_64-asm` on an IFMA-capable x86-64 CPU.
/// Like the other arithmetic in this crate, it may run in variable time.
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub fn try_batch_from_bytes8<C: CurveAffine>(bytes: &[C::Repr; 8]) -> Option<[CtOption<C>; 8]> {
    #[cfg(all(
        feature = "glv",
        feature = "sqrt-table",
        feature = "x86_64-asm",
        target_arch = "x86_64",
        target_pointer_width = "64"
    ))]
    {
        use core::any::TypeId;

        // A matching base field is insufficient: a downstream curve could
        // use a different equation or encoding with that same field.
        if (TypeId::of::<C>() != TypeId::of::<crate::pallas::Affine>()
            && TypeId::of::<C>() != TypeId::of::<crate::vesta::Affine>())
            || !crate::fields::ifma_available_for::<C::Base>()
        {
            return None;
        }
        return batch_from_bytes8_with(bytes, crate::fields::try_sqrt8);
    }
    #[cfg(not(all(
        feature = "glv",
        feature = "sqrt-table",
        feature = "x86_64-asm",
        target_arch = "x86_64",
        target_pointer_width = "64"
    )))]
    {
        let _ = bytes;
        None
    }
}

// The production caller has established the exact curve and encoding. A
// scalar-root callback tests point construction and flags on non-SIMD targets.
#[cfg(all(
    feature = "alloc",
    any(
        test,
        all(
            feature = "glv",
            feature = "sqrt-table",
            feature = "x86_64-asm",
            target_arch = "x86_64",
            target_pointer_width = "64"
        )
    )
))]
fn batch_from_bytes8_with<C: CurveAffine>(
    bytes: &[C::Repr; 8],
    sqrt: impl FnOnce(&[C::Base; 8]) -> Option<[CtOption<C::Base>; 8]>,
) -> Option<[CtOption<C>; 8]> {
    use group::ff::{Field, PrimeField};

    let signs = bytes
        .each_ref()
        .map(|repr| Choice::from(repr.as_ref()[31] >> 7));
    let parsed = bytes.each_ref().map(|repr| {
        let mut x_repr = <C::Base as PrimeField>::Repr::default();
        x_repr.as_mut().copy_from_slice(repr.as_ref());
        x_repr.as_mut()[31] &= 0x7f;
        C::Base::from_repr(x_repr)
    });
    // Noncanonical input flags survive even when their private scratch
    // value is zero; in particular, raw p must not become an identity.
    let xs = parsed.map(|x| x.unwrap_or(C::Base::ZERO));
    let rhs = xs.map(|x| x.square() * x + C::b());
    let roots = sqrt(&rhs)?;
    Some(core::array::from_fn(|lane| {
        let y = roots[lane].unwrap_or(C::Base::ZERO);
        let y = C::Base::conditional_select(&y, &-y, signs[lane] ^ y.is_odd());
        let point = C::from_xy(xs[lane], y);
        let identity = xs[lane].is_zero() & !signs[lane];
        CtOption::new(
            C::conditional_select(&point.unwrap_or(C::identity()), &C::identity(), identity),
            parsed[lane].is_some() & (identity | (roots[lane].is_some() & point.is_some())),
        )
    }))
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
    use group::{CurveAffine as _, Group as _};

    fn assert_batch_decode<C: CurveAffine>(bytes: &[C::Repr; 8]) {
        let expected = bytes
            .each_ref()
            .map(|repr| Option::<C>::from(C::from_bytes(repr)));
        let model =
            batch_from_bytes8_with::<C>(bytes, |values| Some(values.map(|value| value.sqrt())))
                .unwrap();
        assert_eq!(
            model.map(Option::<C>::from),
            expected,
            "scalar-root assembly"
        );
        let actual = try_batch_from_bytes8::<C>(bytes);
        #[cfg(all(
            feature = "glv",
            feature = "sqrt-table",
            feature = "x86_64-asm",
            target_arch = "x86_64",
            target_pointer_width = "64"
        ))]
        if crate::fields::ifma_available_for::<C::Base>() {
            assert!(
                actual.is_some(),
                "supported Pasta decoding must engage SIMD"
            );
        }
        if let Some(actual) = actual {
            assert_eq!(actual.map(Option::<C>::from), expected, "SIMD decoding");
        }
    }

    fn point_repr<C: CurveAffine>(value: &<C::Base as PrimeField>::Repr) -> C::Repr {
        let mut encoded = C::Repr::default();
        encoded.as_mut().copy_from_slice(value.as_ref());
        encoded
    }

    fn batch_decode_cases<C: CurveAffine>() -> alloc::vec::Vec<C::Repr> {
        let generator = C::from(C::CurveExt::generator());
        let mut cases = alloc::vec![
            C::identity().to_bytes(),
            generator.to_bytes(),
            (-generator).to_bytes(),
            point_repr::<C>(&(-C::Base::ONE).to_repr()),
        ];
        let mut signed_zero = C::Repr::default();
        signed_zero.as_mut()[31] = 0x80;
        cases.push(signed_zero);
        // Derive raw p from canonical p-1, without accepting a reduced repr.
        let mut raw_p = point_repr::<C>(&(-C::Base::ONE).to_repr());
        for byte in raw_p.as_mut() {
            let (next, carry) = byte.overflowing_add(1);
            *byte = next;
            if !carry {
                break;
            }
        }
        cases.push(raw_p.clone());
        raw_p.as_mut()[31] |= 0x80;
        cases.push(raw_p);
        let mut maximal = C::Repr::default();
        maximal.as_mut().fill(u8::MAX);
        cases.push(maximal);
        let nonsquare = (1_u64..)
            .map(C::Base::from)
            .find(|x| !bool::from((x.square() * x + C::b()).sqrt().is_some()))
            .unwrap();
        cases.push(point_repr::<C>(&nonsquare.to_repr()));
        let mut signed = point_repr::<C>(&nonsquare.to_repr());
        signed.as_mut()[31] |= 0x80;
        cases.push(signed);
        cases
    }

    fn batch_decode_matches_scalar<C: CurveAffine>() {
        use rand::{Rng, SeedableRng};

        let cases = batch_decode_cases::<C>();
        for shift in 0..cases.len() {
            let bytes = core::array::from_fn(|lane| cases[(shift + lane) % cases.len()].clone());
            assert_batch_decode::<C>(&bytes);
            for sign_mask in 0_u16..=u8::MAX.into() {
                let mut signed = bytes.clone();
                for (lane, repr) in signed.iter_mut().enumerate() {
                    repr.as_mut()[31] ^= ((sign_mask >> lane) as u8 & 1) << 7;
                }
                assert_batch_decode::<C>(&signed);
            }
        }
        let mut rng = rand_xorshift::XorShiftRng::from_seed([0xD3; 16]);
        for iteration in 0..256 {
            let bytes = core::array::from_fn(|_| {
                if iteration % 3 == 0 {
                    C::from(C::CurveExt::generator() * C::ScalarExt::random(&mut rng)).to_bytes()
                } else if iteration % 3 == 1 {
                    // Proof lookahead can contain scalar encodings. They
                    // are simply arbitrary candidate compressed points.
                    let mut repr = C::Repr::default();
                    repr.as_mut()
                        .copy_from_slice(C::ScalarExt::random(&mut rng).to_repr().as_ref());
                    repr
                } else {
                    let mut repr = C::Repr::default();
                    rng.fill_bytes(repr.as_mut());
                    repr
                }
            });
            assert_batch_decode::<C>(&bytes);
        }
        assert!(
            batch_from_bytes8_with::<C>(&core::array::from_fn(|_| C::Repr::default()), |_| None)
                .is_none()
        );
    }

    #[test]
    fn batch_decode_pallas_matches_scalar() {
        batch_decode_matches_scalar::<pallas::Affine>();
    }

    #[test]
    fn batch_decode_vesta_matches_scalar() {
        batch_decode_matches_scalar::<vesta::Affine>();
    }

    #[test]
    fn batch_decode_unsupported_curve_and_configuration() {
        // The isogenous curves use the same base fields, but a different
        // equation. Dispatch must not be based on the base field alone.
        let invalid = [[u8::MAX; 32]; 8];
        assert!(try_batch_from_bytes8::<crate::curves::IsoEpAffine>(&invalid).is_none());
        assert!(try_batch_from_bytes8::<crate::curves::IsoEqAffine>(&invalid).is_none());
        #[cfg(not(all(
            feature = "glv",
            feature = "sqrt-table",
            feature = "x86_64-asm",
            target_arch = "x86_64",
            target_pointer_width = "64"
        )))]
        {
            assert!(try_batch_from_bytes8::<pallas::Affine>(&invalid).is_none());
            assert!(try_batch_from_bytes8::<vesta::Affine>(&invalid).is_none());
        }
    }

    #[test]
    #[ignore = "manual scalar-versus-SIMD point decoding diagnostic"]
    fn batch_decode_timings() {
        fn check<C: CurveAffine>() {
            let bytes = core::array::from_fn(|lane| {
                C::from(C::CurveExt::generator() * C::ScalarExt::from(lane as u64 + 1)).to_bytes()
            });
            let cold = std::time::Instant::now();
            let Some(decoded) = try_batch_from_bytes8::<C>(&bytes) else {
                std::eprintln!(
                    "batch_decode curve={} unsupported",
                    core::any::type_name::<C>()
                );
                return;
            };
            let cold_ns = cold.elapsed().as_nanos();
            let expected = bytes
                .each_ref()
                .map(|repr| Option::<C>::from(C::from_bytes(repr)));
            assert_eq!(decoded.map(Option::<C>::from), expected);
            let iterations = std::env::var("IRONWOOD_DECODE_BENCH_ITERS")
                .ok()
                .and_then(|value| value.parse::<u32>().ok())
                .filter(|iterations| *iterations != 0)
                .unwrap_or(4_000);
            for round in 0..4 {
                let start = std::time::Instant::now();
                for _ in 0..iterations {
                    for repr in core::hint::black_box(&bytes) {
                        core::hint::black_box(C::from_bytes(repr));
                    }
                }
                let scalar_ns = start.elapsed().as_nanos() / u128::from(iterations);
                let start = std::time::Instant::now();
                for _ in 0..iterations {
                    core::hint::black_box(try_batch_from_bytes8::<C>(core::hint::black_box(
                        &bytes,
                    )));
                }
                let batch_ns = start.elapsed().as_nanos() / u128::from(iterations);
                std::eprintln!(
                    "batch_decode curve={} round={round} cold_batch_ns={cold_ns} scalar8_ns={scalar_ns} batch8_ns={batch_ns}",
                    core::any::type_name::<C>(),
                );
            }
        }
        check::<pallas::Affine>();
        check::<vesta::Affine>();
    }

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

    #[test]
    fn shared_scalar_batch_invalid_shape_leaves_output_unchanged() {
        let mut output = [pallas::Point::generator()];
        let expected = output;
        assert!(!pallas::Point::try_batch_multiexp_shared_scalars_vartime(
            &[],
            &[pallas::Scalar::ONE],
            &mut output,
        ));
        assert_eq!(output, expected);
    }
}
