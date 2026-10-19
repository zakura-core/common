//! Nonidentity points and compile-time coordinate validation.

use bento::const_arithmetic::{m255, u256};
use core::{fmt, marker::PhantomData};

use super::{AffinePoint, PastaCurve, Point, ProjectivePoint, curve_rhs};
use crate::field::{PastaField, PrimeModulus, Reduced, ReductionState};

impl<C: PastaCurve> fmt::Debug for AffinePoint<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AffinePoint")
            .field("x", &self.x)
            .field("y", &self.y)
            .finish()
    }
}

impl<C: PastaCurve> AffinePoint<C> {
    /// The curve coefficient `B = 5` in `y² = x³ + B`, in the coordinate field.
    pub const B: PastaField<C::Base> =
        PastaField::from_montgomery_limbs(m255::from_u64!(&C::Base::MODULUS, 5));

    /// The generator `(-1, 2)`.
    pub const GENERATOR: Self = Self {
        x: PastaField::from_montgomery_limbs(m255::from_u256!(
            &C::Base::MODULUS,
            &u256::sub_with_borrow!(&C::Base::MODULUS, &[1, 0, 0, 0]).0,
        )),
        y: PastaField::from_montgomery_limbs(m255::from_u64!(&C::Base::MODULUS, 2)),
        marker: PhantomData,
    };

    /// Checks that reduced coordinates satisfy the curve equation.
    ///
    /// Returns `None` for coordinates off the curve, including `(0, 0)`.
    pub fn from_xy(
        x: PastaField<C::Base, Reduced>,
        y: PastaField<C::Base, Reduced>,
    ) -> Option<Self> {
        if y.square().reduce() != curve_rhs::<C>(&x).reduce() {
            return None;
        }
        Some(Self {
            x,
            y,
            marker: PhantomData,
        })
    }

    /// Borrows the affine coordinates `(x, y)`.
    #[allow(
        clippy::type_complexity,
        reason = "the pair directly describes the borrowed coordinates"
    )]
    pub const fn coordinates(
        &self,
    ) -> (&PastaField<C::Base, Reduced>, &PastaField<C::Base, Reduced>) {
        (&self.x, &self.y)
    }

    /// Applies the order-three endomorphism `(x, y) -> (zeta * x, y)`.
    ///
    /// Here `zeta` is the coordinate field's [`PastaField::ZETA`] value.
    /// This map equals multiplication by the scalar field's
    /// [`PastaField::ZETA`] value.
    pub fn endomorphism(&self) -> Self {
        Self {
            x: self.x.mul(&PastaField::<C::Base>::ZETA).reduce(),
            ..*self
        }
    }

    /// Returns the additive inverse `(x, -y)`.
    pub fn neg(&self) -> Self {
        // Both Pasta groups have prime order, so no nonidentity point has
        // order two and `y` is never zero: `p - y` is already reduced.
        Self {
            x: self.x,
            y: self.y.negate_nonzero(),
            marker: PhantomData,
        }
    }

    /// Includes this point in the identity-capable affine representation.
    pub const fn to_point(&self) -> Point<C> {
        Point(Some(*self))
    }

    /// Lifts this point to Jacobian coordinates with `z = 1`.
    pub const fn to_projective(&self) -> ProjectivePoint<C> {
        ProjectivePoint::from_affine(self)
    }

    /// Completes an affine addition from its slope `λ`.
    ///
    /// Returns `(λ² − x1 − x2, λ(x1 − x) − y1)` with reduced coordinates. The
    /// caller establishes that the operands describe a nonidentity sum.
    #[inline]
    pub(super) fn from_slope<S: ReductionState>(
        x1: &PastaField<C::Base, S>,
        y1: &PastaField<C::Base, S>,
        x2: &PastaField<C::Base, S>,
        slope: &PastaField<C::Base>,
    ) -> Self {
        let x = slope.square().sub(x1).sub(x2);
        let y = slope.mul(&x1.sub(&x)).sub(y1);
        Self {
            x: x.reduce(),
            y: y.reduce(),
            marker: PhantomData,
        }
    }

    /// [`Self::from_slope`] without the closing reductions: the loose
    /// coordinates of the sum, for callers that keep intermediate sums loose.
    #[inline]
    pub(super) fn slope_coordinates<S: ReductionState>(
        x1: &PastaField<C::Base, S>,
        y1: &PastaField<C::Base, S>,
        x2: &PastaField<C::Base, S>,
        slope: &PastaField<C::Base>,
    ) -> (PastaField<C::Base>, PastaField<C::Base>) {
        let x = slope.square().sub(x1).sub(x2);
        let y = slope.mul(&x1.sub(&x)).sub(y1);
        (x, y)
    }

    /// [`Self::from_slope`] with a fused `mul_sub` for the `y` coordinate.
    #[inline]
    pub(super) fn from_slope_fused<S: ReductionState>(
        x1: &PastaField<C::Base, S>,
        y1: &PastaField<C::Base, S>,
        x2: &PastaField<C::Base, S>,
        slope: &PastaField<C::Base>,
    ) -> Self {
        let x = slope.square().sub(x1).sub(x2);
        let y = slope.mul_sub(&x1.sub(&x), y1);
        Self {
            x: x.reduce(),
            y: y.reduce(),
            marker: PhantomData,
        }
    }

    /// The doubling slope numerator `3x²`, as `2x² + x²`.
    #[inline]
    pub(super) fn tangent_numerator(&self) -> PastaField<C::Base> {
        Self::tangent_numerator_at(&self.x)
    }

    /// The same numerator for an accumulator with loose coordinates.
    #[inline]
    pub(super) fn tangent_numerator_at<S: ReductionState>(
        x: &PastaField<C::Base, S>,
    ) -> PastaField<C::Base> {
        let xx = x.square();
        xx.double().add(&xx)
    }

    /// Adds `q` given `inverse = 1 / (q.x − self.x)`; the x coordinates must differ.
    #[inline]
    pub(super) fn chord_with_inverse(&self, q: &Self, inverse: &PastaField<C::Base>) -> Self {
        let slope = q.y.sub(&self.y).mul(inverse);
        Self::from_slope(&self.x, &self.y, &q.x, &slope)
    }

    /// Sums the original affine inputs, reusing their storage during reduction.
    ///
    /// Empty input and cancelling sums return identity. Repeated points and
    /// inverse pairs are accepted. The point slice is scratch: its contents and
    /// order may change, and no final representation is promised in that slice.
    ///
    /// `fields` must contain at least one element per input point. Its initial
    /// contents do not matter; entries beyond `points.len()` are untouched.
    /// Insufficient field scratch panics before either buffer is changed.
    /// Execution is serial, allocation-free and variable-time, with no
    /// constant-time guarantee for secret inputs.
    ///
    /// ```
    /// use zakura_udon::{curve::PallasAffine, field::Fp};
    /// let g = PallasAffine::GENERATOR;
    /// let mut points = [g, g.neg()];
    /// let sum = PallasAffine::sum_in_place(&mut points, &mut [Fp::ZERO; 2]);
    /// assert!(sum.is_identity());
    /// ```
    pub fn sum_in_place(
        points: &mut [Self],
        fields: &mut [PastaField<C::Base>],
    ) -> ProjectivePoint<C> {
        let count = points.len();
        crate::checks::assert_scratch("affine sum", count, fields.len());
        super::reduce::sum(points, &mut fields[..count])
    }

    /// Multiplies by a scalar without inversion.
    ///
    /// Processes the full canonical scalar; zero returns identity. The scalar
    /// uses the loose field representation. Execution is variable-time and uses
    /// bounded internal stack storage, with no caller table, scratch, or
    /// allocation.
    ///
    /// Use [`EisensteinTable`](super::EisensteinTable) or
    /// [`FixedBaseTable`](super::FixedBaseTable) to retain preparation for repeated
    /// multiplication of the same base.
    pub fn mul_projective(&self, scalar: &PastaField<C::Scalar>) -> ProjectivePoint<C> {
        // Short scalars use the binary ladder without paying for table setup.
        let scalar = scalar.to_canonical_uint();
        if scalar.highest_set_bit().is_none_or(|high| high < 64) {
            super::projective::multiply_canonical(scalar, |point| point.add_mixed(self))
        } else {
            super::effective::multiply(&self.to_projective(), scalar)
        }
    }

    // Const generic limbs let the compile-time arithmetic macros validate
    // coordinates even when the public wrapper occurs in a runtime expression.
    /// Expansion support for constructing a point from constant Montgomery limbs.
    ///
    /// Each coordinate consists of four little-endian limbs. Constant evaluation
    /// fails unless both residues are reduced and satisfy the curve equation.
    #[doc(hidden)]
    pub const fn __from_montgomery_coordinates<
        const X0: u64,
        const X1: u64,
        const X2: u64,
        const X3: u64,
        const Y0: u64,
        const Y1: u64,
        const Y2: u64,
        const Y3: u64,
    >() -> Self {
        const {
            let x = PastaField::from_montgomery_limbs([X0, X1, X2, X3]);
            let y = PastaField::from_montgomery_limbs([Y0, Y1, Y2, Y3]);
            let lhs = m255::mul!(&C::Base::MODULUS, &[Y0, Y1, Y2, Y3], &[Y0, Y1, Y2, Y3]);
            let rhs = m255::add!(
                &C::Base::MODULUS,
                &m255::mul!(
                    &C::Base::MODULUS,
                    &m255::mul!(&C::Base::MODULUS, &[X0, X1, X2, X3], &[X0, X1, X2, X3]),
                    &[X0, X1, X2, X3],
                ),
                &Self::B.montgomery_limbs(),
            );
            let mut index = 0;
            while index < 4 {
                assert!(lhs[index] == rhs[index], "point must be on the curve");
                index += 1;
            }
            Self {
                x,
                y,
                marker: PhantomData,
            }
        }
    }
}

/// Constructs a nonidentity Pallas affine point from constant coordinates.
///
/// Both arguments must be [`Fp`](crate::field::Fp) constant expressions with
/// residues satisfying `y² = x³ + 5`. Invalid values, including `(0, 0)`,
/// values from the wrong field, and runtime arguments fail compilation, even
/// when the macro invocation appears in a runtime expression.
///
/// ```
/// use zakura_udon::{curve::PallasAffine, fp_hex, pallas_affine};
/// const G: PallasAffine = pallas_affine!(
///     fp_hex!("0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000"),
///     fp_hex!("0x0000000000000000000000000000000000000000000000000000000000000002"),
/// );
/// assert_eq!(G, PallasAffine::GENERATOR);
/// ```
#[macro_export]
macro_rules! pallas_affine {
    ($x:expr, $y:expr $(,)?) => {
        $crate::__pasta_affine!($crate::field::Fp, $crate::curve::PallasAffine, $x, $y)
    };
}

/// Constructs a nonidentity Vesta affine point from constant coordinates.
///
/// Both arguments must be [`Fq`](crate::field::Fq) constant expressions. Enforces
/// the same coordinate checks as [`pallas_affine!`](crate::pallas_affine).
#[macro_export]
macro_rules! vesta_affine {
    ($x:expr, $y:expr $(,)?) => {
        $crate::__pasta_affine!($crate::field::Fq, $crate::curve::VestaAffine, $x, $y)
    };
}

/// Expansion support for checked constant Pasta coordinates.
#[doc(hidden)]
#[macro_export]
macro_rules! __pasta_affine {
    ($field:ty, $point:ty, $x:expr, $y:expr) => {
        const {
            <$point>::__from_montgomery_coordinates::<
                {
                    let value: $field = ($x).reduce().into_loose();
                    value.montgomery_limbs()[0]
                },
                {
                    let value: $field = ($x).reduce().into_loose();
                    value.montgomery_limbs()[1]
                },
                {
                    let value: $field = ($x).reduce().into_loose();
                    value.montgomery_limbs()[2]
                },
                {
                    let value: $field = ($x).reduce().into_loose();
                    value.montgomery_limbs()[3]
                },
                {
                    let value: $field = ($y).reduce().into_loose();
                    value.montgomery_limbs()[0]
                },
                {
                    let value: $field = ($y).reduce().into_loose();
                    value.montgomery_limbs()[1]
                },
                {
                    let value: $field = ($y).reduce().into_loose();
                    value.montgomery_limbs()[2]
                },
                {
                    let value: $field = ($y).reduce().into_loose();
                    value.montgomery_limbs()[3]
                },
            >()
        }
    };
}
