//! Jacobian formulas specialized to the Pasta equation's zero linear term.

use core::{fmt, marker::PhantomData};

use super::{AffinePoint, IncompleteDoubleAndAdd, PastaCurve, Point, ProjectivePoint};
use crate::field::{CanonicalUint, PastaField};

impl<C: PastaCurve> fmt::Debug for ProjectivePoint<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ProjectivePoint")
            .field("x", &self.x)
            .field("y", &self.y)
            .field("z", &self.z)
            .finish()
    }
}

impl<C: PastaCurve> Default for ProjectivePoint<C> {
    fn default() -> Self {
        Self::IDENTITY
    }
}

impl<C: PastaCurve> PartialEq for ProjectivePoint<C> {
    fn eq(&self, rhs: &Self) -> bool {
        if self.is_identity() || rhs.is_identity() {
            return self.is_identity() == rhs.is_identity();
        }
        // Cross-multiplication compares affine x and y without dividing by z.
        let z1_squared = self.z.square();
        let z2_squared = rhs.z.square();
        self.x.mul(&z2_squared).reduce() == rhs.x.mul(&z1_squared).reduce()
            && self.y.mul(&z2_squared).mul(&rhs.z).reduce()
                == rhs.y.mul(&z1_squared).mul(&self.z).reduce()
    }
}

impl<C: PastaCurve> Eq for ProjectivePoint<C> {}

impl<C: PastaCurve> ProjectivePoint<C> {
    /// The additive identity, represented by zero coordinates.
    pub const IDENTITY: Self = Self {
        x: PastaField::ZERO,
        y: PastaField::ZERO,
        z: PastaField::ZERO,
        marker: PhantomData,
    };
    /// The generator `(-1, 2)` with `z = 1`.
    pub const GENERATOR: Self = AffinePoint::GENERATOR.to_projective();

    /// Lifts a nonidentity affine point with `z = 1`.
    pub const fn from_affine(point: &AffinePoint<C>) -> Self {
        Self {
            x: point.x.into_loose(),
            y: point.y.into_loose(),
            z: PastaField::ONE,
            marker: PhantomData,
        }
    }

    /// Lifts an affine point, preserving identity.
    pub const fn from_point(point: &Point<C>) -> Self {
        match point.as_affine() {
            Some(point) => Self::from_affine(point),
            None => Self::IDENTITY,
        }
    }

    /// Returns whether `z = 0`.
    pub const fn is_identity(&self) -> bool {
        self.z.is_zero()
    }

    /// Selects `other` when `choice` is true, preserving the complete projective
    /// representation without normalization or encoding. All coordinates use
    /// the same mask, so the result inherits the selected point's invariants.
    pub fn select(&self, other: &Self, choice: bool) -> Self {
        let mask = u64::from(choice).wrapping_neg();
        let select = |a: &PastaField<C::Base>, b: &PastaField<C::Base>| {
            let a = a.montgomery_limbs();
            let b = b.montgomery_limbs();
            PastaField::from_montgomery_limbs(core::array::from_fn(|i| {
                a[i] ^ ((a[i] ^ b[i]) & mask)
            }))
        };
        Self {
            x: select(&self.x, &other.x),
            y: select(&self.y, &other.y),
            z: select(&self.z, &other.z),
            marker: PhantomData,
        }
    }

    /// Checks a Jacobian representation without normalizing it.
    ///
    /// Nonidentity inputs must satisfy `y² = x³ + 5z⁶`. A zero `z` denotes
    /// identity and is canonicalized to [`Self::IDENTITY`]. This permits
    /// protocol maps to hand off projective results without an inversion.
    pub fn from_jacobian(
        x: PastaField<C::Base>,
        y: PastaField<C::Base>,
        z: PastaField<C::Base>,
    ) -> Option<Self> {
        if z.is_zero() {
            return Some(Self::IDENTITY);
        }
        let z2 = z.square();
        let z6 = z2.square().mul(&z2);
        let rhs = x.square().mul(&x).add(&z6.mul_by_4().add(&z6));
        (y.square().reduce() == rhs.reduce()).then_some(Self {
            x,
            y,
            z,
            marker: PhantomData,
        })
    }

    /// Borrows the Jacobian coordinates `(x, y, z)`.
    #[expect(
        clippy::type_complexity,
        reason = "Expose coordinates in Jacobian order."
    )]
    pub const fn coordinates(
        &self,
    ) -> (
        &PastaField<C::Base>,
        &PastaField<C::Base>,
        &PastaField<C::Base>,
    ) {
        (&self.x, &self.y, &self.z)
    }

    /// Recovers affine coordinates, inverting only when `z` is neither zero nor one.
    ///
    /// Identity maps to [`Point::IDENTITY`]; `z = 1` only reduces the coordinates.
    /// Use [`super::batch_normalize`] to share the inversion across a slice.
    pub fn to_point(&self) -> Point<C> {
        if self.z.is_one() {
            return AffinePoint {
                x: self.x.reduce(),
                y: self.y.reduce(),
                marker: PhantomData,
            }
            .to_point();
        }
        match self.z.invert() {
            Some(inverse) => self.normalize_with_inverse(&inverse).to_point(),
            None => Point::IDENTITY,
        }
    }

    // Callers establish z != 0 and supply z^-1; this helper cannot represent
    // identity. The squared and cubed inverse undo Jacobian scaling.
    pub(super) fn normalize_with_inverse(&self, inverse: &PastaField<C::Base>) -> AffinePoint<C> {
        let squared = inverse.square();
        AffinePoint {
            x: self.x.mul(&squared).reduce(),
            y: self.y.mul(&squared).mul(inverse).reduce(),
            marker: PhantomData,
        }
    }

    /// Applies [`AffinePoint::endomorphism`] in projective coordinates.
    ///
    /// Multiplies `x` by the coordinate field's [`PastaField::ZETA`] value,
    /// leaving `y` and `z` unchanged. Preserves identity and projective scaling.
    pub fn endomorphism(&self) -> Self {
        Self {
            x: self.x.mul(&PastaField::<C::Base>::ZETA),
            ..*self
        }
    }

    /// Returns the additive inverse `(x, -y, z)`.
    pub fn neg(&self) -> Self {
        Self {
            y: self.y.neg(),
            ..*self
        }
    }

    /// Returns `2 * self`, without inversion.
    pub fn double(&self) -> Self {
        if self.is_identity() {
            return Self::IDENTITY;
        }
        // For y^2 = x^3 + 5, use tangent numerator (3/2)*x^2 and z' = y*z.
        // Scaling this output by (4, 8, 2) gives the usual Jacobian doubling
        // coordinates, so omitting those factors preserves the affine point.
        let b = self.y.square();
        let c = b.square();
        let d = self.x.mul(&b);
        let e = self.x.square().triple().half();
        let f = e.square();
        let z = self.z.mul(&self.y);
        let x = f.sub(&d.double());
        let y = e.mul_sub(&d.sub(&x), &c);
        Self {
            x,
            y,
            z,
            marker: PhantomData,
        }
    }

    /// Computes `A + (A + B)` and both addition slopes without inversion.
    ///
    /// Here `A = self` and `B = rhs`.
    ///
    /// Returns `None` if `A` is identity, or if either addition has equal
    /// affine x-coordinates. These are incomplete additions: equal points
    /// are rejected as well as inverse pairs. A successful result is
    /// nonidentity.
    ///
    /// The result's [`slope_numerators`](IncompleteDoubleAndAdd::slope_numerators)
    /// share the output point's Jacobian `z` as denominator. One inverse of `z`
    /// suffices to recover both slopes and the point's affine coordinates.
    ///
    /// ```
    /// use zakura_udon::{curve::PallasAffine, field::Fq};
    ///
    /// let base = PallasAffine::GENERATOR;
    /// let a = base.to_projective().double();
    /// let step = a.incomplete_double_and_add(&base).unwrap();
    /// assert_eq!(step.point, base.mul_projective(&Fq::from_u64(5)));
    /// assert!(base.to_projective().incomplete_double_and_add(&base).is_none());
    ///
    /// let inverse = step.point.coordinates().2.invert().unwrap();
    /// let slopes = step.slope_numerators.map(|numerator| numerator.mul(&inverse));
    /// let affine_a = a.to_point();
    /// let (ax, ay) = affine_a.coordinates().unwrap();
    /// let intermediate = a.add_mixed(&base).to_point();
    /// for (other, slope) in [base.to_point(), intermediate].iter().zip(slopes) {
    ///     let (x, y) = other.coordinates().unwrap();
    ///     assert_eq!(slope.mul(&x.sub(ax)).reduce(), y.sub(ay).reduce());
    /// }
    /// ```
    pub fn incomplete_double_and_add(
        &self,
        rhs: &AffinePoint<C>,
    ) -> Option<IncompleteDoubleAndAdd<C>> {
        let z_squared = self.z.square();
        let z_cubed = z_squared.mul(&self.z);
        let h = rhs.x.mul_sub(&z_squared, &self.x);
        let r = rhs.y.mul_sub(&z_cubed, &self.y);
        let h_squared = h.square();
        let h_cubed = h_squared.mul(&h);
        let x_h_squared = self.x.mul(&h_squared);
        // R = A + B has x numerator x_r and Jacobian denominator z*h.
        let x_r = r.square().sub(&h_cubed).sub(&x_h_squared.double());
        let d = x_h_squared.sub(&x_r);
        // In affine coordinates, A.x - R.x = d / (self.z*h)^2. The product
        // self.z*h*d therefore vanishes exactly for identity A or equal
        // x-coordinates in either addition.
        let z = self.z.mul(&h).mul(&d);
        if z.is_zero() {
            return None;
        }
        let d_squared = d.square();
        let d_cubed = d_squared.mul(&d);
        let y_h_cubed = self.y.mul(&h_cubed);
        let r_d = r.mul(&d);
        // R's y numerator is r*d - self.y*h^3, so dividing A.y - R.y by
        // A.x - R.x gives (2*self.y*h^3 - r*d) / (self.z*h*d). The first
        // slope r/(self.z*h) uses r*d over that same output z.
        let lambda_2_numerator = y_h_cubed.double().sub(&r_d);
        let x_h_squared_d_squared = x_h_squared.mul(&d_squared);
        let x = lambda_2_numerator
            .square()
            .sub(&x_h_squared_d_squared.double())
            .add(&d_cubed);
        let y = lambda_2_numerator.mul_sub_product(
            &x_h_squared_d_squared.sub(&x),
            &y_h_cubed,
            &d_cubed,
        );
        Some(IncompleteDoubleAndAdd {
            point: Self {
                x,
                y,
                z,
                marker: PhantomData,
            },
            slope_numerators: [r_d, lambda_2_numerator],
        })
    }

    /// Returns `self + rhs`, handling identity, equal points, and inverse pairs
    /// without inversion.
    pub fn add(&self, rhs: &Self) -> Self {
        if self.is_identity() {
            return *rhs;
        }
        if rhs.is_identity() {
            return *self;
        }
        let z1_squared = self.z.square();
        let z2_squared = rhs.z.square();
        let u1 = self.x.mul(&z2_squared);
        let u2 = rhs.x.mul(&z1_squared);
        let s1 = self.y.mul(&z2_squared).mul(&rhs.z);
        let s2 = rhs.y.mul(&z1_squared).mul(&self.z);
        // u1/u2 and s1/s2 use the common scale z1*z2. Equal x coordinates
        // require doubling or identity; the addition formula needs h != 0.
        if u1.reduce() == u2.reduce() {
            return if s1.reduce() == s2.reduce() {
                self.double()
            } else {
                Self::IDENTITY
            };
        }
        let h = u2.sub(&u1);
        // Unscaled differences give z' = z1*z2*h. The common doubled-difference
        // formula scales this output by (4, 8, 2), preserving the affine point.
        let i = h.square();
        let j = h.mul(&i);
        let r = s2.sub(&s1);
        let v = u1.mul(&i);
        let x = r.square().sub(&j).sub(&v.double());
        let y = r.mul_sub_product(&v.sub(&x), &s1, &j);
        let z = self.z.mul(&rhs.z).mul(&h);
        Self {
            x,
            y,
            z,
            marker: PhantomData,
        }
    }

    /// Adds a nonidentity affine point without inversion.
    ///
    /// Handles identity, equal points, and inverse pairs.
    pub fn add_mixed(&self, rhs: &AffinePoint<C>) -> Self {
        if self.is_identity() {
            return Self::from_affine(rhs);
        }
        let z1_squared = self.z.square();
        let u2 = rhs.x.mul(&z1_squared);
        let s2 = rhs.y.mul(&z1_squared).mul(&self.z);
        // This is the general addition formula with the affine operand's z = 1.
        if self.x.reduce() == u2.reduce() {
            return if self.y.reduce() == s2.reduce() {
                self.double()
            } else {
                Self::IDENTITY
            };
        }
        let h = u2.sub(&self.x);
        // The unscaled formula in add specializes to z2 = 1 here.
        let i = h.square();
        let j = h.mul(&i);
        let r = s2.sub(&self.y);
        let v = self.x.mul(&i);
        let x = r.square().sub(&j).sub(&v.double());
        let y = r.mul_sub_product(&v.sub(&x), &self.y, &j);
        let z = self.z.mul(&h);
        Self {
            x,
            y,
            z,
            marker: PhantomData,
        }
    }

    /// Returns `self - rhs`, without inversion.
    pub fn sub(&self, rhs: &Self) -> Self {
        self.add(&rhs.neg())
    }

    /// Multiplies by a scalar without inversion.
    ///
    /// Processes the full canonical scalar; zero returns identity. The scalar
    /// may use either reduced or loose residues. Execution is variable-time and
    /// uses bounded internal stack storage, with no caller table, scratch, or
    /// allocation.
    ///
    /// Use [`EisensteinTable`](super::EisensteinTable) or
    /// [`FixedBaseTable`](super::FixedBaseTable) to retain preparation for repeated
    /// multiplication of the same base.
    pub fn mul(&self, scalar: &PastaField<C::Scalar>) -> Self {
        if self.is_identity() || scalar.is_zero() {
            return Self::IDENTITY;
        }
        // Short scalars use the binary ladder without paying for table setup.
        let scalar = scalar.to_canonical_uint();
        if scalar.highest_set_bit().is_some_and(|high| high < 64) {
            multiply_canonical(scalar, |point| point.add(self))
        } else {
            super::effective::multiply(self, scalar)
        }
    }
}

/// Multiplies a fixed base by an unsigned integer with a binary ladder.
///
/// Each `add_base` call must add the same base to the supplied point.
pub(super) fn multiply_canonical<C: PastaCurve>(
    scalar: CanonicalUint,
    add_base: impl Fn(&ProjectivePoint<C>) -> ProjectivePoint<C>,
) -> ProjectivePoint<C> {
    let mut result = ProjectivePoint::IDENTITY;
    if let Some(high) = scalar.highest_set_bit() {
        for bit in (0..=high).rev() {
            result = result.double();
            if scalar.bit(bit).unwrap() {
                result = add_base(&result);
            }
        }
    }
    result
}
