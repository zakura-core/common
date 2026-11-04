//! Native Pallas arithmetic for protocol consumers, without `ff` or `group`.
//!
//! Projective operations preserve their denominators until explicit normalization.
//! Arithmetic is variable-time, as are the underlying Udon operations.
use super::{Fp, Fq, PallasPoint};
use alloc::{vec, vec::Vec};
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

/// The Pallas base field.
pub type Base = Fp;
/// The Pallas scalar field.
pub type Scalar = Fq;
/// An affine point, including identity.
pub type Affine = PallasPoint;

/// A native Pallas point in projective coordinates, including identity.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Point(pub(crate) udon::curve::PallasProjective);

/// Affine coordinates of a nonidentity Pallas point.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Coordinates {
    x: Fp,
    y: Fp,
}
impl Coordinates {
    /// Returns the x coordinate.
    pub fn x(&self) -> &Fp {
        &self.x
    }
    /// Returns the y coordinate.
    pub fn y(&self) -> &Fp {
        &self.y
    }
}
impl ConditionallySelectable for Coordinates {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            x: Fp::conditional_select(&a.x, &b.x, choice),
            y: Fp::conditional_select(&a.y, &b.y, choice),
        }
    }
}
impl Default for Affine {
    fn default() -> Self {
        Self::identity()
    }
}
impl Affine {
    /// The identity point.
    pub const fn identity() -> Self {
        Self::from_native(udon::curve::PallasPoint::IDENTITY)
    }
    /// The generator `(-1, 2)`.
    pub const fn generator() -> Self {
        Self::from_native(udon::curve::PallasPoint::GENERATOR)
    }
    /// Returns whether this point is identity.
    pub fn is_identity(&self) -> Choice {
        Choice::from(self.native().is_identity() as u8)
    }
    /// Checks affine coordinates; `(0, 0)` represents identity.
    pub fn from_xy(x: Fp, y: Fp) -> CtOption<Self> {
        let point = udon::curve::PallasPoint::from_xy(x.native().reduce(), y.native().reduce());
        CtOption::new(
            Self::from_native(point.unwrap_or(udon::curve::PallasPoint::IDENTITY)),
            Choice::from(point.is_some() as u8),
        )
    }
    /// Returns coordinates, or none for identity.
    pub fn coordinates(&self) -> CtOption<Coordinates> {
        let coordinates = self.native().coordinates().map(|(x, y)| Coordinates {
            x: Fp::from_native(x.into_loose()),
            y: Fp::from_native(y.into_loose()),
        });
        CtOption::new(
            coordinates.unwrap_or_default(),
            Choice::from(coordinates.is_some() as u8),
        )
    }
    /// Returns affine coordinates, using `(0, 0)` for identity.
    pub fn raw_coordinates(&self) -> (Fp, Fp) {
        match self.native().coordinates() {
            Some((x, y)) => (
                Fp::from_native(x.into_loose()),
                Fp::from_native(y.into_loose()),
            ),
            None => (Fp::ZERO, Fp::ZERO),
        }
    }
    /// Lifts the point to projective coordinates without inversion.
    pub const fn to_curve(&self) -> Point {
        Point(self.native().to_projective())
    }
}
impl Point {
    /// Returns the protocol's domain-separated Pallas hash-to-curve map.
    pub fn hash_to_curve(domain: &str) -> impl Fn(&[u8]) -> Self + '_ {
        move |message| super::hash_to_curve::hash(domain, message)
    }

    /// The identity point.
    pub const fn identity() -> Self {
        Self(udon::curve::PallasProjective::IDENTITY)
    }
    /// The generator `(-1, 2)`.
    pub const fn generator() -> Self {
        Self(udon::curve::PallasProjective::GENERATOR)
    }
    /// Wraps a validated native projective point without normalization.
    pub const fn from_native(point: udon::curve::PallasProjective) -> Self {
        Self(point)
    }
    /// Returns the native projective point without normalization.
    pub const fn native(self) -> udon::curve::PallasProjective {
        self.0
    }
    /// Returns whether this point is identity.
    pub fn is_identity(&self) -> Choice {
        Choice::from(self.0.is_identity() as u8)
    }
    /// Returns twice this point without normalization.
    pub fn double(&self) -> Self {
        Self(self.0.double())
    }
    /// Normalizes this point to affine coordinates.
    pub fn to_affine(&self) -> Affine {
        Affine::from_native(self.0.to_point())
    }
    /// Returns the canonical compressed encoding, normalizing as needed.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.to_point().to_bytes()
    }
    /// Decodes a canonical compressed point, including identity.
    ///
    /// Uses [`PallasPoint::from_bytes`]'s validation, returning an empty
    /// [`CtOption`] on rejection.
    pub fn from_bytes(bytes: &[u8; 32]) -> CtOption<Self> {
        let point = udon::curve::PallasPoint::from_bytes(*bytes);
        CtOption::new(
            Self(
                point
                    .unwrap_or(udon::curve::PallasPoint::IDENTITY)
                    .to_projective(),
            ),
            Choice::from(point.is_some() as u8),
        )
    }
    /// Samples an affine x coordinate and a sign, retrying nonsquares.
    ///
    /// This retains the historical Orchard dummy-point distribution and RNG
    /// schedule, including the sign draw on unsuccessful candidates.
    pub fn random(mut rng: impl rand::Rng) -> Self {
        loop {
            let x = Base::random(&mut rng);
            let sign = (rng.next_u32() & 1) as u8;
            // Pallas has equation y² = x³ + 5.
            if let Some(y) = Option::<Base>::from((x.square() * x + Base::from(5)).sqrt()) {
                let y = if y.is_odd().unwrap_u8() == sign {
                    y
                } else {
                    -y
                };
                return Affine::from_xy(x, y).unwrap().to_curve();
            }
        }
    }
    /// Returns the Jacobian coordinates without an inversion.
    pub fn jacobian_coordinates(&self) -> (Fp, Fp, Fp) {
        let (x, y, z) = self.0.coordinates();
        (
            Fp::from_native(*x),
            Fp::from_native(*y),
            Fp::from_native(*z),
        )
    }
    /// Checks Jacobian coordinates without normalizing them.
    pub fn new_jacobian(x: Fp, y: Fp, z: Fp) -> CtOption<Self> {
        let point =
            udon::curve::PallasProjective::from_jacobian(x.native(), y.native(), z.native());
        CtOption::new(
            Self(point.unwrap_or(udon::curve::PallasProjective::IDENTITY)),
            Choice::from(point.is_some() as u8),
        )
    }
    /// Normalizes all points with a shared inversion, preserving identity positions.
    ///
    /// Writes one affine point per input, in the same order.
    ///
    /// # Panics
    ///
    /// Panics before writing `output` if its length differs from `points.len()`.
    pub fn batch_normalize(points: &[Self], output: &mut [Affine]) {
        assert_eq!(points.len(), output.len());
        let points: Vec<_> = points.iter().map(|p| p.0).collect();
        let mut normalized = vec![udon::curve::PallasPoint::IDENTITY; points.len()];
        udon::curve::batch_normalize(
            &points,
            &mut normalized,
            &mut vec![udon::field::Fp::ZERO; points.len()],
        );
        for (out, point) in output.iter_mut().zip(normalized) {
            *out = Affine::from_native(point);
        }
    }
}
impl From<Affine> for Point {
    fn from(point: Affine) -> Self {
        point.to_curve()
    }
}
impl From<Point> for Affine {
    fn from(point: Point) -> Self {
        point.to_affine()
    }
}
impl ConditionallySelectable for Point {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self(a.0.select(&b.0, bool::from(choice)))
    }
}
impl ConstantTimeEq for Point {
    fn ct_eq(&self, rhs: &Self) -> Choice {
        let (x1, y1, z1) = self.jacobian_coordinates();
        let (x2, y2, z2) = rhs.jacobian_coordinates();
        let z1_zero = z1.ct_eq(&Fp::ZERO);
        let z2_zero = z2.ct_eq(&Fp::ZERO);
        let z1s = z1.square();
        let z2s = z2.square();
        (z1_zero & z2_zero)
            | (!z1_zero
                & !z2_zero
                & (x1 * z2s).ct_eq(&(x2 * z1s))
                & (y1 * z2s * z2).ct_eq(&(y2 * z1s * z1)))
    }
}
impl Neg for Point {
    type Output = Self;
    fn neg(self) -> Self {
        Self(self.0.neg())
    }
}
impl Neg for &Point {
    type Output = Point;
    fn neg(self) -> Point {
        -*self
    }
}
impl Neg for Affine {
    type Output = Self;
    fn neg(self) -> Self {
        Self::from_native(self.native().neg())
    }
}

macro_rules! point_op {
    ($trait:ident, $op:ident, $assign:ident, $assign_op:ident, $rhs:ty, $body:expr) => {
        impl $trait<$rhs> for Point {
            type Output = Point;
            fn $op(self, rhs: $rhs) -> Point {
                ($body)(self, rhs)
            }
        }
        impl $trait<&$rhs> for Point {
            type Output = Point;
            fn $op(self, rhs: &$rhs) -> Point {
                self.$op(*rhs)
            }
        }
        impl $trait<$rhs> for &Point {
            type Output = Point;
            fn $op(self, rhs: $rhs) -> Point {
                (*self).$op(rhs)
            }
        }
        impl $trait<&$rhs> for &Point {
            type Output = Point;
            fn $op(self, rhs: &$rhs) -> Point {
                (*self).$op(*rhs)
            }
        }
        impl $assign<$rhs> for Point {
            fn $assign_op(&mut self, rhs: $rhs) {
                *self = self.$op(rhs);
            }
        }
        impl $assign<&$rhs> for Point {
            fn $assign_op(&mut self, rhs: &$rhs) {
                *self = self.$op(*rhs);
            }
        }
    };
}
point_op!(
    Add,
    add,
    AddAssign,
    add_assign,
    Point,
    |a: Point, b: Point| Point(a.0.add(&b.0))
);
point_op!(
    Sub,
    sub,
    SubAssign,
    sub_assign,
    Point,
    |a: Point, b: Point| Point(a.0.sub(&b.0))
);
point_op!(
    Add,
    add,
    AddAssign,
    add_assign,
    Affine,
    |a: Point, b: Affine| {
        match b.native().as_affine() {
            Some(b) => Point(a.0.add_mixed(b)),
            None => a,
        }
    }
);
point_op!(
    Sub,
    sub,
    SubAssign,
    sub_assign,
    Affine,
    |a: Point, b: Affine| a + (-b)
);
point_op!(
    Mul,
    mul,
    MulAssign,
    mul_assign,
    Scalar,
    |a: Point, b: Scalar| Point(a.0.mul(&b.native()))
);
impl Mul<Scalar> for Affine {
    type Output = Point;
    fn mul(self, scalar: Scalar) -> Point {
        Point(self.native().mul_projective(&scalar.native()))
    }
}
impl Mul<&Scalar> for Affine {
    type Output = Point;
    fn mul(self, scalar: &Scalar) -> Point {
        self * *scalar
    }
}
impl core::iter::Sum for Point {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::identity(), |a, b| a + b)
    }
}
impl<'a> core::iter::Sum<&'a Self> for Point {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.copied().sum()
    }
}

// Keep the two independent lanes together so the arithmetic backend can overlap
// their multiplication chains. Weighted Sinsemilla establishes nonexceptional
// inputs, while these complete kernels retain correct behavior for all points.
pub(super) fn add_mixed_pair(a: &Point, b: &Affine, c: &Point, d: &Affine) -> [Point; 2] {
    match (b.native().as_affine(), d.native().as_affine()) {
        (Some(b), Some(d)) => {
            udon::curve::PallasProjective::add_mixed_pair(&a.0, b, &c.0, d).map(Point)
        }
        _ => [*a + *b, *c + *d],
    }
}

/// Normalizes a stream of projective points with one shared inversion.
/// Invalid positions are filtered and restored by the protocol caller.
pub fn normalize_batch(points: impl IntoIterator<Item = Point>) -> Vec<Affine> {
    let points: Vec<_> = points.into_iter().map(Point::native).collect();
    let mut normalized = vec![udon::curve::PallasPoint::IDENTITY; points.len()];
    udon::curve::batch_normalize(
        &points,
        &mut normalized,
        &mut vec![udon::field::Fp::ZERO; points.len()],
    );
    normalized.into_iter().map(Affine::from_native).collect()
}
