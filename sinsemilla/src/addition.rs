use core::ops::Add;

use group::{cofactor::CofactorCurveAffine, Group};
use pasta_curves::{
    arithmetic::{CurveAffine, CurveExt},
    pallas,
};
use subtle::{ConstantTimeEq, CtOption};

/// P ∪ {⊥}
///
/// Simulated incomplete addition built over complete addition.
#[derive(Clone, Copy, Debug)]
pub(super) struct IncompletePoint(CtOption<pallas::Point>);

impl From<pallas::Point> for IncompletePoint {
    fn from(p: pallas::Point) -> Self {
        IncompletePoint(CtOption::new(p, 1.into()))
    }
}

impl From<IncompletePoint> for CtOption<pallas::Point> {
    fn from(p: IncompletePoint) -> Self {
        p.0
    }
}

impl IncompletePoint {
    /// Computes `(self ⸭ rhs) ⸭ self` with the same incomplete-addition
    /// failure conditions as the two separate additions.
    ///
    /// Writing `P = self` and `S = rhs`, the first addition of nonidentity
    /// points fails exactly when `x(P) = x(S)`, which on Pallas means
    /// `P = ±S`. With `T = P + S`, `T = O` iff `P = -S` and `T = P` iff
    /// `S = O`, both already excluded. The remaining failure `T = -P` is
    /// equivalent to `2P + S = O`.
    pub(super) fn double_and_add(self, rhs: pallas::Affine) -> Self {
        IncompletePoint(self.0.and_then(|p| {
            let (p_x, _, p_z) = p.jacobian_coordinates();
            let rhs_coordinates = rhs.coordinates();
            let rhs_is_identity = !rhs_coordinates.is_some();
            let rhs_x = rhs_coordinates
                .map(|coordinates| *coordinates.x())
                .unwrap_or(pallas::Base::zero());

            // The affine x-coordinate of p is p_x / p_z². Cross-multiply
            // instead of normalizing p, which would require an inversion.
            let same_x = p_x.ct_eq(&(rhs_x * p_z.square()));
            let doubled = p.double();
            let result = doubled + rhs;

            CtOption::new(
                result,
                !(p.is_identity() | rhs_is_identity | same_x | result.is_identity()),
            )
        }))
    }
}

impl Add for IncompletePoint {
    type Output = IncompletePoint;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn add(self, rhs: Self) -> Self::Output {
        // ⊥ ⸭ ⊥ = ⊥
        // ⊥ ⸭ P = ⊥
        IncompletePoint(self.0.and_then(|p| {
            // P ⸭ ⊥ = ⊥
            rhs.0.and_then(|q| {
                // 0 ⸭ 0 = ⊥
                // 0 ⸭ P = ⊥
                // P ⸭ 0 = ⊥
                // (x, y) ⸭ (x', y') = ⊥ if x == x'
                // (x, y) ⸭ (x', y') = (x, y) + (x', y') if x != x'
                CtOption::new(
                    p + q,
                    !(p.is_identity() | q.is_identity() | p.ct_eq(&q) | p.ct_eq(&-q)),
                )
            })
        }))
    }
}

impl Add<pallas::Affine> for IncompletePoint {
    type Output = IncompletePoint;

    /// Specialisation of incomplete addition for mixed addition.
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn add(self, rhs: pallas::Affine) -> Self::Output {
        // ⊥ ⸭ ⊥ = ⊥
        // ⊥ ⸭ P = ⊥
        IncompletePoint(self.0.and_then(|p| {
            // P ⸭ ⊥ = ⊥ is satisfied by definition.
            let q = rhs.to_curve();

            // 0 ⸭ 0 = ⊥
            // 0 ⸭ P = ⊥
            // P ⸭ 0 = ⊥
            // (x, y) ⸭ (x', y') = ⊥ if x == x'
            // (x, y) ⸭ (x', y') = (x, y) + (x', y') if x != x'
            CtOption::new(
                // Use mixed addition for efficiency.
                p + rhs,
                !(p.is_identity() | q.is_identity() | p.ct_eq(&q) | p.ct_eq(&-q)),
            )
        }))
    }
}

#[cfg(test)]
mod tests {
    use group::{Curve, Group};
    use pasta_curves::pallas;
    use subtle::CtOption;

    use super::IncompletePoint;

    fn point(scalar: u64) -> pallas::Point {
        pallas::Point::generator() * pallas::Scalar::from(scalar)
    }

    fn assert_matches_two_additions(p: IncompletePoint, q: pallas::Affine, expected_valid: bool) {
        let expected: CtOption<pallas::Point> = ((p + q) + p).into();
        let actual: CtOption<pallas::Point> = p.double_and_add(q).into();

        let expected_is_some = bool::from(expected.is_some());
        let actual_is_some = bool::from(actual.is_some());
        assert_eq!(expected_is_some, expected_valid);
        assert_eq!(actual_is_some, expected_is_some);

        if expected_is_some {
            assert_eq!(actual.unwrap(), expected.unwrap());
        }
    }

    #[test]
    fn double_and_add_preserves_exceptional_cases() {
        let identity = pallas::Point::identity();
        let p = point(3);
        let q = point(7);

        assert_matches_two_additions(IncompletePoint::from(identity), q.to_affine(), false);
        assert_matches_two_additions(IncompletePoint::from(p), identity.to_affine(), false);
        assert_matches_two_additions(IncompletePoint::from(p), p.to_affine(), false);
        assert_matches_two_additions(IncompletePoint::from(p), (-p).to_affine(), false);
        assert_matches_two_additions(IncompletePoint::from(p), (-p.double()).to_affine(), false);

        // Complete mixed addition has its doubling exception here, but both
        // incomplete additions are valid.
        assert_matches_two_additions(IncompletePoint::from(p), p.double().to_affine(), true);
        assert_matches_two_additions(IncompletePoint::from(p), q.to_affine(), true);

        let invalid = IncompletePoint::from(p) + p.to_affine();
        assert_matches_two_additions(invalid, q.to_affine(), false);
    }

    #[test]
    fn double_and_add_matches_two_additions_for_small_multiples() {
        const MULTIPLES: u64 = 32;

        for p_scalar in 0..MULTIPLES {
            let p = IncompletePoint::from(point(p_scalar));
            for q_scalar in 0..MULTIPLES {
                let q = point(q_scalar).to_affine();
                let expected: CtOption<pallas::Point> = ((p + q) + p).into();
                let expected_valid = bool::from(expected.is_some());
                assert_matches_two_additions(p, q, expected_valid);
            }
        }
    }
}
