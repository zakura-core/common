//! [`PastaCurve`] adapters for Pallas and Vesta.

use ff::{PrimeField, WithSmallOrderMulGroup};
use pasta_curves::arithmetic::{CurveAffine, CurveExt, fp_montgomery_limbs, fq_montgomery_limbs};
use pasta_curves::glv::accelerator::split_scalar_vartime;
use pasta_curves::{Fp, Fq, pallas, vesta};

use crate::curve::{Affine, Jacobian};
use crate::field::{Field, Limbs, PALLAS_BASE, VESTA_BASE, to_bytes};
use crate::pipeline::PastaCurve;

/// The Pallas curve (base field $\mathbb{F}_p$, scalar field $\mathbb{F}_q$).
#[derive(Debug, Clone, Copy)]
pub struct Pallas;

/// The Vesta curve (base field $\mathbb{F}_q$, scalar field $\mathbb{F}_p$).
#[derive(Debug, Clone, Copy)]
pub struct Vesta;

fn fp_limbs(value: &Fp) -> Limbs {
    PALLAS_BASE.from_pasta(&fp_montgomery_limbs(value))
}

fn fq_limbs(value: &Fq) -> Limbs {
    VESTA_BASE.from_pasta(&fq_montgomery_limbs(value))
}

impl PastaCurve for Pallas {
    type Scalar = pallas::Scalar;
    type Affine = pallas::Affine;
    type Point = pallas::Point;

    const FIELD: Field = PALLAS_BASE;
    const NAME: &'static str = "pallas";

    fn zeta() -> Limbs {
        fp_limbs(&Fp::ZETA)
    }

    fn affine(point: &Self::Affine) -> Affine {
        // `coordinates` is `None` exactly for the identity.
        match Option::from(point.coordinates()) {
            Some(coordinates) => {
                let coordinates: pasta_curves::arithmetic::Coordinates<pallas::Affine> =
                    coordinates;
                Affine {
                    x: fp_limbs(coordinates.x()),
                    y: fp_limbs(coordinates.y()),
                }
            }
            None => Affine::IDENTITY,
        }
    }

    fn split(scalar: &Self::Scalar) -> ((bool, u128), (bool, u128)) {
        split_scalar_vartime::<pallas::Point>(scalar)
    }

    fn point(jacobian: &Jacobian) -> Option<Self::Point> {
        let field = &Self::FIELD;
        let coordinate =
            |limbs: &Limbs| Option::from(Fp::from_repr(to_bytes(&field.to_canonical(limbs))));
        let (x, y, z) = (
            coordinate(&jacobian.x)?,
            coordinate(&jacobian.y)?,
            coordinate(&jacobian.z)?,
        );
        Option::from(pallas::Point::new_jacobian(x, y, z))
    }
}

impl PastaCurve for Vesta {
    type Scalar = vesta::Scalar;
    type Affine = vesta::Affine;
    type Point = vesta::Point;

    const FIELD: Field = VESTA_BASE;
    const NAME: &'static str = "vesta";

    fn zeta() -> Limbs {
        fq_limbs(&Fq::ZETA)
    }

    fn affine(point: &Self::Affine) -> Affine {
        match Option::from(point.coordinates()) {
            Some(coordinates) => {
                let coordinates: pasta_curves::arithmetic::Coordinates<vesta::Affine> = coordinates;
                Affine {
                    x: fq_limbs(coordinates.x()),
                    y: fq_limbs(coordinates.y()),
                }
            }
            None => Affine::IDENTITY,
        }
    }

    fn split(scalar: &Self::Scalar) -> ((bool, u128), (bool, u128)) {
        split_scalar_vartime::<vesta::Point>(scalar)
    }

    fn point(jacobian: &Jacobian) -> Option<Self::Point> {
        let field = &Self::FIELD;
        let coordinate =
            |limbs: &Limbs| Option::from(Fq::from_repr(to_bytes(&field.to_canonical(limbs))));
        let (x, y, z) = (
            coordinate(&jacobian.x)?,
            coordinate(&jacobian.y)?,
            coordinate(&jacobian.z)?,
        );
        Option::from(vesta::Point::new_jacobian(x, y, z))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use group::{Curve, Group};

    #[test]
    fn zeta_matches_the_endomorphism() {
        let p = pallas::Point::generator() * pallas::Scalar::from(12345u64);
        let affine = Pallas::affine(&p.to_affine());
        let rotated = Affine {
            x: PALLAS_BASE.mul(&affine.x, &Pallas::zeta()),
            y: affine.y,
        };
        let expected = Pallas::affine(&p.endo().to_affine());
        assert_eq!(rotated, expected);

        let p = vesta::Point::generator() * vesta::Scalar::from(54321u64);
        let affine = Vesta::affine(&p.to_affine());
        let rotated = Affine {
            x: VESTA_BASE.mul(&affine.x, &Vesta::zeta()),
            y: affine.y,
        };
        assert_eq!(rotated, Vesta::affine(&p.endo().to_affine()));
    }

    #[test]
    fn points_round_trip() {
        let p = pallas::Point::generator() * pallas::Scalar::from(99u64);
        let jacobian = Pallas::affine(&p.to_affine()).to_jacobian(&PALLAS_BASE);
        assert_eq!(Pallas::point(&jacobian), Some(p));
        assert_eq!(
            Pallas::point(&Jacobian::IDENTITY),
            Some(pallas::Point::identity())
        );
        // A coordinate at or above the modulus is rejected.
        let mut bad = jacobian;
        bad.x = PALLAS_BASE.modulus;
        assert_eq!(Pallas::point(&bad), None);
        // An off-curve point is rejected.
        let mut bad = jacobian;
        bad.y = PALLAS_BASE.add(&bad.y, &PALLAS_BASE.one);
        assert_eq!(Pallas::point(&bad), None);

        let p = vesta::Point::generator() * vesta::Scalar::from(7u64);
        let jacobian = Vesta::affine(&p.to_affine()).to_jacobian(&VESTA_BASE);
        assert_eq!(Vesta::point(&jacobian), Some(p));
    }
}
