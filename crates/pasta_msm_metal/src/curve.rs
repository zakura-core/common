//! Portable Jacobian-coordinate group arithmetic over [`Field`], mirrored
//! by the Metal kernels.
//!
//! Both Pasta curves have the short Weierstrass form $y^2 = x^3 + 5$
//! ($a = 0$), so the formulas below are the `a = 0` specializations from
//! the Explicit-Formulas Database: `dbl-2009-l` for doubling,
//! `madd-2007-bl` for the mixed (Jacobian + affine) addition that fills
//! buckets, and `add-2007-bl` for the full addition that reduces them. The
//! exceptional cases (either operand the identity, equal or opposite
//! inputs) are handled by explicit branches: every input to the backend is
//! public, so variable time is acceptable, and the branches keep the
//! arithmetic exact for duplicate bases.
//!
//! As in `field.rs`, every function has a twin in
//! `shaders/pasta_msm.metal`; keep them in step.

use crate::field::{Field, Limbs};

/// An affine point in Montgomery-form limbs; `(0, 0)` encodes the identity
/// (no point of either curve has $x = 0$ and $y = 0$: $0 \ne 5$).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Affine {
    /// The x-coordinate.
    pub x: Limbs,
    /// The y-coordinate.
    pub y: Limbs,
}

/// A Jacobian point $(X : Y : Z)$ with $x = X/Z^2$, $y = Y/Z^3$; $Z = 0$
/// encodes the identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Jacobian {
    /// The X-coordinate.
    pub x: Limbs,
    /// The Y-coordinate.
    pub y: Limbs,
    /// The Z-coordinate.
    pub z: Limbs,
}

impl Affine {
    /// The affine identity encoding.
    pub const IDENTITY: Affine = Affine {
        x: Field::ZERO,
        y: Field::ZERO,
    };

    /// Whether this is the identity encoding.
    #[inline]
    pub fn is_identity(&self) -> bool {
        Field::is_zero(&self.x) && Field::is_zero(&self.y)
    }

    /// The negation $(x, -y)$.
    #[inline]
    pub fn neg(&self, field: &Field) -> Affine {
        Affine {
            x: self.x,
            y: field.neg(&self.y),
        }
    }

    /// Lifts to Jacobian coordinates with $Z = 1$.
    #[inline]
    pub fn to_jacobian(self, field: &Field) -> Jacobian {
        if self.is_identity() {
            Jacobian::IDENTITY
        } else {
            Jacobian {
                x: self.x,
                y: self.y,
                z: field.one,
            }
        }
    }
}

impl Jacobian {
    /// The Jacobian identity encoding.
    pub const IDENTITY: Jacobian = Jacobian {
        x: Field::ZERO,
        y: Field::ZERO,
        z: Field::ZERO,
    };

    /// Whether this is the identity.
    #[inline]
    pub fn is_identity(&self) -> bool {
        Field::is_zero(&self.z)
    }

    /// $2P$ (`dbl-2009-l`, $a = 0$).
    pub fn double(&self, f: &Field) -> Jacobian {
        if self.is_identity() {
            return Jacobian::IDENTITY;
        }
        let a = f.square(&self.x);
        let b = f.square(&self.y);
        let c = f.square(&b);
        // D = 2((X + B)^2 - A - C)
        let xb = f.add(&self.x, &b);
        let d = f.double(&f.sub(&f.sub(&f.square(&xb), &a), &c));
        // E = 3A, F = E^2
        let e = f.add(&f.double(&a), &a);
        let ff = f.square(&e);
        let x3 = f.sub(&ff, &f.double(&d));
        // Y3 = E(D - X3) - 8C
        let c8 = f.double(&f.double(&f.double(&c)));
        let y3 = f.sub(&f.mul(&e, &f.sub(&d, &x3)), &c8);
        let z3 = f.double(&f.mul(&self.y, &self.z));
        Jacobian {
            x: x3,
            y: y3,
            z: z3,
        }
    }

    /// $P + Q$ for affine $Q$ (`madd-2007-bl`), with exact exceptional cases.
    pub fn add_mixed(&self, q: &Affine, f: &Field) -> Jacobian {
        if q.is_identity() {
            return *self;
        }
        if self.is_identity() {
            return q.to_jacobian(f);
        }
        let z1z1 = f.square(&self.z);
        let u2 = f.mul(&q.x, &z1z1);
        let s2 = f.mul(&q.y, &f.mul(&self.z, &z1z1));
        let h = f.sub(&u2, &self.x);
        let r = f.double(&f.sub(&s2, &self.y));
        if Field::is_zero(&h) {
            // Same x: either the same point (double) or opposites (identity).
            return if Field::is_zero(&r) {
                self.double(f)
            } else {
                Jacobian::IDENTITY
            };
        }
        let hh = f.square(&h);
        let i = f.double(&f.double(&hh));
        let j = f.mul(&h, &i);
        let v = f.mul(&self.x, &i);
        // X3 = r^2 - J - 2V
        let x3 = f.sub(&f.sub(&f.square(&r), &j), &f.double(&v));
        // Y3 = r(V - X3) - 2 Y1 J
        let y3 = f.sub(&f.mul(&r, &f.sub(&v, &x3)), &f.double(&f.mul(&self.y, &j)));
        // Z3 = (Z1 + H)^2 - Z1Z1 - HH
        let z3 = f.sub(&f.sub(&f.square(&f.add(&self.z, &h)), &z1z1), &hh);
        Jacobian {
            x: x3,
            y: y3,
            z: z3,
        }
    }

    /// $P + Q$ (`add-2007-bl`), with exact exceptional cases.
    pub fn add(&self, q: &Jacobian, f: &Field) -> Jacobian {
        if q.is_identity() {
            return *self;
        }
        if self.is_identity() {
            return *q;
        }
        let z1z1 = f.square(&self.z);
        let z2z2 = f.square(&q.z);
        let u1 = f.mul(&self.x, &z2z2);
        let u2 = f.mul(&q.x, &z1z1);
        let s1 = f.mul(&self.y, &f.mul(&q.z, &z2z2));
        let s2 = f.mul(&q.y, &f.mul(&self.z, &z1z1));
        let h = f.sub(&u2, &u1);
        let r = f.double(&f.sub(&s2, &s1));
        if Field::is_zero(&h) {
            return if Field::is_zero(&r) {
                self.double(f)
            } else {
                Jacobian::IDENTITY
            };
        }
        // I = (2H)^2, J = H I, V = U1 I
        let i = f.square(&f.double(&h));
        let j = f.mul(&h, &i);
        let v = f.mul(&u1, &i);
        let x3 = f.sub(&f.sub(&f.square(&r), &j), &f.double(&v));
        let y3 = f.sub(&f.mul(&r, &f.sub(&v, &x3)), &f.double(&f.mul(&s1, &j)));
        // Z3 = ((Z1 + Z2)^2 - Z1Z1 - Z2Z2) H
        let z3 = f.mul(
            &f.sub(&f.sub(&f.square(&f.add(&self.z, &q.z)), &z1z1), &z2z2),
            &h,
        );
        Jacobian {
            x: x3,
            y: y3,
            z: z3,
        }
    }

    /// $-P$.
    #[inline]
    pub fn neg(&self, f: &Field) -> Jacobian {
        Jacobian {
            x: self.x,
            y: f.neg(&self.y),
            z: self.z,
        }
    }

    /// $2^k P$.
    pub fn double_n(&self, k: u32, f: &Field) -> Jacobian {
        let mut acc = *self;
        for _ in 0..k {
            acc = acc.double(f);
        }
        acc
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{PALLAS_BASE, VESTA_BASE, limbs_from_u64, limbs_to_bytes};
    use ff::{Field as _, PrimeField};
    use group::CurveAffine as _;
    use group::{Curve, Group};
    use pasta_curves::arithmetic::{
        CurveAffine, CurveExt, fp_montgomery_limbs, fq_montgomery_limbs,
    };
    use pasta_curves::{Fp, Fq, pallas, vesta};
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    fn pallas_affine(p: &pallas::Affine) -> Affine {
        match Option::<pasta_curves::arithmetic::Coordinates<_>>::from(p.coordinates()) {
            Some(c) => Affine {
                x: limbs_from_u64(fp_montgomery_limbs(c.x())),
                y: limbs_from_u64(fp_montgomery_limbs(c.y())),
            },
            None => Affine::IDENTITY,
        }
    }

    fn pallas_point(j: &Jacobian) -> pallas::Point {
        let f = &PALLAS_BASE;
        let coord = |l: &Limbs| Fp::from_repr(limbs_to_bytes(&f.from_montgomery(l))).unwrap();
        Option::from(pallas::Point::new_jacobian(
            coord(&j.x),
            coord(&j.y),
            coord(&j.z),
        ))
        .expect("on curve")
    }

    fn vesta_affine(p: &vesta::Affine) -> Affine {
        match Option::<pasta_curves::arithmetic::Coordinates<_>>::from(p.coordinates()) {
            Some(c) => Affine {
                x: limbs_from_u64(fq_montgomery_limbs(c.x())),
                y: limbs_from_u64(fq_montgomery_limbs(c.y())),
            },
            None => Affine::IDENTITY,
        }
    }

    fn vesta_point(j: &Jacobian) -> vesta::Point {
        let f = &VESTA_BASE;
        let coord = |l: &Limbs| Fq::from_repr(limbs_to_bytes(&f.from_montgomery(l))).unwrap();
        Option::from(vesta::Point::new_jacobian(
            coord(&j.x),
            coord(&j.y),
            coord(&j.z),
        ))
        .expect("on curve")
    }

    #[test]
    fn pallas_arithmetic_matches_pasta_curves() {
        let f = &PALLAS_BASE;
        let mut rng = XorShiftRng::from_seed([3; 16]);
        let mut points: Vec<pallas::Point> =
            (0..40).map(|_| pallas::Point::random(&mut rng)).collect();
        points.push(pallas::Point::identity());
        for p in &points {
            let pa = pallas_affine(&p.to_affine());
            let pj = pa.to_jacobian(f);
            assert_eq!(pallas_point(&pj), *p);
            assert_eq!(pallas_point(&pj.double(f)), p.double());
            assert_eq!(pallas_point(&pj.neg(f)), -*p);
            assert_eq!(pallas_point(&pa.neg(f).to_jacobian(f)), -*p);
            assert_eq!(
                pallas_point(&pj.double_n(5, f)),
                *p * pallas::Scalar::from(32)
            );
            for q in &points {
                let qa = pallas_affine(&q.to_affine());
                let qj = qa.to_jacobian(f);
                assert_eq!(pallas_point(&pj.add_mixed(&qa, f)), *p + *q);
                assert_eq!(pallas_point(&pj.add(&qj, f)), *p + *q);
                // Doubled Z to exercise the non-normalized paths.
                let pj2 = pj.add(&pj, f).add(&pj.neg(f), f);
                assert_eq!(pallas_point(&pj2), *p);
                assert_eq!(pallas_point(&pj2.add_mixed(&qa, f)), *p + *q);
                assert_eq!(pallas_point(&pj2.add(&qj, f)), *p + *q);
                assert_eq!(pallas_point(&pj2.add_mixed(&qa.neg(f), f)), *p - *q);
                assert_eq!(pallas_point(&pj2.add(&qj.neg(f), f)), *p - *q);
            }
        }
    }

    #[test]
    fn vesta_arithmetic_matches_pasta_curves() {
        let f = &VESTA_BASE;
        let mut rng = XorShiftRng::from_seed([4; 16]);
        let mut points: Vec<vesta::Point> =
            (0..25).map(|_| vesta::Point::random(&mut rng)).collect();
        points.push(vesta::Point::identity());
        for p in &points {
            let pa = vesta_affine(&p.to_affine());
            let pj = pa.to_jacobian(f);
            assert_eq!(vesta_point(&pj), *p);
            assert_eq!(vesta_point(&pj.double(f)), p.double());
            for q in &points {
                let qa = vesta_affine(&q.to_affine());
                let qj = qa.to_jacobian(f);
                assert_eq!(vesta_point(&pj.add_mixed(&qa, f)), *p + *q);
                assert_eq!(vesta_point(&pj.add(&qj, f)), *p + *q);
                let pj2 = pj.double(f).add(&pj.neg(f), f);
                assert_eq!(vesta_point(&pj2.add_mixed(&qa.neg(f), f)), *p - *q);
                assert_eq!(vesta_point(&pj2.add(&qj, f)), *p + *q);
            }
        }
    }

    #[test]
    fn identity_encodings() {
        let f = &PALLAS_BASE;
        assert!(Affine::IDENTITY.is_identity());
        assert!(Jacobian::IDENTITY.is_identity());
        assert!(Affine::IDENTITY.to_jacobian(f).is_identity());
        assert!(Jacobian::IDENTITY.double(f).is_identity());
        let g = pallas_affine(&pallas::Point::generator().to_affine());
        let gj = g.to_jacobian(f);
        assert_eq!(gj.add_mixed(&Affine::IDENTITY, f), gj);
        assert_eq!(Jacobian::IDENTITY.add_mixed(&g, f), gj);
        assert_eq!(gj.add(&Jacobian::IDENTITY, f), gj);
        assert_eq!(Jacobian::IDENTITY.add(&gj, f), gj);
        assert!(gj.add_mixed(&g.neg(f), f).is_identity());
        assert!(gj.add(&gj.neg(f), f).is_identity());
        // (0, 0) is exactly pasta_curves' own affine identity encoding, and
        // no curve point has x = 0 and y = 0, so the encoding is unambiguous.
        let zero = pallas::Affine::from_xy(Fp::ZERO, Fp::ZERO).unwrap();
        assert!(bool::from(zero.is_identity()));
        assert_eq!(pallas_affine(&zero), Affine::IDENTITY);
        let zero = vesta::Affine::from_xy(Fq::ZERO, Fq::ZERO).unwrap();
        assert!(bool::from(zero.is_identity()));
        assert_eq!(vesta_affine(&zero), Affine::IDENTITY);
    }
}
