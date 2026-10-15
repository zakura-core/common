use num_bigint::BigUint;

use super::{reference::Reference, *};
use crate::field::pasta::test_support::modulus;

fn group_laws<C: PastaCurve>() {
    let generator = Point::<C>::GENERATOR;
    let affine = AffinePoint::<C>::GENERATOR;
    let projective = ProjectivePoint::<C>::GENERATOR;
    let identity = Point::<C>::IDENTITY;
    assert_eq!(generator, Point::GENERATOR);
    assert_eq!(affine, AffinePoint::GENERATOR);
    assert_eq!(projective, ProjectivePoint::GENERATOR);
    assert_eq!(identity, Point::default());
    assert_eq!(ProjectivePoint::<C>::IDENTITY, ProjectivePoint::default());
    assert_eq!(affine.to_point(), generator);
    assert_eq!(affine.to_projective(), projective);
    assert_eq!(generator.coordinates(), Some(affine.coordinates()));
    assert_eq!(identity.coordinates(), None);
    assert_eq!(affine.x, PastaField::<C::Base>::ONE.neg().reduce());
    assert_eq!(affine.y, PastaField::from_u64(2));
    assert_eq!(AffinePoint::<C>::from_xy(affine.x, affine.y), Some(affine));
    assert_eq!(
        AffinePoint::<C>::from_xy(PastaField::ZERO, PastaField::ZERO),
        None
    );
    assert_eq!(
        Point::<C>::from_xy(PastaField::ZERO, PastaField::ZERO),
        Some(identity)
    );
    assert_eq!(Point::<C>::from_xy(affine.x, affine.y), Some(generator));
    assert_eq!(Point::<C>::from_xy(PastaField::ONE, PastaField::ONE), None);
    assert_eq!(generator.neg().neg(), generator);
    assert_eq!(generator.add(&identity), projective);
    assert_eq!(identity.add(&generator), projective);
    assert_eq!(generator.sub(&generator), ProjectivePoint::IDENTITY);
    assert_eq!(generator.add(&generator.neg()), ProjectivePoint::IDENTITY);
    assert_eq!(generator.add(&generator), generator.double());
    assert_eq!(identity.double(), ProjectivePoint::IDENTITY);
    assert_eq!(identity.neg(), identity);
    assert_eq!(projective.add(&projective), projective.double());
    assert_eq!(projective.add_mixed(&affine), projective.double());
    assert_eq!(
        projective.add_mixed(&affine.neg()),
        ProjectivePoint::IDENTITY
    );
    assert_eq!(projective.sub(&projective), ProjectivePoint::IDENTITY);
    assert_eq!(ProjectivePoint::IDENTITY.add_mixed(&affine), projective);
    assert_eq!(projective.neg().neg(), projective);

    let p = modulus::<C::Base>();
    let reference = Reference::generator(&p);
    let mut multiple = Reference::identity();
    let mut point = identity;
    for i in 0..20 {
        multiple.assert_point(&point);
        let scaled = scaled(&point, i + 2);
        assert_eq!(scaled, point.to_projective());
        assert_eq!(scaled.to_point(), point);
        assert_eq!(scaled.double(), point.to_projective().double());
        assert_eq!(
            scaled.add_mixed(&affine),
            point.to_projective().add(&projective)
        );
        assert_eq!(scaled.add(&projective), projective.add(&scaled));
        assert_eq!(scaled.add(&scaled.neg()), ProjectivePoint::IDENTITY);
        point = point.add(&generator).to_point();
        multiple = multiple.add(&reference, &p);
    }
    assert_ne!(projective, projective.double());
    assert_ne!(projective, ProjectivePoint::IDENTITY);
    assert_eq!(scaled(&identity, 3), ProjectivePoint::IDENTITY);
    assert!(std::format!("{affine:?} {generator:?} {projective:?}").contains("x"));

    // Protocol map handoff and selection retain projective scaling. The paired
    // kernel must also preserve equal/inverse and identity lane semantics.
    let coordinates = |p: &ProjectivePoint<C>| {
        let (x, y, z) = p.coordinates();
        [
            x.montgomery_limbs(),
            y.montgomery_limbs(),
            z.montgomery_limbs(),
        ]
    };
    for i in 0..12 {
        let point = generator
            .mul_projective(&PastaField::from_u64(i))
            .to_point();
        let lhs = scaled(&point, i + 2);
        let (x, y, z) = lhs.coordinates();
        let checked = ProjectivePoint::from_jacobian(*x, *y, *z).unwrap();
        assert_eq!(checked, lhs);
        if !lhs.is_identity() {
            assert_eq!(coordinates(&checked), coordinates(&lhs));
        }
        assert_eq!(
            coordinates(&lhs.select(&projective, false)),
            coordinates(&lhs)
        );
        assert_eq!(
            coordinates(&lhs.select(&projective, true)),
            coordinates(&projective)
        );
        for rhs in [
            affine,
            affine.neg(),
            *projective.double().to_point().as_affine().unwrap(),
        ] {
            for other in [ProjectivePoint::IDENTITY, lhs.neg(), projective] {
                assert_eq!(
                    ProjectivePoint::add_mixed_pair(&lhs, &rhs, &other, &affine),
                    [lhs.add(&rhs.to_projective()), other.add(&projective)]
                );
            }
        }
    }
    assert_eq!(
        ProjectivePoint::<C>::from_jacobian(PastaField::ONE, PastaField::ONE, PastaField::ONE),
        None
    );

    // Exercise general addition where both inputs have different non-unit z.
    for a in 0..8 {
        for b in 0..8 {
            let lhs = generator
                .mul_projective(&PastaField::<_>::from_u64(a))
                .to_point();
            let rhs = generator
                .mul_projective(&PastaField::<_>::from_u64(b))
                .to_point();
            let expected = Reference::from_point(&lhs).add(&Reference::from_point(&rhs), &p);
            expected.assert_point(&scaled(&lhs, 7).add(&scaled(&rhs, 13)).to_point());
        }
    }
    // Full-width coordinates and unrelated Jacobian scales exercise reduction
    // carries and the equal/inverse branches independently of output scaling.
    let scale = |p: &AffinePoint<C>, z: PastaField<C::Base>| ProjectivePoint {
        x: p.x.mul(&z.square()),
        y: p.y.mul(&z.square()).mul(&z),
        z,
        marker: PhantomData,
    };
    let scales: Vec<_> = field_samples::<C::Base>()
        .filter(|z| !z.is_zero())
        .take(32)
        .collect();
    for (i, scalar) in field_samples::<C::Scalar>()
        .filter(|s| !s.is_zero())
        .take(16)
        .enumerate()
    {
        let p = *affine
            .mul_projective(&scalar)
            .to_point()
            .as_affine()
            .unwrap();
        let q = *p.to_point().add(&generator).to_point().as_affine().unwrap();
        let a = scale(&p, scales[2 * i]);
        let same = scale(&p, scales[2 * i + 1]);
        let b = scale(&q, scales[2 * i + 1]);
        let modulus = modulus::<C::Base>();
        let rp = Reference::from_point(&p.to_point());
        let rq = Reference::from_point(&q.to_point());
        let pp = p.to_point();
        let qp = q.to_point();
        rp.add(&rq, &modulus).assert_point(&pp.add(&qp).to_point());
        rp.add(&Reference::from_point(&qp.neg()), &modulus)
            .assert_point(&pp.sub(&qp).to_point());
        rp.add(&rp, &modulus).assert_point(&pp.double().to_point());
        assert_eq!(pp.add(&pp), pp.double());
        assert!(pp.add(&pp.neg()).is_identity());
        assert_eq!(pp.add(&identity), p.to_projective());
        assert_eq!(identity.add(&pp), p.to_projective());
        rp.add(&rq, &modulus).assert_point(&a.add(&b).to_point());
        rp.add(&rq, &modulus)
            .assert_point(&a.add_mixed(&q).to_point());
        rp.add(&rp, &modulus).assert_point(&a.double().to_point());
        assert_eq!(a.add(&same), a.double());
        assert_eq!(a.add(&same.neg()), ProjectivePoint::IDENTITY);
        assert_eq!(a.add_mixed(&p), a.double());
        assert_eq!(a.add_mixed(&p.neg()), ProjectivePoint::IDENTITY);
    }
}

fn scalar_multiplication<C: PastaCurve>() {
    let p = modulus::<C::Base>();
    let reference = Reference::generator(&p);
    let generator = AffinePoint::<C>::GENERATOR;
    let projective = scaled(&generator.to_point(), 11);
    let scalars = scalar_corpus::<C>();
    for scalar in &scalars {
        let expected = reference.mul(&BigUint::from_bytes_le(&scalar.to_bytes()), &p);
        let mixed = generator.mul_projective(scalar);
        expected.assert_point(&mixed.to_point());
        assert_eq!(projective.mul(scalar), mixed);
        assert_eq!(generator.to_point().mul_projective(scalar), mixed);
        assert_eq!(
            Point::<C>::IDENTITY.mul_projective(scalar),
            ProjectivePoint::IDENTITY
        );
        assert_eq!(
            ProjectivePoint::<C>::IDENTITY.mul(scalar),
            ProjectivePoint::IDENTITY
        );
    }
    // Multiply by the unreduced group order as an integer. Converting it to
    // the scalar field would reduce to zero and make this test vacuous.
    let order = CanonicalUint::from_limbs(C::Scalar::MODULUS);
    let mut result = ProjectivePoint::IDENTITY;
    for bit in (0..255).rev() {
        result = result.double();
        if order.bit(bit).unwrap() {
            result = result.add_mixed(&generator);
        }
    }
    assert!(result.is_identity());
    assert_eq!(
        generator.mul_projective(&PastaField::<_>::ONE.neg()),
        generator.neg().to_projective()
    );
}

#[test]
fn pallas_group_operations_match_integer_arithmetic() {
    group_laws::<Pallas>();
}
#[test]
fn vesta_group_operations_match_integer_arithmetic() {
    group_laws::<Vesta>();
}
#[test]
fn pallas_full_width_scalars_match_integer_arithmetic() {
    scalar_multiplication::<Pallas>();
}
#[test]
fn vesta_full_width_scalars_match_integer_arithmetic() {
    scalar_multiplication::<Vesta>();
}

fn encodings<C: PastaCurve>(generator_hex: &str) {
    let expected: Vec<u8> = generator_hex
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| u8::from_str_radix(core::str::from_utf8(pair).unwrap(), 16).unwrap())
        .collect();
    let expected: [u8; 32] = expected.try_into().unwrap();
    let generator = Point::<C>::GENERATOR;
    assert_eq!(generator.to_bytes(), expected);
    assert_eq!(Point::<C>::from_bytes(expected), Some(generator));
    let mut negative = expected;
    negative[31] |= 0x80;
    assert_eq!(generator.neg().to_bytes(), negative);
    assert_eq!(Point::<C>::from_bytes(negative), Some(generator.neg()));
    assert_eq!(Point::<C>::from_bytes([0; 32]), Some(Point::IDENTITY));
    assert_eq!(Point::<C>::IDENTITY.to_bytes(), [0; 32]);
    assert_eq!(AffinePoint::<C>::from_bytes([0; 32]), None);
    let mut signed_zero = [0; 32];
    signed_zero[31] = 0x80;
    assert_eq!(Point::<C>::from_bytes(signed_zero), None);
    assert_eq!(Point::<C>::from_bytes([0xff; 32]), None);
    for sign in [0, 0x80] {
        let mut modulus = CanonicalUint::from_limbs(C::Base::MODULUS).to_le_bytes();
        modulus[31] |= sign;
        assert_eq!(Point::<C>::from_bytes(modulus), None);
    }
    let p = modulus::<C::Base>();
    let mut nonsquare = None;
    for x in 1_u64..100 {
        let rhs = (BigUint::from(x).pow(3) + 5_u32) % &p;
        if rhs.modpow(&((&p - 1_u32) >> 1), &p) == &p - 1_u32 {
            nonsquare = Some(x);
            break;
        }
    }
    let mut invalid = [0; 32];
    invalid[..8].copy_from_slice(&nonsquare.unwrap().to_le_bytes());
    assert_eq!(Point::<C>::from_bytes(invalid), None);
    for scalar in scalar_corpus::<C>().iter().step_by(4) {
        let point = generator.mul_projective(scalar).to_point();
        assert_eq!(Point::<C>::from_bytes(point.to_bytes()), Some(point));
        if let Some(affine) = point.as_affine() {
            assert_eq!(
                AffinePoint::<C>::from_bytes(affine.to_bytes()),
                Some(*affine)
            );
        }
    }
}

#[test]
fn compressed_encodings_are_canonical() {
    encodings::<Pallas>("00000000ed302d991bf94c09fc98462200000000000000000000000000000040");
    encodings::<Vesta>("0000000021eb468cdda89409fc98462200000000000000000000000000000040");
}
