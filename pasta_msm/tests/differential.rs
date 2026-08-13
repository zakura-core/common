use pasta_curves::{
    group::{
        ff::{Field, PrimeField},
        prime::PrimeCurveAffine,
        Curve, Group,
    },
    pallas, vesta,
};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

fn pallas_fixture(size: usize, seed: u8) -> (Vec<pallas::Affine>, Vec<pallas::Scalar>) {
    let mut rng = ChaCha20Rng::from_seed([seed; 32]);
    let scalars = (0..size)
        .map(|_| pallas::Scalar::random(&mut rng))
        .collect::<Vec<_>>();
    let points = (0..size)
        .map(|_| (pallas::Point::generator() * pallas::Scalar::random(&mut rng)).to_affine())
        .collect();
    (points, scalars)
}

fn vesta_fixture(size: usize, seed: u8) -> (Vec<vesta::Affine>, Vec<vesta::Scalar>) {
    let mut rng = ChaCha20Rng::from_seed([seed; 32]);
    let scalars = (0..size)
        .map(|_| vesta::Scalar::random(&mut rng))
        .collect::<Vec<_>>();
    let points = (0..size)
        .map(|_| (vesta::Point::generator() * vesta::Scalar::random(&mut rng)).to_affine())
        .collect();
    (points, scalars)
}

fn pallas_reference(points: &[pallas::Affine], scalars: &[pallas::Scalar]) -> pallas::Point {
    points
        .iter()
        .zip(scalars)
        .fold(pallas::Point::identity(), |sum, (point, scalar)| {
            sum + *point * *scalar
        })
}

fn vesta_reference(points: &[vesta::Affine], scalars: &[vesta::Scalar]) -> vesta::Point {
    points
        .iter()
        .zip(scalars)
        .fold(vesta::Point::identity(), |sum, (point, scalar)| {
            sum + *point * *scalar
        })
}

fn scalar_with_bits<F: PrimeField>(bits: &[usize]) -> F {
    let mut repr = F::Repr::default();
    for bit in bits {
        assert!(*bit < F::NUM_BITS as usize);
        repr.as_mut()[bit / 8] |= 1 << (bit % 8);
    }
    Option::from(F::from_repr(repr)).expect("test scalar must be canonical")
}

#[test]
fn pallas_matches_reference_at_window_boundaries() {
    for (case, size) in [0, 1, 2, 16, 31, 32, 33, 255, 2_048]
        .into_iter()
        .enumerate()
    {
        let (points, mut scalars) = pallas_fixture(size, case as u8);
        if size >= 3 {
            scalars[0] = pallas::Scalar::ZERO;
            scalars[1] = pallas::Scalar::ONE;
            scalars[2] = -pallas::Scalar::ONE;
        }
        assert_eq!(
            pasta_msm::pallas_vartime(&points, &scalars),
            pallas_reference(&points, &scalars),
            "size {size}"
        );
    }
}

#[test]
fn vesta_matches_reference_at_window_boundaries() {
    for (case, size) in [0, 1, 2, 16, 31, 32, 33, 255, 2_048]
        .into_iter()
        .enumerate()
    {
        let (points, mut scalars) = vesta_fixture(size, case as u8 + 32);
        if size >= 3 {
            scalars[0] = vesta::Scalar::ZERO;
            scalars[1] = vesta::Scalar::ONE;
            scalars[2] = -vesta::Scalar::ONE;
        }
        assert_eq!(
            pasta_msm::vesta_vartime(&points, &scalars),
            vesta_reference(&points, &scalars),
            "size {size}"
        );
    }
}

#[test]
fn identity_points_and_zero_scalars_match_reference() {
    const SIZE: usize = 257;

    let (mut pallas_points, mut pallas_scalars) = pallas_fixture(SIZE, 64);
    for index in (0..SIZE).step_by(3) {
        pallas_points[index] = pallas::Point::identity().to_affine();
    }
    for index in (0..SIZE).step_by(5) {
        pallas_scalars[index] = pallas::Scalar::ZERO;
    }
    assert_eq!(
        pasta_msm::pallas_vartime(&pallas_points, &pallas_scalars),
        pallas_reference(&pallas_points, &pallas_scalars)
    );

    let (mut vesta_points, mut vesta_scalars) = vesta_fixture(SIZE, 65);
    for index in (0..SIZE).step_by(3) {
        vesta_points[index] = vesta::Point::identity().to_affine();
    }
    for index in (0..SIZE).step_by(5) {
        vesta_scalars[index] = vesta::Scalar::ZERO;
    }
    assert_eq!(
        pasta_msm::vesta_vartime(&vesta_points, &vesta_scalars),
        vesta_reference(&vesta_points, &vesta_scalars)
    );
}

#[test]
fn signed_booth_scalar_boundaries_match_reference() {
    let carry_bits = (0..9).collect::<Vec<_>>();

    let mut pallas_scalars = vec![
        pallas::Scalar::ZERO,
        pallas::Scalar::ONE,
        -pallas::Scalar::ONE,
        scalar_with_bits(&[8]),
        scalar_with_bits(&carry_bits),
        scalar_with_bits(&[9]),
        scalar_with_bits(&[0, 9]),
    ];
    pallas_scalars
        .extend([17, 18, 251, 252, 253, 254].map(|bit| scalar_with_bits::<pallas::Scalar>(&[bit])));
    let pallas_points = (1..=pallas_scalars.len() as u64)
        .map(|scalar| (pallas::Point::generator() * pallas::Scalar::from(scalar)).to_affine())
        .collect::<Vec<_>>();
    assert_eq!(
        pasta_msm::pallas_vartime(&pallas_points, &pallas_scalars),
        pallas_reference(&pallas_points, &pallas_scalars)
    );

    let mut vesta_scalars = vec![
        vesta::Scalar::ZERO,
        vesta::Scalar::ONE,
        -vesta::Scalar::ONE,
        scalar_with_bits(&[8]),
        scalar_with_bits(&carry_bits),
        scalar_with_bits(&[9]),
        scalar_with_bits(&[0, 9]),
    ];
    vesta_scalars
        .extend([17, 18, 251, 252, 253, 254].map(|bit| scalar_with_bits::<vesta::Scalar>(&[bit])));
    let vesta_points = (1..=vesta_scalars.len() as u64)
        .map(|scalar| (vesta::Point::generator() * vesta::Scalar::from(scalar)).to_affine())
        .collect::<Vec<_>>();
    assert_eq!(
        pasta_msm::vesta_vartime(&vesta_points, &vesta_scalars),
        vesta_reference(&vesta_points, &vesta_scalars)
    );
}

#[test]
#[should_panic(expected = "length mismatch")]
fn pallas_rejects_length_mismatch() {
    pasta_msm::pallas_vartime(&[pallas::Affine::identity()], &[]);
}

#[test]
#[should_panic(expected = "length mismatch")]
fn vesta_rejects_length_mismatch() {
    pasta_msm::vesta_vartime(&[vesta::Affine::identity()], &[]);
}
