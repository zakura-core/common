//! Uses a renamed dependency with and without the consumer interfaces.

use arithmetic as udon;
use udon::{
    curve::PallasPoint,
    exec::{ExecutionOptions, SerialExecutor},
    fft::{Domain, Transform, reference},
    field::{Fp, Fq},
};

fn main() {
    let value = Fp::from_u64(7);
    assert!(value.mul(&value.invert().unwrap()).is_one());
    assert_eq!(
        PallasPoint::GENERATOR.mul_projective(&Fq::from_u64(2)),
        PallasPoint::GENERATOR.double(),
    );
    let lifted = udon::curve::PallasProjective::from_point(&PallasPoint::GENERATOR);
    assert_eq!(lifted.to_point(), PallasPoint::GENERATOR);

    assert_eq!(udon::field::low_u64(&value), 7);
    assert_eq!(
        udon::field::random::<udon::field::PallasBase>(|bytes| bytes.fill(0)).reduce(),
        <Fp>::ZERO.reduce()
    );
    assert_eq!(
        udon::field::dot(&[value], &[value]).reduce(),
        <Fp>::from_u64(49).reduce()
    );
    assert_eq!(
        udon::field::dot_iter(
            [value, Fp::ONE].iter(),
            [<Fp>::from_u64(2), <Fp>::from_u64(3)].iter().rev()
        )
        .reduce(),
        <Fp>::from_u64(23).reduce()
    );

    let mut inverses = [value, Fp::ZERO];
    udon::field::batch_invert(&mut inverses, &mut [Fp::ZERO; 2]);
    assert_eq!(
        inverses.map(Fp::reduce),
        [value.invert().unwrap().reduce(), <Fp>::ZERO.reduce()]
    );
    udon::field::batch_invert_groups(&mut [&mut inverses[..]], &mut [Fp::ZERO; 1]);
    assert_eq!(
        inverses.map(Fp::reduce),
        [value.reduce(), <Fp>::ZERO.reduce()]
    );

    let domain = Domain::<Fp>::new(2).unwrap();
    let input = [value, Fp::ONE, Fp::ZERO, Fp::DELTA];
    let mut expected = input;
    reference::transform(&mut expected, &domain.root());
    let mut actual = input;
    let transform = Transform::new(domain.subgroup());
    transform
        .forward(
            &mut actual,
            ExecutionOptions::default(),
            &SerialExecutor,
            &mut [],
        )
        .unwrap();
    assert_eq!(actual.map(Fp::reduce), expected.map(Fp::reduce));

    let mut basis = [Fp::ZERO; 4];
    domain
        .subgroup()
        .evaluate_lagrange(&<Fp>::ZERO, 0..4, &mut basis, &mut [])
        .unwrap();
    assert_eq!(basis.map(Fp::reduce), [domain.size_inverse().reduce(); 4]);

    // Native polynomial arithmetic remains available without consumer traits.
    let coefficients = [Fp::ONE, value, Fp::ONE];
    let point = <Fp>::from_u64(2);
    assert_eq!(
        udon::polynomial::evaluate(&coefficients, &point).reduce(),
        <Fp>::from_u64(19).reduce()
    );
    let mut divided = coefficients;
    let split = udon::polynomial::divide_linear_in_place(&mut divided, &point);
    assert_eq!(split, 1);
    assert_eq!(
        divided.map(Fp::reduce),
        [19, 9, 1].map(|value| <Fp>::from_u64(value).reduce())
    );

    #[cfg(feature = "field")]
    field();
    #[cfg(feature = "curve")]
    curve();
    #[cfg(feature = "domain")]
    {
        use udon::field::{Field, FieldAdapter};
        let domain = FieldAdapter::<udon::field::PallasBase>::domain(2).unwrap();
        let mut generic = input;
        domain.transform(FieldAdapter::from_slice_mut(&mut generic));
        assert_eq!(generic.map(Fp::reduce), expected.map(Fp::reduce));
        let mut values = [Fp::ZERO; 4];
        assert_eq!(
            domain.lagrange_evaluations(
                FieldAdapter::new(Fp::ZERO),
                FieldAdapter::from_slice_mut(&mut values),
                &mut []
            ),
            None
        );
        assert_eq!(values.map(Fp::reduce), basis.map(Fp::reduce));
    }
    #[cfg(feature = "polynomial")]
    {
        use udon::field::FieldAdapter;
        let coefficients = FieldAdapter::from_slice(&coefficients);
        let point = FieldAdapter::new(point);
        assert_eq!(
            udon::polynomial::evaluate_iter(coefficients, point)
                .into_inner()
                .reduce(),
            divided[0].reduce()
        );
        let mut quotient: Vec<_> =
            udon::polynomial::divide_linear_rev(coefficients.iter().copied(), point)
                .map(FieldAdapter::into_inner)
                .collect();
        quotient.reverse();
        assert!(
            quotient
                .iter()
                .map(|value| value.reduce())
                .eq(divided[split..].iter().map(|value| value.reduce()))
        );
        assert_eq!(
            udon::polynomial::geometric_sum(FieldAdapter::new(Fp::ONE), 3)
                .into_inner()
                .reduce(),
            <Fp>::from_u64(3).reduce()
        );
    }
    #[cfg(feature = "cycle")]
    cycle::<udon::cycle::Pasta>();
    #[cfg(feature = "poseidon-parameters")]
    {
        let base: udon::poseidon::PoseidonParameters<Fp, 5> = udon::poseidon::PALLAS_BASE;
        let scalar: udon::poseidon::PoseidonParameters<Fq, 5> = udon::poseidon::PALLAS_SCALAR;
        assert_eq!(base.rounds(), 64);
        assert_eq!(scalar.rounds(), 64);
        let base3: udon::poseidon::PoseidonParameters<Fp, 3> = udon::poseidon::PALLAS_BASE_T3;
        let scalar3: udon::poseidon::PoseidonParameters<Fq, 3> = udon::poseidon::PALLAS_SCALAR_T3;
        assert_eq!(base3.rate(), 2);
        assert_eq!(scalar3.rate(), 2);
    }
    #[cfg(feature = "poseidon-interface")]
    {
        use udon::poseidon::*;
        poseidon::<_, PoseidonFp, 5>(PALLAS_BASE);
        poseidon::<_, PoseidonFq, 5>(PALLAS_SCALAR);
        poseidon::<_, PoseidonFpT3, 3>(PALLAS_BASE_T3);
        poseidon::<_, PoseidonFqT3, 3>(PALLAS_SCALAR_T3);
    }
}

#[cfg(feature = "field")]
fn field() {
    fn generic<F: udon::field::Field>(values: &mut [F]) {
        let value = F::from(7);
        assert_eq!(
            F::random(|bytes| {
                bytes.fill(0);
                bytes[0] = 7;
            }),
            value
        );
        let repr: F::Repr = value.to_bytes();
        assert_eq!(F::from_bytes(repr), Some(value));
        assert_eq!(F::ZETA.pow_u64(3), F::ONE);
        let mut accumulator = F::Accumulator::default();
        F::mul_accumulate(&mut accumulator, &value, &value);
        F::mul_accumulate(&mut accumulator, &F::ONE, &F::from(2));
        assert_eq!(F::reduce(accumulator), F::from(51));

        let domain = F::domain(1).unwrap();
        let mut coefficients = [value, F::ONE];
        domain.transform(&mut coefficients);
        assert_eq!(coefficients, [F::from(8), F::from(6)]);
        domain.inverse_transform(&mut coefficients);
        assert_eq!(coefficients, [value, F::ONE]);

        assert_eq!(value.mul_add(&F::from(3), &F::from(2)), F::from(23));
        assert_eq!(F::sum_of_products_slice(&[value], &[value]), F::from(49));
        assert_eq!(
            F::sum_of_product_pairs(
                [value, F::ONE]
                    .iter()
                    .zip([F::from(2), F::from(3)].iter().rev())
            ),
            F::from(23)
        );
        F::batch_invert(values, &mut [F::ZERO; 2]);
        assert_eq!(values[0] * F::from(7), F::ONE);
        assert_eq!(values[1], F::ZERO);
    }
    generic(udon::field::FieldAdapter::from_slice_mut(&mut [
        Fp::from_u64(7),
        Fp::ZERO,
    ]));
}

#[cfg(feature = "curve")]
fn curve() {
    fn generic<A: udon::curve::Affine>() {
        assert_eq!(A::msm(&[], &[]), A::identity().to_projective());
        for point in [A::identity(), A::generator()] {
            let projective: A::Projective = point.into();
            assert_eq!(A::from(projective), point);
        }
    }
    generic::<udon::curve::AffineAdapter<udon::curve::Pallas>>();
}

#[cfg(feature = "cycle")]
fn cycle<C: udon::cycle::Cycle>() {}

#[cfg(feature = "poseidon-interface")]
fn poseidon<
    M: udon::field::PrimeModulus,
    P: udon::poseidon::PoseidonPermutation<udon::field::FieldAdapter<M>>
        + Default,
    const T: usize,
>(native: udon::poseidon::PoseidonParameters<udon::field::PastaField<M>, T>) {
    let instance = P::default();
    assert_eq!(P::T, T);
    assert_eq!(P::RATE, native.rate());
    assert_eq!(P::ALPHA, native.alpha);
    assert_eq!(instance.round_constants().len(), native.rounds());
    assert_eq!(instance.mds_matrix().len(), native.width());
    for (row, expected) in instance
        .round_constants()
        .iter()
        .zip(native.round_constants)
    {
        assert_eq!(
            row.as_ref(),
            udon::field::FieldAdapter::from_slice(expected)
        );
    }
    for (row, expected) in instance.mds_matrix().iter().zip(native.mds) {
        assert_eq!(
            row.as_ref(),
            udon::field::FieldAdapter::from_slice(expected)
        );
    }
}
