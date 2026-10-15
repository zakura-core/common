use crate::curve::{Affine as _, Projective as _};
use std::vec::Vec;

use super::*;
use crate::{
    curve::{Pallas, PallasPoint, PastaCurve, Point, ProjectiveAdapter, Vesta, VestaPoint},
    field::{Field, FieldAdapter, Fp, PallasScalar, PastaField, PrimeModulus},
    poseidon::{PALLAS_BASE, PALLAS_SCALAR, PoseidonFp, PoseidonParameters},
};

/// `count` distinct nonidentity points, the generator multiples starting
/// at `first`; disjoint ranges give disjoint points.
fn leaked<C: PastaCurve>(count: usize, first: u64) -> &'static [Point<C>] {
    let points: Vec<Point<C>> = (first..first + count as u64)
        .map(|index| {
            Point::<C>::GENERATOR
                .mul_projective(&crate::field::PastaField::from_u64(index * 7 + 3))
                .to_point()
        })
        .collect();
    Vec::leak(points)
}

fn params() -> PastaParams {
    PastaParams::new(
        Generators::new(leaked::<Pallas>(3, 1), leaked::<Pallas>(1, 50)[0]),
        Generators::new(leaked::<Vesta>(2, 1), leaked::<Vesta>(1, 50)[0]),
    )
}

#[test]
fn pasta_generators_are_reached_through_the_cycle() {
    let params = params();
    let pallas = <Pasta as Cycle>::nested_generators(&params);
    let vesta = <Pasta as Cycle>::host_generators(&params);
    assert_eq!(pallas.g().len(), 3);
    assert_eq!(vesta.g().len(), 2);
    assert_eq!(pallas.g(), params.pallas().g());
    assert_eq!(vesta.h(), params.vesta().h());
    assert!(pallas.g().iter().all(|point| !point.is_identity()));
    assert!(!pallas.h().is_identity());

    let _: ProjectiveAdapter<Pallas> = pallas.g()[0] * FieldAdapter::<PallasScalar>::from(2);
}

fn check_poseidon<M: PrimeModulus, P: PoseidonPermutation<FieldAdapter<M>>, const T: usize>(
    instance: &P,
    parameters: &PoseidonParameters<PastaField<M>, T>,
) {
    assert_eq!(P::T, parameters.width());
    assert_eq!(P::RATE, parameters.rate());
    assert_eq!(P::FULL_ROUNDS, parameters.full_rounds);
    assert_eq!(P::PARTIAL_ROUNDS, parameters.partial_rounds);
    assert_eq!(P::ALPHA, parameters.alpha);
    let rows = instance.round_constants();
    assert_eq!(rows.len(), parameters.rounds());
    // Separate uses of a const table need not share an address.
    for (row, expected) in rows.iter().zip(parameters.round_constants) {
        assert_eq!(row.as_ref(), FieldAdapter::from_slice(expected));
    }
    let mds = instance.mds_matrix();
    assert_eq!(mds.len(), T);
    for (row, expected) in mds.iter().zip(parameters.mds) {
        assert_eq!(row.as_ref(), FieldAdapter::from_slice(expected));
    }
}

#[test]
fn pasta_poseidon_instances_are_the_parameter_constants() {
    let params = params();
    check_poseidon(<Pasta as Cycle>::circuit_poseidon(&params), &PALLAS_BASE);
    check_poseidon(<Pasta as Cycle>::scalar_poseidon(&params), &PALLAS_SCALAR);
    assert_eq!(<Pasta as Cycle>::CircuitPoseidon::default(), PoseidonFp);
}

#[test]
fn cycle_is_usable_through_generic_bounds() {
    fn commit<C: Cycle>(params: &C::Params, value: C::CircuitField) -> C::HostCurve {
        let generators = C::host_generators(params);
        (generators.g()[0] * value + *generators.h() * C::CircuitField::ONE).to_affine()
    }
    fn width<C: Cycle>() -> usize {
        C::CircuitPoseidon::T + C::ScalarPoseidon::RATE
    }
    let params = params();
    let expected = params.vesta().g()[0]
        .as_inner()
        .mul_projective(&Fp::from_u64(9))
        .add(&params.vesta().h().as_inner().to_projective())
        .to_point();
    assert_eq!(
        commit::<Pasta>(&params, FieldAdapter::from(9)).into_inner(),
        expected
    );
    assert_eq!(width::<Pasta>(), 9);
}

#[test]
#[should_panic(expected = "at least one vector generator")]
fn generators_reject_an_empty_vector() {
    let _ = Generators::<Pallas>::new(&[], PallasPoint::GENERATOR);
}

#[test]
#[should_panic(expected = "must not be identity")]
fn generators_reject_identity() {
    static G: [PallasPoint; 2] = [PallasPoint::GENERATOR, PallasPoint::IDENTITY];
    let _ = Generators::<Pallas>::new(&G, PallasPoint::GENERATOR.neg());
}

#[test]
#[should_panic(expected = "must not appear among the vector generators")]
fn generators_reject_a_repeated_blinding_generator() {
    let g = leaked::<Pallas>(3, 1);
    let _ = Generators::<Pallas>::new(g, g[1]);
}

#[test]
fn generator_distinctness_is_reported() {
    let distinct = Generators::new(leaked::<Vesta>(5, 1), leaked::<Vesta>(1, 50)[0]);
    assert!(distinct.are_distinct());
    assert!(Generators::new(leaked::<Vesta>(1, 1), leaked::<Vesta>(1, 50)[0]).are_distinct());

    let points = leaked::<Vesta>(4, 1);
    let repeated: &'static [VestaPoint] =
        Vec::leak(std::vec![points[0], points[1], points[2], points[1]]);
    assert!(!Generators::new(repeated, points[3]).are_distinct());
    // Reaching the same point by another route is still a repeat.
    let same: &'static [VestaPoint] = Vec::leak(std::vec![
        points[0],
        points[1].to_projective().double().to_point(),
        points[1].add(&points[1]).to_point(),
    ]);
    assert!(!Generators::new(same, points[3]).are_distinct());
}

#[test]
fn pasta_cycle_exposes_compatible_endomorphisms() {
    use crate::{
        curve::{EndomorphismAffine, EndomorphismProjective},
        cycle::{Cycle, Pasta},
        field::Field,
    };

    fn check<A: EndomorphismAffine>() {
        for scalar in [A::Scalar::ZERO, A::Scalar::ONE, A::Scalar::from(13)] {
            let point = A::generator() * scalar;
            let affine = point.to_affine();
            assert_eq!(point.endomorphism(), point * A::Scalar::ZETA);
            assert_eq!(affine.endomorphism().to_projective(), point.endomorphism());
            if let Some((x, y)) = affine.coordinates() {
                assert_eq!(y.square(), x.square() * x + A::B);
                assert_eq!(
                    affine.endomorphism().coordinates(),
                    Some((A::Base::ZETA * x, y))
                );
            } else {
                assert!(affine.endomorphism().is_identity());
            }
        }
    }
    fn cycle<C: Cycle>() {
        check::<C::HostCurve>();
        check::<C::NestedCurve>();
    }
    cycle::<Pasta>();
}
