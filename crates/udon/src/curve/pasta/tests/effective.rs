use super::*;
use crate::{
    curve::{
        Pallas, Vesta,
        pasta::{
            eisenstein,
            tests::{multiply, scalar_corpus, scaled},
        },
    },
    field::PrimeModulus,
};
use std::{vec, vec::Vec};

fn ladder<C: PastaCurve>(
    base: &ProjectivePoint<C>,
    value: &PastaField<C::Scalar>,
) -> ProjectivePoint<C> {
    multiply(value, |sum| sum.add(base))
}

fn representatives<C: PastaCurve>() {
    let g = ProjectivePoint::<C>::GENERATOR;
    for multiple in [1, 2, 3, 17, 42] {
        let point = ladder(&g, &PastaField::from_u64(multiple)).to_point();
        for scale in [1, 2, 99, u64::MAX] {
            let base = scaled(&point, scale);
            let mut fields = [PastaField::ZERO; 24];
            let inversions = crate::field::count_inversions(|| {
                EffectiveTable::prepare(&base, &mut fields);
            });
            assert_eq!(inversions, 0);
            let table = EffectiveTable::prepare(&base, &mut fields);
            assert!(!table.denominator.is_zero());
            for (index, &(a, b)) in eisenstein::REPRESENTATIVES.iter().enumerate() {
                let signed = |v: i8| {
                    let p = ladder(&base, &PastaField::from_u64(u64::from(v.unsigned_abs())));
                    if v < 0 { p.neg() } else { p }
                };
                let expected = signed(a).add(&signed(b).endomorphism());
                for unit in 0..6 {
                    let entry = table.digit(super::Digit::from_code((6 * index + unit + 1) as u8));
                    let result = ProjectivePoint {
                        x: entry.x,
                        y: entry.y,
                        z: table.denominator,
                        marker: PhantomData,
                    };
                    let mut expected = expected;
                    for _ in 0..unit / 2 {
                        expected = expected.endomorphism();
                    }
                    if unit & 1 == 1 {
                        expected = expected.neg();
                    }
                    assert_eq!(result, expected);
                    let d2 = table.denominator.square();
                    let d6 = d2.square().mul(&d2);
                    assert_eq!(
                        entry.y.square().reduce(),
                        entry
                            .x
                            .square()
                            .mul(&entry.x)
                            .add(&PastaField::<C::Base>::from_u64(5).mul(&d6))
                            .reduce()
                    );
                }
            }
        }
    }
}

#[test]
fn omitted_denominators_restore_all_representatives() {
    representatives::<Pallas>();
    representatives::<Vesta>();
}

fn loose<M: PrimeModulus>(value: PastaField<M>) -> PastaField<M> {
    let mut limbs = value.reduce().montgomery_limbs();
    let mut carry = 0u128;
    for (limb, modulus) in limbs.iter_mut().zip(M::MODULUS) {
        carry += u128::from(*limb) + u128::from(modulus);
        *limb = carry as u64;
        carry >>= 64;
    }
    assert_eq!(carry, 0);
    PastaField::from_montgomery_limbs(limbs)
}

fn products<C: PastaCurve>() {
    let generator = ProjectivePoint::<C>::GENERATOR;
    let values = scalar_corpus::<C>();
    for base_scalar in values.iter().step_by(5) {
        let base = ladder(&generator, base_scalar).to_point();
        for scale in [1, 19, u64::MAX] {
            let mut p = scaled(&base, scale);
            p.x = loose(p.x);
            p.y = loose(p.y);
            p.z = loose(p.z);
            for scalar in &values {
                let value = loose(*scalar);
                let expected = ladder(&p, &value);
                assert_eq!(
                    crate::field::count_inversions(|| {
                        assert_eq!(p.mul(&value), expected);
                        assert_eq!(base.mul_projective(&value), expected);
                    }),
                    0
                );
            }
        }
    }
}

#[test]
fn public_products_use_no_inversions_and_match_binary_ladders() {
    products::<Pallas>();
    products::<Vesta>();
}

fn exceptions<C: PastaCurve>() {
    let base = ProjectivePoint::<C>::GENERATOR.double();
    let mut storage = [PastaField::ZERO; 24];
    let table = EffectiveTable::prepare(&base, &mut storage);
    let xy = table.digit(super::Digit::from_code(1));
    let p = Jacobian {
        xy,
        z: PastaField::ONE,
    };
    let restore = |v: Jacobian<C>| ProjectivePoint {
        x: v.xy.x,
        y: v.xy.y,
        z: v.z.mul(&table.denominator),
        marker: PhantomData,
    };
    assert_eq!(restore(p.add(xy)), base.double());
    let cancelled = p.add(xy.transform(0, true));
    assert!(restore(cancelled).is_identity());
    assert!(restore(cancelled.double()).is_identity());
    assert_eq!(restore(cancelled.add(xy)), base);
    assert_eq!(restore(cancelled.double().add(xy)), base);
}

#[test]
fn private_ladder_handles_equal_inverse_and_identity_additions() {
    exceptions::<Pallas>();
    exceptions::<Vesta>();
}

fn batches<C: PastaCurve>() {
    use crate::exec::SerialExecutor;
    let g = ProjectivePoint::<C>::GENERATOR;
    for n in [32, 33, 65] {
        let inputs: Vec<_> = (0..n)
            .map(|i| {
                let p = ladder(&g, &PastaField::from_u64(i as u64)).to_point();
                scaled(&p, i as u64 + 17)
            })
            .collect();
        for scalar in scalar_corpus::<C>().iter().step_by(7) {
            let expected: Vec<_> = inputs.iter().map(|p| ladder(p, scalar)).collect();
            let prepared = EisensteinScalar::new(scalar);
            let mut fields = vec![PastaField::ONE; same_scalar_scratch::<C>(n).unwrap()];
            let mut result = inputs.clone();
            let inversions = crate::field::count_inversions(|| {
                batch_mul_same_scalar_prepared(
                    &mut result,
                    &prepared,
                    &mut fields,
                    TaskBudget::SERIAL,
                    &SerialExecutor,
                );
            });
            assert_eq!(result, expected);
            assert_eq!(inversions, prepared.digits().len().saturating_sub(1));
            result.copy_from_slice(&inputs);
            assert_eq!(
                crate::field::count_inversions(|| {
                    batch_mul_same_scalar_prepared(
                        &mut result,
                        &prepared,
                        &mut [],
                        TaskBudget::SERIAL,
                        &SerialExecutor,
                    );
                }),
                0
            );
            assert_eq!(result, expected);
        }
    }
}

#[test]
fn batches_restore_scaled_inputs_and_share_only_ladder_inversions() {
    batches::<Pallas>();
    batches::<Vesta>();
}
