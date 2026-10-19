use num_bigint::BigUint;

use super::*;
use crate::{
    curve::{Pallas, Point, Vesta, pasta::test_reference::Reference},
    field::pasta::test_support::modulus,
};
use std::{vec, vec::Vec};

#[test]
fn affine_reducer_and_weighted_collapse_match_biguint() {
    fn check<C: PastaCurve>() {
        let modulus = modulus::<C::Base>();
        let g = AffinePoint::<C>::GENERATOR;
        let pool: Vec<_> = (1..=13)
            .map(|i| {
                *g.mul_projective(&PastaField::<_>::from_u64(i))
                    .to_point()
                    .as_affine()
                    .unwrap()
            })
            .collect();
        for case in 0..96 {
            let mut points = Vec::new();
            let mut starts = Vec::new();
            let mut lens = Vec::new();
            let mut expected = Vec::new();
            for bucket in 0..7 {
                starts.push(points.len());
                let n = (case * 7 + bucket * 3) % 19;
                lens.push(n);
                let mut sum = Reference::identity();
                for i in 0..n {
                    // Includes all-cancelling levels, odd survivors, and equal
                    // operands alongside distinct points.
                    let mut p = pool[if case % 3 == 0 {
                        bucket
                    } else {
                        (case + i / 2) % pool.len()
                    }];
                    if case % 2 == 0 && i % 2 == 1 {
                        p = p.neg();
                    }
                    sum = sum.add(&Reference::from_point(&p.to_point()), &modulus);
                    points.push(p);
                }
                expected.push(sum);
            }
            let mut control = points.clone();
            let mut control_lens = lens.clone();
            let pairs = points.len() / 2;
            let mut fused = points.clone();
            let mut fused_lens = lens.clone();
            let mut fields = vec![PastaField::ONE; pairs * 2 + 3];
            while fused_lens.iter().any(|&n| n > 1) {
                reduce_fused::<C, false>(
                    &mut fused,
                    &starts,
                    &mut fused_lens,
                    &mut fields[..pairs * 2],
                );
            }
            reduce_original(
                &mut control,
                &starts,
                &mut control_lens,
                &mut vec![PastaField::ZERO; pairs * 6],
                &mut vec![0; pairs],
            );
            reduce(
                &mut points,
                &starts,
                &mut lens,
                &mut vec![PastaField::ONE; pairs * 2 + 2 * (pairs + starts.len())],
                &mut vec![0; starts.len()],
            );
            assert_eq!(lens, control_lens);
            assert_eq!(lens, fused_lens);
            assert!(
                fields[pairs * 2..]
                    .iter()
                    .all(|x| x.reduce() == PastaField::ONE)
            );
            let mut survivors = vec![g; starts.len()];
            let mut weighted = Reference::identity();
            for i in 0..starts.len() {
                let result = if lens[i] == 0 {
                    Point::IDENTITY
                } else {
                    survivors[i] = points[starts[i]];
                    assert_eq!(points[starts[i]], control[starts[i]]);
                    assert_eq!(points[starts[i]], fused[starts[i]]);
                    points[starts[i]].to_point()
                };
                expected[i].assert_point(&result);
                weighted =
                    weighted.add(&expected[i].mul(&BigUint::from(i + 1), &modulus), &modulus);
            }
            weighted.assert_point(&collapse(&survivors, &lens).to_point());
        }
    }
    check::<Pallas>();
    check::<Vesta>();
}

#[test]
fn affine_sums_in_place_match_independent_group_sums() {
    fn check<C: PastaCurve>() {
        let g = AffinePoint::<C>::GENERATOR;
        let mut bank = Vec::new();
        let mut current = ProjectivePoint::<C>::IDENTITY;
        for _ in 0..19 {
            current = current.add_mixed(&g);
            bank.push(*current.to_point().as_affine().unwrap());
        }
        let positive = bank.len();
        for index in 0..positive {
            bank.push(bank[index].neg());
        }
        let modulus = crate::field::pasta::test_support::modulus::<C::Base>();
        for len in [0, 1, 16, 17, 531, 532] {
            for pattern in 0..4 {
                let input: Vec<_> = (0..len)
                    .map(|i| {
                        bank[match pattern {
                            0 => i % positive,
                            1 => 0,
                            2 => {
                                if i % 2 == 0 {
                                    0
                                } else {
                                    positive
                                }
                            }
                            _ => [0, 1, positive, positive + 1][i % 4],
                        }]
                    })
                    .collect();
                let expected = input
                    .iter()
                    .rev()
                    .fold(ProjectivePoint::<C>::IDENTITY, |sum, point| {
                        sum.add(&point.to_projective())
                    });
                if len <= 17 {
                    let reference = input.iter().fold(Reference::identity(), |sum, point| {
                        sum.add(&Reference::from_point(&point.to_point()), &modulus)
                    });
                    reference.assert_point(&expected.to_point());
                }
                for extra in [0, 3] {
                    let mut points = input.clone();
                    points.extend([g; 3]);
                    let sentinel = PastaField::<C::Base>::from_u64(71);
                    let mut fields = vec![sentinel; len + extra];
                    let result = AffinePoint::sum_in_place(&mut points[..len], &mut fields);
                    assert_eq!(result, expected);
                    assert!(points[len..].iter().all(|point| *point == g));
                    assert!(
                        fields[len..].iter().all(|field| {
                            field.montgomery_limbs() == sentinel.montgomery_limbs()
                        })
                    );
                    // Reuse the modified field scratch with restored input points.
                    points[..len].copy_from_slice(&input);
                    assert_eq!(
                        AffinePoint::sum_in_place(&mut points[..len], &mut fields),
                        expected
                    );
                }
            }
        }
    }
    check::<Pallas>();
    check::<Vesta>();
}

#[test]
fn affine_sum_short_scratch_rejection_preserves_both_buffers() {
    fn check<C: PastaCurve>() {
        let g = AffinePoint::<C>::GENERATOR;
        for len in [1, 16, 17, 531, 532] {
            let mut points = vec![g; len + 3];
            let original_points = points.clone();
            let mut fields = vec![PastaField::<C::Base>::from_u64(29); len + 3];
            let original_fields = fields.clone();
            assert!(
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    AffinePoint::sum_in_place(&mut points[..len], &mut fields[..len - 1]);
                }))
                .is_err()
            );
            assert_eq!(
                bento::bytes_of_slice(&points),
                bento::bytes_of_slice(&original_points)
            );
            assert_eq!(
                bento::bytes_of_slice(&fields),
                bento::bytes_of_slice(&original_fields)
            );
        }
    }
    check::<Pallas>();
    check::<Vesta>();
}
