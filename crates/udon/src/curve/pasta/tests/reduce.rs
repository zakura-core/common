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

fn collapse_points<C: PastaCurve>() -> Vec<AffinePoint<C>> {
    let mut state = 0x9e37_79b9_7f4a_7c15_u64;
    (0..128)
        .map(|_| {
            // Full-width loose Montgomery scalars; both Pasta fields have 2p
            // above 2^255. Point generation is outside the collapse oracle.
            let mut limbs = core::array::from_fn(|_| {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                state
            });
            limbs[3] &= (1_u64 << 63) - 1;
            let scalar = PastaField::<C::Scalar>::from_montgomery_limbs(limbs);
            assert!(!scalar.is_zero());
            *AffinePoint::<C>::GENERATOR
                .mul_projective(&scalar)
                .to_point()
                .as_affine()
                .unwrap()
        })
        .collect()
}

#[test]
fn four_front_weighted_collapse_matches_biguint() {
    fn check<C: PastaCurve>() {
        let original = collapse_points::<C>();
        let p = modulus::<C::Base>();
        let g = AffinePoint::<C>::GENERATOR;
        // Reuse the same work through nonempty, empty and cancelling cases.
        // Extra entries are sentinels beyond each documented capacity.
        let mut scratch = vec![g; 450];
        let mut fields = vec![PastaField::ONE; 578];
        let mut starts = vec![usize::MAX; 98];
        let mut loose_starts = vec![usize::MAX; 98];
        let dense_expected = collapse(&original, &[1; 128]);
        for case in 0..9 {
            let mut points = original.clone();
            let mut occupied = vec![1; 128];
            match case {
                0 => (),                      // Dense 128 buckets.
                1 => occupied[111..].fill(0), // GLV top-window bound.
                2 => {
                    for (i, len) in occupied.iter_mut().enumerate() {
                        *len = usize::from(i % 7 == 0 || i == 127);
                    }
                }
                3 => occupied.fill(0),
                4 => {
                    occupied.fill(0);
                    occupied[127] = 1;
                }
                5 => {
                    for pair in points.chunks_exact_mut(2) {
                        pair[1] = pair[0];
                    }
                }
                6 => {
                    for pair in points.chunks_exact_mut(2) {
                        pair[1] = pair[0].neg();
                    }
                }
                7 => {
                    for group in points.chunks_exact_mut(4) {
                        group[2] = group[0].neg();
                        group[3] = group[1].neg();
                    }
                }
                8 => {
                    for group in points.chunks_exact_mut(16) {
                        for i in 0..8 {
                            group[i + 8] = group[i].neg();
                        }
                    }
                }
                _ => unreachable!(),
            }
            // Independent ordinary-residue arithmetic, weighting each input
            // directly instead of reproducing either collapse recurrence.
            let mut expected = Reference::identity();
            for (i, (point, &len)) in points.iter().zip(&occupied).enumerate() {
                if len != 0 {
                    let term = Reference::from_point(&point.to_point());
                    expected = expected.add(&term.mul(&BigUint::from(i + 1), &p), &p);
                }
            }
            expected.assert_point(&collapse(&points, &occupied).to_point());
            for repeat in 0..2 {
                let mut lengths = occupied.clone();
                let actual = collapse_with_scratch(
                    &points,
                    &mut lengths,
                    &mut scratch,
                    &mut fields,
                    &mut starts,
                    &mut loose_starts,
                );
                expected.assert_point(&actual.to_point());
                assert_eq!(&scratch[448..], &[g; 2]);
                assert!(
                    fields[576..]
                        .iter()
                        .all(|x| x.montgomery_limbs()
                            == PastaField::<C::Base>::ONE.montgomery_limbs())
                );
                assert_eq!(&starts[96..], &[usize::MAX; 2]);
                assert_eq!(&loose_starts[96..], &[usize::MAX; 2]);
                if repeat == 0 {
                    // Overwrite work with dense data before repeating the
                    // original sparse/cancelling input, exposing stale flags.
                    assert_eq!(
                        collapse_with_scratch(
                            &original,
                            &mut [1; 128],
                            &mut scratch,
                            &mut fields,
                            &mut starts,
                            &mut loose_starts,
                        ),
                        dense_expected
                    );
                }
            }
        }
    }
    check::<Pallas>();
    check::<Vesta>();
}

#[test]
fn four_front_weighted_collapse_falls_back_with_short_scratch() {
    fn check<C: PastaCurve>() {
        let points = collapse_points::<C>();
        let g = AffinePoint::<C>::GENERATOR;
        let mut scratch = vec![g; 448];
        let mut fields = vec![PastaField::ONE; 576];
        let mut starts = vec![usize::MAX; 96];
        let mut loose_starts = vec![usize::MAX; 96];
        for case in 0..5 {
            let n = if case == 4 { 127 } else { 128 };
            let mut occupied = vec![1; n];
            let affine_len = if case == 0 { 447 } else { 448 };
            let field_len = if case == 1 { 575 } else { 576 };
            let starts_len = if case == 2 { 95 } else { 96 };
            let loose_len = if case == 3 { 95 } else { 96 };
            assert_eq!(
                collapse_with_scratch(
                    &points[..n],
                    &mut occupied,
                    &mut scratch[..affine_len],
                    &mut fields[..field_len],
                    &mut starts[..starts_len],
                    &mut loose_starts[..loose_len],
                ),
                collapse(&points[..n], &vec![1; n])
            );
            assert_eq!(occupied, vec![1; n]);
            assert!(scratch.iter().all(|point| *point == g));
            assert!(
                fields.iter().all(|field| field.montgomery_limbs()
                    == PastaField::<C::Base>::ONE.montgomery_limbs())
            );
            assert!(starts.iter().all(|&index| index == usize::MAX));
            assert!(loose_starts.iter().all(|&index| index == usize::MAX));
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
