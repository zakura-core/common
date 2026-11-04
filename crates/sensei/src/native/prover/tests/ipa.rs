//! IPA challenge handling and folds against materialized reference calculations.

use crate::Error;
use crate::native::prover;
use crate::native::test_support::reduced_values;
use alloc::{sync::Arc, vec::Vec};

/// The retry-on-zero policy: a zero challenge asks for fresh randomness,
/// anything else inverts exactly.
#[test]
fn ipa_challenge_inversion_retries_on_zero() {
    use crate::native::field::Fp;
    assert_eq!(
        prover::ipa::invert_ipa_challenge(&<Fp>::ZERO).err(),
        Some(Error::RetryRandomness)
    );
    for value in [<Fp>::ONE, <Fp>::from_u64(7), <Fp>::ONE.neg()] {
        let inverse = prover::ipa::invert_ipa_challenge(&value).unwrap();
        assert_eq!((value.mul(&inverse)).reduce(), (<Fp>::ONE).reduce());
    }
}

#[test]
fn ipa_evaluation_subtraction_matches_horner() {
    use crate::native::polynomial::evaluate;
    use prover::ipa::subtract_ipa_evaluation;
    use prover::{Fp, N};

    let mut boundary_terms = alloc::vec![<Fp>::ZERO; N];
    for index in [0, N / 2 - 1, N / 2, N - 1] {
        boundary_terms[index] = <Fp>::from_u64(index as u64 + 3);
    }
    let dense = (0..N)
        .map(|index| {
            <Fp>::from_u64(
                (index as u64)
                    .wrapping_mul(0xd6e8_feb8_6659_fd93)
                    .wrapping_add(17),
            )
            .square()
        })
        .collect::<Vec<_>>();
    for coefficients in [alloc::vec![<Fp>::ZERO; N], boundary_terms, dense] {
        for point in [
            <Fp>::ZERO,
            <Fp>::ONE,
            <Fp>::ONE.neg(),
            <Fp>::from_u64(29).square(),
            <Fp>::from_u64(0xa5a5_5a5a_1234_5678).neg(),
        ] {
            let expected_evaluation = evaluate(&coefficients, &point);
            let mut actual = coefficients.clone();
            let (powers, x_to_half) =
                subtract_ipa_evaluation(crate::test_codec::execution(), &mut actual, &point)
                    .unwrap();
            assert_eq!(
                actual[0].reduce(),
                coefficients[0].sub(&expected_evaluation).reduce()
            );
            assert_eq!(
                reduced_values(&actual[1..]),
                reduced_values(&coefficients[1..])
            );
            assert!(evaluate(&actual, &point).is_zero());

            assert_eq!(powers.len(), N / 2);
            let mut expected_power = <Fp>::ONE;
            for power in powers {
                assert_eq!(power.reduce(), expected_power.reduce());
                expected_power = expected_power.mul(&point);
            }
            assert_eq!(x_to_half.reduce(), expected_power.reduce());
        }
    }

    for length in [0, N - 1, N + 1] {
        let mut invalid = alloc::vec![<Fp>::ONE; length];
        assert_eq!(
            subtract_ipa_evaluation(crate::test_codec::execution(), &mut invalid, &<Fp>::ONE).err(),
            Some(Error::InternalInvariant)
        );
        assert!(invalid.iter().all(Fp::is_one));
    }
}

#[test]
fn virtual_generator_folds_match_materialized_ipa_rounds() {
    use crate::native::commitment::sum_prepared;
    use crate::native::curve::{PreparedAffinePoint, VestaAffine, VestaPoint};
    use prover::Fp;
    use prover::ipa::VirtualGeneratorFold;

    fn run_schedule(count: usize, rounds: usize) {
        let generator = VestaPoint::GENERATOR;
        let affine_bases: Vec<VestaAffine> = (0..count as u64)
            .map(|index| {
                // Duplicate one base so MSM buckets add equal points.
                let multiplier = if index == 7 {
                    3 * 17 + 3
                } else {
                    index * 17 + 3
                };
                *generator
                    .mul_projective(&<Fp>::from_u64(multiplier))
                    .to_point()
                    .as_affine()
                    .expect("nonzero multiples of the generator are nonidentity")
            })
            .collect();
        let bases = affine_bases
            .iter()
            .copied()
            .map(|point| PreparedAffinePoint::from_affine(&point))
            .collect::<Vec<_>>();
        let challenges = [
            <Fp>::ONE,
            <Fp>::from_u64(0xd6e8_feb8_6659_fd93).square(),
            <Fp>::ZERO,
            <Fp>::ONE.neg(),
            <Fp>::from_u64(29).invert().unwrap(),
            <Fp>::from_u64(0xa5a5_5a5a_1234_5678).square().neg(),
        ];

        let mut materialized: Vec<VestaPoint> =
            affine_bases.iter().map(|base| base.to_point()).collect();
        let mut virtual_fold = VirtualGeneratorFold::new(bases.len());
        let powers = Arc::new(
            (0..count / 2)
                .map(|index| <Fp>::from_u64(index as u64 * 7 + 3).square())
                .collect::<Vec<_>>(),
        );
        let mut seed = 1u64;
        for round in 0..rounds {
            let half = materialized.len() / 2;
            assert!(half >= 1);
            let p_prime: Vec<Fp> = (0..2 * half)
                .map(|index| {
                    seed = seed
                        .wrapping_mul(6364136223846793005)
                        .wrapping_add(1442695040888963407);
                    match index % 5 {
                        0 => <Fp>::ZERO,
                        1 => <Fp>::from_u64(seed),
                        _ => <Fp>::from_u64(seed).square().neg(),
                    }
                })
                .collect();

            let explicit_sum = |scalars: &[Fp], points: &[VestaPoint]| {
                scalars
                    .iter()
                    .zip(points)
                    .fold(VestaPoint::IDENTITY, |sum, (scalar, base)| {
                        sum.add(&base.mul_projective(scalar).to_point()).to_point()
                    })
            };
            let expected_left = explicit_sum(&p_prime[half..], &materialized[..half]);
            let expected_right = explicit_sum(&p_prime[..half], &materialized[half..]);

            // Each round's polynomial is fresh here (no polynomial fold), so
            // the preparation returns it unchanged with its upper inner
            // product; the coefficient fold is the pending challenge's.
            let prepared = virtual_fold
                .prepare_round(
                    crate::test_codec::execution(),
                    p_prime.clone(),
                    None,
                    half,
                    &powers,
                )
                .unwrap();
            assert_eq!(
                reduced_values(&(prepared.polynomial)),
                reduced_values(&(p_prime))
            );
            let expected_upper = (0..half).fold(<Fp>::ZERO, |sum, index| {
                sum.add(&p_prime[index + half].mul(&powers[index]))
            });
            assert_eq!(
                (prepared.upper_inner_product).reduce(),
                (expected_upper).reduce()
            );
            assert_eq!(virtual_fold.left_indices.len(), count / 2);
            assert_eq!(virtual_fold.right_indices.len(), count / 2);
            let gather = |indices: &[u32]| {
                indices
                    .iter()
                    .map(|&index| bases[index as usize])
                    .collect::<Vec<_>>()
            };
            let actual_left = sum_prepared(
                &gather(&virtual_fold.left_indices),
                &virtual_fold.left_scalars,
            )
            .unwrap()
            .to_point();
            let actual_right = sum_prepared(
                &gather(&virtual_fold.right_indices),
                &virtual_fold.right_scalars,
            )
            .unwrap()
            .to_point();
            assert_eq!(actual_left, expected_left, "L round {round} count {count}");
            assert_eq!(
                actual_right, expected_right,
                "R round {round} count {count}"
            );

            let challenge = challenges[round % challenges.len()];
            for index in 0..half {
                materialized[index] = materialized[index]
                    .add(
                        &materialized[index + half]
                            .mul_projective(&challenge)
                            .to_point(),
                    )
                    .to_point();
            }
            materialized.truncate(half);
            virtual_fold.apply_challenge(&challenge, half);
        }
    }

    // Full depth through the interleaved and serial windowed MSM paths,
    // then the parallel windowed path for the widest rounds.
    run_schedule(16, 4);
    run_schedule(64, 6);
    run_schedule(512, 3);
}

/// The round preparation's deferred polynomial fold: with a pending
/// challenge inverse the previous polynomial (twice the round's length) is
/// folded into the round's polynomial, the staged scalars read the folded
/// values, the inner product is the folded upper half's, and the staging
/// order is ascending generator order across every chunk.
#[test]
fn round_preparation_folds_the_previous_polynomial() {
    use prover::Fp;
    use prover::ipa::VirtualGeneratorFold;

    for (count, half) in [(16usize, 4usize), (16, 1), (64, 8), (2048, 512), (2048, 1)] {
        let mut virtual_fold = VirtualGeneratorFold::new(count);
        let inverse = <Fp>::from_u64(0x9e37_79b9_7f4a_7c15).square();
        let challenge = <Fp>::from_u64(0x1234_5678).neg();
        let previous = (0..4 * half)
            .map(|index| <Fp>::from_u64(index as u64 * 0x5851_f42d + 11).square())
            .collect::<Vec<_>>();
        let powers = Arc::new(
            (0..half)
                .map(|index| <Fp>::from_u64(index as u64 + 5))
                .collect::<Vec<_>>(),
        );
        // A pending challenge over the previous split scales the
        // coefficients of the generators whose `2 * half` bit is set.
        virtual_fold.apply_challenge(&challenge, 2 * half);
        let prepared = virtual_fold
            .prepare_round(
                crate::test_codec::execution(),
                previous.clone(),
                Some(inverse),
                half,
                &powers,
            )
            .unwrap();
        let expected: Vec<Fp> = (0..2 * half)
            .map(|index| previous[index].add(&inverse.mul(&previous[index + 2 * half])))
            .collect();
        assert_eq!(
            reduced_values(&(prepared.polynomial)),
            reduced_values(&(expected))
        );
        let expected_upper = (0..half).fold(<Fp>::ZERO, |sum, index| {
            sum.add(&expected[index + half].mul(&powers[index]))
        });
        assert_eq!(
            (prepared.upper_inner_product).reduce(),
            (expected_upper).reduce()
        );
        assert_eq!(virtual_fold.left_indices.len(), count / 2);
        assert_eq!(virtual_fold.right_indices.len(), count / 2);
        assert!(
            virtual_fold
                .left_indices
                .windows(2)
                .all(|pair| pair[0] < pair[1])
        );
        assert!(
            virtual_fold
                .right_indices
                .windows(2)
                .all(|pair| pair[0] < pair[1])
        );
        for (side, indices, scalars) in [
            (
                0usize,
                &virtual_fold.left_indices,
                &virtual_fold.left_scalars,
            ),
            (1, &virtual_fold.right_indices, &virtual_fold.right_scalars),
        ] {
            for (&m, scalar) in indices.iter().zip(scalars.iter()) {
                let m = m as usize;
                assert_eq!(usize::from(m & half != 0), side);
                let coefficient = if m & (2 * half) != 0 {
                    challenge
                } else {
                    <Fp>::ONE
                };
                let folded_index = m & (half - 1);
                let value = if side == 0 {
                    expected[folded_index + half]
                } else {
                    expected[folded_index]
                };
                assert_eq!(
                    (*scalar).reduce(),
                    (coefficient.mul(&value)).reduce(),
                    "generator {m}"
                );
            }
        }
        // Wrong polynomial lengths are rejected.
        assert!(
            virtual_fold
                .prepare_round(
                    crate::test_codec::execution(),
                    alloc::vec![ <Fp>::ZERO; 2 * half],
                    Some(inverse),
                    half,
                    &powers
                )
                .is_err()
        );
    }
}

#[test]
fn zero_ipa_folding_challenge_requires_fresh_randomness() {
    assert_eq!(
        reduced_values(&(prover::ipa::invert_ipa_challenge(&<prover::Fp>::ZERO))),
        Err(Error::RetryRandomness)
    );
    assert_eq!(
        reduced_values(&(prover::ipa::invert_ipa_challenge(&<prover::Fp>::ONE))),
        reduced_values(&(Ok(<prover::Fp>::ONE)))
    );
}
