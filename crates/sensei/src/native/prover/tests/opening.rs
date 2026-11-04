//! Opening plans, evaluations, and folds against independent references.

use super::ONE_ACTION_FIXTURE;
use crate::Error;
use crate::native::prover;
use crate::native::test_support::reduced_values;
use crate::types::ProvingRequest;
use alloc::{sync::Arc, vec::Vec};

#[test]
fn opening_source_census_matches_frozen_target() {
    use crate::native::evaluation::rotated_evaluation_point;
    use prover::opening::{
        GroupedOpenings, OpeningPolynomial, OpeningQuery, OpeningSource, group_opening_queries,
        opening_query_plan,
    };
    use prover::{Fp, N};

    let target = crate::test_codec::target();
    let x = <Fp>::from_u64(7);
    let x_next = rotated_evaluation_point(&x, target.domain().omega(), 1);
    let x_previous = rotated_evaluation_point(&x, target.domain().omega_inverse(), 1);
    let x_last = rotated_evaluation_point(
        &x,
        target.domain().omega_inverse(),
        crate::native::target::BLINDING_FACTORS + 1,
    );
    let coefficient_bytes = N * core::mem::size_of::<Fp>();
    assert_eq!(coefficient_bytes, 65_536);

    // Counts are in first-seen point-set order. The lifetime classes are
    // prepared fixed/sigma forms, dynamic forms already needed by an
    // evaluation or commitment, and the opening-only quotient fold. The
    // quotient is folded rather than scanned, and the linear vanishing
    // mask evaluates as one multiply-add, and sparse instances use shared
    // Lagrange weights, so none of these counts as an evaluation scan.
    for (
        action_count,
        expected_groups,
        expected_query_count,
        expected_evaluation_scans,
        expected_lifetimes,
        expected_collapse_bytes,
        expected_evaluation_bytes,
    ) in [
        (
            1,
            [50, 9, 5, 2, 3],
            95,
            92,
            [44, 23, 1],
            4_456_448,
            6_029_312,
        ),
        (
            2,
            [54, 18, 10, 4, 6],
            144,
            140,
            [44, 45, 1],
            5_898_240,
            9_175_040,
        ),
    ] {
        let plan = opening_query_plan(target, action_count, &x).unwrap();
        assert_eq!(plan.len(), expected_query_count);
        let evaluation_scans = plan
            .iter()
            .filter(|query| {
                !matches!(
                    query.polynomial,
                    OpeningPolynomial::Quotient
                        | OpeningPolynomial::Vanishing
                        | OpeningPolynomial::Instance(_)
                )
            })
            .count();
        assert_eq!(evaluation_scans, expected_evaluation_scans);
        assert_eq!(
            evaluation_scans * coefficient_bytes,
            expected_evaluation_bytes
        );

        let coefficients = prover::SharedPoly::new(alloc::vec![ <Fp>::ZERO; N]);
        let queries = plan
            .into_iter()
            .map(|planned| OpeningQuery {
                polynomial: planned.polynomial,
                source: OpeningSource::Coefficients(prover::PolySource::Arc(coefficients.clone())),
                blind: <Fp>::ONE,
                point: planned.point,
            })
            .collect();
        let GroupedOpenings {
            point_sets,
            commitments,
            polynomial_groups,
        } = group_opening_queries(queries).unwrap();
        assert_eq!(
            reduced_values(&(point_sets)),
            reduced_values(
                &(alloc::vec![
                    alloc::vec![x],
                    alloc::vec![x, x_next],
                    alloc::vec![x, x_next, x_previous],
                    alloc::vec![x, x_next, x_last],
                    alloc::vec![x, x_previous],
                ])
            )
        );
        assert_eq!(
            polynomial_groups.iter().map(Vec::len).collect::<Vec<_>>(),
            expected_groups
        );

        let mut lifetime_counts = [0usize; 3];
        for commitment in &commitments {
            let class = match commitment.polynomial {
                OpeningPolynomial::Instance(_) => continue,
                OpeningPolynomial::Fixed(_) | OpeningPolynomial::Sigma(_) => 0,
                OpeningPolynomial::Quotient => 2,
                _ => 1,
            };
            lifetime_counts[class] += 1;
        }
        assert_eq!(lifetime_counts, expected_lifetimes);

        // Logical full-length source bytes excluding instances. The quotient
        // fold and vanishing mask count as one polynomial apiece here; this
        // census is not a count of physical coefficient or basis reads.
        let collapse_bytes = polynomial_groups
            .iter()
            .map(|group| {
                group
                    .iter()
                    .filter(|&&index| {
                        !matches!(
                            commitments[index].polynomial,
                            OpeningPolynomial::Instance(_)
                        )
                    })
                    .count()
                    * coefficient_bytes
            })
            .collect::<Vec<_>>();
        assert_eq!(
            collapse_bytes.iter().sum::<usize>(),
            expected_collapse_bytes
        );
        // Each point set materializes and retains one Q_i, clones one Q_i
        // for division, and later scans one Q_i for its transcript value.
        assert_eq!(point_sets.len() * coefficient_bytes, 327_680);
    }
}

/// The group's members for `action_count` Actions as the dynamic
/// construction names them, in fold order.
fn expanded_opening_polynomials(
    group: &prover::opening_schedule::OpeningGroup,
    action_count: usize,
) -> Vec<prover::opening::OpeningPolynomial> {
    use prover::opening::OpeningPolynomial;
    use prover::opening_schedule::{ActionPolynomial, FixedPolynomial};
    let mut polynomials = Vec::with_capacity(group.len(action_count));
    for action_index in 0..action_count {
        for polynomial in group.per_action() {
            polynomials.push(match *polynomial {
                ActionPolynomial::Instance => OpeningPolynomial::Instance(action_index),
                ActionPolynomial::Advice(column) => {
                    OpeningPolynomial::Advice(action_index, column as usize)
                }
                ActionPolynomial::Permutation(set) => {
                    OpeningPolynomial::Permutation(action_index, set as usize)
                }
                ActionPolynomial::LookupProduct(lookup) => {
                    OpeningPolynomial::LookupProduct(action_index, lookup as usize)
                }
                ActionPolynomial::LookupInput(lookup) => {
                    OpeningPolynomial::LookupInput(action_index, lookup as usize)
                }
                ActionPolynomial::LookupTable(lookup) => {
                    OpeningPolynomial::LookupTable(action_index, lookup as usize)
                }
            });
        }
    }
    for polynomial in group.fixed() {
        polynomials.push(match *polynomial {
            FixedPolynomial::Fixed(column) => OpeningPolynomial::Fixed(column as usize),
            FixedPolynomial::Sigma(column) => OpeningPolynomial::Sigma(column as usize),
            FixedPolynomial::Quotient => OpeningPolynomial::Quotient,
            FixedPolynomial::Vanishing => OpeningPolynomial::Vanishing,
        });
    }
    polynomials
}

/// The compile-time opening schedule reproduces the dynamic first-appearance
/// grouping — the point sets, their order, and every set's fold order — for
/// several Action counts and evaluation points, and the coincident-point case
/// the stage rejects is one the dynamic construction rejected too.
#[test]
fn generated_opening_schedule_matches_dynamic_grouping() {
    use crate::native::evaluation::rotated_query_point;
    use prover::opening::{
        GroupedOpenings, OpeningPolynomial, OpeningQuery, OpeningSource, group_opening_queries,
        opening_query_plan,
    };
    use prover::opening_schedule::{
        ACTION_COMMITMENTS, FIXED_COMMITMENTS, OPENING_GROUPS, OPENING_POINTS, OPENING_ROTATIONS,
    };
    use prover::{Fp, N, PolySource, SharedPoly};

    let target = crate::test_codec::target();
    let mut seed = <Fp>::from_u64(0x9e37_79b9_7f4a_7c15);
    for action_count in 1..=3 {
        for _ in 0..3 {
            seed = seed.square().add(&<Fp>::from_u64(action_count as u64));
            let x = seed;
            let plan = opening_query_plan(target, action_count, &x).unwrap();
            // One distinct buffer and blind per polynomial, so the dynamic
            // grouping's identity checks are exercised.
            let mut sources: Vec<(OpeningPolynomial, SharedPoly, Fp)> = Vec::new();
            let queries = plan
                .into_iter()
                .map(|planned| {
                    let index = match sources
                        .iter()
                        .position(|(polynomial, _, _)| *polynomial == planned.polynomial)
                    {
                        Some(index) => index,
                        None => {
                            sources.push((
                                planned.polynomial,
                                SharedPoly::new(alloc::vec![ <Fp>::ZERO; N]),
                                <Fp>::from_u64(sources.len() as u64 + 1),
                            ));
                            sources.len() - 1
                        }
                    };
                    let (_, coefficients, blind) = &sources[index];
                    OpeningQuery {
                        polynomial: planned.polynomial,
                        source: OpeningSource::Coefficients(PolySource::Arc(coefficients.clone())),
                        blind: *blind,
                        point: planned.point,
                    }
                })
                .collect::<Vec<_>>();
            let GroupedOpenings {
                point_sets,
                commitments,
                polynomial_groups,
            } = group_opening_queries(queries).unwrap();
            assert_eq!(
                commitments.len(),
                action_count * ACTION_COMMITMENTS + FIXED_COMMITMENTS
            );
            assert_eq!(point_sets.len(), OPENING_GROUPS.len());
            let points: [Fp; OPENING_POINTS] =
                core::array::from_fn(|id| rotated_query_point(target, &x, OPENING_ROTATIONS[id]));
            for (group, (dynamic_points, members)) in OPENING_GROUPS
                .iter()
                .zip(point_sets.iter().zip(&polynomial_groups))
            {
                assert_eq!(
                    reduced_values(dynamic_points),
                    reduced_values(&(group.point_ids().map(|id| points[id]).collect::<Vec<_>>()))
                );
                assert_eq!(members.len(), group.len(action_count));
                let dynamic_members = members
                    .iter()
                    .map(|&index| commitments[index].polynomial)
                    .collect::<Vec<_>>();
                assert_eq!(
                    dynamic_members,
                    expanded_opening_polynomials(group, action_count)
                );
            }
        }
    }

    // `x = 0` makes every rotated point coincide: the dynamic construction
    // found a polynomial opened twice at one point and failed, and the stage
    // now rejects the coincident points up front.
    let plan = opening_query_plan(target, 1, &<Fp>::ZERO).unwrap();
    let coefficients = SharedPoly::new(alloc::vec![ <Fp>::ZERO; N]);
    let queries = plan
        .into_iter()
        .map(|planned| OpeningQuery {
            polynomial: planned.polynomial,
            source: OpeningSource::Coefficients(PolySource::Arc(coefficients.clone())),
            blind: <Fp>::ONE,
            point: planned.point,
        })
        .collect();
    assert!(group_opening_queries(queries).is_err());
}

#[test]
fn cached_deferred_evaluations_match_horner_evaluations() {
    let coefficients = (0..prover::N)
        .map(|index| {
            <prover::Fp>::from_u64(
                (index as u64)
                    .wrapping_mul(0xd6e8_feb8_6659_fd93)
                    .wrapping_add(17),
            )
            .square()
        })
        .collect::<Vec<_>>();
    let points = [
        <prover::Fp>::ZERO,
        <prover::Fp>::ONE,
        <prover::Fp>::ONE.neg(),
        <prover::Fp>::from_u64(3),
        <prover::Fp>::from_u64(29).square(),
        <prover::Fp>::from_u64(0xa5a5_5a5a_1234_5678).neg(),
    ];
    let mut cache = prover::EvaluationPowerCache::new();
    for (index, point) in points.iter().enumerate() {
        assert_eq!(
            (cache.evaluate(&coefficients, point).unwrap()).reduce(),
            (crate::native::polynomial::evaluate(&coefficients, point)).reduce()
        );
        assert_eq!(cache.entries.len(), index + 1);
        assert_eq!(
            (cache.evaluate(&coefficients, point).unwrap()).reduce(),
            (crate::native::polynomial::evaluate(&coefficients, point)).reduce()
        );
        assert_eq!(cache.entries.len(), index + 1);
    }
    assert_eq!(
        reduced_values(&(cache.evaluate(&coefficients[..prover::N - 1], &points[0]))),
        Err(Error::InternalInvariant)
    );
}

#[test]
fn parallel_evaluations_match_cached_serial_order() {
    let polynomials = (0..17u64)
        .map(|polynomial| {
            (0..prover::N)
                .map(|index| {
                    <prover::Fp>::from_u64(
                        (index as u64)
                            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                            .wrapping_add(polynomial * 31 + 7),
                    )
                    .square()
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let points = [
        <prover::Fp>::from_u64(3),
        <prover::Fp>::from_u64(29).square(),
        <prover::Fp>::from_u64(0xa5a5_5a5a_1234_5678).neg(),
    ];
    let mut cache = prover::EvaluationPowerCache::new();
    let expected = polynomials
        .iter()
        .enumerate()
        .map(|(index, polynomial)| cache.evaluate(polynomial, &points[index % 3]).unwrap())
        .collect::<Vec<_>>();
    let jobs = polynomials
        .iter()
        .enumerate()
        .map(|(index, polynomial)| prover::EvaluationJob {
            coefficients: prover::EvaluationSource::Dense(prover::PolySource::Arc(
                prover::SharedPoly::new(polynomial.clone()),
            )),
            point: points[index % 3],
        })
        .collect();
    assert_eq!(
        reduced_values(
            &(prover::parallel_evaluate_polynomials(crate::test_codec::execution(), jobs).unwrap())
        ),
        reduced_values(&(expected))
    );
    assert_eq!(
        reduced_values(
            &(prover::parallel_evaluate_polynomials(
                crate::test_codec::execution(),
                alloc::vec![prover::EvaluationJob {
                    coefficients: prover::EvaluationSource::Dense(prover::PolySource::Arc(
                        prover::SharedPoly::new(polynomials[0][..prover::N - 1].to_vec())
                    )),
                    point: points[0],
                }]
            ))
        ),
        Err(Error::InternalInvariant)
    );

    // The linear mask evaluates exactly as its zero-padded dense form.
    let mask = [
        <prover::Fp>::from_u64(41).square(),
        <prover::Fp>::from_u64(43).square(),
    ];
    let mut padded = alloc::vec![ <prover::Fp>::ZERO; prover::N];
    padded[..2].copy_from_slice(&mask);
    assert_eq!(
        reduced_values(
            &(prover::parallel_evaluate_polynomials(
                crate::test_codec::execution(),
                alloc::vec![prover::EvaluationJob {
                    coefficients: prover::EvaluationSource::Linear(mask),
                    point: points[1],
                }]
            )
            .unwrap())
        ),
        reduced_values(&(alloc::vec![cache.evaluate(&padded, &points[1]).unwrap()]))
    );
}

/// Instance prefixes combine before expansion, including unequal anchors,
/// zero/cancelling weights and groups containing only instance sources.
#[test]
fn sparse_instance_openings_match_dense_horner_collapse() {
    use prover::opening::{
        OpeningSource, WeightedGroup, deferred_horner_polynomial_fold, parallel_weighted_sums,
        push_weighted_source,
    };
    use prover::{Fp, N, PolySource, SharedPoly};

    let request = ProvingRequest::decode_iwpr_for_test(ONE_ACTION_FIXTURE).unwrap();
    let statements: Arc<[_]> = (0..4)
        .map(|i| {
            let mut statement = request.actions()[0].statement.clone();
            statement.anchor =
                crate::Fp::from_bytes(<Fp>::from_u64(17 + i * 31).square().to_bytes()).unwrap();
            statement.enable_spend = i % 2 == 0;
            statement.enable_output = i % 3 == 0;
            statement.native()
        })
        .collect::<Vec<_>>()
        .into();
    let dense_instances = statements
        .iter()
        .map(|statement| {
            let mut coefficients = statement.instance_column(N);
            assert!(crate::native::polynomial::ifft(&mut coefficients));
            coefficients
        })
        .collect::<Vec<_>>();
    let leading = (0..N)
        .map(|i| <Fp>::from_u64((i * 7 + 3) as u64).square())
        .collect::<Vec<_>>();
    let mask = [Fp::from_u64(41), Fp::from_u64(43)];
    let mut trailing = alloc::vec![Fp::ZERO; N];
    trailing[..2].copy_from_slice(&mask);
    for count in 1..=4 {
        for challenge in [
            Fp::ZERO,
            Fp::ONE,
            <Fp>::ONE.neg(),
            <Fp>::from_u64(59).square(),
        ] {
            for mixed in [false, true] {
                let mut sources = Vec::new();
                let mut dense_sources = Vec::new();
                if mixed {
                    sources.push(OpeningSource::Coefficients(PolySource::Arc(
                        SharedPoly::new(leading.clone()),
                    )));
                    dense_sources.push(leading.as_slice());
                }
                for (index, dense) in dense_instances.iter().enumerate().take(count) {
                    sources.push(OpeningSource::Instance {
                        statements: Arc::clone(&statements),
                        index,
                    });
                    dense_sources.push(dense.as_slice());
                }
                if mixed {
                    sources.push(OpeningSource::Linear(mask));
                    dense_sources.push(trailing.as_slice());
                }
                let expected = deferred_horner_polynomial_fold(&dense_sources, &challenge).unwrap();
                let mut group = WeightedGroup {
                    dense: Vec::new(),
                    sparse: Vec::new(),
                    instance: None,
                };
                let source_count = sources.len();
                for (index, source) in sources.into_iter().enumerate() {
                    let weight = challenge.pow_u64((source_count - 1 - index) as u64);
                    push_weighted_source(&mut group, source, &weight, &Fp::ONE).unwrap();
                }
                assert_eq!(group.dense.len(), usize::from(mixed));
                let actual = parallel_weighted_sums(
                    crate::test_codec::execution(),
                    alloc::vec![group],
                    crate::test_codec::target()
                        .prepared_instance()
                        .coefficient_rows(),
                )
                .unwrap();
                assert_eq!(
                    reduced_values(&actual[0].as_slice()),
                    reduced_values(&expected)
                );
            }
        }
    }
}

/// A linear opening source collapses exactly as the zero-padded dense
/// polynomial it stands for, including when it is the group's only source.
#[test]
fn linear_opening_source_matches_zero_padded_dense_collapse() {
    use prover::opening::{OpeningSource, WeightedGroup, push_weighted_source};
    use prover::{Fp, N, PolySource, SharedPoly};

    let dense = (0..N)
        .map(|index| <Fp>::from_u64(index as u64 * 7 + 3).square())
        .collect::<Vec<_>>();
    let mask = [<Fp>::from_u64(41).square(), <Fp>::from_u64(43).square()];
    let mut padded = alloc::vec![ <Fp>::ZERO; N];
    padded[..2].copy_from_slice(&mask);
    let challenge = <Fp>::from_u64(59).square();
    let xn = <Fp>::from_u64(61);

    // Fold order [dense, mask]: Horner weights [challenge, 1].
    let mut mixed = WeightedGroup {
        instance: None,
        dense: Vec::new(),
        sparse: Vec::new(),
    };
    push_weighted_source(
        &mut mixed,
        OpeningSource::Coefficients(PolySource::Arc(SharedPoly::new(dense.clone()))),
        &challenge,
        &xn,
    )
    .unwrap();
    push_weighted_source(&mut mixed, OpeningSource::Linear(mask), &<Fp>::ONE, &xn).unwrap();
    assert_eq!((mixed.dense.len(), mixed.sparse.len()), (1, 2));
    let mut alone = WeightedGroup {
        instance: None,
        dense: Vec::new(),
        sparse: Vec::new(),
    };
    push_weighted_source(&mut alone, OpeningSource::Linear(mask), &<Fp>::ONE, &xn).unwrap();
    assert_eq!((alone.dense.len(), alone.sparse.len()), (0, 2));
    let collapsed = prover::opening::parallel_weighted_sums(
        crate::test_codec::execution(),
        alloc::vec![mixed, alone],
        crate::test_codec::target()
            .prepared_instance()
            .coefficient_rows(),
    )
    .unwrap();
    assert_eq!(
        reduced_values(&(collapsed[0].as_slice())),
        reduced_values(
            &(prover::opening::deferred_horner_polynomial_fold(&[&dense, &padded], &challenge)
                .unwrap()
                .as_slice())
        )
    );
    assert_eq!(
        reduced_values(&(collapsed[1].as_slice())),
        reduced_values(&(padded.as_slice()))
    );
}

#[test]
fn deferred_polynomial_fold_matches_elementwise_horner() {
    let polynomials = (0..12u64)
        .map(|polynomial| {
            (0..prover::N)
                .map(|index| {
                    <prover::Fp>::from_u64(
                        (index as u64)
                            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                            .wrapping_add(polynomial * 19 + 5),
                    )
                    .square()
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    for count in [1, 3, 4, 7, 8, 11, 12] {
        let references = polynomials[..count]
            .iter()
            .map(Vec::as_slice)
            .collect::<Vec<_>>();
        for challenge in [
            <prover::Fp>::ZERO,
            <prover::Fp>::ONE,
            <prover::Fp>::from_u64(29).square().neg(),
        ] {
            let mut expected = alloc::vec![ <prover::Fp>::ZERO; prover::N];
            for polynomial in &references {
                prover::opening::fold_polynomial(&mut expected, polynomial, &challenge).unwrap();
            }
            assert_eq!(
                reduced_values(
                    &(prover::opening::deferred_horner_polynomial_fold(&references, &challenge)
                        .unwrap())
                ),
                reduced_values(&(expected)),
                "polynomial count {count}"
            );
        }
    }
    assert_eq!(
        reduced_values(
            &(prover::opening::deferred_horner_polynomial_fold(&[], &<prover::Fp>::ONE))
        ),
        Err(Error::InternalInvariant)
    );
}

/// The chunked pool fold reproduces the serial deferred
/// fold coefficient for coefficient, with the leading polynomial standing
/// for `Q'`, for the stage's group count and for degenerate challenges.
#[test]
fn parallel_deferred_fold_matches_serial_fold() {
    let polynomials: Vec<Vec<prover::Fp>> = (0..6u64)
        .map(|polynomial| {
            (0..prover::N)
                .map(|index| {
                    <prover::Fp>::from_u64(
                        ((index as u64) << 20)
                            .wrapping_mul(0x2545_f491_4f6c_dd1d)
                            .wrapping_add(polynomial * 31 + 7),
                    )
                    .square()
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let shared = polynomials
        .iter()
        .map(|polynomial| prover::SharedPoly::new(polynomial.to_vec()))
        .collect::<Vec<_>>();
    for count in [1, 2, 6] {
        let references = polynomials[..count]
            .iter()
            .map(Vec::as_slice)
            .collect::<Vec<_>>();
        for challenge in [
            <prover::Fp>::ZERO,
            <prover::Fp>::ONE,
            <prover::Fp>::from_u64(0x0123_4567_89ab_cdef).square().neg(),
        ] {
            assert_eq!(
                reduced_values(
                    &(prover::opening::parallel_deferred_horner_fold(
                        crate::test_codec::execution(),
                        prover::SharedPoly::new(shared[0].to_vec()),
                        &shared[1..count],
                        &challenge
                    )
                    .unwrap())
                ),
                reduced_values(
                    &(prover::opening::deferred_horner_polynomial_fold(&references, &challenge)
                        .unwrap())
                ),
                "polynomial count {count}"
            );
        }
    }
    let short = prover::SharedPoly::new(alloc::vec![ <prover::Fp>::ZERO; 3
    ]);
    assert_eq!(
        reduced_values(
            &(prover::opening::parallel_deferred_horner_fold(
                crate::test_codec::execution(),
                short,
                &[],
                &<prover::Fp>::ONE
            ))
        ),
        Err(Error::InternalInvariant)
    );
}

#[test]
fn direct_quotient_piece_fold_matches_dense_intermediate() {
    use crate::native::target::QUOTIENT_PIECES;
    use prover::opening::{OpeningSource, WeightedGroup, push_weighted_source};
    use prover::{N, QuotientPiece, VestaPoint};

    let polynomial = |salt: u64| {
        (0..N)
            .map(|index| {
                <prover::Fp>::from_u64(
                    (index as u64)
                        .wrapping_mul(0xd6e8_feb8_6659_fd93)
                        .wrapping_add(salt),
                )
                .square()
            })
            .collect::<Vec<_>>()
    };
    let leading = polynomial(11);
    let trailing = polynomial(97);
    let pieces = (0..QUOTIENT_PIECES)
        .map(|piece| QuotientPiece {
            coefficients: prover::SharedPoly::new(polynomial(piece as u64 * 17 + 31)),
            blind: <prover::Fp>::from_u64(piece as u64 * 13 + 5),
            commitment: VestaPoint::IDENTITY,
        })
        .collect::<Vec<_>>();
    let shared = |values: &Vec<prover::Fp>| {
        OpeningSource::Coefficients(prover::PolySource::Arc(prover::SharedPoly::new(
            values.clone(),
        )))
    };
    // Fold order: the leading dense source, the quotient, the trailing dense
    // source, with Horner weights [c², c, 1] as the stage assigns them.
    let sources = [
        shared(&leading),
        OpeningSource::QuotientPieces(&pieces),
        shared(&trailing),
    ];

    for (xn, challenge) in [
        (<prover::Fp>::ZERO, <prover::Fp>::from_u64(19)),
        (<prover::Fp>::ONE, <prover::Fp>::ZERO),
        (
            <prover::Fp>::from_u64(29).square().neg(),
            <prover::Fp>::from_u64(37).square(),
        ),
    ] {
        let mut quotient = alloc::vec![ <prover::Fp>::ZERO; N];
        for piece in pieces.iter().rev() {
            prover::opening::fold_polynomial(&mut quotient, &piece.coefficients, &xn).unwrap();
        }
        let expected = prover::opening::deferred_horner_polynomial_fold(
            &[&leading, &quotient, &trailing],
            &challenge,
        )
        .unwrap();
        let mut weights = alloc::vec![ <prover::Fp>::ZERO; sources.len()];
        let mut weight = <prover::Fp>::ONE;
        for group_weight in weights.iter_mut().rev() {
            *group_weight = weight;
            weight = weight.mul(&challenge);
        }
        let mut weighted = WeightedGroup {
            instance: None,
            dense: Vec::new(),
            sparse: Vec::new(),
        };
        for (source, weight) in sources.iter().zip(&weights) {
            push_weighted_source(&mut weighted, source.clone(), weight, &xn).unwrap();
        }
        assert_eq!(weighted.dense.len(), sources.len() + QUOTIENT_PIECES - 1);
        assert!(weighted.sparse.is_empty());
        assert_eq!(
            reduced_values(
                &(prover::opening::deferred_weighted_polynomial_sum(&weighted.dense, 0..N)
                    .unwrap())
            ),
            reduced_values(&(expected))
        );

        let expected_blind = pieces
            .iter()
            .rev()
            .fold(<prover::Fp>::ZERO, |blind, piece| {
                blind.mul_add(&xn, &piece.blind)
            });
        assert_eq!(
            (prover::opening::fold_quotient_blind(&pieces, &xn).unwrap()).reduce(),
            (expected_blind).reduce()
        );
    }
}

#[test]
fn multiopen_quotient_matches_monic_long_division() {
    use crate::native::evaluation::rotated_query_point;
    use prover::opening::parallel_multiopen_quotient;
    use prover::opening_schedule::{OPENING_GROUPS, OPENING_POINTS, OPENING_ROTATIONS};
    use prover::{Fp, N, SharedPoly};

    // Build each complete divisor and use ordinary long division, without
    // extracting or sharing any linear factor between groups.
    fn reference_quotient(polynomial: &[Fp], points: &[Fp]) -> Vec<Fp> {
        let mut divisor = alloc::vec![<Fp>::ONE];
        for point in points {
            let mut product = alloc::vec![<Fp>::ZERO; divisor.len() + 1];
            for (index, coefficient) in divisor.iter().enumerate() {
                product[index] = product[index].sub(&coefficient.mul(point));
                product[index + 1] = product[index + 1].add(coefficient);
            }
            divisor = product;
        }
        let degree = divisor.len() - 1;
        let mut remainder = polynomial.to_vec();
        let mut quotient = alloc::vec![<Fp>::ZERO; polynomial.len()];
        for index in (degree..polynomial.len()).rev() {
            let coefficient = remainder[index];
            quotient[index - degree] = coefficient;
            for (offset, divisor_coefficient) in divisor.iter().enumerate() {
                let term = &mut remainder[index - degree + offset];
                *term = term.sub(&coefficient.mul(divisor_coefficient));
            }
        }
        assert!(remainder[degree..].iter().all(Fp::is_zero));
        quotient
    }

    let target = crate::test_codec::target();
    // Low-degree inputs exercise nonzero remainders and differently sized
    // quotient suffixes; dense inputs exercise the full coefficient walk.
    for active in [0, 1, 2, 3, 4, N] {
        let polynomials = (0..OPENING_GROUPS.len())
            .map(|group| {
                let mut coefficients = alloc::vec![<Fp>::ZERO; N];
                for (index, coefficient) in coefficients[..active].iter_mut().enumerate() {
                    *coefficient = <Fp>::from_u64((index * 17 + group * 31 + 5) as u64)
                        .square()
                        .square();
                }
                SharedPoly::new(coefficients)
            })
            .collect::<Vec<_>>();
        for x in [<Fp>::ONE, <Fp>::from_u64(0x0123_4567_89ab_cdef).square()] {
            let points: [Fp; OPENING_POINTS] =
                core::array::from_fn(|id| rotated_query_point(target, &x, OPENING_ROTATIONS[id]));
            let terms = OPENING_GROUPS
                .iter()
                .zip(&polynomials)
                .map(|(group, polynomial)| {
                    reference_quotient(
                        polynomial,
                        &group.point_ids().map(|id| points[id]).collect::<Vec<_>>(),
                    )
                })
                .collect::<Vec<_>>();
            for challenge in [
                <Fp>::ZERO,
                <Fp>::ONE,
                <Fp>::ONE.neg(),
                <Fp>::from_u64(0xfedc_ba98_7654_3210).square(),
            ] {
                let mut expected = alloc::vec![<Fp>::ZERO; N];
                for term in &terms {
                    for (coefficient, next) in expected.iter_mut().zip(term) {
                        *coefficient = coefficient.mul(&challenge).add(next);
                    }
                }
                let actual = parallel_multiopen_quotient(
                    crate::test_codec::execution(),
                    &polynomials,
                    &points,
                    &challenge,
                )
                .unwrap();
                assert_eq!(
                    reduced_values(&actual),
                    reduced_values(&expected),
                    "active coefficients: {active}"
                );
            }
        }
    }
}

#[test]
fn multiopen_quotient_rejects_invalid_shapes() {
    use prover::inventory::opening_stage::POINT_SETS;
    use prover::opening::parallel_multiopen_quotient;
    use prover::opening_schedule::OPENING_POINTS;
    use prover::{Fp, N, SharedPoly};

    for (count, len) in [
        (0, N),
        (POINT_SETS - 1, N),
        (POINT_SETS + 1, N),
        (POINT_SETS, 0),
        (POINT_SETS, N - 1),
        (POINT_SETS, N + 1),
    ] {
        let polynomials = alloc::vec![SharedPoly::new(alloc::vec![<Fp>::ZERO; len]); count];
        assert!(matches!(
            parallel_multiopen_quotient(
                crate::test_codec::execution(),
                &polynomials,
                &[<Fp>::ONE; OPENING_POINTS],
                &<Fp>::ONE,
            ),
            Err(Error::InternalInvariant)
        ));
    }
}

#[test]
fn parallel_polynomial_fold_matches_serial_horner() {
    fn check<const COUNT: usize>() {
        let polynomials: [Vec<prover::Fp>; COUNT] = core::array::from_fn(|polynomial| {
            (0..prover::N)
                .map(|index| {
                    <prover::Fp>::from_u64(
                        (index as u64)
                            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                            .wrapping_add(polynomial as u64 * 19 + 5),
                    )
                    .square()
                    .square()
                })
                .collect()
        });
        for challenge in [
            <prover::Fp>::ZERO,
            <prover::Fp>::ONE,
            <prover::Fp>::ONE.neg(),
            <prover::Fp>::from_u64(0x0123_4567_89ab_cdef)
                .square()
                .square(),
        ] {
            let mut expected = polynomials[0].clone();
            for polynomial in &polynomials[1..] {
                prover::opening::fold_polynomial(&mut expected, polynomial, &challenge).unwrap();
            }
            assert_eq!(
                reduced_values(
                    &(prover::opening::parallel_horner_polynomial_fold(
                        crate::test_codec::execution(),
                        polynomials.clone(),
                        &challenge
                    )
                    .unwrap())
                ),
                reduced_values(&(expected)),
                "polynomial count {COUNT}"
            );
        }
    }
    check::<1>();
    check::<2>();
    check::<{ prover::inventory::opening_stage::POINT_SETS }>();
}

#[test]
fn parallel_polynomial_fold_rejects_invalid_shapes() {
    assert_eq!(
        reduced_values(
            &(prover::opening::parallel_horner_polynomial_fold::<Vec<prover::Fp>, 0>(
                crate::test_codec::execution(),
                [],
                &<prover::Fp>::ONE
            ))
        ),
        Err(Error::InternalInvariant)
    );
    for len in [0, prover::N - 1, prover::N + 1] {
        assert_eq!(
            reduced_values(
                &(prover::opening::parallel_horner_polynomial_fold(
                    crate::test_codec::execution(),
                    [
                        alloc::vec![<prover::Fp>::ZERO; prover::N],
                        alloc::vec![<prover::Fp>::ZERO; len],
                    ],
                    &<prover::Fp>::ONE
                ))
            ),
            Err(Error::InternalInvariant)
        );
    }
}
