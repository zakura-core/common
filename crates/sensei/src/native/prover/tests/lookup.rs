//! Prepared lookup inventories, reconstruction, and commitment references.

use super::{ONE_ACTION_FIXTURE, TWO_ACTION_FIXTURE, randomness_from_tape};
use crate::native::prover::{self, ProverPrefix};
use crate::native::test_support::reduced_values;
use crate::{Error, types::ProvingRequest};
use alloc::vec::Vec;

#[test]
fn lookup_permutation_matches_the_production_leftover_order() {
    let values = |values: &[u64]| values.iter().copied().map(<prover::Fp>::from_u64).collect();
    let (input, table) =
        prover::lookup::permute_usable_values(values(&[2, 1, 2, 3]), values(&[4, 3, 2, 1]))
            .unwrap();
    assert_eq!(
        reduced_values(&(input)),
        reduced_values(&(values(&[1, 2, 2, 3])))
    );
    assert_eq!(
        reduced_values(&(table)),
        reduced_values(&(values(&[1, 2, 4, 3])))
    );
    assert_eq!(
        reduced_values(&(prover::lookup::permute_usable_values(values(&[1, 5]), values(&[1, 2])))),
        Err(Error::UnsatisfiedWitness)
    );
}

/// Every lookup's table side must be a fixed-only
/// expression, so its distinct-tuple index is preparable from committed
/// data; pins the prepared index shapes.
#[test]
fn lookup_table_sides_are_fixed_only_with_prepared_indices() {
    let target = crate::test_codec::target();
    let prepared = crate::test_codec::target()
        .lookup_preparation()
        .tables
        .as_slice();
    assert_eq!(prepared.len(), target.lookups().len());
    let shapes = prepared
        .iter()
        .map(|table| {
            let counts: Vec<usize> = match table.as_deref().expect("table side must be fixed-only")
            {
                prover::lookup::PreparedLookupTable::Distinct { distinct } => distinct
                    .iter()
                    .map(|&(_, count)| usize::from(count))
                    .collect(),
                prover::lookup::PreparedLookupTable::Static { order, .. } => order
                    .entries
                    .iter()
                    .map(|&(_, count)| usize::from(count))
                    .collect(),
            };
            assert_eq!(counts.iter().sum::<usize>(), prover::USABLE_ROWS_END);
            let is_static = matches!(
                table.as_deref().unwrap(),
                prover::lookup::PreparedLookupTable::Static { .. }
            );
            (counts.len(), counts.into_iter().max().unwrap(), is_static)
        })
        .collect::<Vec<_>>();
    // (distinct tuples, largest multiplicity, fully-static order) per
    // lookup: every table has 1,024 distinct tuples with the padding
    // value on 1,019 of the 2,042 usable rows; only the first lookup's
    // table side is a single expression with a θ-independent order.
    assert_eq!(
        shapes,
        alloc::vec![
            (1_024, 1_019, true),
            (1_024, 1_019, false),
            (1_024, 1_019, false)
        ]
    );
}

/// The prepared tuple index must agree exactly with canonical byte-encoded
/// tuple membership: every usable-row table tuple is a member, every
/// single-component perturbation is a member only if the byte set holds
/// it, and the index holds the pinned 1,024 distinct tuples per lookup.
#[test]
fn prepared_tuple_index_matches_canonical_tuple_set() {
    use alloc::collections::BTreeSet;

    use prover::{Fp, USABLE_ROWS_END};

    let sides = crate::test_codec::target()
        .lookup_preparation()
        .sides
        .as_slice();
    assert_eq!(sides.len(), 3);
    for side in sides {
        let side = side.as_ref().expect("table side must be fixed-only");
        let components = &side.components;
        let index = &side.tuples;
        assert_eq!(index.arity(), components.len());
        assert_eq!(index.len(), 1_024);
        // Keep the independent standard-library set oracle free of accounting metadata.
        let encode = |values: &[Fp]| -> std::vec::Vec<u8> {
            values.iter().flat_map(|value| value.to_bytes()).collect()
        };
        let canonical = (0..USABLE_ROWS_END)
            .map(|row| {
                encode(
                    &components
                        .iter()
                        .map(|column| column[row])
                        .collect::<Vec<_>>(),
                )
            })
            .collect::<BTreeSet<_>>();
        assert_eq!(canonical.len(), 1_024);
        for row in 0..USABLE_ROWS_END {
            let usable: Vec<Vec<Fp>> = components
                .iter()
                .map(|column| column[..USABLE_ROWS_END].to_vec())
                .collect();
            let id = index
                .find_row(&usable, row)
                .expect("every table row is a member");
            assert_eq!(
                reduced_values(&(index.tuple(id))),
                reduced_values(
                    &(Some(
                        components
                            .iter()
                            .map(|column| column[row])
                            .collect::<Vec<_>>()
                            .as_slice()
                    ))
                )
            );
            for perturbed in 0..components.len() {
                let mut tuple: Vec<Fp> = components.iter().map(|column| column[row]).collect();
                tuple[perturbed] = tuple[perturbed].add(&<Fp>::ONE);
                let inputs: Vec<Vec<Fp>> = tuple.iter().map(|value| alloc::vec![*value]).collect();
                assert_eq!(
                    index.find_row(&inputs, 0).is_some(),
                    canonical.contains(&encode(&tuple))
                );
            }
        }
    }
}

/// Run counts of the permuted lookup columns for the
/// committed fixtures' real witnesses and tapes. Interval commitments
/// cost roughly one point-op per run boundary instead of a
/// 2,048-point Lagrange MSM per column, so these counts bound that win.
#[test]
fn permuted_lookup_column_run_census() {
    use crate::native::witness;
    use prover::{Fp, USABLE_ROWS_END};

    const ONE_ACTION_TAPE: &[u8] = crate::test_codec::FIXTURES[0].tape;
    const TWO_ACTION_TAPE: &[u8] = crate::test_codec::FIXTURES[1].tape;

    let runs = |column: &[Fp]| {
        1 + column[..USABLE_ROWS_END]
            .windows(2)
            .filter(|pair| (pair[0]).reduce() != (pair[1]).reduce())
            .count()
    };

    let mut census = Vec::new();
    for (fixture, tape_bytes) in [
        (ONE_ACTION_FIXTURE, ONE_ACTION_TAPE),
        (TWO_ACTION_FIXTURE, TWO_ACTION_TAPE),
    ] {
        let request = ProvingRequest::decode_iwpr_for_test(fixture).unwrap();
        let randomness = randomness_from_tape(tape_bytes, request.action_count());
        let (matrices, feeds) = witness::build_native_witness_matrices(
            crate::test_codec::target(),
            crate::test_codec::execution(),
            &request,
            &request.native_statements(),
            &crate::native::prover::LookupWorkspace::default(),
        )
        .unwrap();
        let mut prover_workspace = crate::native::ProverWorkspace::new();
        let mut prover = ProverPrefix::initialize(
            crate::test_codec::target(),
            &mut prover_workspace,
            crate::test_codec::execution(),
            &request,
            &request.native_statements(),
        )
        .unwrap();
        let advice = prover.commit_advice(matrices, randomness.advice).unwrap();
        let lookup = prover
            .commit_lookup_permutations(&advice, feeds, randomness.lookup_permutations)
            .unwrap();
        for action_lookups in &lookup.lookups {
            for permuted in action_lookups {
                census.push((
                    runs(&permuted.permuted_input),
                    runs(&permuted.permuted_table),
                ));
            }
        }
    }
    // (input runs, table runs) per action/lookup pair. The frozen
    // leftover rule fragments the table side: unused distinct table
    // values land as singleton runs, so table columns approach half of
    // dense count while input columns stay run-friendly.
    assert_eq!(
        census,
        alloc::vec![
            (321, 1_107),
            (629, 1_058),
            (605, 1_045),
            (321, 1_107),
            (629, 1_236),
            (605, 1_217),
            (312, 1_114),
            (646, 1_235),
            (608, 1_219),
        ]
    );
}

/// Joint lookup recipes agree with dense commitments on the real columns,
/// including both random tails and blinds.
#[test]
fn interval_lookup_commitments_match_dense_on_fixtures() {
    lookup_commitment_fixtures(None, false, crate::test_codec::execution());
}

#[test]
fn lookup_commitments_match_dense_with_theta_collisions() {
    use prover::Fp;
    for theta in [<Fp>::ZERO, <Fp>::ONE, <Fp>::ONE.neg()] {
        lookup_commitment_fixtures(Some(theta), false, crate::test_codec::execution());
    }
}

pub(super) fn lookup_commitment_fixtures(
    theta: Option<prover::Fp>,
    measure: bool,
    execution: crate::native::worker::Execution<'_>,
) {
    use crate::native::{commitment::normalized, target::USABLE_ROWS_END, witness};

    const ONE_ACTION_TAPE: &[u8] = crate::test_codec::FIXTURES[0].tape;
    const TWO_ACTION_TAPE: &[u8] = crate::test_codec::FIXTURES[1].tape;

    let target = crate::test_codec::target();
    for (fixture, tape_bytes) in [
        (ONE_ACTION_FIXTURE, ONE_ACTION_TAPE),
        (TWO_ACTION_FIXTURE, TWO_ACTION_TAPE),
    ] {
        let request = ProvingRequest::decode_iwpr_for_test(fixture).unwrap();
        let randomness = randomness_from_tape(tape_bytes, request.action_count());
        let (matrices, feeds) = witness::build_native_witness_matrices(
            crate::test_codec::target(),
            execution,
            &request,
            &request.native_statements(),
            &crate::native::prover::LookupWorkspace::default(),
        )
        .unwrap();
        let mut prover_workspace = crate::native::ProverWorkspace::new();
        let mut prover = ProverPrefix::initialize(
            crate::test_codec::target(),
            &mut prover_workspace,
            execution,
            &request,
            &request.native_statements(),
        )
        .unwrap();
        let mut advice = prover.commit_advice(matrices, randomness.advice).unwrap();
        if let Some(theta) = theta {
            advice.theta = theta;
        }
        let lookup = prover
            .commit_lookup_permutations(&advice, feeds, randomness.lookup_permutations)
            .unwrap();
        if measure {
            let columns = lookup.lookups.iter().flatten().collect::<Vec<_>>();
            let runs = columns
                .iter()
                .map(|pair| {
                    (
                        prover::lookup::column_runs(&pair.permuted_input[..USABLE_ROWS_END]),
                        prover::lookup::column_runs(&pair.permuted_table[..USABLE_ROWS_END]),
                    )
                })
                .collect::<Vec<_>>();
            let pairs = columns
                .iter()
                .zip(&runs)
                .map(
                    |(pair, (input_runs, table_runs))| crate::native::target::LookupCommitPair {
                        input: &pair.permuted_input,
                        table: &pair.permuted_table,
                        input_runs,
                        table_runs,
                        input_blind: pair.input_blind,
                        table_blind: pair.table_blind,
                    },
                )
                .collect::<Vec<_>>();
            eprintln!("LOOKUP_FIXTURE actions={}", request.action_count());
            target
                .parameters()
                .measure_lookup_pair_recipes(&pairs, execution);
        }
        for action_lookups in &lookup.lookups {
            for permuted in action_lookups {
                let parameters = target.parameters();
                let dense = normalized(&[
                    parameters
                        .commit_lagrange_projective(
                            &permuted.permuted_input,
                            &permuted.input_blind,
                            &mut crate::native::commitment::MsmWorkspace::new(),
                            execution,
                        )
                        .unwrap(),
                    parameters
                        .commit_lagrange_projective(
                            &permuted.permuted_table,
                            &permuted.table_blind,
                            &mut crate::native::commitment::MsmWorkspace::new(),
                            execution,
                        )
                        .unwrap(),
                ]);
                assert_eq!(dense[0], permuted.input_commitment);
                assert_eq!(dense[1], permuted.table_commitment);
            }
        }
    }
}

/// Dense-shadow reference for the counting lookup permutation: an
/// arbitrary table multiset and input multiset must reconstruct exactly
/// the columns the reference sort produces, and an input value absent
/// from the table must fail identically.
#[test]
fn counting_lookup_reconstruction_matches_reference_permutation() {
    use prover::lookup::TableOrder;
    use prover::{Error, Fp};

    // Distinct values with duplicate table structure; total rows 20.
    let table_shape: [(u64, u16); 7] = [
        (97, 3),
        (5, 1),
        (1_000_003, 4),
        (2, 1),
        (68_111, 2),
        (31, 5),
        (777, 4),
    ];
    // Input occurrences per value, summing to the same 20 rows; two
    // values never appear and several repeat.
    let input_shape: [(u64, u32); 7] = [
        (97, 5),
        (5, 1),
        (1_000_003, 9),
        (2, 0),
        (68_111, 3),
        (31, 2),
        (777, 0),
    ];

    let expand = |shape: &[(u64, u32)]| {
        let mut rows = Vec::new();
        for &(seed, count) in shape {
            for _ in 0..count {
                rows.push(<Fp>::from_u64(seed).square());
            }
        }
        // Deterministic scramble by a stride coprime to the length.
        let scrambled = (0..rows.len())
            .map(|index| rows[(index * 13) % rows.len()])
            .collect::<Vec<_>>();
        assert_eq!(scrambled.len(), rows.len());
        scrambled
    };
    let table_rows = expand(
        &table_shape
            .iter()
            .map(|&(seed, count)| (seed, u32::from(count)))
            .collect::<Vec<_>>(),
    );
    let input_rows = expand(&input_shape);
    assert_eq!(table_rows.len(), input_rows.len());

    let (reference_input, reference_table) =
        prover::lookup::permute_usable_values(input_rows.clone(), table_rows.clone()).unwrap();

    let mut keyed = table_shape
        .iter()
        .map(|&(seed, count)| {
            let value = <Fp>::from_u64(seed).square();
            (value.to_canonical_uint(), value, count)
        })
        .collect::<Vec<_>>();
    keyed.sort_unstable_by_key(|entry| entry.0);
    let entries = keyed
        .into_iter()
        .map(|(_, value, count)| (value, count))
        .collect::<Vec<_>>();
    let probe = prover::lookup::build_value_map(&entries);
    let order = TableOrder {
        entries: entries.into(),
    };

    let counts = prover::lookup::count_input_values(&order, &probe, &input_rows).unwrap();
    let counting =
        prover::lookup::reconstruct_permuted_columns(&order, &counts, input_rows.len()).unwrap();
    assert!(reduced_values(&(counting.input)) == reduced_values(&(reference_input)));
    assert!(reduced_values(&(counting.table)) == reduced_values(&(reference_table)));
    assert_eq!(
        reduced_values(&(counting.input_runs)),
        reduced_values(&(prover::lookup::column_runs(&counting.input)))
    );
    assert_eq!(
        reduced_values(&(counting.table_runs)),
        reduced_values(&(prover::lookup::column_runs(&counting.table)))
    );

    // An input value the table does not contain fails identically.
    let missing = <Fp>::from_u64(4_242).square();
    let mut bad_inputs = input_rows;
    bad_inputs[7] = missing;
    assert!(matches!(
        prover::lookup::count_input_values(&order, &probe, &bad_inputs),
        Err(Error::UnsatisfiedWitness)
    ));
    assert!(matches!(
        prover::lookup::permute_usable_values(bad_inputs, table_rows),
        Err(Error::UnsatisfiedWitness)
    ));
}

#[test]
fn counting_lookup_reconstruction_handles_run_boundaries() {
    use prover::Fp;

    for (table, input) in [
        (&[][..], &[][..]),
        (&[1, 2, 3, 4][..], &[4, 2, 1, 3][..]),
        (&[1, 1, 2, 3, 3, 4][..], &[1, 1, 1, 1, 1, 1][..]),
        (&[1, 1, 2, 3, 3, 4][..], &[4, 4, 4, 4, 4, 4][..]),
        (&[1, 1, 2, 3, 3, 4][..], &[2, 3, 2, 3, 2, 3][..]),
    ] {
        let table = table.iter().copied().map(Fp::from_u64).collect::<Vec<_>>();
        let input = input.iter().copied().map(Fp::from_u64).collect::<Vec<_>>();
        let mut entries: Vec<(Fp, u16)> = Vec::new();
        for &value in &table {
            match entries.last_mut() {
                Some((previous, count)) if previous.reduce() == value.reduce() => *count += 1,
                _ => entries.push((value, 1)),
            }
        }
        let probe = prover::lookup::build_value_map(&entries);
        let order = prover::lookup::TableOrder {
            entries: entries.into(),
        };
        let counts = prover::lookup::count_input_values(&order, &probe, &input).unwrap();
        let counting =
            prover::lookup::reconstruct_permuted_columns(&order, &counts, input.len()).unwrap();
        let (reference_input, reference_table) =
            prover::lookup::permute_usable_values(input, table).unwrap();
        assert_eq!(
            reduced_values(&counting.input),
            reduced_values(&reference_input)
        );
        assert_eq!(
            reduced_values(&counting.table),
            reduced_values(&reference_table)
        );
        assert_eq!(
            reduced_values(&counting.input_runs),
            reduced_values(&prover::lookup::column_runs(&counting.input))
        );
        assert_eq!(
            reduced_values(&counting.table_runs),
            reduced_values(&prover::lookup::column_runs(&counting.table))
        );
    }
}

#[test]
fn lookup_indices_match_equivalent_loose_representations() {
    use prover::lookup::{TableOrder, TupleIndex, build_value_map, count_input_values};
    use udon::field::{Fp, PallasBase, PrimeModulus};

    let zero = <Fp>::ZERO;
    let loose_zero = <Fp>::from_montgomery_limbs(PallasBase::MODULUS);
    let one = <Fp>::ONE;
    let loose_one = one.add(&loose_zero);
    assert_ne!(zero.montgomery_limbs(), loose_zero.montgomery_limbs());
    assert_ne!(one.montgomery_limbs(), loose_one.montgomery_limbs());

    let components = vec![vec![zero, loose_zero, one, loose_one], vec![one; 4]];
    let index = TupleIndex::build(&components, 4);
    assert_eq!(index.len(), 2);
    assert_eq!(index.counts(), &[2, 2]);
    assert_eq!(index.row_ids(), &[0, 0, 1, 1]);
    assert_eq!(index.find_tuple(&[loose_zero, loose_one]), Some(0));
    assert_eq!(
        index.find_row(&[vec![loose_one], vec![loose_one]], 0),
        Some(1)
    );
    assert_eq!(index.find_tuple(&[one, zero]), None);

    let order = TableOrder {
        entries: vec![(zero, 2), (one, 2)].into(),
    };
    let map = build_value_map(&order.entries);
    let input = vec![loose_one, zero, loose_zero, one];
    assert_eq!(
        count_input_values(&order, &map, &input).unwrap(),
        vec![2, 2]
    );
    let (permuted_input, permuted_table) =
        prover::lookup::permute_usable_values(input, vec![one, loose_zero, loose_one, zero])
            .unwrap();
    assert_eq!(
        reduced_values(&permuted_input),
        reduced_values(&[zero, zero, one, one])
    );
    assert_eq!(
        reduced_values(&permuted_table),
        reduced_values(&[zero, one, one, zero])
    );
}
