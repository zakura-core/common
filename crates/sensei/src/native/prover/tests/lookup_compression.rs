//! Lookup compression and kernels against expression-tree references.

use super::{ONE_ACTION_FIXTURE, TWO_ACTION_FIXTURE};
use crate::native::prover;
use crate::native::test_support::reduced_values;
use crate::types::ProvingRequest;
use alloc::{sync::Arc, vec::Vec};

/// Feed-based lookup compression must equal
/// the dense post-blinding evaluation on every row of every side. Real
/// fixture witnesses provide the feed; a deterministic nonzero junk tail
/// stands in for the advice blinding randomness so the boundary-row patch
/// is exercised, including the row-0 wraparound through rotation −1.
#[test]
fn feed_compression_matches_dense_reference_on_fixtures() {
    use crate::native::witness;
    use prover::{Fp, N, USABLE_ROWS_END};

    let target = crate::test_codec::target();
    let theta = <Fp>::from_u64(0x7e57_7e57).square().add(&<Fp>::from_u64(7));
    for fixture in [ONE_ACTION_FIXTURE, TWO_ACTION_FIXTURE] {
        let request = ProvingRequest::decode_iwpr_for_test(fixture).unwrap();
        let (matrices, feeds) = witness::build_native_witness_matrices(
            crate::test_codec::target(),
            crate::test_codec::execution(),
            &request,
            &request.native_statements(),
            &crate::native::prover::LookupWorkspace::default(),
        )
        .unwrap();
        let instance_columns = request.instance_columns();
        let feeds = feeds.into_actions();
        for ((matrix, mut instance), action_feeds) in
            matrices.into_iter().zip(instance_columns).zip(feeds)
        {
            instance.resize_with(N, || <Fp>::ZERO);
            let mut advice = matrix.columns().to_vec();
            for (column_index, column) in advice.iter_mut().enumerate() {
                for (row, cell) in column.iter_mut().enumerate().skip(USABLE_ROWS_END) {
                    *cell = <Fp>::from_u64((column_index * N + row) as u64 + 1).square();
                }
            }
            for ((lookup_index, lookup), ids) in target
                .lookups()
                .iter()
                .enumerate()
                .zip(action_feeds.into_lookups())
            {
                let dense_table = prover::lookup::compress_expressions(
                    lookup.tables(),
                    &theta,
                    target,
                    &advice,
                    &instance,
                )
                .unwrap();
                let prepared_table = prover::lookup::compress_table_from_prepared(
                    crate::test_codec::target(),
                    lookup_index,
                    &theta,
                )
                .unwrap();
                assert_eq!(
                    reduced_values(&(prepared_table)),
                    reduced_values(&(dense_table))
                );

                let dense_input = prover::lookup::compress_expressions(
                    lookup.inputs(),
                    &theta,
                    target,
                    &advice,
                    &instance,
                )
                .unwrap();
                let tuples =
                    prover::prepared_lookup_table_tuples(crate::test_codec::target(), lookup_index)
                        .unwrap();
                let gathered_input = prover::lookup::compress_input_from_ids(
                    &ids,
                    &prepared_table,
                    tuples,
                    &theta,
                    target,
                    &advice,
                    &instance,
                )
                .unwrap();
                assert_eq!(
                    reduced_values(&(gathered_input)),
                    reduced_values(&(dense_input))
                );

                // Counting through identities agrees with probing every
                // compressed value, patched rows included.
                let access = prover::lookup::prepared_table_access(
                    crate::test_codec::target(),
                    lookup_index,
                    &prepared_table,
                )
                .expect("no compressed collision at this theta");
                let (order, probe, entry_of_id) = access.parts();
                assert_eq!(
                    prover::lookup::count_input_entries(
                        order,
                        probe,
                        entry_of_id,
                        ids.ids(),
                        &gathered_input
                    )
                    .unwrap(),
                    prover::lookup::count_input_values(
                        order,
                        probe,
                        &gathered_input[..USABLE_ROWS_END]
                    )
                    .unwrap()
                );
            }
        }
    }
}

/// The table sides compress from a coset stack carrying no advice or
/// instance cosets at all (the quotient wave's fixed-only view) and match
/// the serial reference, while an input side offered that view fails as an
/// invariant error instead of reading past an empty advice list.
#[test]
fn table_compression_accepts_a_fixed_only_view() {
    let target = crate::test_codec::target();
    let column = |seed: u64| -> Vec<prover::Fp> {
        (0..prover::EXTENDED_N)
            .map(|row| {
                let row = row as u64;
                <prover::Fp>::from_u64(row.wrapping_mul(seed | 3) ^ (seed << 11) ^ (row >> 2) ^ 5)
            })
            .collect()
    };
    let fixed: Vec<Vec<prover::Fp>> = (0..crate::native::target::FIXED_COLUMNS as u64)
        .map(|index| column(index * 19 + 7))
        .collect();
    let advice: Vec<Vec<prover::Fp>> = (0..prover::ADVICE_COLUMNS as u64)
        .map(|index| column(index * 37 + 11))
        .collect();
    let instance = column(101);
    let fixed_only_stack = || {
        Arc::new(prover::CosetStack {
            advice: Vec::with_capacity(0),
            fixed: fixed.clone(),
        })
    };
    let theta = <prover::Fp>::from_u64(0x0f1e_2d3c_4b5a_6978);
    let table_jobs: Vec<_> = target
        .lookups()
        .iter()
        .map(|ranges| (0usize, ranges.tables()))
        .collect();
    let actual = prover::lookup::parallel_compress_lookup_expressions(
        table_jobs.clone(),
        theta,
        target,
        fixed_only_stack(),
    )
    .unwrap();
    assert_eq!(actual.len(), table_jobs.len());
    for ((_, programs), actual) in table_jobs.iter().zip(&actual) {
        let expected = prover::lookup::compress_expressions_on_coset(
            *programs,
            &theta,
            target,
            &advice,
            &fixed,
            core::slice::from_ref(&instance),
        )
        .unwrap();
        for row in 0..prover::EXTENDED_N {
            assert_eq!(
                (actual[row]).reduce(),
                (expected[row]).reduce(),
                "row {row}"
            );
        }
    }
    let input_jobs: Vec<_> = target
        .lookups()
        .iter()
        .map(|ranges| (0usize, ranges.inputs()))
        .collect();
    assert!(matches!(
        prover::lookup::parallel_compress_lookup_expressions(
            input_jobs,
            theta,
            target,
            fixed_only_stack(),
        ),
        Err(prover::Error::InternalInvariant)
    ));
}

#[test]
fn prepared_table_compression_matches_windowed_compression() {
    use prover::{CosetStack, Fp};
    let target = crate::test_codec::target();
    let preparation = target.lookup_preparation();
    let jobs = preparation
        .sources()
        .iter()
        .enumerate()
        .filter(|&(index, source)| index == *source)
        .map(|(index, _)| (0, target.lookups()[index].tables()))
        .collect::<Vec<_>>();
    for theta in [Fp::ZERO, Fp::ONE, <Fp>::from_u64(0x17b9).square()] {
        let expected = prover::lookup::parallel_compress_lookup_expressions(
            jobs.clone(),
            theta,
            target,
            Arc::new(CosetStack {
                advice: Vec::new(),
                fixed: target.fixed_polynomials().cosets().collect_views(),
            }),
        )
        .unwrap();
        let actual = preparation
            .compress_cosets(theta, target, crate::test_codec::execution())
            .unwrap();
        for (actual, expected) in actual.iter().zip(&expected) {
            assert_eq!(
                reduced_values(&actual.to_dense_rows()),
                reduced_values(&expected.to_dense_rows())
            );
        }
        assert_eq!(actual.len(), expected.len());
    }
}

#[test]
fn parallel_lookup_compression_matches_serial_reference() {
    let target = crate::test_codec::target();
    let column = |seed: u64| -> Vec<prover::Fp> {
        (0..prover::EXTENDED_N)
            .map(|row| {
                let row = row as u64;
                <prover::Fp>::from_u64(row.wrapping_mul(seed | 1) ^ (seed << 9) ^ (row >> 3) ^ 7)
            })
            .collect()
    };
    // Pseudo-random fixed columns: the selectors and runs the kernels
    // factor are arbitrary field values here, not booleans.
    let fixed: Vec<Vec<prover::Fp>> = (0..crate::native::target::FIXED_COLUMNS as u64)
        .map(|index| column(index * 17 + 5))
        .collect();
    // One to three Actions: the shared row pass with a single member,
    // and the grouped chunking with even and uneven row splits.
    for action_count in 1..=3u64 {
        let advice_actions: Vec<Vec<Vec<prover::Fp>>> = (0..action_count)
            .map(|action| {
                (0..prover::ADVICE_COLUMNS as u64)
                    .map(|index| column(action * 977 + index * 31 + 3))
                    .collect()
            })
            .collect();
        let instance_actions: Vec<Vec<prover::Fp>> = (0..action_count)
            .map(|action| column(action * 613 + 97))
            .collect();
        let tiled = |columns: &[Vec<prover::Fp>]| -> Vec<prover::ExtendedCoset> {
            columns
                .iter()
                .map(|column| prover::extended_coset_from_dense_rows(column.clone()).unwrap())
                .collect()
        };
        let mut jobs = Vec::new();
        for action_index in 0..action_count as usize {
            for ranges in target.lookups() {
                jobs.push((action_index, ranges.inputs()));
                jobs.push((action_index, ranges.tables()));
            }
        }
        // Degenerate challenges alongside an arbitrary one.
        for theta in [
            <prover::Fp>::ZERO,
            <prover::Fp>::ONE,
            <prover::Fp>::from_u64(0x1234_5678_9abc_def1),
        ] {
            let actual = prover::lookup::parallel_compress_lookup_expressions(
                jobs.clone(),
                theta,
                target,
                Arc::new(prover::CosetStack {
                    advice: advice_actions
                        .iter()
                        .map(|columns| tiled(columns))
                        .collect(),
                    fixed: fixed.clone(),
                }),
            )
            .unwrap();
            assert_eq!(actual.len(), jobs.len());
            for ((action_index, programs), actual) in jobs.iter().zip(&actual) {
                let expected = prover::lookup::compress_expressions_on_coset(
                    *programs,
                    &theta,
                    target,
                    &advice_actions[*action_index],
                    &fixed,
                    &instance_actions[*action_index..=*action_index],
                )
                .unwrap();
                assert!(
                    (0..prover::EXTENDED_N)
                        .all(|row| (actual[row]).reduce() == (expected[row]).reduce())
                );
            }
        }
    }
}

#[test]
fn shared_sinsemilla_cubics_match_lookup_trees_and_rotations() {
    use crate::native::generated_expressions::{
        GATE_QUERY_DESCRIPTORS, QueryKind, SinsemillaCubics, evaluate, program_trees,
    };
    use crate::native::queries::{ADVICE_QUERIES, FIXED_QUERIES};
    use prover::Fp;
    use prover::lookup::{LookupInputRowCoefficients, LookupKernelConstants, ThetaConstants};

    let target = crate::test_codec::target();
    let constants = LookupKernelConstants::load();
    let mut state = 0xb07c_d913_526a_e8f4u64;
    for case in 0..512 {
        let mut value = || match case {
            0 => <Fp>::ZERO,
            1 => <Fp>::ONE,
            2 => <Fp>::ONE.neg(),
            _ => {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                <Fp>::from_u64(state).square().square()
            }
        };
        // Three independent rows per column distinguish +1 from -1.
        // Resolve frame slots and tree queries through the original
        // column/rotation metadata, so neither
        // bank's hard-coded cubic slots supply their own reference.
        let advice: Vec<_> = (0..prover::ADVICE_COLUMNS)
            .map(|_| [value(), value(), value()])
            .collect();
        let fixed: Vec<_> = (0..crate::native::target::FIXED_COLUMNS)
            .map(|_| [value(), value(), value()])
            .collect();
        let query = |kind: QueryKind, index: usize, row: i32| {
            let (columns, descriptor) = match kind {
                QueryKind::Advice => (&advice, ADVICE_QUERIES[index]),
                QueryKind::Fixed => (&fixed, FIXED_QUERIES[index]),
                QueryKind::Instance => return Err(prover::Error::InternalInvariant),
            };
            Ok(columns[descriptor.column][(row + descriptor.rotation).rem_euclid(3) as usize])
        };
        let frame =
            |row| GATE_QUERY_DESCRIPTORS.map(|(kind, index)| query(kind, index, row).unwrap());
        let cubics = SinsemillaCubics::at_row(&frame(0));
        assert_eq!(
            reduced_values(&SinsemillaCubics::at_next_row(&frame(0))),
            reduced_values(&SinsemillaCubics::at_row(&frame(1))),
            "case {case} rotation"
        );
        for theta in [<Fp>::ZERO, <Fp>::ONE, <Fp>::ONE.neg(), value()] {
            let theta_constants = ThetaConstants::new(theta, &constants);
            for lookup_index in 1..=2 {
                let kernel = prover::lookup::lookup_input_row_kernel(target, lookup_index).unwrap();
                let coefficients = LookupInputRowCoefficients::at_row(
                    kernel,
                    &constants,
                    &theta_constants,
                    &fixed,
                    0,
                );
                let actual = coefficients.evaluate(&constants, &advice, 0, 1, &cubics);
                let expected = target.lookups()[lookup_index].inputs().indices().fold(
                    <Fp>::ZERO,
                    |acc, program| {
                        let component =
                            evaluate(&program_trees(program).unwrap().tree, &mut |kind, index| {
                                query(kind, index, 0)
                            })
                            .unwrap();
                        acc.mul_add(&theta, &component)
                    },
                );
                assert_eq!(
                    actual.reduce(),
                    expected.reduce(),
                    "case {case} lookup {lookup_index}"
                );
            }
        }
    }
}

/// Every pinned lookup side must resolve to kernels, so production's
/// parallel compression uses them for all seven input programs and the
/// fixed-query table sides. Resolution depends only on circuit query metadata.
#[test]
fn every_pinned_lookup_side_has_kernels() {
    let target = crate::test_codec::target();
    for (lookup_index, lookup) in target.lookups().iter().enumerate() {
        for (is_input, side) in [(true, lookup.inputs()), (false, lookup.tables())] {
            let kernels =
                prover::lookup::lookup_kernels(target, side).expect("pinned side has kernels");
            assert_eq!(kernels.len(), side.len());
            // Exactly the two Sinsemilla input sides take the fused row
            // pass the parity test above exercises; the rest sweep per
            // component.
            assert_eq!(
                prover::lookup::sinsemilla_fused_kernel(&kernels).is_some(),
                is_input && lookup_index != 0,
                "lookup {lookup_index} input {is_input}"
            );
            // The two three-column table sides take the fused fixed-column
            // pass; the single-column range table has nothing to fold.
            assert_eq!(
                prover::lookup::fixed_columns_fused_kernel(&kernels).is_some(),
                !is_input && lookup_index != 0,
                "lookup {lookup_index} table {}",
                !is_input
            );
        }
    }
}

/// Each pinned lookup side's kernel list reads exactly the query
/// dependencies of the programs it implements, kernel by kernel: the
/// hand-transcribed formulas cannot silently read a column their program
/// does not, nor miss one it does.
#[test]
fn lookup_kernels_read_exactly_their_programs_dependencies() {
    let target = crate::test_codec::target();
    for (lookup_index, lookup) in target.lookups().iter().enumerate() {
        for side in [lookup.inputs(), lookup.tables()] {
            let kernels =
                prover::lookup::lookup_kernels(target, side).expect("pinned side has kernels");
            for (kernel, program) in kernels.iter().zip(side.indices()) {
                let expected = prover::generated_expressions::program_trees(program)
                    .unwrap()
                    .tree
                    .query_dependencies();
                let actual = kernel.reads();
                assert_eq!(
                    (actual.fixed, actual.advice, actual.instance),
                    (expected.fixed, expected.advice, expected.instance),
                    "lookup {lookup_index} program {program}"
                );
            }
        }
    }
}
