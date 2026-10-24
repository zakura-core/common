//! Quotient addressing and class folds against full-row dense references.

use super::{ONE_ACTION_FIXTURE, TWO_ACTION_FIXTURE, randomness_from_tape};
use crate::native::evaluation::EXTENDED_ROTATION_STRIDE;
use crate::native::prover::quotient::FoldWindow;
use crate::native::prover::{self, FOLD_CHUNK_ROWS, Fp, N, ProverPrefix};
use crate::native::test_support::reduced_values;
use crate::{Error, types::ProvingRequest};
use alloc::vec::Vec;

#[test]
fn masked_rotation_addressing_matches_euclidean_reference() {
    // Reference implementations with explicit Euclidean remainders; the
    // shipping functions use wrapping-add-and-mask addressing.
    let reference_extended = |row: usize, rotation: i32| -> usize {
        let scale = (prover::EXTENDED_N / prover::N) as i64;
        (row as i64 + i64::from(rotation) * scale).rem_euclid(prover::EXTENDED_N as i64) as usize
    };
    let reference = |row: usize, rotation: i32| -> usize {
        (row as i64 + i64::from(rotation)).rem_euclid(prover::N as i64) as usize
    };
    for row in 0..prover::EXTENDED_N {
        for rotation in -8..=8 {
            assert_eq!(
                crate::native::evaluation::rotated_extended_row(row, rotation),
                reference_extended(row, rotation)
            );
        }
        let [previous, current, next] = crate::native::evaluation::gate_query_rows(row);
        assert_eq!(
            previous,
            crate::native::evaluation::rotated_extended_row(row, -1)
        );
        assert_eq!(
            current,
            crate::native::evaluation::rotated_extended_row(row, 0)
        );
        assert_eq!(
            next,
            crate::native::evaluation::rotated_extended_row(row, 1)
        );
    }
    for row in 0..prover::N {
        for rotation in -8..=8 {
            assert_eq!(
                crate::native::evaluation::rotated_row(row, rotation),
                reference(row, rotation)
            );
        }
    }
}

#[test]
fn retained_dynamic_polynomial_forms_match_independent_transforms() {
    let values = (0..prover::N)
        .map(|index| <prover::Fp>::from_u64(index as u64 + 1))
        .collect::<Vec<_>>();
    let forms = prover::lagrange_to_forms(&values).unwrap();

    let mut expected_coefficients = values.clone();
    assert!(crate::native::polynomial::ifft(&mut expected_coefficients));
    let mut expected_coset = values;
    assert!(crate::native::polynomial::base_lagrange_to_extended_coset(
        &mut expected_coset
    ));
    assert_eq!(
        reduced_values(&(forms.coefficients)),
        reduced_values(&(expected_coefficients))
    );
    assert_eq!(
        reduced_values(&(forms.coset.to_dense_rows())),
        reduced_values(&(expected_coset))
    );

    assert!(matches!(
        prover::lagrange_to_forms(&expected_coefficients[..prover::N - 1]),
        Err(Error::InternalInvariant)
    ));
}

#[test]
fn parallel_map_matches_serial_map_in_order() {
    for count in [0usize, 1, 5, 8, 17, 46] {
        let items: Vec<usize> = (0..count).collect();
        let expected: Vec<usize> = items.iter().map(|value| value * 2 + 1).collect();
        assert_eq!(
            (items)
                .into_iter()
                .map(|value| value * 2 + 1)
                .collect::<Vec<_>>(),
            expected
        );
    }
}

/// Applies a fold routine to disjoint residue-major windows of the four
/// degree-class accumulators as pool tasks and hands each task's finished
/// chunks to `assemble` with its window.
///
/// Windows are [`FOLD_CHUNK_ROWS`] rows of one residue; the 4N, 2N, and N
/// chunks are as long as the 8N chunk when the residue folds on that class
/// (even residues, residues 0 and 4, residue 0) and empty otherwise. The
/// routine must derive each value only from its absolute row over shared
/// inputs; results are then identical for every chunking.
pub(super) fn fold_classed_rows(
    execution: crate::native::worker::Execution<'_>,
    fold_chunk: impl Fn(FoldWindow, &mut [Fp], &mut [Fp], &mut [Fp], &mut [Fp]) -> Result<(), Error>
    + Send
    + Sync,
    mut assemble: impl FnMut(
        FoldWindow,
        prover::Buffer<Fp>,
        prover::Buffer<Fp>,
        prover::Buffer<Fp>,
        prover::Buffer<Fp>,
    ) -> Result<(), Error>,
) -> Result<(), Error> {
    const _: () = assert!(N.is_multiple_of(FOLD_CHUNK_ROWS));
    let windows = (0..EXTENDED_ROTATION_STRIDE)
        .flat_map(|residue| {
            (0..N)
                .step_by(FOLD_CHUNK_ROWS)
                .map(move |k_offset| FoldWindow { residue, k_offset })
        })
        .collect::<Vec<_>>();
    let chunks = execution.map(windows.clone(), move |window, _| {
        let class_rows = |folds: bool| if folds { FOLD_CHUNK_ROWS } else { 0 };
        let mut chunk_8n = execution.buffer(FOLD_CHUNK_ROWS, false);
        let mut chunk_4n = execution.buffer(class_rows(window.residue.is_multiple_of(2)), false);
        let mut chunk_2n = execution.buffer(class_rows(window.residue.is_multiple_of(4)), false);
        let mut chunk_n = execution.buffer(class_rows(window.residue == 0), false);
        fold_chunk(
            window,
            &mut chunk_8n,
            &mut chunk_4n,
            &mut chunk_2n,
            &mut chunk_n,
        )?;
        Ok::<_, Error>((chunk_8n, chunk_4n, chunk_2n, chunk_n))
    });
    for (window, chunk) in windows.into_iter().zip(chunks) {
        let (chunk_8n, chunk_4n, chunk_2n, chunk_n) = chunk?;
        assemble(window, chunk_8n, chunk_4n, chunk_2n, chunk_n)?;
    }
    Ok(())
}

#[test]
fn parallel_classed_fold_matches_serial_fold() {
    use prover::quotient::FoldWindow;
    let y = <prover::Fp>::from_u64(31);
    // Every class value is a function of its absolute row alone.
    let value_8n = move |row: usize| {
        <prover::Fp>::from_u64(row as u64 + 2)
            .mul_add(&y, &<prover::Fp>::from_u64((row * row + 5) as u64))
    };
    let value_4n = |row: usize| <prover::Fp>::from_u64((row * 3 + 1) as u64);
    let value_2n = |row: usize| <prover::Fp>::from_u64((row * 7 + 2) as u64);
    let value_n = |row: usize| <prover::Fp>::from_u64((row + 9) as u64);
    let serial_8n: Vec<_> = (0..prover::EXTENDED_N).map(value_8n).collect();
    let serial_4n: Vec<_> = (0..prover::EXTENDED_N).step_by(2).map(value_4n).collect();
    let serial_2n: Vec<_> = (0..prover::EXTENDED_N).step_by(4).map(value_2n).collect();
    let serial_n: Vec<_> = (0..prover::EXTENDED_N).step_by(8).map(value_n).collect();

    let (mut parallel_8n, mut parallel_4n, mut parallel_2n, mut parallel_n) = (
        alloc::vec![ <prover::Fp>::ZERO; prover::EXTENDED_N],
        alloc::vec![ <prover::Fp>::ZERO; prover::EXTENDED_N / 2],
        alloc::vec![ <prover::Fp>::ZERO; prover::EXTENDED_N / 4],
        alloc::vec![ <prover::Fp>::ZERO; prover::EXTENDED_N / 8],
    );
    let mut windows_seen = 0;
    fold_classed_rows(
        crate::test_codec::execution(),
        move |window: FoldWindow, c8, c4, c2, c1| {
            // The class chunks are full for the residues that fold on them
            // and empty otherwise.
            assert_eq!(
                c4.len(),
                if window.residue.is_multiple_of(2) {
                    c8.len()
                } else {
                    0
                }
            );
            assert_eq!(
                c2.len(),
                if window.residue.is_multiple_of(4) {
                    c8.len()
                } else {
                    0
                }
            );
            assert_eq!(c1.len(), if window.residue == 0 { c8.len() } else { 0 });
            for (offset, slot) in c8.iter_mut().enumerate() {
                let row = window.row(offset);
                *slot = value_8n(row);
                if !c4.is_empty() {
                    c4[offset] = value_4n(row);
                }
                if !c2.is_empty() {
                    c2[offset] = value_2n(row);
                }
                if !c1.is_empty() {
                    c1[offset] = value_n(row);
                }
            }
            Ok(())
        },
        |window, c8, c4, c2, c1| {
            windows_seen += 1;
            for (offset, value) in c8.into_iter().enumerate() {
                parallel_8n[window.row(offset)] = value;
            }
            for (offset, value) in c4.into_iter().enumerate() {
                parallel_4n[window.row(offset) / 2] = value;
            }
            for (offset, value) in c2.into_iter().enumerate() {
                parallel_2n[window.row(offset) / 4] = value;
            }
            for (offset, value) in c1.into_iter().enumerate() {
                parallel_n[window.row(offset) / 8] = value;
            }
            Ok(())
        },
    )
    .unwrap();
    assert_eq!(windows_seen, prover::EXTENDED_N / prover::FOLD_CHUNK_ROWS);
    assert_eq!(reduced_values(&(parallel_8n)), reduced_values(&(serial_8n)));
    assert_eq!(reduced_values(&(parallel_4n)), reduced_values(&(serial_4n)));
    assert_eq!(reduced_values(&(parallel_2n)), reduced_values(&(serial_2n)));
    assert_eq!(reduced_values(&(parallel_n)), reduced_values(&(serial_n)));
}

/// Dense single-accumulator quotient reference: every term is evaluated
/// on the full extended coset and folded in protocol order (gates
/// through the tree evaluator), then telescoped through the
/// vanishing division — the former dense shape, kept as the class-split
/// oracle.
fn dense_quotient_coefficients_reference(
    target: &crate::native::target::FixedTarget,
    instance_polynomials: &[prover::SharedPoly],
    advice: &prover::AdvicePrefix,
    lookup: &prover::LookupPrefix,
    permutations: &prover::PermutationPrefix,
    lookup_products: &prover::LookupProductPrefix,
    y: &prover::Fp,
) -> Vec<prover::Fp> {
    use crate::native::evaluation::{evaluate_expression_coset_row, rotated_extended_row};
    use crate::native::target::ColumnKind;
    use crate::native::target::PERMUTATION_CHUNK_LEN;
    use crate::native::{polynomial::quotient_numerator_to_coefficients, target::BLINDING_FACTORS};
    use prover::lookup::compress_expressions_on_coset;
    use prover::{EXTENDED_N, Fp, N, generated_expressions, owned_lagrange_to_forms};

    fn fold(numerator: &mut [Fp], y: &Fp, term: impl Fn(usize) -> Fp) {
        for (row, accumulator) in numerator.iter_mut().enumerate() {
            *accumulator = accumulator.mul_add(y, &term(row));
        }
    }

    let fixed_coset_views = target.fixed_polynomials().cosets().collect_views();
    let sigma_coset_views = target.sigma_polynomials().cosets().collect_views();
    let fixed_cosets = fixed_coset_views.as_slice();
    let sigma_cosets = sigma_coset_views.as_slice();
    let instance_cosets: Vec<Vec<Fp>> = instance_polynomials
        .iter()
        .map(|instance| {
            owned_lagrange_to_forms(
                instance.to_vec(),
                target.fft(),
                crate::test_codec::execution(),
            )
            .unwrap()
            .coset
            .to_dense_rows()
        })
        .collect();
    let advice_cosets: Vec<Vec<Vec<Fp>>> = advice
        .values
        .iter()
        .map(|columns| {
            columns
                .iter()
                .map(|column| {
                    owned_lagrange_to_forms(
                        column.to_vec(),
                        crate::test_codec::target().fft(),
                        crate::test_codec::execution(),
                    )
                    .unwrap()
                    .coset
                    .to_dense_rows()
                })
                .collect()
        })
        .collect();
    let beta_deltas: Vec<Fp> = target
        .permutation_identities()
        .deltas()
        .iter()
        .map(|delta| lookup.beta.mul(delta))
        .collect();
    let l_0 = target.boundaries().l_0();
    let l_last = target.boundaries().l_last();
    let active_rows = target.boundaries().active_rows();
    let coset_points: Vec<Fp> = (0..EXTENDED_N)
        .scan(*target.domain().coset_generator(), |point, _| {
            let value = *point;
            *point = point.mul(target.domain().extended_omega());
            Some(value)
        })
        .collect();

    let mut numerator = alloc::vec![ <Fp>::ZERO; EXTENDED_N];
    for action_index in 0..advice.values.len() {
        let action_advice = &advice_cosets[action_index];
        let instance_slice = &instance_cosets[action_index..=action_index];
        for program in 0..generated_expressions::GATE_CONSTRAINT_COUNT {
            fold(&mut numerator, y, |row| {
                evaluate_expression_coset_row(
                    program,
                    target,
                    action_advice,
                    fixed_cosets,
                    instance_slice,
                    row,
                )
                .unwrap()
            });
        }

        // The dense reference reads every product on the full extended
        // coset; the singleton set's 2N class form is re-expanded here.
        let products: Vec<Vec<Fp>> = permutations.products[action_index]
            .iter()
            .map(|product| product.forms.dense_coset().unwrap())
            .collect();
        fold(&mut numerator, y, |row| {
            <Fp>::ONE.sub(&products[0][row]).mul(&l_0[row])
        });
        fold(&mut numerator, y, |row| {
            products[products.len() - 1][row]
                .square()
                .sub(&products[products.len() - 1][row])
                .mul(&l_last[row])
        });
        for set_index in 1..products.len() {
            fold(&mut numerator, y, |row| {
                let last_row = rotated_extended_row(row, -((BLINDING_FACTORS + 1) as i32));
                products[set_index][row]
                    .sub(&products[set_index - 1][last_row])
                    .mul(&l_0[row])
            });
        }
        for (set_index, (columns, chunk_beta_deltas)) in target
            .permutation_columns()
            .chunks(PERMUTATION_CHUNK_LEN)
            .zip(beta_deltas.chunks(PERMUTATION_CHUNK_LEN))
            .enumerate()
        {
            let sigma_columns = &sigma_cosets[set_index * PERMUTATION_CHUNK_LEN..][..columns.len()];
            // Dense row-major copies of the set's columns, whatever their
            // source layout.
            let column_values: Vec<Vec<Fp>> = columns
                .iter()
                .map(|column| {
                    (0..EXTENDED_N)
                        .map(|row| match column.kind {
                            ColumnKind::Advice => action_advice[column.index][row],
                            ColumnKind::Fixed => fixed_cosets[column.index][row],
                            ColumnKind::Instance => instance_cosets[action_index][row],
                        })
                        .collect()
                })
                .collect();
            fold(&mut numerator, y, |row| {
                let next_row = rotated_extended_row(row, 1);
                let mut left = products[set_index][next_row];
                let mut right = products[set_index][row];
                for ((values, sigma), beta_delta) in column_values
                    .iter()
                    .zip(sigma_columns)
                    .zip(chunk_beta_deltas)
                {
                    left = left.mul(
                        &values[row]
                            .add(&lookup.beta.mul(&sigma[row]))
                            .add(&lookup.gamma),
                    );
                    right = right.mul(
                        &values[row]
                            .add(&beta_delta.mul(&coset_points[row]))
                            .add(&lookup.gamma),
                    );
                }
                left.sub(&right).mul(&active_rows[row])
            });
        }

        for (lookup_index, permuted) in lookup.lookups[action_index].iter().enumerate() {
            let ranges = target.lookups()[lookup_index];
            let compressed_input = compress_expressions_on_coset(
                ranges.inputs(),
                &advice.theta,
                target,
                action_advice,
                fixed_cosets,
                instance_slice,
            )
            .unwrap();
            let compressed_table = compress_expressions_on_coset(
                ranges.tables(),
                &advice.theta,
                target,
                action_advice,
                fixed_cosets,
                instance_slice,
            )
            .unwrap();
            let permuted_input = owned_lagrange_to_forms(
                permuted.permuted_input.to_vec(),
                crate::test_codec::target().fft(),
                crate::test_codec::execution(),
            )
            .unwrap()
            .coset;
            let permuted_table = owned_lagrange_to_forms(
                permuted.permuted_table.to_vec(),
                crate::test_codec::target().fft(),
                crate::test_codec::execution(),
            )
            .unwrap()
            .coset;
            let product = lookup_products.products[action_index][lookup_index]
                .forms
                .dense_coset()
                .unwrap();
            fold(&mut numerator, y, |row| {
                <Fp>::ONE.sub(&product[row]).mul(&l_0[row])
            });
            fold(&mut numerator, y, |row| {
                product[row].square().sub(&product[row]).mul(&l_last[row])
            });
            fold(&mut numerator, y, |row| {
                let next_row = rotated_extended_row(row, 1);
                let left = product[next_row]
                    .mul(&permuted_input[row].add(&lookup.beta))
                    .mul(&permuted_table[row].add(&lookup.gamma));
                let right = product[row]
                    .mul(&compressed_input[row].add(&lookup.beta))
                    .mul(&compressed_table[row].add(&lookup.gamma));
                left.sub(&right).mul(&active_rows[row])
            });
            fold(&mut numerator, y, |row| {
                permuted_input[row].sub(&permuted_table[row]).mul(&l_0[row])
            });
            fold(&mut numerator, y, |row| {
                let previous_row = rotated_extended_row(row, -1);
                permuted_input[row]
                    .sub(&permuted_table[row])
                    .mul(&permuted_input[row].sub(&permuted_input[previous_row]))
                    .mul(&active_rows[row])
            });
        }
    }
    quotient_numerator_to_coefficients(numerator, N).unwrap()
}

/// The class-split quotient must match a dense, protocol-ordered fold.
/// Challenge overrides exercise zero weights, equal weights, and cancellation
/// across one and two Actions as well as the original transcript challenges.
#[test]
fn class_split_quotient_matches_dense_reference_on_fixtures() {
    use crate::native::target::ColumnKind;
    use crate::native::witness;
    use prover::Fp;

    const ONE_ACTION_TAPE: &[u8] = crate::test_codec::FIXTURES[0].tape;
    const TWO_ACTION_TAPE: &[u8] = crate::test_codec::FIXTURES[1].tape;

    let target = crate::test_codec::target();
    #[derive(Clone, Copy, Debug)]
    enum ChallengeCase {
        Original,
        Fold(Fp),
        FixedLeftZero,
        FixedRightZero,
        LookupTableZero,
    }

    for (fixture, tape_bytes, case) in [
        (ONE_ACTION_FIXTURE, ONE_ACTION_TAPE),
        (TWO_ACTION_FIXTURE, TWO_ACTION_TAPE),
    ]
    .into_iter()
    .flat_map(|(fixture, tape_bytes)| {
        [
            ChallengeCase::Original,
            ChallengeCase::Fold(<Fp>::ZERO),
            ChallengeCase::Fold(<Fp>::ONE),
            ChallengeCase::Fold(<Fp>::ONE.neg()),
            ChallengeCase::FixedLeftZero,
            ChallengeCase::FixedRightZero,
            ChallengeCase::LookupTableZero,
        ]
        .map(|case| (fixture, tape_bytes, case))
    }) {
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
        let mut lookup = prover
            .commit_lookup_permutations(&advice, feeds, randomness.lookup_permutations)
            .unwrap();
        let (permutations, lookup_products) = prover
            .commit_product_arguments(
                &advice,
                &lookup,
                randomness.permutation_products,
                randomness.lookup_products,
            )
            .unwrap();
        let mut vanishing = prover
            .commit_vanishing_random_polynomial(
                &permutations,
                &lookup_products,
                randomness.vanishing,
            )
            .unwrap();
        // Changing challenges after product construction need not preserve
        // the witness relation: this compares the two quotient polynomials
        // for arbitrary inputs, including zeros in the shared factors.
        match case {
            ChallengeCase::Original => {}
            ChallengeCase::Fold(y) => vanishing.y = y,
            ChallengeCase::FixedLeftZero | ChallengeCase::FixedRightZero => {
                let (index, column) = target
                    .permutation_columns()
                    .iter()
                    .enumerate()
                    .find(|(_, column)| column.kind == ColumnKind::Fixed)
                    .unwrap();
                let row = prover::EXTENDED_N - 1;
                let fixed = target.fixed_polynomials().cosets().collect_views();
                let offset = if matches!(case, ChallengeCase::FixedLeftZero) {
                    let sigma = target.sigma_polynomials().cosets().collect_views();
                    lookup.beta.mul(&sigma.as_slice()[index][row])
                } else {
                    let point = target
                        .domain()
                        .coset_generator()
                        .mul(&target.domain().extended_omega().pow_u64(row as u64));
                    lookup
                        .beta
                        .mul(&target.permutation_identities().deltas()[index])
                        .mul(&point)
                };
                lookup.gamma = fixed.as_slice()[column.index][row].add(&offset).neg();
            }
            ChallengeCase::LookupTableZero => {
                let fixed = target.fixed_polynomials().cosets().collect_views();
                let table = prover::lookup::compress_expressions_on_coset(
                    target.lookups()[1].tables(),
                    &advice.theta,
                    target,
                    &[],
                    fixed.as_slice(),
                    &[],
                )
                .unwrap();
                lookup.gamma = table[prover::FOLD_CHUNK_ROWS * 8].neg();
            }
        }
        // The prover released its dense instance columns with the product
        // stage; the reference rebuilds them from the statement records.
        let instance_polynomials = request
            .native_statements()
            .iter()
            .map(|statement| prover::SharedPoly::new(statement.instance_column(prover::N)))
            .collect::<Vec<_>>();
        let dense = dense_quotient_coefficients_reference(
            target,
            &instance_polynomials,
            &advice,
            &lookup,
            &permutations,
            &lookup_products,
            &vanishing.y,
        );
        let quotient = prover
            .construct_quotient(
                advice,
                lookup,
                permutations,
                lookup_products,
                &vanishing,
                randomness.quotient_piece_blinds,
                randomness.ipa_mask,
            )
            .unwrap();
        let class_split: Vec<Fp> = quotient
            .pieces
            .iter()
            .flat_map(|piece| piece.coefficients.iter().copied())
            .collect();
        assert_eq!(
            reduced_values(&(class_split)),
            reduced_values(&(dense)),
            "{case:?} with {} Actions",
            request.action_count(),
        );
    }
}
