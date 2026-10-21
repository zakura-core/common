//! Product walks and commitments against serial and dense references.

use super::{ONE_ACTION_FIXTURE, TWO_ACTION_FIXTURE, randomness_from_tape};
use crate::native::prover::{self, ProverPrefix};
use crate::native::test_support::reduced_values;
use crate::{Error, types::ProvingRequest};
use alloc::vec::Vec;

/// The two-lane exclusive walk reproduces the serial ratio scan exactly on
/// even, odd, tiny, and empty lengths, reports every denominator in row
/// order, and hands a zero denominator product back to the caller.
#[test]
fn two_lane_exclusive_walk_matches_serial_ratio_scan() {
    use prover::Fp;
    use prover::products::two_lane_exclusive_walk;

    let sample = |tag: u64, index: usize| {
        <Fp>::from_u64(
            (index as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ (tag * 0x1234_5678_9abc_def1),
        )
        .square()
        .add(&<Fp>::from_u64(tag + 1))
    };
    for len in [0usize, 1, 2, 3, 8, 15, 16, 267, 624, 2_043] {
        let numerators = (0..len).map(|index| sample(1, index)).collect::<Vec<_>>();
        let denominators = (0..len).map(|index| sample(2, index)).collect::<Vec<_>>();
        let sentinel = <Fp>::from_u64(71);
        let mut states = alloc::vec![sentinel; len + 3];
        let mut recorded = alloc::vec![sentinel; len + 3];
        let final_product = two_lane_exclusive_walk(
            len,
            |index| Ok((numerators[index], denominators[index])),
            &mut states,
            &mut recorded,
        )
        .unwrap()
        .expect("nonzero denominators invert");
        assert_eq!(
            reduced_values(&recorded[..len]),
            reduced_values(&(denominators))
        );
        let mut expected = <Fp>::ONE;
        assert_eq!(
            reduced_values(&states[len..]),
            reduced_values(&[sentinel; 3])
        );
        assert_eq!(
            reduced_values(&recorded[len..]),
            reduced_values(&[sentinel; 3])
        );
        for (index, state) in states[..len].iter().enumerate() {
            assert_eq!(
                (*state).reduce(),
                (expected).reduce(),
                "len {len}, row {index}"
            );
            expected = expected
                .mul(&numerators[index])
                .mul(&denominators[index].invert().unwrap());
        }
        assert_eq!(
            (final_product).reduce(),
            (expected).reduce(),
            "len {len}, final"
        );
    }

    // A zero denominator anywhere is reported, with the denominators
    // recorded for the caller's fallback.
    let mut states = alloc::vec![ <Fp>::ZERO; 5];
    let mut recorded = alloc::vec![ <Fp>::ONE; 5];
    let walk = two_lane_exclusive_walk(
        5,
        |index| {
            Ok((
                <Fp>::from_u64(index as u64 + 2),
                if index == 3 {
                    <Fp>::ZERO
                } else {
                    <Fp>::from_u64(index as u64 + 7)
                },
            ))
        },
        &mut states,
        &mut recorded,
    )
    .unwrap();
    assert!(walk.is_none());
    assert_eq!(recorded.len(), 5);
    assert!(recorded[3].is_zero());

    // Reject short scratch before evaluating a row or changing either slice.
    for (states_len, denominators_len) in [(4, 5), (5, 4)] {
        let mut states = vec![<Fp>::ONE; states_len];
        let mut denominators = vec![<Fp>::ONE; denominators_len];
        assert_eq!(
            two_lane_exclusive_walk(
                5,
                |_| panic!("short scratch evaluated a row"),
                &mut states,
                &mut denominators
            )
            .err(),
            Some(Error::InternalInvariant)
        );
        assert!(
            states
                .iter()
                .chain(&denominators)
                .all(|value| value.reduce() == <Fp>::ONE.reduce())
        );
    }
}

#[test]
/// The zero-preserving inverter's remaining contract cases: empty and
/// all-nonzero inputs (the zero-containing case is the test below).
fn grouped_batch_inversion_handles_empty_and_nonzero_groups() {
    let mut scratch = Vec::new();
    let mut empty: [Vec<prover::Fp>; 0] = [];
    prover::products::batch_invert_groups(&mut empty, &mut scratch);
    let mut empty_groups = [Vec::new(), Vec::new()];
    prover::products::batch_invert_groups(&mut empty_groups, &mut scratch);
    assert!(empty_groups.iter().all(Vec::is_empty));

    let originals = [
        (1..=5u64).map(<prover::Fp>::from_u64).collect::<Vec<_>>(),
        alloc::vec![<prover::Fp>::from_u64(0x1234_5678), <prover::Fp>::ONE.neg()],
    ];
    let mut groups = originals.clone();
    prover::products::batch_invert_groups(&mut groups, &mut scratch);
    for (group, original) in groups.iter().zip(&originals) {
        for (inverse, value) in group.iter().zip(original) {
            assert_eq!((*inverse).reduce(), (value.invert().unwrap()).reduce());
        }
    }
}

/// Dense-shadow reference for the active-edge permutation product
/// build: materializes every numerator and denominator factor for every
/// row and column, exactly as the pre-schedule implementation did, and
/// must agree bit-for-bit with `prepare_permutation_products` for
/// arbitrary values and challenges.
#[test]
fn active_edge_permutation_products_match_dense_reference() {
    use prover::Fp;
    let beta = <Fp>::from_u64(0x5eed_beef).square().add(&<Fp>::from_u64(3));
    let gamma = <Fp>::from_u64(0x00c0_ffee)
        .square()
        .add(&<Fp>::from_u64(11));
    check_permutation_products_against_dense_reference(beta, Some(gamma));
    // A challenge that zeroes one active row's denominator factor
    // exercises the walk's reference fallback (zero inverse, zero product
    // from the following row on) in every set behind it.
    check_permutation_products_against_dense_reference(beta, None);
}

/// Builds one Action's permutation products for arbitrary column values
/// under `beta` and either the given `gamma` or one chosen to zero the
/// first active row's first denominator factor of set 0, and checks them
/// against the dense reference.
fn check_permutation_products_against_dense_reference(beta: prover::Fp, gamma: Option<prover::Fp>) {
    use crate::native::target::PERMUTATION_CHUNK_LEN;
    use prover::{ADVICE_COLUMNS, Fp, N, USABLE_ROWS_END};

    let target = crate::test_codec::target();
    let set_count = target
        .permutation_columns()
        .len()
        .div_ceil(PERMUTATION_CHUNK_LEN);
    let advice_columns = (0..ADVICE_COLUMNS)
        .map(|column| {
            prover::SharedPoly::new(
                (0..N)
                    .map(|row| {
                        <Fp>::from_u64((row as u64) * 977 + column as u64 * 131 + 29).square()
                    })
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<Vec<_>>();
    let instance_column = (0..N)
        .map(|row| <Fp>::from_u64((row as u64) * 1_009 + 41).square())
        .collect::<Vec<_>>();
    let gamma = gamma.unwrap_or_else(|| {
        let &(row, mask) = target.permutation_edge_schedule()[0]
            .active_rows()
            .first()
            .expect("set 0 has copy edges");
        let column = mask.trailing_zeros() as usize;
        let value = prover::products::permutation_column_values(
            &target.permutation_columns()[column],
            &advice_columns,
            target.fixed_values(),
            &instance_column,
            N,
        )
        .unwrap()[usize::from(row)];
        beta.mul(&target.sigma_values()[column][usize::from(row)])
            .add(&value)
            .neg()
    });
    let blindings = || -> [crate::native::randomness::PermutationBlinding; crate::native::randomness::PERMUTATION_SETS_PER_ACTION] {
        core::array::from_fn(|set| crate::native::randomness::PermutationBlinding {
            rows: core::array::from_fn(|row| <Fp>::from_u64((set * 7 + row + 1) as u64)),
            blind: <Fp>::from_u64(set as u64 + 5),
        })
    };

    let products = prover::products::prepare_permutation_products(
        target,
        core::slice::from_ref(&advice_columns),
        &[prover::SharedPoly::new(instance_column.clone())],
        alloc::vec![blindings()],
        &beta,
        &gamma,
        set_count,
        crate::test_codec::execution(),
    )
    .unwrap()
    .pop()
    .unwrap();
    assert_eq!(products.len(), set_count);

    let mut last_product = <Fp>::ONE;
    for (((columns, sigma_columns), identities), (product, blinding)) in target
        .permutation_columns()
        .chunks(PERMUTATION_CHUNK_LEN)
        .zip(target.sigma_values().chunks(PERMUTATION_CHUNK_LEN))
        .zip(
            target
                .permutation_identities()
                .values()
                .chunks(PERMUTATION_CHUNK_LEN),
        )
        .zip(products.iter().zip(blindings()))
    {
        let values = columns
            .iter()
            .map(|column| {
                prover::products::permutation_column_values(
                    column,
                    &advice_columns,
                    target.fixed_values(),
                    &instance_column,
                    N,
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let mut ratios = alloc::vec![ <Fp>::ONE; N];
        for (value, sigma) in values.iter().zip(sigma_columns) {
            for ((ratio, value), sigma_value) in ratios.iter_mut().zip(*value).zip(sigma) {
                *ratio = ratio.mul(&beta.mul(sigma_value).add(&gamma).add(value));
            }
        }
        let mut groups = [ratios];
        prover::products::batch_invert_groups(&mut groups, &mut Vec::new());
        let [mut ratios] = groups;
        let mut state = last_product;
        for row in 0..USABLE_ROWS_END {
            let mut current = ratios[row];
            for (value, identity) in values.iter().zip(identities) {
                current = current.mul(&beta.mul(&identity[row]).add(&gamma).add(&value[row]));
            }
            ratios[row] = state;
            state = state.mul(&current);
        }
        ratios[USABLE_ROWS_END] = state;
        ratios[USABLE_ROWS_END + 1..].clone_from_slice(&blinding.rows);
        last_product = state;

        assert!(
            reduced_values(&(*product.forms.staged().unwrap().to_vec()))
                == reduced_values(&(ratios))
        );

        // The scanned step runs must reproduce every row of the
        // interval-committed usable prefix, and the interval-path
        // commitment must equal the dense Lagrange commitment.
        let mut runs = alloc::vec![(0u32, ratios[0])];
        runs.reserve_exact(USABLE_ROWS_END - 1);
        for (index, pair) in ratios[..USABLE_ROWS_END].windows(2).enumerate() {
            if (pair[1]).reduce() != (pair[0]).reduce() {
                runs.push((index as u32 + 1, pair[1]));
            }
        }
        let mut expanded = alloc::vec![ <Fp>::ZERO; USABLE_ROWS_END];
        for (index, &(start, value)) in runs.iter().enumerate() {
            let end = runs
                .get(index + 1)
                .map_or(USABLE_ROWS_END, |&(next, _)| next as usize);
            assert!((start as usize) < end);
            expanded[start as usize..end].fill(value);
        }
        assert!(reduced_values(&(expanded[..])) == reduced_values(&(ratios[..USABLE_ROWS_END])));

        let dense = target
            .parameters()
            .commit_lagrange_projective(
                &ratios,
                &blinding.blind,
                &mut crate::native::commitment::MsmWorkspace::new(),
                crate::test_codec::execution(),
            )
            .unwrap();
        let interval = target
            .parameters()
            .commit_lagrange_mixed_batch_projective(
                &[(
                    crate::native::target::LagrangeCommitScalars::PiecewiseConstantPrefix {
                        runs: &runs,
                        dense: &prover::SharedPoly::new(ratios.to_vec()),
                    },
                    &blinding.blind,
                )],
                &mut crate::native::commitment::MsmWorkspace::new(),
                crate::test_codec::execution(),
            )
            .unwrap();
        let normalized = crate::native::commitment::normalized(&[dense, interval[0]]);
        assert_eq!(normalized[0], normalized[1]);
    }
}

/// On the real fixture tapes, every permutation
/// grand-product commitment produced through the prefix-sum interval
/// path must equal the dense commitment of the same polynomial under
/// the same blind.
#[test]
fn interval_permutation_product_commitments_match_dense_on_fixtures() {
    use crate::native::{commitment::normalized, witness};

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
        let (permutations, _lookups) = prover
            .commit_product_arguments(
                &advice,
                &lookup,
                randomness.permutation_products,
                randomness.lookup_products,
            )
            .unwrap();
        for action_products in &permutations.products {
            for product in action_products {
                // The staged Lagrange rows were replaced by the retained
                // coefficient form, so the dense recomputation commits
                // that form against the coefficient-basis generators.
                let dense = target
                    .parameters()
                    .commit_coefficients_batch_projective(
                        &[(product.forms.coefficients().unwrap(), &product.blind)],
                        &mut crate::native::commitment::MsmWorkspace::new(),
                        crate::test_codec::execution(),
                    )
                    .unwrap();
                let dense = normalized(&dense);
                assert_eq!(dense[0], product.commitment);
            }
        }
    }
}
