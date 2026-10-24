use crate::native::test_support::reduced_values;

// Differential checks and independent reference implementations for this module.

use crate::{Error, native::witness::build_native_witness, types::ProvingRequest};
use alloc::{sync::Arc, vec::Vec};

use super::{
    AdviceMatrix, SharedPoly, check_witness_constraints,
    copies::check_copies,
    prepared_lookup_table_tuples,
    reference::{
        check_gates, check_gates_batch, check_gates_fixed, check_gates_full, check_gates_serial,
        check_lookups,
    },
};
use crate::native::{field::Fp, target::ColumnKind};

const ONE_ACTION: &[u8] = include_bytes!("../../../tests/fixtures/one-action.iwpr");

const TWO_ACTION: &[u8] = include_bytes!("../../../tests/fixtures/two-action.iwpr");

const COMPACT_FIXTURES: [&[u8]; 2] = [ONE_ACTION, TWO_ACTION];

#[test]
fn sparse_gate_check_requires_prepared_metadata() {
    let target = crate::test_codec::target();
    let advice: &[Vec<Fp>] = &[];
    assert_eq!(
        super::super::evaluation::sparse_gate_expression_is_zero(
            super::super::generated_expressions::GATE_CONSTRAINT_COUNT,
            target,
            advice,
            &[],
        ),
        Err(Error::InternalInvariant),
    );
}

/// The shared full-round work has identical active rows. The other
/// repeated bodies cataloged in HANDOFF execute on disjoint rows, so
/// caching them across selectors would not eliminate any evaluation.
#[test]
fn shared_preflight_active_row_census() {
    let target = crate::test_codec::target();
    let rows = |program| target.gate_active_rows(program).unwrap();
    assert!(!rows(75).is_empty());
    assert_eq!(rows(75), rows(76));
    assert_eq!(rows(75), rows(77));
    let overlap = |left, right| {
        rows(left)
            .iter()
            .filter(|row| rows(right).binary_search(row).is_ok())
            .count()
    };
    assert_eq!(overlap(75, 78), 0);
    let body = |program| {
        super::super::generated_expressions::program_trees(program)
            .unwrap()
            .dynamic_body()
    };
    let pairs = (119..156).map(|left| (left, left + 37)).chain(
        [135, 140, 172, 177]
            .into_iter()
            .enumerate()
            .flat_map(|(i, left)| {
                [135, 140, 172, 177]
                    .into_iter()
                    .skip(i + 1)
                    .flat_map(move |right| {
                        (0..4).map(move |offset| (left + offset, right + offset))
                    })
            }),
    );
    for (left, right) in pairs {
        assert_eq!(body(left), body(right));
        assert_eq!(overlap(left, right), 0, "programs {left} and {right}");
    }
}

#[test]
fn grouped_poseidon_preflight_rejects_corrupted_outputs() {
    let request = ProvingRequest::decode_iwpr_for_test(ONE_ACTION).unwrap();
    let matrix = build_native_witness(&request.actions()[0])
        .unwrap()
        .into_matrix()
        .unwrap();
    let target = crate::test_codec::target();
    let mut instance = request.actions()[0].statement.native_values();
    instance.resize_with(super::N, || <Fp>::ZERO);
    let instance = SharedPoly::new(instance);
    let rows = target.gate_active_rows(75).unwrap();
    for output in [22, 18, 19] {
        for index in [0, 63, 64, rows.len() - 1] {
            let Some(&row) = rows.get(index) else {
                continue;
            };
            let query = &target.queries().advice()[output];
            let row = super::super::evaluation::rotated_row(usize::from(row), query.rotation);
            let mut columns = matrix.columns().to_vec();
            columns[query.column][row] = columns[query.column][row].add(&<Fp>::ONE);
            let corrupted = Arc::new(
                AdviceMatrix::from_columns_with_support(columns, matrix.support_words().to_vec())
                    .unwrap(),
            );
            assert_eq!(
                check_gates(target, &corrupted, &instance),
                Err(Error::UnsatisfiedWitness)
            );
            assert_eq!(
                check_gates_full(target, &corrupted, &instance),
                Err(Error::UnsatisfiedWitness)
            );
        }
    }
}

#[test]
fn native_preflight_accepts_checked_fixtures() {
    for fixture in COMPACT_FIXTURES {
        let request = ProvingRequest::decode_iwpr_for_test(fixture).unwrap();
        let matrices = request
            .actions()
            .iter()
            .map(|action| Arc::new(build_native_witness(action).unwrap().into_matrix().unwrap()))
            .collect::<Vec<_>>();
        assert!(
            check_witness_constraints(
                crate::test_codec::execution(),
                crate::test_codec::target(),
                &request,
                &request.native_statements(),
                &matrices,
                &crate::native::prover::LookupWorkspace::default(),
            )
            .is_ok()
        );
        let target = crate::test_codec::target();
        for (action, matrix) in request.actions().iter().zip(&matrices) {
            let mut instance = action.statement.native_values();
            instance.resize_with(super::N, || <Fp>::ZERO);
            let instance = SharedPoly::new(instance);
            assert_eq!(check_gates(target, matrix, &instance), Ok(()));
            assert_eq!(check_gates_fixed(target, matrix, &instance), Ok(()));
            assert_eq!(check_gates_serial(target, matrix, &instance), Ok(()));
            assert_eq!(check_gates_full(target, matrix, &instance), Ok(()));
        }
    }
}

#[test]
fn compact_fixtures_cover_required_action_semantics() {
    let single = ProvingRequest::decode_iwpr_for_test(ONE_ACTION).unwrap();
    assert_eq!(single.action_count(), 1);
    let batch = ProvingRequest::decode_iwpr_for_test(TWO_ACTION).unwrap();
    assert_eq!(batch.action_count(), 2);

    for action in single.actions().iter().chain(batch.actions()) {
        assert_eq!(action.witness.v_old, 0);
        assert_eq!(action.witness.v_new, 0);
        assert!(action.statement.enable_spend && action.statement.enable_output);
        assert!(!action.statement.disable_cross_address);
        assert!(
            action.witness.g_d_old != action.witness.g_d_new
                || action.witness.pk_d_old != action.witness.pk_d_new
        );
    }
}

#[test]
fn compact_fixture_hashes_are_frozen() {
    use sha2::{Digest, Sha256};

    for (fixture, expected) in [
        (
            ONE_ACTION,
            "a8049f10af1bcc04c1caddcfcac68b95b690fa4a8e3d579afc3b16ca7934ac70",
        ),
        (
            TWO_ACTION,
            "bea52cf6ca9bd884738e6f4c6c6237c01fe66a0aca2989396aa4999b914eb1a8",
        ),
    ] {
        assert_eq!(hex::encode(Sha256::digest(fixture)), expected);
    }
}

/// The proof-wide gate and lookup waves reproduce the per-Action
/// checks — identical identities for every Action — and attribute a
/// corrupted Action's failure to that Action alone.
#[test]
fn batched_preflight_waves_match_per_action_checks() {
    let request = ProvingRequest::decode_iwpr_for_test(TWO_ACTION).unwrap();
    let target = crate::test_codec::target();
    let matrices = request
        .actions()
        .iter()
        .map(|action| Arc::new(build_native_witness(action).unwrap().into_matrix().unwrap()))
        .collect::<Vec<_>>();
    let instances = request
        .actions()
        .iter()
        .map(|action| {
            let mut instance = action.statement.native_values();
            instance.resize_with(super::N, || <Fp>::ZERO);
            SharedPoly::new(instance)
        })
        .collect::<Vec<_>>();
    assert_eq!(matrices.len(), 2);
    let scratch = super::LookupWorkspace::default();
    scratch.provision_ids(matrices.len());
    let inventory = scratch.inventory();
    scratch.dirty();

    let gates = check_gates_batch(crate::test_codec::execution(), target, &matrices);
    assert_eq!(gates, alloc::vec![Ok(()), Ok(())]);
    let batched = super::check_lookups_batch_in(
        crate::test_codec::execution(),
        target,
        &matrices,
        &instances,
        &scratch,
    );
    for ((matrix, instance), batched) in matrices.iter().zip(&instances).zip(batched) {
        let single = check_lookups(target, matrix, instance).unwrap();
        let batched = batched.unwrap();
        assert_eq!(single.lookups().len(), batched.lookups().len());
        for (single, batched) in single.lookups().iter().zip(batched.lookups()) {
            assert_eq!(single.programs().indices(), batched.programs().indices());
            assert_eq!(single.ids(), batched.ids());
        }
    }
    assert_eq!(scratch.inventory(), inventory);

    // Corrupting the second Action alone fails only its slot, on the
    // same cells the single-Action test corrupts.
    let corrupt = |column: usize, row: usize, delta: Fp| {
        let mut columns = matrices[1].columns().to_vec();
        columns[column][row] = columns[column][row].add(&delta);
        let mut corrupted = matrices.clone();
        corrupted[1] = Arc::new(
            AdviceMatrix::from_columns_with_support(columns, matrices[1].support_words().to_vec())
                .unwrap(),
        );
        corrupted
    };
    let lookup_corrupted = corrupt(9, 538, <Fp>::from_u64(1 << 20));
    scratch.dirty();
    let batched = super::check_lookups_batch_in(
        crate::test_codec::execution(),
        target,
        &lookup_corrupted,
        &instances,
        &scratch,
    );
    assert!(batched[0].is_ok());
    assert_eq!(batched[1].as_ref().err(), Some(&Error::UnsatisfiedWitness));
    drop(batched);
    assert_eq!(scratch.inventory(), inventory);
    // Both the per-Action path and the batch path can reuse leases returned
    // by a failed membership check, without retaining partially written IDs.
    for (matrix, instance) in matrices.iter().zip(&instances) {
        scratch.dirty();
        let actual = super::check_lookups_in(target, matrix, instance, &scratch).unwrap();
        let expected = check_lookups(target, matrix, instance).unwrap();
        for (actual, expected) in actual.lookups().iter().zip(expected.lookups()) {
            assert_eq!(actual.ids(), expected.ids());
        }
    }
    scratch.dirty();
    let valid = super::check_lookups_batch_in(
        crate::test_codec::execution(),
        target,
        &matrices,
        &instances,
        &scratch,
    );
    assert!(valid.iter().all(Result::is_ok));
    drop(valid);
    assert_eq!(scratch.inventory(), inventory);
    let gate_corrupted = corrupt(0, 1745, <Fp>::ONE);
    assert_eq!(
        check_gates_batch(crate::test_codec::execution(), target, &gate_corrupted),
        alloc::vec![Ok(()), Err(Error::UnsatisfiedWitness)]
    );
}

#[test]
fn native_preflight_rejects_gate_copy_and_lookup_corruption() {
    let request = ProvingRequest::decode_iwpr_for_test(ONE_ACTION).unwrap();
    let matrix = Arc::new(
        build_native_witness(&request.actions()[0])
            .unwrap()
            .into_matrix()
            .unwrap(),
    );
    let target = crate::test_codec::target();
    let mut instance = request.actions()[0].statement.native_values();
    instance.resize_with(super::N, || <Fp>::ZERO);
    let instance = SharedPoly::new(instance);

    assert_eq!(check_gates(target, &matrix, &instance), Ok(()));
    assert_eq!(check_copies(target, &matrix, &instance), Ok(()));
    let feeds = check_lookups(target, &matrix, &instance).unwrap();
    // The fused kernels' membership hits name exactly the table tuples the
    // tree reference's input tuples equal, on every usable row.
    for (lookup_index, lookup) in target.lookups().iter().enumerate() {
        let components = lookup
            .inputs()
            .indices()
            .map(|program| {
                super::evaluate_expression(program, target, matrix.columns(), &instance).unwrap()
            })
            .collect::<Vec<_>>();
        let table =
            prepared_lookup_table_tuples(crate::test_codec::target(), lookup_index).unwrap();
        let ids = feeds.lookups()[lookup_index].ids();
        assert_eq!(ids.len(), super::USABLE_ROWS_END);
        for (row, &id) in ids.iter().enumerate() {
            let expected = components
                .iter()
                .map(|column| column[row])
                .collect::<Vec<_>>();
            assert_eq!(
                reduced_values(&(table.tuple(id))),
                reduced_values(&(Some(expected.as_slice()))),
                "lookup {lookup_index} row {row}"
            );
        }
    }
    // Corrupting a Sinsemilla input on a live selector row fails the
    // fused membership pass.
    let selector_column = target.queries().fixed()[16].column;
    let live_row = (0..super::USABLE_ROWS_END)
        .find(|&row| !target.fixed_values()[selector_column][row].is_zero())
        .unwrap();
    let mut sinsemilla_columns = matrix.columns().to_vec();
    sinsemilla_columns[1][live_row] = sinsemilla_columns[1][live_row].add(&<Fp>::ONE);
    let sinsemilla_matrix = Arc::new(
        AdviceMatrix::from_columns_with_support(
            sinsemilla_columns,
            matrix.support_words().to_vec(),
        )
        .unwrap(),
    );
    assert_eq!(
        check_lookups(target, &sinsemilla_matrix, &instance).map(|_| ()),
        Err(Error::UnsatisfiedWitness)
    );

    // Region 393 carries the final top-level Action relations.
    let mut gate_columns = matrix.columns().to_vec();
    gate_columns[0][1745] = gate_columns[0][1745].add(&<Fp>::ONE);
    let gate_matrix = Arc::new(
        AdviceMatrix::from_columns_with_support(gate_columns, matrix.support_words().to_vec())
            .unwrap(),
    );
    assert_eq!(
        check_gates(target, &gate_matrix, &instance),
        Err(Error::UnsatisfiedWitness)
    );
    assert_eq!(
        check_gates_fixed(target, &gate_matrix, &instance),
        Err(Error::UnsatisfiedWitness)
    );
    assert_eq!(
        check_gates_serial(target, &gate_matrix, &instance),
        Err(Error::UnsatisfiedWitness)
    );
    assert_eq!(
        check_gates_full(target, &gate_matrix, &instance),
        Err(Error::UnsatisfiedWitness)
    );

    // Region 294 starts a 10-bit running sum used by the range lookup.
    let mut lookup_columns = matrix.columns().to_vec();
    lookup_columns[9][538] = lookup_columns[9][538].add(&<Fp>::from_u64(1 << 20));
    let lookup_matrix = Arc::new(
        AdviceMatrix::from_columns_with_support(lookup_columns, matrix.support_words().to_vec())
            .unwrap(),
    );
    assert_eq!(
        check_lookups(target, &lookup_matrix, &instance).err(),
        Some(Error::UnsatisfiedWitness)
    );

    let (advice_column, source_row) = target
        .copy_classes()
        .classes()
        .flat_map(<[u16]>::iter)
        .find_map(|&cell| {
            let column = target
                .permutation_columns()
                .get(usize::from(cell) / super::N)?;
            (column.kind == ColumnKind::Advice)
                .then_some((column.index, usize::from(cell) % super::N))
        })
        .expect("the fixed target has nontrivial advice copies");
    let mut copy_columns = matrix.columns().to_vec();
    copy_columns[advice_column][source_row] =
        copy_columns[advice_column][source_row].add(&<Fp>::ONE);
    let copy_matrix = Arc::new(
        AdviceMatrix::from_columns_with_support(copy_columns, matrix.support_words().to_vec())
            .unwrap(),
    );
    assert_eq!(
        check_copies(target, &copy_matrix, &instance),
        Err(Error::UnsatisfiedWitness)
    );
}
