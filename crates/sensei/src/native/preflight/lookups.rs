//! Lookup membership and retained table tuple identities.
//!
//! The fused proof-wide wave and per-Action fallback preserve lookup and row
//! order when assembling results, including the first reported failure.

use super::{ActionLookupFeeds, LookupInputIds};
use crate::Error;
use crate::native::{
    evaluation::evaluate_expression,
    field::Fp,
    generated_expressions::{LookupInputKernel, MAX_LOOKUP_INPUT_COMPONENTS},
    polynomial::SharedPoly,
    prover::{AdviceMatrix, LookupWorkspace, prepared_lookup_table_tuples},
    target::{FixedTarget, N, USABLE_ROWS_END},
    try_array_from_fn,
    worker::Execution,
};
use alloc::{sync::Arc, vec::Vec};
use core::ops::Range;

/// Usable rows per lookup membership task.
///
/// Tuning knob: any value in `1..=USABLE_ROWS_END`; the only dependent is the
/// membership task count (a rejected row rejects regardless of chunking).
const MEMBERSHIP_CHUNK_ROWS: usize = 256;

const _: () = assert!(MEMBERSHIP_CHUNK_ROWS >= 1 && MEMBERSHIP_CHUNK_ROWS <= USABLE_ROWS_END);

/// The lookup check of every Action as one pool wave: when every lookup
/// has a fused input kernel (all three circuit lookups), the fused row-chunk
/// tasks of every Action are submitted together and each Action's identities
/// assembled from its own chunks in lookup and row order — the same tasks and
/// the same first-failure order as [`check_lookups_in`] per Action. Should any
/// lookup lack a kernel, every Action runs [`check_lookups_in`] in sequence
/// instead, exactly as before.
pub(super) fn check_lookups_batch_in(
    execution: Execution<'_>,
    target: &FixedTarget,
    matrices: &[Arc<AdviceMatrix>],
    instances: &[SharedPoly],
    scratch: &LookupWorkspace,
) -> Vec<Result<ActionLookupFeeds, Error>> {
    let lookups = target.lookups();
    scratch.provision_ids(matrices.len());
    let kernels = target.preflight().kernels;
    if kernels.iter().any(|kernel| {
        kernel.is_none_or(|kernel| {
            matrices
                .iter()
                .any(|matrix| !kernel.accepts(matrix.columns()))
        })
    }) {
        return matrices
            .iter()
            .zip(instances)
            .map(|(matrix, instance)| check_lookups_in(target, matrix, instance, scratch))
            .collect();
    }
    let kernels = kernels.map(|kernel| kernel.expect("checked kernel"));

    let chunks_per_lookup = USABLE_ROWS_END.div_ceil(MEMBERSHIP_CHUNK_ROWS);
    let mut ids = (0..matrices.len() * lookups.len())
        .map(|_| scratch.ids.take(USABLE_ROWS_END, 0, false))
        .collect::<Vec<_>>();
    let mut jobs = Vec::with_capacity(ids.len() * chunks_per_lookup);
    for (index, ids) in ids.iter_mut().enumerate() {
        let action = index / lookups.len();
        let lookup = index % lookups.len();
        for (chunk, output) in ids.chunks_mut(MEMBERSHIP_CHUNK_ROWS).enumerate() {
            jobs.push((action, lookup, chunk * MEMBERSHIP_CHUNK_ROWS, output));
        }
    }
    let statuses = execution.map(jobs, |(action, lookup, start, output), _| {
        let table = prepared_lookup_table_tuples(target, lookup).ok_or(Error::InternalInvariant)?;
        let kernel = kernels[lookup];
        let mut tuple = [Fp::ZERO; MAX_LOOKUP_INPUT_COMPONENTS];
        for (offset, id) in output.iter_mut().enumerate() {
            let tuple = kernel.row(
                matrices[action].columns(),
                target.fixed_values(),
                start + offset,
                &mut tuple,
            );
            *id = table.find_tuple(tuple).ok_or(Error::UnsatisfiedWitness)?;
        }
        Ok::<(), Error>(())
    });
    let mut statuses = statuses.into_iter();
    let mut ids = ids.into_iter();
    (0..matrices.len())
        .map(|_| {
            let mut first_error = None;
            let checked = try_array_from_fn(|index| {
                let lookup = *lookups.get(index).ok_or(Error::InternalInvariant)?;
                for _ in 0..chunks_per_lookup {
                    if let Err(error) = statuses.next().unwrap_or(Err(Error::InternalInvariant)) {
                        first_error.get_or_insert(error);
                    }
                }
                let ids = ids.next().ok_or(Error::InternalInvariant)?;
                LookupInputIds::new(lookup, ids)
            })?;
            if let Some(error) = first_error {
                return Err(error);
            }
            ActionLookupFeeds::new(target, checked)
        })
        .collect()
}

/// Checks every lookup's input tuples against its prepared table and returns
/// the usable rows' table tuple identities (one [`LookupInputIds`] per
/// lookup) that θ-compression and the permutation consume.
///
/// Every lookup with a fused input kernel (all three circuit lookups: the
/// range check and the two Sinsemilla families) runs it in one pass per row
/// chunk: the chunk's usable rows are evaluated from the resolved columns and
/// each row's tuple is probed as it is formed; the probe's hit *is* the
/// retained result, so no component value is stored or read back. A lookup
/// without a resolving kernel (none today) evaluates its programs through the
/// flat evaluator (one task per program) and probes the finished columns in
/// row chunks. Results are folded in lookup and row order, so the first
/// failure reported is the one a serial pass would have found.
pub(super) fn check_lookups_in(
    target: &FixedTarget,
    matrix: &Arc<AdviceMatrix>,
    instance: &[Fp],
    scratch: &LookupWorkspace,
) -> Result<ActionLookupFeeds, Error> {
    let lookups = target.lookups();
    let mut kernels = Vec::with_capacity(lookups.len());
    let mut feed_jobs =
        Vec::with_capacity(lookups.iter().map(|lookup| lookup.inputs().len()).sum());
    let mut fused_jobs =
        Vec::with_capacity(lookups.len() * USABLE_ROWS_END.div_ceil(MEMBERSHIP_CHUNK_ROWS));
    for (lookup_index, lookup) in lookups.iter().enumerate() {
        if lookup.inputs().is_empty() || lookup.inputs().len() != lookup.tables().len() {
            return Err(Error::InternalInvariant);
        }
        let kernel = LookupInputKernel::resolve(target, lookup_index)
            .filter(|kernel| kernel.accepts(matrix.columns()));
        match kernel {
            Some(kernel) => fused_jobs.extend(
                (0..USABLE_ROWS_END)
                    .step_by(MEMBERSHIP_CHUNK_ROWS)
                    .map(move |start| (lookup_index, kernel, start)),
            ),
            None => feed_jobs.extend(
                lookup
                    .inputs()
                    .indices()
                    .map(|program| (lookup_index, program)),
            ),
        }
        kernels.push(kernel);
    }

    let matrix_ref = Arc::clone(matrix);
    let fused_chunks = (fused_jobs)
        .into_iter()
        .map(move |(lookup_index, kernel, start)| {
            let table_tuples = prepared_lookup_table_tuples(target, lookup_index)
                .ok_or(Error::InternalInvariant)?;
            if table_tuples.arity() != kernel.components() {
                return Err(Error::InternalInvariant);
            }
            let end = (start + MEMBERSHIP_CHUNK_ROWS).min(USABLE_ROWS_END);
            let mut ids = Vec::with_capacity(end - start);
            let mut tuple = [<Fp>::ZERO; MAX_LOOKUP_INPUT_COMPONENTS];
            for row in start..end {
                let tuple =
                    kernel.row(matrix_ref.columns(), target.fixed_values(), row, &mut tuple);
                ids.push(
                    table_tuples
                        .find_tuple(tuple)
                        .ok_or(Error::UnsatisfiedWitness)?,
                );
            }
            Ok(ids)
        })
        .collect::<Vec<_>>();

    let (matrix_ref, instance_ref) = (matrix, instance);
    let mut feeds = (feed_jobs)
        .into_iter()
        .map(move |(_, program)| {
            evaluate_expression(program, target, matrix_ref.columns(), instance_ref)
        })
        .collect::<Vec<_>>()
        .into_iter();
    let mut fused_chunks = fused_chunks.into_iter();
    let mut pending = Vec::with_capacity(lookups.len());
    for (lookup, kernel) in lookups.iter().zip(&kernels) {
        if kernel.is_some() {
            let mut ids = scratch.ids.take(USABLE_ROWS_END, 0, false);
            ids.clear();
            for _ in (0..USABLE_ROWS_END).step_by(MEMBERSHIP_CHUNK_ROWS) {
                ids.extend(fused_chunks.next().ok_or(Error::InternalInvariant)??);
            }
            // The kernel probed every usable row as it formed: the identities
            // are checked and complete.
            pending.push(PendingIds::Checked(LookupInputIds::new(*lookup, ids)?));
        } else {
            let inputs = feeds
                .by_ref()
                .take(lookup.inputs().len())
                .collect::<Result<Vec<_>, Error>>()?;
            if inputs.len() != lookup.inputs().len()
                || inputs.iter().any(|values| values.len() != N)
            {
                return Err(Error::InternalInvariant);
            }
            // The membership tasks below read these columns by handle.
            pending.push(PendingIds::Unchecked(Arc::new(inputs)));
        }
    }
    if feeds.next().is_some() || fused_chunks.next().is_some() {
        return Err(Error::InternalInvariant);
    }

    let membership_jobs = pending
        .iter()
        .enumerate()
        .filter_map(|(lookup_index, feed)| match feed {
            PendingIds::Unchecked(inputs) => Some((lookup_index, inputs)),
            PendingIds::Checked(_) => None,
        })
        .flat_map(|(lookup_index, inputs)| {
            (0..USABLE_ROWS_END)
                .step_by(MEMBERSHIP_CHUNK_ROWS)
                .map(move |start| (lookup_index, Arc::clone(inputs), start))
        })
        .collect::<Vec<_>>();
    let mut results = (membership_jobs)
        .into_iter()
        .map(|(lookup_index, inputs, start)| {
            check_membership(
                target,
                lookup_index,
                &inputs,
                start..(start + MEMBERSHIP_CHUNK_ROWS).min(USABLE_ROWS_END),
            )
        })
        .collect::<Vec<_>>()
        .into_iter();
    let mut pending = pending.into_iter();
    let checked = try_array_from_fn(|index| {
        let lookup = lookups.get(index).ok_or(Error::InternalInvariant)?;
        match pending.next().ok_or(Error::InternalInvariant)? {
            PendingIds::Checked(ids) => Ok(ids),
            PendingIds::Unchecked(_) => {
                let mut ids = scratch.ids.take(USABLE_ROWS_END, 0, false);
                ids.clear();
                for _ in (0..USABLE_ROWS_END).step_by(MEMBERSHIP_CHUNK_ROWS) {
                    ids.extend(results.next().ok_or(Error::InternalInvariant)??);
                }
                LookupInputIds::new(*lookup, ids)
            }
        }
    })?;
    if results.next().is_some() || pending.next().is_some() {
        return Err(Error::InternalInvariant);
    }
    ActionLookupFeeds::new(target, checked)
}

/// One lookup's identities between assembly and the returned container:
/// owned once its membership is established, shared (as evaluated columns)
/// only while tree-fallback membership tasks still read them.
enum PendingIds {
    Checked(LookupInputIds),
    Unchecked(Arc<Vec<Vec<Fp>>>),
}

/// Checks that every input tuple in `rows` is one of the lookup's prepared
/// table tuples and returns their identities. The prepared index uses reduced
/// Montgomery limbs, so equivalent loose representations share a key without
/// conversion to canonical integers.
fn check_membership(
    target: &FixedTarget,
    lookup_index: usize,
    inputs: &[Vec<Fp>],
    rows: Range<usize>,
) -> Result<Vec<u16>, Error> {
    let table_tuples =
        prepared_lookup_table_tuples(target, lookup_index).ok_or(Error::InternalInvariant)?;
    if table_tuples.arity() != inputs.len() {
        return Err(Error::InternalInvariant);
    }
    rows.map(|row| {
        table_tuples
            .find_row(inputs, row)
            .ok_or(Error::UnsatisfiedWitness)
    })
    .collect()
}
