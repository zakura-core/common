//! Unit-seeded permutation-set scans and chained product assembly.

use super::two_lane_exclusive_walk;
use crate::Error;
use crate::native::buffer::Buffer;
use crate::native::curve::VestaPoint;
use crate::native::field::Fp;
use crate::native::polynomial::SharedPoly;
use crate::native::prover::{PermutationProduct, ProductForms};
use crate::native::randomness::{PERMUTATION_SETS_PER_ACTION, PermutationBlinding};
use crate::native::target::{
    BLINDING_FACTORS, FixedTarget, N, PERMUTATION_CHUNK_LEN, PermutationColumn, USABLE_ROWS_END,
};
use crate::native::{try_array_from_fn, worker::Execution};
use alloc::vec::Vec;

/// One permutation set's grand product scanned from a unit seed, with the
/// final running product the next set's scan would have continued from.
struct PreparedPermutationSet {
    /// Staged Lagrange rows: the unit-seeded scan on `0..=USABLE_ROWS_END`
    /// and the blinding rows behind it.
    rows: Buffer<Fp>,
    /// The scan's final state (the product over every active row).
    final_product: Fp,
    /// The scan's constant stretches over the usable prefix as ascending
    /// `(start row, value)` runs: one per active row plus the trailing
    /// stretch, so the run *positions* are structural (the fixed copy
    /// graph's edge schedule, the same for every witness) while the values
    /// are this witness's. A trailing stretch that begins at
    /// `USABLE_ROWS_END` is omitted: that row belongs to the densely
    /// committed tail.
    runs: Vec<(u32, Fp)>,
}

/// Prepares every Action's chained permutation products as one pool task per
/// permutation set. Each set's denominators are inverted in their own batch
/// and scanned from a unit seed; the chain across a set's predecessors — the
/// reference continues each set from the previous set's final product — is
/// restored during assembly by scaling the later sets' usable rows by the
/// running product of the preceding final states. Field arithmetic is exact,
/// so the products are identical to the serial chained scan.
#[allow(clippy::too_many_arguments)] // borrowed columns, owned blinds, and challenges stay separate
pub(in crate::native::prover) fn prepare_permutation_products(
    target: &FixedTarget,
    advice: &[Vec<SharedPoly>],
    instance_polynomials: &[SharedPoly],
    blindings: Vec<[PermutationBlinding; PERMUTATION_SETS_PER_ACTION]>,
    beta: &Fp,
    gamma: &Fp,
    set_count: usize,
    execution: Execution<'_>,
) -> Result<Vec<[PermutationProduct; PERMUTATION_SETS_PER_ACTION]>, Error> {
    if set_count != PERMUTATION_SETS_PER_ACTION {
        return Err(crate::native::invariant::failed(
            crate::native::invariant::Invariant::PermutationSetCount,
        ));
    }
    if advice.len() != instance_polynomials.len() || blindings.len() != advice.len() {
        return Err(Error::InternalInvariant);
    }
    let action_count = advice.len();
    let job_count = action_count * set_count;
    execution.provision(N, job_count + 2 * job_count.min(execution.budget.get()));
    // Smaller active-row buffers are independent capacity classes. Reserve
    // their maximum concurrent denominator/prefix pairs before dispatch so
    // scheduling cannot grow the pool on a later identical proof.
    for schedule in target.permutation_edge_schedule() {
        let len = schedule.active_rows().len();
        if len == 0 || len.next_power_of_two() == N {
            continue;
        }
        let sets = target
            .permutation_edge_schedule()
            .iter()
            .filter(|other| {
                other.active_rows().len().next_power_of_two() == len.next_power_of_two()
            })
            .count();
        execution.provision(len, 2 * (action_count * sets).min(execution.budget.get()));
    }
    let mut set_jobs = Vec::with_capacity(action_count * set_count);
    let mut blinds = Vec::with_capacity(action_count * set_count);
    for (action, ((advice_columns, instance_column), action_blindings)) in advice
        .iter()
        .zip(instance_polynomials)
        .zip(blindings)
        .enumerate()
    {
        for (set, blinding) in action_blindings.into_iter().enumerate() {
            set_jobs.push((
                action,
                advice_columns.as_slice(),
                instance_column,
                set,
                blinding.rows,
            ));
            blinds.push(blinding.blind);
        }
    }
    let (beta, gamma) = (*beta, *gamma);
    let prepared_sets = execution
        .map(
            set_jobs,
            move |(_action, advice_columns, instance_column, set, rows), execution| {
                prepare_permutation_set(
                    target,
                    set,
                    advice_columns,
                    instance_column,
                    rows,
                    &beta,
                    &gamma,
                    execution,
                )
            },
        )
        .into_iter()
        .collect::<Result<Vec<_>, Error>>()?;

    // Restore the chain: set `k` of an Action is scaled by the product of the
    // final states of sets `0..k`; set 0 is already exact.
    let mut sets = prepared_sets.into_iter();
    let mut blinds = blinds.into_iter();
    let mut products = Vec::with_capacity(action_count);
    for _ in 0..action_count {
        let mut running = <Fp>::ONE;
        let action_products = try_array_from_fn(|_| {
            let prepared = sets.next().ok_or(Error::InternalInvariant)?;
            let blind = blinds.next().ok_or(Error::InternalInvariant)?;
            let scale = running;
            running = running.mul(&prepared.final_product);
            let mut rows = prepared.rows;
            let mut interval_runs = prepared.runs;
            if (scale).reduce() != (<Fp>::ONE).reduce() {
                for value in &mut rows[..=USABLE_ROWS_END] {
                    *value = value.mul(&scale);
                }
                // Runs cover the usable prefix; the boundary row is scaled
                // above, and the random tail beyond it remains unchanged.
                for (_, value) in &mut interval_runs {
                    *value = value.mul(&scale);
                }
            }
            Ok(PermutationProduct {
                forms: ProductForms::staged_rows(rows)?,
                blind,
                commitment: VestaPoint::IDENTITY,
                interval_runs,
            })
        })?;
        products.push(action_products);
    }
    if sets.next().is_some() || blinds.next().is_some() {
        return Err(Error::InternalInvariant);
    }
    Ok(products)
}

/// Prepares one permutation set's grand product for one Action, scanned from
/// a unit seed. Sets share no mutable state, so callers may run this complete
/// unit on an independent worker.
#[allow(clippy::too_many_arguments)] // each worker receives a set's columns, blinds, and challenges
fn prepare_permutation_set(
    target: &FixedTarget,
    set: usize,
    advice_columns: &[SharedPoly],
    instance_column: &[Fp],
    blinding_rows: [Fp; BLINDING_FACTORS],
    beta: &Fp,
    gamma: &Fp,
    execution: Execution<'_>,
) -> Result<PreparedPermutationSet, Error> {
    let schedule = target
        .permutation_edge_schedule()
        .get(set)
        .ok_or(Error::InternalInvariant)?;
    let columns = target
        .permutation_columns()
        .chunks(PERMUTATION_CHUNK_LEN)
        .nth(set)
        .ok_or(Error::InternalInvariant)?;
    let sigma_columns = target
        .sigma_values()
        .chunks(PERMUTATION_CHUNK_LEN)
        .nth(set)
        .ok_or(Error::InternalInvariant)?;
    let identities = target
        .permutation_identities()
        .values()
        .chunks(PERMUTATION_CHUNK_LEN)
        .nth(set)
        .ok_or(Error::InternalInvariant)?;
    if columns.len() != sigma_columns.len() || columns.len() != identities.len() {
        return Err(Error::InternalInvariant);
    }
    let mut values = [&[][..]; PERMUTATION_CHUNK_LEN];
    for (slot, column) in values.iter_mut().zip(columns) {
        *slot = super::permutation_column_values(
            column,
            advice_columns,
            target.fixed_values(),
            instance_column,
            N,
        )?;
    }
    let values = &values[..columns.len()];

    // A permutation fixed point contributes the same factor to the numerator
    // and the denominator for every witness and challenge, so those factors
    // cancel exactly and only the prepared nontrivial edges are materialized.
    // `row_product` multiplies one active row's factors over a table (sigma
    // for denominators, the identity for numerators) as an independent
    // product seeded by the row's first factor: `m − 1` multiplications for
    // `m` factors, none of them on the walk's prefix chain.
    let row_product = |table: &[[Fp; N]], row: usize, mask: u8| {
        let mut remaining = u32::from(mask);
        let mut product: Option<Fp> = None;
        while remaining != 0 {
            let column = remaining.trailing_zeros() as usize;
            remaining &= remaining - 1;
            let entry = table.get(column).ok_or(Error::InternalInvariant)?;
            let value = values.get(column).ok_or(Error::InternalInvariant)?;
            let factor = beta.mul(&entry[row]).add(gamma).add(&value[row]);
            product = Some(match product {
                Some(product) => product.mul(&factor),
                None => factor,
            });
        }
        Ok::<Fp, Error>(product.unwrap_or(<Fp>::ONE))
    };

    // Grand-product walk in the lookup products' form: every active row's
    // numerator product enters the running numerator prefix alongside that
    // row's denominator product, the denominator prefix is inverted once,
    // and a backward walk recovers each row's exclusive inverse denominator
    // prefix — in two interleaved lanes ([`two_lane_exclusive_walk`]). Per
    // active row with `m` factors that is `2m + 2` multiplications against
    // the `2m + 4` of a batch inversion followed by a ratio scan, with no
    // prefix bookkeeping, and field arithmetic is exact so the rows are
    // equal as field elements. The output's prefix temporarily holds z just
    // before each active row, followed by the product over every active row.
    let active_rows = schedule.active_rows();
    let mut denominators = execution.buffer(active_rows.len(), false);
    let mut rows = execution.buffer(N, false);
    let states = &mut rows[..active_rows.len() + 1];
    let (exclusive, final_state) = states
        .split_last_mut()
        .map(|(last, rest)| (rest, last))
        .expect("the state vector holds the final product");
    let walk = two_lane_exclusive_walk(
        active_rows.len(),
        |index| {
            let (row, mask) = active_rows[index];
            let row = usize::from(row);
            Ok((
                row_product(identities, row, mask)?,
                row_product(sigma_columns, row, mask)?,
            ))
        },
        exclusive,
        &mut denominators,
    )?;

    match walk {
        Some(final_product) => *final_state = final_product,
        None => {
            // Reference form: a zero denominator inverts to zero and zeroes
            // the running product from the following row on, exactly as the
            // grouped inverter leaves it.
            let mut prefixes = execution.buffer(denominators.len(), false);
            crate::native::field::batch_invert(&mut denominators, &mut prefixes);
            let inverted = &denominators;
            let mut state = <Fp>::ONE;
            for ((&(row, mask), inverse), slot) in active_rows
                .iter()
                .zip(inverted.iter())
                .zip(states.iter_mut())
            {
                *slot = state;
                state = state
                    .mul(&row_product(identities, usize::from(row), mask)?)
                    .mul(inverse);
            }
            *states.last_mut().expect("the state vector is nonempty") = state;
        }
    }

    // Expand the packed states backwards in place. Active row k is at least
    // k, so filling its run cannot overwrite an earlier packed state. The
    // trailing stretch carries the final product, including for an empty set.
    let final_product = rows[active_rows.len()];
    let mut runs = Vec::with_capacity(active_rows.len() + 1);
    let cursor = active_rows
        .last()
        .map_or(0, |&(row, _)| usize::from(row) + 1);
    rows[cursor..=USABLE_ROWS_END].fill(final_product);
    if cursor < USABLE_ROWS_END {
        runs.push((cursor as u32, final_product));
    }
    for (index, &(row, _)) in active_rows.iter().enumerate().rev() {
        let start = index
            .checked_sub(1)
            .map_or(0, |previous| usize::from(active_rows[previous].0) + 1);
        let state = rows[index];
        rows[start..=usize::from(row)].fill(state);
        runs.push((start as u32, state));
    }
    runs.reverse();
    rows[USABLE_ROWS_END + 1..].clone_from_slice(&blinding_rows);
    Ok(PreparedPermutationSet {
        rows,
        final_product,
        runs,
    })
}

/// Resolves one permutation column to its value slice of the expected length
/// (`N` for ordinary rows, `EXTENDED_N` for extended-coset rows).
pub(in crate::native::prover) fn permutation_column_values<'a, A: AsRef<[Fp]>, F: AsRef<[Fp]>>(
    column: &PermutationColumn,
    advice: &'a [A],
    fixed: &'a [F],
    instance: &'a [Fp],
    expected_len: usize,
) -> Result<&'a [Fp], Error> {
    use crate::native::target::ColumnKind;

    match column.kind {
        ColumnKind::Advice => advice.get(column.index).map(AsRef::as_ref),
        ColumnKind::Fixed => fixed.get(column.index).map(AsRef::as_ref),
        ColumnKind::Instance if column.index == 0 => Some(instance),
        ColumnKind::Instance => None,
    }
    .filter(|values| values.len() == expected_len)
    .ok_or(Error::InternalInvariant)
}
