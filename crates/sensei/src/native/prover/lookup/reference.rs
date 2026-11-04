//! Lookup compression references and test adapters.
//!
//! Dense references evaluate expressions independently; the windowed compression
//! plan shares production kernels to check their batching and row coefficients.

use super::*;
use crate::native::evaluation::{evaluate_expression, evaluate_expression_coset_row};
use crate::native::prover::CosetStack;

/// Serial column-major reference for the parallel batched compression below.
#[cfg(test)]
pub(in crate::native::prover) fn compress_expressions_on_coset<
    F: Index<usize, Output = Fp> + Sync,
>(
    programs: ExpressionRange,
    theta: &Fp,
    target: &FixedTarget,
    advice: &[Vec<Fp>],
    fixed: &[F],
    instance: &[Vec<Fp>],
) -> Result<Vec<Fp>, Error> {
    let evaluate_full = |expression: usize| -> Result<Vec<Fp>, Error> {
        (0..EXTENDED_N)
            .map(|row| {
                evaluate_expression_coset_row(expression, target, advice, fixed, instance, row)
            })
            .collect()
    };
    let mut programs = programs.indices();
    let first = programs.next().ok_or(Error::InternalInvariant)?;
    let mut compressed = evaluate_full(first)?;
    for program in programs {
        let values = evaluate_full(program)?;
        for (accumulator, value) in compressed.iter_mut().zip(values) {
            *accumulator = accumulator.mul_add(theta, &value);
        }
    }
    Ok(compressed)
}

/// Plans test-only windowed compression for comparison with the prepared
/// table kernels and the fused quotient fold. Jobs over the same expression
/// range share fixed-column/challenge coefficients across their Actions.
/// Each kernel group is resolved once; [`Self::windows`] lists its row
/// windows, [`Self::compress_window`] evaluates one, and [`Self::assemble`]
/// copies the chunks in order into one extended coset per job.
#[cfg(test)]
pub(in crate::native::prover) struct CompressionPlan {
    jobs: Vec<(usize, ExpressionRange)>,
    groups: Vec<(ExpressionRange, Vec<usize>)>,
    kernels: Vec<LookupKernelGroup>,
    theta: ThetaConstants,
}

#[cfg(test)]
impl CompressionPlan {
    /// One window per residue per job: the windows are the output tiles.
    const RESIDUES: usize = EXTENDED_N / N;

    /// Resolves each job's kernel group; jobs over the same expression range
    /// share a group and split each residue into one window per member.
    pub(in crate::native::prover) fn new(
        jobs: Vec<(usize, ExpressionRange)>,
        theta: Fp,
        target: &FixedTarget,
    ) -> Result<Self, Error> {
        const _: () = assert!(COMPRESSION_CHUNK_ROWS == N);
        let job_count = jobs.len();
        let mut groups: Vec<(ExpressionRange, Vec<usize>)> = Vec::with_capacity(job_count);
        for (job_index, &(_, programs)) in jobs.iter().enumerate() {
            match groups
                .iter_mut()
                .find(|(range, _)| range.indices() == programs.indices())
            {
                Some((_, members)) => members.push(job_index),
                None => {
                    // Group sizes partition the jobs data-dependently; sizing
                    // each at `job_count` would cost O(groups × jobs) storage.
                    let members = alloc::vec![job_index];
                    groups.push((programs, members));
                }
            }
        }
        // The kernel group of each range is resolved once here, not per
        // chunk: no per-job heap storage.
        let kernels = groups
            .iter()
            .map(|&(programs, _)| {
                lookup_kernel_group(target, programs).ok_or(Error::InternalInvariant)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            jobs,
            groups,
            kernels,
            theta: ThetaConstants::new(theta, &LookupKernelConstants::load()),
        })
    }

    // A group's residue splits into one window per member, so each task
    // still covers one job-residue of work whatever the grouping.
    fn window_rows(members: usize) -> usize {
        N.div_ceil(members)
    }

    fn windows_per_residue(members: usize) -> usize {
        N.div_ceil(Self::window_rows(members))
    }

    /// The wave's tasks, `(group, window)`, in [`Self::assemble`] order.
    pub(in crate::native::prover) fn windows(&self) -> Vec<(usize, usize)> {
        self.groups
            .iter()
            .enumerate()
            .flat_map(|(group, (_, members))| {
                let windows = Self::windows_per_residue(members.len());
                (0..Self::RESIDUES * windows).map(move |window| (group, window))
            })
            .collect()
    }

    /// Runs one task: the group's kernels over one row window for each
    /// member job, one output chunk per member. Advice cosets are read from
    /// `cosets` only when a kernel needs them; a fixed-only group (the table
    /// sides) accepts a stack with no advice at all.
    pub(in crate::native::prover) fn compress_window<F>(
        &self,
        (group_index, window_index): (usize, usize),
        cosets: &CosetStack<F>,
        execution: Execution<'_>,
    ) -> Result<Vec<Buffer<Fp>>, Error>
    where
        F: Index<usize, Output = Fp>,
    {
        let (_, members) = &self.groups[group_index];
        let kernels = self.kernels[group_index].as_slice();
        let windows = Self::windows_per_residue(members.len());
        let window_rows = Self::window_rows(members.len());
        let k_offset = (window_index % windows) * window_rows;
        let window = RowWindow {
            residue: window_index / windows,
            k_offset,
            rows: window_rows.min(N - k_offset),
        };
        let rows = window.rows;
        let fixed_only = !kernels.iter().any(|kernel| kernel.reads_advice());
        let advice_actions = members
            .iter()
            .map(|&job| match cosets.advice.get(self.jobs[job].0) {
                Some(advice) => Ok(advice.as_slice()),
                None if fixed_only => Ok(&[] as &[ExtendedCoset]),
                None => Err(Error::InternalInvariant),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut outs: Vec<_> = (0..members.len())
            .map(|_| execution.buffer(rows, false))
            .collect();
        compress_kernel_rows_shared(
            kernels,
            &self.theta,
            &advice_actions,
            &cosets.fixed,
            window,
            &mut outs,
        )?;
        Ok(outs)
    }

    /// Reassembles the tasks' chunks, in [`Self::windows`] order, into one
    /// extended coset per job.
    pub(in crate::native::prover) fn assemble(
        &self,
        execution: Execution<'_>,
        mut chunks: impl Iterator<Item = Result<Vec<Buffer<Fp>>, Error>>,
    ) -> Result<Vec<ExtendedCoset>, Error> {
        let mut outputs: Vec<_> = (0..self.jobs.len())
            .map(|_| execution.buffer(Self::RESIDUES * N, false))
            .collect();
        for (_, members) in &self.groups {
            let chunk_count = Self::RESIDUES * Self::windows_per_residue(members.len());
            let mut offset = 0;
            for _ in 0..chunk_count {
                let outs = chunks.next().ok_or(Error::InternalInvariant)??;
                if outs.len() != members.len() {
                    return Err(Error::InternalInvariant);
                }
                let len = outs.first().ok_or(Error::InternalInvariant)?.len();
                for (&job, out) in members.iter().zip(outs) {
                    if out.len() != len {
                        return Err(Error::InternalInvariant);
                    }
                    outputs[job]
                        .get_mut(offset..offset + len)
                        .ok_or(Error::InternalInvariant)?
                        .copy_from_slice(&out);
                }
                offset += len;
            }
            if offset != Self::RESIDUES * N {
                return Err(Error::InternalInvariant);
            }
        }
        if chunks.next().is_some() {
            return Err(Error::InternalInvariant);
        }
        outputs
            .into_iter()
            .map(|values| {
                ExtendedCoset::from_flat(values)
                    .ok_or_else(|| invariant::failed(Invariant::ExtendedDomainLength))
            })
            .collect()
    }
}

/// Runs each window of a [`CompressionPlan`] and reassembles one extended
/// coset per job using the test execution context. The parity tests
/// compare this retained windowed path with the dense expression reference.
#[cfg(test)]
pub(in crate::native::prover) fn parallel_compress_lookup_expressions<F>(
    jobs: Vec<(usize, ExpressionRange)>,
    theta: Fp,
    target: &FixedTarget,
    cosets: Arc<CosetStack<F>>,
) -> Result<Vec<ExtendedCoset>, Error>
where
    F: Index<usize, Output = Fp> + Send + Sync + 'static,
{
    let plan = Arc::new(CompressionPlan::new(jobs, theta, target)?);
    let windows = plan.windows();
    let tasks = Arc::clone(&plan);
    let chunks = (windows)
        .into_iter()
        .map(move |window| tasks.compress_window(window, &cosets, crate::test_codec::execution()))
        .collect::<Vec<_>>();
    plan.assemble(crate::test_codec::execution(), chunks.into_iter())
}

#[cfg(test)]
impl LookupKernel {
    /// The query dependencies this kernel's reads imply — its fixed and
    /// advice columns at their rotations, mapped back to query indices through
    /// the shared query tables — so the metadata test can hold each kernel to
    /// exactly the dependencies of the program it implements. The formulas
    /// are transcribed by hand; this is the association that keeps them
    /// honest.
    pub(in crate::native::prover) fn reads(&self) -> crate::native::expressions::QueryDependencies {
        use crate::native::queries::{ADVICE_QUERIES, FIXED_QUERIES};
        let fixed = |column: usize| -> u32 {
            let index = FIXED_QUERIES
                .iter()
                .position(|query| query.column == column && query.rotation == 0)
                .unwrap_or_else(|| panic!("no fixed query for column {column}"));
            1 << index
        };
        let advice = |column: usize, rotation: i32| -> u32 {
            let index = ADVICE_QUERIES
                .iter()
                .position(|query| query.column == column && query.rotation == rotation)
                .unwrap_or_else(|| panic!("no advice query for column {column} at {rotation}"));
            1 << index
        };
        let (fixed_bits, advice_bits) = match *self {
            // Fixed queries 14 and 15 are columns 14 and 15; advice column 9
            // at the row and the next row.
            Self::WindowedRangeInput => (fixed(14) | fixed(15), advice(9, 0) | advice(9, 1)),
            Self::ShortRangeInput {
                selector,
                run,
                column,
            } => (
                fixed(selector) | fixed(run),
                advice(column, 0) | advice(column, 1),
            ),
            Self::SelectedAdvice { selector, column } => (fixed(selector), advice(column, 0)),
            Self::SelectedQuadratic {
                selector,
                b,
                d,
                p,
                q,
            } => (
                fixed(selector),
                advice(b, 0) | advice(d, 0) | advice(p, 0) | advice(q, 0),
            ),
            Self::FixedColumn(column) => (fixed(column), 0),
        };
        crate::native::expressions::QueryDependencies {
            fixed: fixed_bits,
            advice: advice_bits,
            instance: 0,
        }
    }
}

/// [`lookup_kernel_group`] as an owned list, for the dependency and parity
/// tests that pin each kernel against its program.
#[cfg(test)]
pub(in crate::native::prover) fn lookup_kernels(
    target: &FixedTarget,
    programs: ExpressionRange,
) -> Option<Vec<LookupKernel>> {
    lookup_kernel_group(target, programs).map(|group| group.as_slice().to_vec())
}

/// One row pass of the fused Sinsemilla input family over every Action at
/// once, through [`SinsemillaRowCoefficients`]. Columns are validated by the
/// caller.
#[cfg(test)]
fn compress_sinsemilla_rows_shared<F: Index<usize, Output = Fp>>(
    kernel: SinsemillaFusedKernel,
    constants: &LookupKernelConstants,
    theta: &ThetaConstants,
    advice_actions: &[&[ExtendedCoset]],
    fixed: &[F],
    window: RowWindow,
    outs: &mut [Buffer<Fp>],
) {
    let rows = outs.first().map_or(0, |out| out.len());
    for offset in 0..rows {
        let row = window.row(offset);
        let next = rotated_extended_row(row, 1);
        let coefficients = SinsemillaRowCoefficients::at_row(kernel, constants, theta, fixed, row);
        for (advice, out) in advice_actions.iter().zip(outs.iter_mut()) {
            out[offset] = coefficients.evaluate(kernel, constants, advice, row, next);
        }
    }
}

/// One row pass of the windowed range input over every Action at once,
/// through [`RangeRowCoefficients`]. Columns are validated by the caller.
#[cfg(test)]
fn compress_windowed_range_rows_shared<F: Index<usize, Output = Fp>>(
    constants: &LookupKernelConstants,
    advice_actions: &[&[ExtendedCoset]],
    fixed: &[F],
    window: RowWindow,
    outs: &mut [Buffer<Fp>],
) {
    let rows = outs.first().map_or(0, |out| out.len());
    for offset in 0..rows {
        let row = window.row(offset);
        let next = rotated_extended_row(row, 1);
        let coefficients = RangeRowCoefficients::at_row(constants, fixed, row);
        for (advice, out) in advice_actions.iter().zip(outs.iter_mut()) {
            out[offset] = coefficients.evaluate(advice, row, next);
        }
    }
}

/// Compresses one row window of a pinned lookup expression range for every
/// Action in `advice_actions` (one output per Action). Input sides share
/// their row coefficients across Actions; table sides and any other range
/// carry nothing Action-independent to share and compress member by member.
#[cfg(test)]
fn compress_kernel_rows_shared<F: Index<usize, Output = Fp>>(
    kernels: &[LookupKernel],
    theta: &ThetaConstants,
    advice_actions: &[&[ExtendedCoset]],
    fixed: &[F],
    window: RowWindow,
    outs: &mut [Buffer<Fp>],
) -> Result<(), Error> {
    const FIXED_COLUMNS_READ: usize = 18;
    let rows = outs.first().map_or(0, |out| out.len());
    // Fixed-only kernel groups (the table sides) accept an empty advice view.
    let reads_advice = kernels.iter().any(|kernel| kernel.reads_advice());
    if outs.len() != advice_actions.len()
        || (reads_advice
            && advice_actions
                .iter()
                .any(|advice| advice.len() < ADVICE_COLUMNS))
        || outs.iter().any(|out| out.len() != rows)
        || fixed.len() < FIXED_COLUMNS_READ
        || window.rows != rows
        || !window.is_valid()
    {
        return Err(Error::InternalInvariant);
    }
    let constants = LookupKernelConstants::load();
    if let Some(fused) = sinsemilla_fused_kernel(kernels) {
        compress_sinsemilla_rows_shared(
            fused,
            &constants,
            theta,
            advice_actions,
            fixed,
            window,
            outs,
        );
        return Ok(());
    }
    if let [LookupKernel::WindowedRangeInput] = kernels {
        compress_windowed_range_rows_shared(&constants, advice_actions, fixed, window, outs);
        return Ok(());
    }
    for (advice, out) in advice_actions.iter().zip(outs.iter_mut()) {
        compress_kernel_rows(kernels, &theta.theta, advice, fixed, window, out)?;
    }
    Ok(())
}

/// θ-compresses one lookup input side from its preflight tuple identities.
///
/// A usable row's input tuple equals the table tuple its identity names, so
/// its Horner fold equals the compressed table's value at that tuple's
/// representative row: the column is gathered, never folded. The identities
/// were probed on the unblinded witness, so every blinding-visible row is
/// re-evaluated here on the blinded columns; the result equals a
/// dense post-blinding evaluation on every row.
#[cfg(test)]
pub(in crate::native::prover) fn compress_input_from_ids<A: AsRef<[Fp]>>(
    ids: &LookupInputIds,
    compressed_table: &[Fp],
    tuples: &TupleIndex,
    theta: &Fp,
    target: &FixedTarget,
    advice: &[A],
    instance: &[Fp],
) -> Result<Buffer<Fp>, Error> {
    compress_input_in(
        ids,
        compressed_table,
        tuples,
        theta,
        target,
        advice,
        instance,
        crate::test_codec::execution(),
    )
}

/// θ-compresses one lookup table side from its prepared fixed-only component
/// vectors — witness-independent on every row, blinding tail included.
///
/// Each distinct usable-row tuple is folded once and the usable rows gather
/// their tuple's value (equal tuples fold to equal values, so this is
/// equal to folding every row); the tail rows fold directly.
#[cfg(test)]
pub(in crate::native::prover) fn compress_table_from_prepared(
    target: &FixedTarget,
    lookup_index: usize,
    theta: &Fp,
) -> Result<Buffer<Fp>, Error> {
    compress_table_in(target, lookup_index, theta, crate::test_codec::execution())
}

/// Dense reference compression, retained as the `cfg(test)` oracle for the
/// feed-based paths.
#[cfg(test)]
pub(in crate::native::prover) fn compress_expressions<A: AsRef<[Fp]>>(
    programs: ExpressionRange,
    theta: &Fp,
    target: &FixedTarget,
    advice: &[A],
    instance: &[Fp],
) -> Result<Vec<Fp>, Error> {
    let mut programs = programs.indices();
    let first = programs.next().ok_or(Error::InternalInvariant)?;
    let mut compressed = evaluate_expression(first, target, advice, instance)?;
    for program in programs {
        let values = evaluate_expression(program, target, advice, instance)?;
        for (accumulator, value) in compressed.iter_mut().zip(values) {
            *accumulator = accumulator.mul_add(theta, &value);
        }
    }
    Ok(compressed)
}

#[cfg(test)]
pub(in crate::native::prover) fn permute_usable_values(
    input_values: Vec<Fp>,
    table_values: Vec<Fp>,
) -> Result<(Vec<Fp>, Vec<Fp>), Error> {
    permute_sorted_usable_values(
        sort_usable_values(input_values),
        sort_usable_values(table_values),
    )
}

/// Reference counting by value: probes every compressed input value. The
/// `cfg(test)` oracle for [`count_input_entries_in`].
#[cfg(test)]
pub(in crate::native::prover) fn count_input_values(
    order: &TableOrder,
    probe: &RawValueMap,
    compressed_input: &[Fp],
) -> Result<Vec<u32>, Error> {
    let mut counts = alloc::vec![ 0u32; order.entries.len()];
    for value in compressed_input {
        let index =
            probe_value_map(probe, &order.entries, value).ok_or(Error::UnsatisfiedWitness)?;
        counts[index] += 1;
    }
    Ok(counts)
}

/// Rebuilds the reference permuted columns from table occurrence counts and
/// the input's per-entry counts over `usable_rows` rows.
///
/// Matches `permute_sorted_usable_values` on collision-free tables: sorted
/// first occurrences claim their table row and leftover table values
/// ascending fill repeated input rows descending.
#[cfg(test)]
pub(in crate::native::prover) fn reconstruct_permuted_columns(
    order: &TableOrder,
    input_counts: &[u32],
    usable_rows: usize,
) -> Result<PermutedColumns, Error> {
    reconstruct_permuted_in(
        order,
        input_counts,
        usable_rows,
        crate::test_codec::execution(),
        &LookupWorkspace::default(),
    )
}

/// Extracts the maximal `(start row, value)` runs of a column prefix.
#[cfg(test)]
pub(in crate::native::prover) fn column_runs(values: &[Fp]) -> Vec<(u32, Fp)> {
    let mut runs = Vec::with_capacity(values.len());
    for (row, value) in values.iter().enumerate() {
        if row == 0 || (values[row - 1]).reduce() != (value).reduce() {
            runs.push((row as u32, *value));
        }
    }
    runs
}

#[cfg(test)]
pub(in crate::native::prover) fn prepared_table_access(
    target: &FixedTarget,
    lookup_index: usize,
    compressed_table: &[Fp],
) -> Option<TableAccess> {
    prepared_table_access_in(
        target,
        lookup_index,
        compressed_table,
        &LookupWorkspace::default(),
    )
}

#[cfg(test)]
pub(in crate::native::prover) fn count_input_entries(
    order: &TableOrder,
    probe: &RawValueMap,
    entry_of_id: &[u16],
    ids: &[u16],
    compressed_input: &[Fp],
) -> Result<Buffer<u32>, Error> {
    count_input_entries_in(
        order,
        probe,
        entry_of_id,
        ids,
        compressed_input,
        &LookupWorkspace::default(),
    )
}
