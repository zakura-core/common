//! Lookup preparation, compression, permutation, and commitments.
//!
//! Fixed table tuples and membership indices live for the process. Compression
//! depends on this proof's theta; input identities and permuted columns belong to
//! an Action. Blinding-visible rows are recomputed from the masked advice.
//! The test-only `reference` child keeps dense and windowed compression checks;
//! [`scratch`] owns the workspace pools used through these stages.

use crate::native::{buffer::Buffer, try_array_from_fn, worker::Execution};
#[cfg(test)]
mod reference;
mod scratch;
use alloc::{sync::Arc, vec::Vec};
use core::ops::Index;
#[cfg(test)]
pub(super) use reference::{
    column_runs, compress_expressions, compress_expressions_on_coset, compress_input_from_ids,
    compress_table_from_prepared, count_input_entries, count_input_values, lookup_kernels,
    parallel_compress_lookup_expressions, permute_usable_values, prepared_table_access,
    reconstruct_permuted_columns,
};
pub(crate) use scratch::LookupWorkspace;
use sensei_shared::FIXED_COLUMNS;

use crate::Error;
use crate::native::commitment::normalized;
use crate::native::curve::VestaPoint;
use crate::native::evaluation::rotated_extended_row;
use crate::native::field::Fp;
use crate::native::generated_expressions;
use crate::native::generated_expressions::{ExpressionRange, LookupExpressionRanges};
use crate::native::invariant::{self, Invariant};
use crate::native::polynomial::SharedPoly;
use crate::native::preflight::{LookupInputIds, WitnessFeeds};
use crate::native::randomness::{LOOKUPS_PER_ACTION, LookupBlinding};
use crate::native::target::{
    ADVICE_COLUMNS, EXTENDED_N, FixedTarget, LookupCommitPair, N, PERMUTATION_CHUNK_LEN,
    PERMUTATION_COLUMN_COUNT, PERMUTATION_SETS, USABLE_ROWS_END,
};

use super::inventory::lookup_stage;
use super::quotient::KEPT_PERMUTATION_SETS;
use super::{
    AdvicePrefix, COEFFICIENT_CHUNK, COMPRESSION_CHUNK_ROWS, ExtendedCoset, LookupPrefix,
    PermutedLookup, ProverPrefix,
};

const _: () = assert!(EXTENDED_N.is_multiple_of(COMPRESSION_CHUNK_ROWS) && COEFFICIENT_CHUNK > 0);

/// Pairs lookup columns with their corresponding compressed table.
///
/// Only this module can bind an input to its same-index table. Equality covers the
/// usable prefix; the independently blinded tail is deliberately excluded.
pub(super) struct CertifiedLookupProductInput {
    permuted: PermutedLookup,
    compressed_table: SharedPoly,
}

impl CertifiedLookupProductInput {
    pub(super) fn parts(&self) -> (&PermutedLookup, &[Fp]) {
        (&self.permuted, &self.compressed_table)
    }
}

impl LookupPrefix {
    /// Shares the product inputs for one action without allocating a collection.
    ///
    /// Full table-bearing prefixes originate in successful lookup preparation:
    /// both reconstruction routes preserve each side's usable-row multiset.
    /// Quotient windows deliberately replace these tables with empty handles,
    /// so their prefixes cannot certify product inputs.
    pub(super) fn certified_product_inputs(
        &self,
        action: usize,
    ) -> Result<impl ExactSizeIterator<Item = CertifiedLookupProductInput> + '_, Error> {
        let lookups = self.lookups.get(action).ok_or(Error::InternalInvariant)?;
        if self.compressed_tables.iter().any(|table| table.len() != N)
            || lookups.iter().any(|lookup| {
                lookup.compressed_input.len() != N
                    || lookup.permuted_input.len() != N
                    || lookup.permuted_table.len() != N
            })
        {
            return Err(Error::InternalInvariant);
        }
        Ok(lookups
            .iter()
            .cloned()
            .zip(self.compressed_tables.iter().cloned())
            .map(|(permuted, compressed_table)| CertifiedLookupProductInput {
                permuted,
                compressed_table,
            }))
    }
}

impl ProverPrefix<'_> {
    /// Compresses every fixed lookup program from the preflight witness feeds
    /// and the prepared fixed-only table sides, permutes the compressed
    /// columns, then writes the input/table commitments and squeezes `beta`
    /// and `gamma`.
    ///
    /// # Transcript contract
    ///
    /// - **Requires** `θ` from the [`AdvicePrefix`]; no other challenge.
    /// - **Publishes** every Action's lookup commitments, Action-major and
    ///   lookup-ascending, each lookup as the pair (permuted input
    ///   commitment, permuted table commitment), from one mixed Lagrange
    ///   commitment batch.
    /// - **Squeezes** `β` then `γ`, in that order, carried on the returned
    ///   [`LookupPrefix`] for the product stage.
    /// - **Draws** no randomness: each lookup's `BLINDING_FACTORS + 1` tail
    ///   rows for both permuted columns and its two commitment blinds arrive
    ///   pre-sampled and are appended in lookup order.
    ///
    /// Preparation — `θ`-compression of the table sides (once per lookup,
    /// shared by every Action) and of each Action's input sides, then the
    /// sorted-permutation reconstruction of each (input, table) pair — is a
    /// mathematical dependency on `θ`, the advice, the instance columns, and
    /// the fixed tables, free to run in any task order; the write loop is the
    /// only transcript-ordered section and follows the batch's job order.
    ///
    /// # Work and buffer inventory
    ///
    /// Logical counts, in field elements, from [`lookup_stage`].
    ///
    /// - **Shared, once per proof:** `SHARED_TABLE_COLUMNS` `θ`-compressed
    ///   table columns of `N` rows, each one pass over the fixed table
    ///   columns of its lookup; plus, when a prepared table order exists,
    ///   the access structure that lets a pair's permutation be
    ///   reconstructed instead of sorted.
    /// - **Per (Action, lookup) pair:** one pass over the lookup's input
    ///   programs' preflight feeds and the advice/instance columns to build
    ///   the `N`-row compressed input; a permutation of the
    ///   `PERMUTED_ROWS_PER_PAIR` usable rows into the (permuted input,
    ///   permuted table) pair — reconstructed from the prepared order or,
    ///   in the fallback, two sorts of `PERMUTED_ROWS_PER_PAIR` values; then
    ///   `MASK_ROWS_PER_COLUMN` pre-sampled rows appended to each permuted
    ///   column; then `COMMITMENTS_PER_PAIR` commitments, selecting independent
    ///   columns or one column and their difference from observed scalar
    ///   support. Columns use interval MSMs or ascending ten-bit suffix sums;
    ///   both include the actual random tails and commitment blinds.
    /// - **Alive at return:** `RETAINED_PER_PAIR` elements per pair (the
    ///   three `N`-row columns) and the shared table columns, plus two blinds
    ///   per pair. Nothing is transformed here; the quotient stage's
    ///   transforms take over the permuted columns later.
    pub(crate) fn commit_lookup_permutations(
        &mut self,
        advice: &AdvicePrefix,
        feeds: WitnessFeeds,
        blindings: Vec<[LookupBlinding; LOOKUPS_PER_ACTION]>,
    ) -> Result<LookupPrefix, Error> {
        let target = self.target;
        if advice.values.len() != self.instance_polynomials.len()
            || advice.values.iter().any(|columns| {
                columns.len() != ADVICE_COLUMNS || columns.iter().any(|column| column.len() != N)
            })
            || self
                .instance_polynomials
                .iter()
                .any(|column| column.len() != N)
        {
            return Err(Error::InternalInvariant);
        }

        // Shape-check the pre-sampled blinding schedule: one `LookupBlinding`
        // per lookup per action, each masking `BLINDING_FACTORS + 1` tail
        // rows on both permuted columns.
        let blind_rows = lookup_stage::MASK_ROWS_PER_COLUMN;
        // Inventory tie: the fixed lookup count is the per-Action pair count.
        if target.lookups().len() != lookup_stage::LOOKUPS_PER_ACTION {
            return Err(crate::native::invariant::failed(
                crate::native::invariant::Invariant::LookupCount,
            ));
        }
        if blindings.len() != advice.values.len()
            || blindings.iter().any(|action_blindings| {
                action_blindings.len() != target.lookups().len()
                    || action_blindings.iter().any(|blinding| {
                        blinding.input_rows.len() != blind_rows
                            || blinding.table_rows.len() != blind_rows
                    })
            })
        {
            return Err(Error::InternalInvariant);
        }

        let lookup_feeds = feeds.into_actions();
        if lookup_feeds.len() != advice.values.len() {
            return Err(Error::InternalInvariant);
        }
        let lookup_count = target.lookups().len();
        let scratch = &self.workspace.lookup;
        scratch.provision(target, advice.values.len(), self.execution.budget.get());
        let theta = advice.theta;
        // A table releases its dependent input jobs as soon as compression
        // finishes. Other tables and their inputs can still occupy the pool.
        let table_sources = &target.lookup_preparation().sources;
        if table_sources.len() != lookup_count {
            return Err(Error::InternalInvariant);
        }
        let preparation = target.lookup_preparation();
        let side_pairs = advice.values.len() * lookup_count;
        let mut table_jobs: Vec<_> = preparation
            .unique_sources
            .iter()
            .zip(&preparation.consumer_counts)
            .map(|(&index, &consumers)| {
                (index, Vec::with_capacity(advice.values.len() * consumers))
            })
            .collect();
        for (action, ((advice_columns, instance_column), action_feeds)) in advice
            .values
            .iter()
            .zip(&self.instance_polynomials)
            .zip(lookup_feeds)
            .enumerate()
        {
            for (lookup_index, ids) in action_feeds.into_lookups().into_iter().enumerate() {
                let position = *preparation
                    .source_positions
                    .get(lookup_index)
                    .ok_or(Error::InternalInvariant)?;
                let (_, inputs) = table_jobs
                    .get_mut(position)
                    .ok_or(Error::InternalInvariant)?;
                inputs.push((
                    action * lookup_count + lookup_index,
                    lookup_index,
                    ids,
                    advice_columns.as_slice(),
                    instance_column,
                ));
            }
        }
        let table_sides = self
            .execution
            .map(table_jobs, |(lookup_index, inputs), execution| {
                let compressed =
                    SharedPoly::new(compress_table_in(target, lookup_index, &theta, execution)?);
                let access = prepared_table_access_in(target, lookup_index, &compressed, scratch);
                let pairs = execution
                    .map(
                        inputs,
                        |(position, lookup_index, ids, advice_columns, instance_column),
                         execution| {
                            let job = LookupInputJob {
                                lookup_index,
                                ids,
                                advice_columns,
                                instance_column,
                                compressed_table: &compressed,
                                access: &access,
                            };
                            prepare_lookup_input(job, target, &theta, execution, scratch)
                                .map(|pair| (position, pair))
                        },
                    )
                    .into_iter()
                    .collect::<Result<Vec<_>, Error>>()?;
                Ok::<_, Error>((compressed, pairs))
            })
            .into_iter()
            .collect::<Result<Vec<_>, Error>>()?;
        let compressed_tables = try_array_from_fn(|index| {
            let position = *preparation
                .source_positions
                .get(index)
                .ok_or(Error::InternalInvariant)?;
            Ok(table_sides
                .get(position)
                .ok_or(Error::InternalInvariant)?
                .0
                .clone())
        })?;
        if compressed_tables.len() != lookup_stage::SHARED_TABLE_COLUMNS {
            return Err(Error::InternalInvariant);
        }
        // Restore transcript order independently of completion order.
        let mut pairs: Vec<_> = (0..side_pairs).map(|_| None).collect();
        for (_, inputs) in table_sides {
            for (position, pair) in inputs {
                let slot = pairs.get_mut(position).ok_or(Error::InternalInvariant)?;
                if slot.replace(pair).is_some() {
                    return Err(Error::InternalInvariant);
                }
            }
        }
        let mut pairs = pairs.into_iter();
        let mut prepared = Vec::with_capacity(advice.values.len());
        let mut run_pairs = Vec::with_capacity(side_pairs);
        for action_blindings in blindings.into_iter() {
            let mut action_blindings = action_blindings.into_iter();
            let action_lookups = try_array_from_fn(|_| {
                let blinding = action_blindings.next().ok_or(Error::InternalInvariant)?;
                let (compressed_input, columns) =
                    pairs.next().flatten().ok_or(Error::InternalInvariant)?;
                let mut permuted_input = columns.input;
                let mut permuted_table = columns.table;
                run_pairs.push((columns.input_runs, columns.table_runs));
                permuted_input.extend(blinding.input_rows);
                permuted_table.extend(blinding.table_rows);
                if permuted_input.len() != N || permuted_table.len() != N {
                    return Err(Error::InternalInvariant);
                }

                Ok(PermutedLookup {
                    compressed_input,
                    permuted_input: SharedPoly::new(permuted_input),
                    permuted_table: SharedPoly::new(permuted_table),
                    input_blind: blinding.input_blind,
                    table_blind: blinding.table_blind,
                    input_commitment: VestaPoint::IDENTITY,
                    table_commitment: VestaPoint::IDENTITY,
                })
            })?;
            prepared.push(action_lookups);
        }
        if pairs.next().is_some() || run_pairs.len() != side_pairs {
            return Err(Error::InternalInvariant);
        }
        // Physical recipes may reconstruct a commitment; publication still
        // contains input then table for every (Action, lookup) pair.
        let jobs = prepared
            .iter()
            .flatten()
            .zip(&run_pairs)
            .map(|(lookup, (input_runs, table_runs))| LookupCommitPair {
                input: &lookup.permuted_input,
                table: &lookup.permuted_table,
                input_runs,
                table_runs,
                input_blind: lookup.input_blind,
                table_blind: lookup.table_blind,
            })
            .collect::<Vec<_>>();
        if 2 * jobs.len() != lookup_stage::commitment_jobs(advice.values.len()) {
            return Err(Error::InternalInvariant);
        }
        // These columns and run pairs were assembled to the target's lookup
        // layout above; commitment errors signal a broken internal contract.
        let pending_commitments = target
            .parameters()
            .commit_lookup_pairs_projective(&jobs, &mut self.workspace.msm, self.execution)
            .map_err(|_| Error::InternalInvariant)?;
        drop(jobs);
        drop(run_pairs);

        // Either freshly blinded member may be identity, which requires
        // retrying proof creation because the transcript cannot encode it.
        let mut normalized = normalized(&pending_commitments).into_iter();
        for action_lookups in &mut prepared {
            for lookup in action_lookups {
                lookup.input_commitment = normalized.next().ok_or(Error::InternalInvariant)?;
                lookup.table_commitment = normalized.next().ok_or(Error::InternalInvariant)?;
                self.transcript
                    .write_point(&lookup.input_commitment)
                    .map_err(|_| Error::RetryRandomness)?;
                self.transcript
                    .write_point(&lookup.table_commitment)
                    .map_err(|_| Error::RetryRandomness)?;
            }
        }
        if normalized.next().is_some() {
            return Err(Error::InternalInvariant);
        }
        let beta = self.transcript.squeeze_challenge();
        let gamma = self.transcript.squeeze_challenge();

        Ok(LookupPrefix {
            lookups: prepared,
            compressed_tables,
            beta,
            gamma,
        })
    }
}

const _: () = assert!(
    PERMUTATION_COLUMN_COUNT % PERMUTATION_CHUNK_LEN == 1
        && KEPT_PERMUTATION_SETS + 1 == PERMUTATION_SETS
);

/// The challenge-only constants of one θ-compression batch: `θ`, `θ²`, and
/// the Sinsemilla family's value on an unselected row, `θ·K47 + K48`.
#[derive(Clone, Copy)]
pub(super) struct ThetaConstants {
    pub(super) theta: Fp,
    pub(super) theta_squared: Fp,
    pub(super) unselected: Fp,
}

impl ThetaConstants {
    pub(super) fn new(theta: Fp, constants: &LookupKernelConstants) -> Self {
        Self {
            theta,
            theta_squared: theta.square(),
            unselected: theta.mul(&constants.k47).add(&constants.k48),
        }
    }
}

/// One residue-major window of extended rows: rows `residue + 8k` for `k`
/// in `k_offset..k_offset + rows`, the unit the compression tasks and the
/// residue-major coset records share.
#[derive(Clone, Copy)]
struct RowWindow {
    residue: usize,
    k_offset: usize,
    rows: usize,
}

impl RowWindow {
    /// The extended row at `offset` into the window.
    #[inline(always)]
    fn row(&self, offset: usize) -> usize {
        self.residue + ((self.k_offset + offset) << (EXTENDED_N / N).trailing_zeros())
    }

    fn is_valid(&self) -> bool {
        self.residue < EXTENDED_N / N && self.k_offset + self.rows <= N
    }
}

/// Theta-compresses one expression range over a contiguous row window.
/// A direct kernel for one pinned lookup expression program on the extended
/// coset: the same polynomial the source tree defines, with its queries
/// resolved to columns at construction instead of per row.
///
/// Column and rotation indices mirror the pinned query tables (`ADVICE_QUERIES`
/// and `FIXED_QUERIES` in `sensei-shared`); `⁺` marks the next-row rotation.
/// `lookup_kernel_group` assigns kernels by lookup index and side, and the
/// parallel-compression parity test checks every kernel against the
/// tree evaluator on pseudo-random cosets, so a kernel that drifted from its
/// program would fail there.
#[derive(Clone, Copy)]
pub(super) enum LookupKernel {
    /// `f14 · (f15 · (a9 − 2¹⁰·a9⁺) + (1 − f15) · a9)`.
    WindowedRangeInput,
    /// `f_s · (a_c − 2¹⁰ · (f_r − f_r · (f_r − 1)) · a_c⁺)`.
    ShortRangeInput {
        selector: usize,
        run: usize,
        column: usize,
    },
    /// `f_s · a_c + (1 − f_s) · K47`.
    SelectedAdvice { selector: usize, column: usize },
    /// `f_s · (K7 · (a_b + a_d) · (2·a_p + a_q − a_b²) − a_b · (a_p − a_q)) + K48 · (1 − f_s)`.
    SelectedQuadratic {
        selector: usize,
        b: usize,
        d: usize,
        p: usize,
        q: usize,
    },
    /// A bare fixed-column query.
    FixedColumn(usize),
}

impl LookupKernel {
    /// Whether the kernel reads any advice column. The table-side kernels
    /// are bare fixed-column queries, so a compression of table sides needs
    /// no advice cosets and can run before any exist (the fixed-only view of
    /// the quotient stage's single input wave).
    pub(super) fn reads_advice(self) -> bool {
        !matches!(self, Self::FixedColumn(_))
    }
}

/// Shared expression constants the kernels read.
pub(super) struct LookupKernelConstants {
    pub(super) two_pow_10: Fp,
    pub(super) k7: Fp,
    pub(super) k47: Fp,
    pub(super) k48: Fp,
}

impl LookupKernelConstants {
    pub(super) fn load() -> Self {
        Self {
            two_pow_10: generated_expressions::constant(6),
            k7: generated_expressions::constant(7),
            k47: generated_expressions::constant(47),
            k48: generated_expressions::constant(48),
        }
    }
}

/// The kernel sequence for one lookup expression range, or `None` when the
/// range is not one of the pinned lookup sides (the caller then walks trees).
/// The largest pinned lookup expression range: the Sinsemilla sides have
/// three programs, the range check one.
const MAX_LOOKUP_KERNELS: usize = 3;

/// The kernels of one pinned lookup expression range, held inline — one or
/// three `Copy` descriptors — so a resolved group needs no heap storage.
#[derive(Clone, Copy)]
struct LookupKernelGroup {
    kernels: [LookupKernel; MAX_LOOKUP_KERNELS],
    len: usize,
}

impl LookupKernelGroup {
    fn one(kernel: LookupKernel) -> Self {
        Self {
            kernels: [kernel; MAX_LOOKUP_KERNELS],
            len: 1,
        }
    }

    fn three(kernels: [LookupKernel; MAX_LOOKUP_KERNELS]) -> Self {
        Self { kernels, len: 3 }
    }

    /// The kernels in program order.
    fn as_slice(&self) -> &[LookupKernel] {
        &self.kernels[..self.len]
    }
}

/// Resolves a pinned lookup expression range to its kernels. Production
/// requires every range to resolve before scheduling compression jobs.
fn lookup_kernel_group(
    target: &FixedTarget,
    programs: ExpressionRange,
) -> Option<LookupKernelGroup> {
    resolve_lookup_kernel_group(target.lookups(), programs)
}

fn resolve_lookup_kernel_group(
    lookups: &[LookupExpressionRanges],
    programs: ExpressionRange,
) -> Option<LookupKernelGroup> {
    use LookupKernel::*;
    let range = programs.indices();
    for (lookup_index, lookup) in lookups.iter().enumerate() {
        let group = if lookup.inputs().indices() == range {
            match lookup_index {
                0 => LookupKernelGroup::one(WindowedRangeInput),
                1 => LookupKernelGroup::three([
                    ShortRangeInput {
                        selector: 16,
                        run: 12,
                        column: 2,
                    },
                    SelectedAdvice {
                        selector: 16,
                        column: 1,
                    },
                    SelectedQuadratic {
                        selector: 16,
                        b: 3,
                        d: 4,
                        p: 0,
                        q: 1,
                    },
                ]),
                2 => LookupKernelGroup::three([
                    ShortRangeInput {
                        selector: 17,
                        run: 13,
                        column: 7,
                    },
                    SelectedAdvice {
                        selector: 17,
                        column: 6,
                    },
                    SelectedQuadratic {
                        selector: 17,
                        b: 8,
                        d: 9,
                        p: 5,
                        q: 6,
                    },
                ]),
                _ => return None,
            }
        } else if lookup.tables().indices() == range {
            match lookup_index {
                0 => LookupKernelGroup::one(FixedColumn(0)),
                1 | 2 => LookupKernelGroup::three([FixedColumn(0), FixedColumn(1), FixedColumn(2)]),
                _ => return None,
            }
        } else {
            continue;
        };
        return (group.len == programs.len()).then_some(group);
    }
    None
}

/// Evaluates one kernel at `row` of the extended coset. Columns are validated
/// to `EXTENDED_N` entries by the caller.
fn evaluate_lookup_kernel<F: Index<usize, Output = Fp>>(
    kernel: LookupKernel,
    constants: &LookupKernelConstants,
    advice: &[ExtendedCoset],
    fixed: &[F],
    row: usize,
) -> Fp {
    let next = rotated_extended_row(row, 1);
    let fixed = |column: usize| fixed[column][row];
    let one_minus = |selector: Fp| <Fp>::ONE.sub(&selector);
    match kernel {
        LookupKernel::WindowedRangeInput => {
            let (f14, f15) = (fixed(14), fixed(15));
            let (a9, a9_next) = (advice[9][row], advice[9][next]);
            let windowed = a9.sub(&a9_next.mul(&constants.two_pow_10));
            f14.mul(&f15.mul(&windowed).add(&one_minus(f15).mul(&a9)))
        }
        LookupKernel::ShortRangeInput {
            selector,
            run,
            column,
        } => {
            let (f_s, f_r) = (fixed(selector), fixed(run));
            let (a, a_next) = (advice[column][row], advice[column][next]);
            let run_gate = f_r.sub(&f_r.mul(&f_r.sub(&<Fp>::ONE)));
            f_s.mul(&a.sub(&run_gate.mul(&a_next).mul(&constants.two_pow_10)))
        }
        LookupKernel::SelectedAdvice { selector, column } => {
            let f_s = fixed(selector);
            f_s.mul(&advice[column][row])
                .add(&one_minus(f_s).mul(&constants.k47))
        }
        LookupKernel::SelectedQuadratic {
            selector,
            b,
            d,
            p,
            q,
        } => {
            let f_s = fixed(selector);
            let (a_b, a_d, a_p, a_q) = (
                advice[b][row],
                advice[d][row],
                advice[p][row],
                advice[q][row],
            );
            let quadratic = a_p.add(&a_p).add(&a_q).sub(&a_b.square());
            let selected = constants
                .k7
                .mul(&a_b.add(&a_d).mul(&quadratic))
                .sub(&a_b.mul(&a_p.sub(&a_q)));
            f_s.mul(&selected).add(&one_minus(f_s).mul(&constants.k48))
        }
        LookupKernel::FixedColumn(column) => fixed(column),
    }
}

/// The Sinsemilla input family's three component kernels — a short-range
/// input, a selected advice value, and a selected quadratic under one
/// selector — recognized as one fused row kernel, so the compression writes
/// each θ-folded row once instead of sweeping the chunk once per component.
#[derive(Clone, Copy)]
pub(super) struct SinsemillaFusedKernel {
    pub(super) selector: usize,
    pub(super) run: usize,
    pub(super) short: usize,
    pub(super) advice: usize,
    pub(super) b: usize,
    pub(super) d: usize,
    pub(super) p: usize,
    pub(super) q: usize,
}

pub(super) fn sinsemilla_fused_kernel(kernels: &[LookupKernel]) -> Option<SinsemillaFusedKernel> {
    match kernels {
        [
            LookupKernel::ShortRangeInput {
                selector,
                run,
                column: short,
            },
            LookupKernel::SelectedAdvice {
                selector: advice_selector,
                column: advice,
            },
            LookupKernel::SelectedQuadratic {
                selector: quadratic_selector,
                b,
                d,
                p,
                q,
            },
        ] if selector == advice_selector && selector == quadratic_selector => {
            Some(SinsemillaFusedKernel {
                selector: *selector,
                run: *run,
                short: *short,
                advice: *advice,
                b: *b,
                d: *d,
                p: *p,
                q: *q,
            })
        }
        _ => None,
    }
}

/// One extended row's Action-independent coefficients of the fused Sinsemilla
/// input family, formed once per row and applied to every Action's advice.
///
/// Derivation: with selector `S`, run `R`, and `B = 2¹⁰·(R − R·(R − 1))`,
/// the row's Horner fold `((short · θ) + advice) · θ + quadratic` of the
/// three components `S·(a − B·a⁺)`, `S·v + (1 − S)·K47`, and
/// `S·Q + (1 − S)·K48` (with `Q = K7·(b + d)·(2p + q − b²) − b·(p − q)`)
/// equals `S·θ²·(a − B·a⁺) + S·θ·v + S·Q + (1 − S)·(θ·K47 + K48)`. The
/// coefficients `B`, `S·θ²`, `S·θ`, and `(1 − S)·(θ·K47 + K48)` depend on
/// the row's fixed columns and the challenge only (five multiplications per
/// row); standalone evaluation of each Action then costs eight
/// multiplications, five of them in two reductions, against the fourteen
/// the separate components cost. The quotient instead reuses the gates'
/// cubic through [`Self::evaluate_with_cubic`]. Field
/// arithmetic is exact, so every value equals the component
/// fold (pinned by `parallel_lookup_compression_matches_serial_reference`).
#[derive(Clone, Copy)]
pub(super) struct SinsemillaRowCoefficients {
    pub(super) f_s: Fp,
    pub(super) window: Fp,
    pub(super) selected_theta_squared: Fp,
    pub(super) selected_theta: Fp,
    pub(super) unselected: Fp,
}

impl SinsemillaRowCoefficients {
    #[inline(always)]
    pub(super) fn at_row<F: Index<usize, Output = Fp>>(
        kernel: SinsemillaFusedKernel,
        constants: &LookupKernelConstants,
        theta: &ThetaConstants,
        fixed: &[F],
        row: usize,
    ) -> Self {
        let f_s = fixed[kernel.selector][row];
        let f_r = fixed[kernel.run][row];
        let run_gate = f_r.sub(&f_r.mul(&f_r.sub(&<Fp>::ONE)));
        Self {
            f_s,
            window: run_gate.mul(&constants.two_pow_10),
            selected_theta_squared: f_s.mul(&theta.theta_squared),
            selected_theta: f_s.mul(&theta.theta),
            unselected: <Fp>::ONE.sub(&f_s).mul(&theta.unselected),
        }
    }

    /// The Action's compressed input at the row (`next` is the row's `+1`
    /// rotation).
    #[cfg(test)]
    #[inline(always)]
    pub(super) fn evaluate<A: Index<usize, Output = Fp>>(
        &self,
        kernel: SinsemillaFusedKernel,
        constants: &LookupKernelConstants,
        advice: &[A],
        row: usize,
        next: usize,
    ) -> Fp {
        let (a_b, a_d, a_p, a_q) = (
            advice[kernel.b][row],
            advice[kernel.d][row],
            advice[kernel.p][row],
            advice[kernel.q][row],
        );
        let quadratic = a_p.add(&a_p).add(&a_q).sub(&a_b.square());
        let selected = <Fp>::sum_of_products(
            &[constants.k7.mul(&a_b.add(&a_d)), a_b.neg()],
            &[quadratic, a_p.sub(&a_q)],
        );
        self.compress(kernel, advice, row, next, selected)
    }

    /// Reuse the quotient gates' cubic `T = (b + d)·(2p + q − b²)`.
    #[inline(always)]
    fn evaluate_with_cubic<A: Index<usize, Output = Fp>>(
        &self,
        kernel: SinsemillaFusedKernel,
        constants: &LookupKernelConstants,
        advice: &[A],
        rows: [usize; 2],
        cubic: &Fp,
    ) -> Fp {
        let [row, next] = rows;
        let selected = <Fp>::sum_of_products(
            &[constants.k7, advice[kernel.b][row].neg()],
            &[*cubic, advice[kernel.p][row].sub(&advice[kernel.q][row])],
        );
        self.compress(kernel, advice, row, next, selected)
    }

    #[inline(always)]
    fn compress<A: Index<usize, Output = Fp>>(
        &self,
        kernel: SinsemillaFusedKernel,
        advice: &[A],
        row: usize,
        next: usize,
        selected: Fp,
    ) -> Fp {
        let (a, a_next) = (advice[kernel.short][row], advice[kernel.short][next]);
        <Fp>::sum_of_products(
            &[self.selected_theta_squared, self.selected_theta, self.f_s],
            &[
                a.sub(&self.window.mul(&a_next)),
                advice[kernel.advice][row],
                selected,
            ],
        )
        .add(&self.unselected)
    }
}

/// One extended row's coefficients of the windowed range input:
/// `f14·(f15·(a − 2¹⁰·a⁺) + (1 − f15)·a) = f14·a − (2¹⁰·f14·f15)·a⁺`, whose
/// two coefficients depend on the row's fixed columns only, so each Action
/// costs two multiplications in one reduction against four. Exact field
/// arithmetic keeps the field values equal.
#[derive(Clone, Copy)]
pub(super) struct RangeRowCoefficients {
    pub(super) f14: Fp,
    pub(super) window: Fp,
}

impl RangeRowCoefficients {
    #[inline(always)]
    pub(super) fn at_row<F: Index<usize, Output = Fp>>(
        constants: &LookupKernelConstants,
        fixed: &[F],
        row: usize,
    ) -> Self {
        let f14 = fixed[14][row];
        Self {
            f14,
            window: f14.mul(&fixed[15][row]).mul(&constants.two_pow_10).neg(),
        }
    }

    #[inline(always)]
    pub(super) fn evaluate<A: Index<usize, Output = Fp>>(
        &self,
        advice: &[A],
        row: usize,
        next: usize,
    ) -> Fp {
        let a9 = &advice[9];
        <Fp>::sum_of_products(&[self.f14, self.window], &[a9[row], a9[next]])
    }
}

/// The input-side kernel of one lookup as the fold evaluates it at a row.
/// Every pinned lookup resolves to one of these
/// (`every_pinned_lookup_side_has_kernels`).
#[derive(Clone, Copy)]
pub(super) enum LookupInputRowKernel {
    Range,
    Sinsemilla {
        kernel: SinsemillaFusedKernel,
        cubic_bank: usize,
    },
}

pub(super) fn lookup_input_row_kernel(
    target: &FixedTarget,
    lookup_index: usize,
) -> Result<LookupInputRowKernel, Error> {
    let programs = target
        .lookups()
        .get(lookup_index)
        .ok_or(Error::InternalInvariant)?
        .inputs();
    let group = lookup_kernel_group(target, programs).ok_or(Error::InternalInvariant)?;
    if let Some(kernel) = sinsemilla_fused_kernel(group.as_slice()) {
        // These columns must match the gate frame's two shared cubics.
        let cubic_bank = match (kernel.p, kernel.q, kernel.b, kernel.d) {
            (0, 1, 3, 4) => 0,
            (5, 6, 8, 9) => 1,
            _ => return Err(Error::InternalInvariant),
        };
        return Ok(LookupInputRowKernel::Sinsemilla { kernel, cubic_bank });
    }
    if let [LookupKernel::WindowedRangeInput] = group.as_slice() {
        return Ok(LookupInputRowKernel::Range);
    }
    Err(Error::InternalInvariant)
}

/// One lookup's input-kernel coefficients at one row.
#[derive(Clone, Copy)]
pub(super) enum LookupInputRowCoefficients {
    Range(RangeRowCoefficients),
    Sinsemilla {
        kernel: SinsemillaFusedKernel,
        coefficients: SinsemillaRowCoefficients,
        cubic_bank: usize,
    },
}

impl LookupInputRowCoefficients {
    #[inline(always)]
    pub(super) fn at_row<F: Index<usize, Output = Fp>>(
        kernel: LookupInputRowKernel,
        constants: &LookupKernelConstants,
        theta: &ThetaConstants,
        fixed: &[F],
        row: usize,
    ) -> Self {
        match kernel {
            LookupInputRowKernel::Range => {
                Self::Range(RangeRowCoefficients::at_row(constants, fixed, row))
            }
            LookupInputRowKernel::Sinsemilla { kernel, cubic_bank } => Self::Sinsemilla {
                kernel,
                coefficients: SinsemillaRowCoefficients::at_row(
                    kernel, constants, theta, fixed, row,
                ),
                cubic_bank,
            },
        }
    }

    #[inline(always)]
    pub(super) fn evaluate<A: Index<usize, Output = Fp>>(
        &self,
        constants: &LookupKernelConstants,
        advice: &[A],
        row: usize,
        next: usize,
        cubics: &[Fp; 2],
    ) -> Fp {
        match self {
            Self::Range(coefficients) => coefficients.evaluate(advice, row, next),
            Self::Sinsemilla {
                kernel,
                coefficients,
                cubic_bank,
            } => coefficients.evaluate_with_cubic(
                *kernel,
                constants,
                advice,
                [row, next],
                &cubics[*cubic_bank],
            ),
        }
    }
}

/// A three-column lookup table side — three bare fixed-column kernels —
/// recognized as one fused row pass writing `((f_a·θ) + f_b)·θ + f_c` once
/// per row instead of one write and two read-modify-write sweeps.
pub(super) fn fixed_columns_fused_kernel(kernels: &[LookupKernel]) -> Option<[usize; 3]> {
    match kernels {
        [
            LookupKernel::FixedColumn(a),
            LookupKernel::FixedColumn(b),
            LookupKernel::FixedColumn(c),
        ] => Some([*a, *b, *c]),
        _ => None,
    }
}

/// One row pass of a three-column table side; columns are validated by the
/// caller.
fn compress_fixed_columns_rows<F: Index<usize, Output = Fp>>(
    [a, b, c]: [usize; 3],
    theta: &Fp,
    fixed: &[F],
    window: RowWindow,
    out: &mut [Fp],
) {
    let (a, b, c) = (&fixed[a], &fixed[b], &fixed[c]);
    for (offset, slot) in out.iter_mut().enumerate() {
        let row = window.row(offset);
        *slot = a[row].mul_add(theta, &b[row]).mul_add(theta, &c[row]);
    }
}

/// Compresses one range of pinned lookup programs through their kernels.
fn compress_kernel_rows<F: Index<usize, Output = Fp>>(
    kernels: &[LookupKernel],
    theta: &Fp,
    advice: &[ExtendedCoset],
    fixed: &[F],
    window: RowWindow,
    out: &mut [Fp],
) -> Result<(), Error> {
    const FIXED_COLUMNS_READ: usize = 18;
    if (advice.len() < ADVICE_COLUMNS && kernels.iter().any(|kernel| kernel.reads_advice()))
        || fixed.len() < FIXED_COLUMNS_READ
        || window.rows != out.len()
        || !window.is_valid()
    {
        return Err(Error::InternalInvariant);
    }
    let constants = LookupKernelConstants::load();
    if let Some(columns) = fixed_columns_fused_kernel(kernels) {
        compress_fixed_columns_rows(columns, theta, fixed, window, out);
        return Ok(());
    }
    let (first, rest) = kernels.split_first().ok_or(Error::InternalInvariant)?;
    for (offset, slot) in out.iter_mut().enumerate() {
        *slot = evaluate_lookup_kernel(*first, &constants, advice, fixed, window.row(offset));
    }
    for kernel in rest {
        for (offset, accumulator) in out.iter_mut().enumerate() {
            let value =
                evaluate_lookup_kernel(*kernel, &constants, advice, fixed, window.row(offset));
            *accumulator = accumulator.mul_add(theta, &value);
        }
    }
    Ok(())
}

/// One `commit_lookup_permutations` input-side job: one Action's lookup
/// identities with the columns its blinding-visible rows are re-evaluated on,
/// and the lookup's shared compressed table and counting access.
struct LookupInputJob<'a> {
    lookup_index: usize,
    ids: LookupInputIds,
    advice_columns: &'a [SharedPoly],
    instance_column: &'a SharedPoly,
    compressed_table: &'a SharedPoly,
    access: &'a Option<TableAccess>,
}

/// Prepares one Action's compressed input and permuted pair for one lookup.
fn prepare_lookup_input(
    job: LookupInputJob<'_>,
    target: &FixedTarget,
    theta: &Fp,
    execution: Execution<'_>,
    scratch: &LookupWorkspace,
) -> Result<(SharedPoly, PermutedColumns), Error> {
    let tuple_index =
        prepared_lookup_table_tuples(target, job.lookup_index).ok_or(Error::InternalInvariant)?;
    let compressed_input = compress_input_in(
        &job.ids,
        job.compressed_table,
        tuple_index,
        theta,
        target,
        job.advice_columns,
        job.instance_column,
        execution,
    )?;
    let columns = match job.access.as_ref() {
        Some(access) => {
            let (order, value_probe, entry_of_id) = access.parts();
            let counts = count_input_entries_in(
                order,
                value_probe,
                entry_of_id,
                job.ids.ids(),
                &compressed_input,
                scratch,
            )?;
            reconstruct_permuted_in(order, &counts, USABLE_ROWS_END, execution, scratch)?
        }
        None => {
            let (input, table) = permute_sorted_usable_values(
                sort_usable_values(usable_rows_with_tail_capacity(&compressed_input)),
                sort_usable_values(usable_rows_with_tail_capacity(job.compressed_table)),
            )?;
            let input_runs = column_runs_in(&input, scratch);
            let table_runs = column_runs_in(&table, scratch);
            PermutedColumns {
                input: input.into(),
                table: table.into(),
                input_runs,
                table_runs,
            }
        }
    };
    Ok((SharedPoly::new(compressed_input), columns))
}

/// The largest backward (`(0, max_negative)`) and forward
/// (`(max_positive)`) advice query rotations, from the circuit's query table.
const ADVICE_ROTATION_REACH: (usize, usize) = {
    let queries = &crate::native::queries::ADVICE_QUERIES;
    let mut negative = 0usize;
    let mut positive = 0usize;
    let mut index = 0;
    while index < queries.len() {
        let rotation = queries[index].rotation;
        if rotation < 0 {
            let reach = rotation.unsigned_abs() as usize;
            if reach > negative {
                negative = reach;
            }
        } else {
            let reach = rotation as usize;
            if reach > positive {
                positive = reach;
            }
        }
        index += 1;
    }
    (negative, positive)
};

/// Rows whose advice-dependent expression evaluation can observe the advice
/// blinding tail `USABLE_ROWS_END..N`, derived from the query rotations: a
/// backward rotation by `r` makes rows `0..r` wrap onto the tail, and a
/// forward rotation by `r` makes rows from `USABLE_ROWS_END - r` read into
/// it (the tail rows themselves read it at rotation zero).
///
/// # Blinding contract
///
/// The preflight lookup feeds are evaluated on the *unblinded* witness (so
/// the checks see the values the circuit constrains); every row listed here
/// is re-evaluated on the blinded columns before θ-compression, so the
/// committed compressed input equals a dense post-blinding evaluation on
/// every row. The set must contain every row any rotation can carry into
/// the tail; the assertion below pins it to the two-piece shape the current
/// rotations (at most one row either way) produce.
fn blinding_visible_rows() -> impl Iterator<Item = usize> {
    let (negative, positive) = ADVICE_ROTATION_REACH;
    (0..negative).chain(USABLE_ROWS_END - positive..N)
}

const _: () = {
    let (negative, positive) = ADVICE_ROTATION_REACH;
    assert!(negative <= 1 && positive <= 1);
    assert!(negative == 1 && positive == 1);
    // Rows `0..1` and `USABLE_ROWS_END - 1..N`: the set the implementation
    // has always re-evaluated.
    assert!(USABLE_ROWS_END - positive == USABLE_ROWS_END - 1);
};

#[allow(clippy::too_many_arguments)] // tuple reuse and blinded-row evaluation need distinct inputs
fn compress_input_in<A: AsRef<[Fp]>>(
    ids: &LookupInputIds,
    compressed_table: &[Fp],
    tuples: &TupleIndex,
    theta: &Fp,
    target: &FixedTarget,
    advice: &[A],
    instance: &[Fp],
    execution: Execution<'_>,
) -> Result<Buffer<Fp>, Error> {
    let representatives = tuples.representatives();
    if compressed_table.len() != N || ids.ids().len() != USABLE_ROWS_END {
        return Err(Error::InternalInvariant);
    }
    let mut compressed = execution.buffer(N, false);
    for (slot, &id) in compressed.iter_mut().zip(ids.ids()) {
        let row = representatives
            .get(usize::from(id))
            .ok_or(Error::InternalInvariant)?;
        *slot = compressed_table[usize::from(*row)];
    }
    // The tail and wraparound rows must read the blinded advice. Reuse the
    // prepared fused kernels, with the interpreter retained for other recipes.
    if let Some(kernel) = target
        .lookups()
        .iter()
        .position(|lookup| lookup.inputs().indices() == ids.programs().indices())
        .and_then(|index| target.preflight().kernels[index])
        .filter(|kernel| kernel.accepts(advice))
    {
        let mut tuple = [Fp::ZERO; generated_expressions::MAX_LOOKUP_INPUT_COMPONENTS];
        for row in blinding_visible_rows() {
            let values = kernel.row(advice, target.fixed_values(), row, &mut tuple);
            let (first, rest) = values.split_first().ok_or(Error::InternalInvariant)?;
            compressed[row] = rest
                .iter()
                .fold(*first, |acc, value| acc.mul_add(theta, value));
        }
        return Ok(compressed);
    }
    let mut evaluations = ids
        .programs()
        .indices()
        .map(|index| {
            crate::native::compiled_expressions::program(index)?
                .full
                .bind(target.fixed_values(), advice, instance)
        })
        .collect::<Result<Vec<_>, Error>>()?;
    let (first, rest) = evaluations
        .split_first_mut()
        .ok_or(Error::InternalInvariant)?;
    for row in blinding_visible_rows() {
        let mut accumulator = first.evaluate(row);
        for evaluation in rest.iter_mut() {
            accumulator = accumulator.mul_add(theta, &evaluation.evaluate(row));
        }
        compressed[row] = accumulator;
    }
    Ok(compressed)
}

/// The usable rows whose compressed input was re-evaluated on the blinded
/// columns; the permutation probes them by value instead of reading their
/// identity.
fn patched_usable_rows() -> impl Iterator<Item = usize> {
    blinding_visible_rows().filter(|&row| row < USABLE_ROWS_END)
}

fn compress_table_in(
    target: &FixedTarget,
    lookup_index: usize,
    theta: &Fp,
    execution: Execution<'_>,
) -> Result<Buffer<Fp>, Error> {
    let side = target
        .lookup_preparation()
        .sides
        .get(lookup_index)
        .and_then(Option::as_ref)
        .ok_or(Error::InternalInvariant)?;
    let (first, rest) = side
        .components
        .split_first()
        .ok_or(Error::InternalInvariant)?;
    if rest.is_empty() {
        return Ok(execution.copy(first));
    }
    let tuples = &side.tuples;
    let fold = |values: &[Fp]| -> Option<Fp> {
        let (head, tail) = values.split_first()?;
        Some(tail.iter().fold(*head, |accumulator, value| {
            accumulator.mul_add(theta, value)
        }))
    };
    let mut distinct = execution.buffer(tuples.len(), false);
    for (id, value) in distinct.iter_mut().enumerate() {
        *value = tuples
            .tuple(id as u16)
            .and_then(fold)
            .ok_or(Error::InternalInvariant)?;
    }
    let mut compressed = execution.buffer(N, false);
    compressed.clear();
    for &id in tuples.row_ids() {
        compressed.push(
            *distinct
                .get(usize::from(id))
                .ok_or(Error::InternalInvariant)?,
        );
    }
    for (row, head) in first.iter().enumerate().skip(compressed.len()) {
        let mut accumulator = *head;
        for values in rest {
            accumulator = accumulator.mul_add(theta, &values[row]);
        }
        compressed.push(accumulator);
    }
    if compressed.len() != N {
        return Err(Error::InternalInvariant);
    }
    Ok(compressed)
}

/// Copies one compressed side's usable rows into a buffer with room for the
/// `N`-row permuted column its blinding tail completes, so the tail append
/// never reallocates.
fn usable_rows_with_tail_capacity(column: &[Fp]) -> Vec<Fp> {
    let mut rows = Vec::with_capacity(N);
    rows.extend_from_slice(&column[..USABLE_ROWS_END]);
    rows
}

/// One θ-compressed lookup side's usable rows in **canonical numeric order**
/// (ascending `to_canonical_uint`, the order reduced `Fp`'s `Ord` defines) — the
/// reference sort of the permutation argument. Built only by
/// [`sort_usable_values`]; the permutation walk relies on the order for its
/// merge, and the interval commitments on the equal-value runs it produces.
/// This is the sorting representation; membership and probing use the
/// reduced Montgomery representation instead (see the lookup preparation phases).
struct SortedUsableValues(Vec<Fp>);

fn sort_usable_values(mut values: Vec<Fp>) -> SortedUsableValues {
    // Sorting by the canonical representative matches reduced `PastaField`'s `Ord` but
    // reduces each element out of Montgomery form once, instead of twice on
    // every comparison.
    values.sort_by_cached_key(|value| value.to_canonical_uint());
    SortedUsableValues(values)
}

/// The reference permutation over two sorted sides of equal length: the input
/// column stays in its sorted order; each first occurrence of an input value
/// claims that value's next table row (the `<` comparisons walk the same
/// canonical order the sort established), and the leftover table values fill
/// the repeated-input rows from the last upward. An input value absent from
/// the table is `UnsatisfiedWitness`. The result therefore satisfies, on every
/// usable row, `input[row] == table[row]` or `input[row] == input[row - 1]`.
fn permute_sorted_usable_values(
    input_values: SortedUsableValues,
    table_values: SortedUsableValues,
) -> Result<(Vec<Fp>, Vec<Fp>), Error> {
    let (SortedUsableValues(input_values), SortedUsableValues(table_values)) =
        (input_values, table_values);
    if input_values.len() != table_values.len() {
        return Err(Error::InternalInvariant);
    }

    let usable_rows = input_values.len();
    // Sized for the `N`-row column the blinding tail completes; the sorted
    // input keeps its caller's capacity for the same reason.
    let mut permuted_table_values = Vec::with_capacity(N.max(usable_rows));
    permuted_table_values.resize(usable_rows, <Fp>::ZERO);
    let mut consumed_table_rows = Vec::with_capacity(usable_rows);
    let mut repeated_input_rows = Vec::with_capacity(usable_rows);
    let mut table_row = 0;
    for row in 0..usable_rows {
        if row == 0 || (input_values[row]).reduce() != (input_values[row - 1]).reduce() {
            permuted_table_values[row] = input_values[row];
            while table_row < usable_rows
                && (table_values[table_row]).reduce() < (input_values[row]).reduce()
            {
                table_row += 1;
            }
            if table_values.get(table_row).map(|value| value.reduce())
                != Some(input_values[row].reduce())
            {
                return Err(Error::UnsatisfiedWitness);
            }
            consumed_table_rows.push(table_row);
            table_row += 1;
        } else {
            repeated_input_rows.push(row);
        }
    }

    let mut consumed_table_rows = consumed_table_rows.into_iter().peekable();
    for (row, value) in table_values.into_iter().enumerate() {
        if consumed_table_rows.peek() == Some(&row) {
            consumed_table_rows.next();
        } else {
            let destination = repeated_input_rows.pop().ok_or(Error::InternalInvariant)?;
            permuted_table_values[destination] = value;
        }
    }
    if consumed_table_rows.next().is_some() || !repeated_input_rows.is_empty() {
        return Err(Error::InternalInvariant);
    }
    Ok((input_values, permuted_table_values))
}

/// Distinct-tuple index of one fixed-only lookup table side.
// Diagnostic tickets enlarge each Vec; keep the ordinary storage layout.
pub(super) enum PreparedLookupTable {
    /// Multi-expression table: distinct tuples as `(representative usable
    /// row, occurrences)` in identity order; the compressed order is
    /// θ-dependent and must be derived per proof.
    Distinct { distinct: Vec<(u16, u16)> },
    /// Single-expression table: compressed values equal the fixed values for
    /// every θ, so the ascending order, probe map, and each identity's entry
    /// are fully prepared.
    Static {
        order: TableOrder,
        probe: RawValueMap,
        entry_of_id: Vec<u16>,
    },
}

/// The earliest lookup with the same ordered, fixed-only table trees.
/// Source equality, arity, and component order all matter for θ-compression.
/// This metadata depends on circuit structure, never on a witness or θ.
fn table_sources() -> Vec<usize> {
    let tables = generated_expressions::LOOKUPS
        .iter()
        .map(|lookup| {
            lookup
                .tables()
                .indices()
                .map(|program| {
                    crate::native::compiled_expressions::program(program)
                        .expect("validated lookup program")
                        .full
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    tables
        .iter()
        .enumerate()
        .map(|(index, table)| {
            if table.iter().all(|tree| tree.is_fixed_only()) {
                tables[..index]
                    .iter()
                    .position(|other| other == table)
                    .unwrap_or(index)
            } else {
                index
            }
        })
        .collect()
}

/// Restore lookup-index order while retaining exactly one buffer per distinct
/// table tuple. Inventory errors cannot silently drop or misassign a column.
pub(super) fn share_compressed_tables(
    sources: &[usize],
    columns: Vec<ExtendedCoset>,
) -> Result<Vec<Arc<ExtendedCoset>>, Error> {
    let mut columns = columns.into_iter();
    let mut tables: Vec<Arc<ExtendedCoset>> = Vec::with_capacity(sources.len());
    for (index, &source) in sources.iter().enumerate() {
        let table = if source == index {
            Arc::new(columns.next().ok_or(Error::InternalInvariant)?)
        } else {
            Arc::clone(tables.get(source).ok_or(Error::InternalInvariant)?)
        };
        tables.push(table);
    }
    if columns.next().is_some() {
        return Err(Error::InternalInvariant);
    }
    Ok(tables)
}

/// Build immutable preparation once per distinct table and retain the lookup
/// indices expected by preflight and the independent permutation consumers.
fn prepare_unique_tables<T>(
    sources: &[usize],
    build: impl Fn(usize) -> Option<T>,
) -> Vec<Option<Arc<T>>> {
    let mut tables: Vec<Option<Arc<T>>> = Vec::with_capacity(sources.len());
    for (index, &source) in sources.iter().enumerate() {
        let table = if index == source {
            build(index).map(|value| Arc::new(value))
        } else {
            tables[source].clone()
        };
        tables.push(table);
    }
    tables
}

// ----------------------------------------------------------------------------
// Lookup preparation phases
//
// A lookup travels through four representations, each a named record whose
// constructor establishes the facts its consumers rely on. Their reuse
// scopes differ, and nothing crosses a scope boundary implicitly:
//
// - **Component tuples** (fixed, process lifetime): the table side's raw
//   expression values per row (`PreparedTableSide::components`, exactly the
//   fixed-only table programs evaluated on every row) and the exact
//   distinct-tuple sets built from them — `TupleIndex` over the usable rows
//   for preflight membership, and `PreparedLookupTable` for the permutation
//   (`Distinct`: representative rows and counts; `Static`: a single
//   expression's fully prepared order and probe). All of it is independent
//   of θ and of any witness.
// - **Tuple identities** (per Action, from preflight): each usable input
//   row's `TupleIndex` identity — the hit of the membership probe
//   (`LookupInputIds`). Rows the blinding can reach are re-evaluated on the
//   blinded columns instead of trusting their identity.
// - **θ-compressed values** (per proof for the table, per Action for the
//   inputs): Horner folds of the components by the proof's θ — each distinct
//   table tuple once, gathered onto the table's rows and, through the
//   identities, onto each Action's input rows (`compress_table_from_prepared`,
//   `compress_input_from_ids`). Two distinct component tuples may compress to
//   equal values; a compressed collision is *not* an equal tuple, so
//   `prepared_table_access` refuses the counting reconstruction whenever the
//   compressed distinct tuples collide and that proof falls back to the
//   reference sort.
// - **Canonical order** (per proof): `TableOrder` — distinct compressed
//   values ascending by canonical representation with their usable-row
//   occurrence counts, and each identity's entry in it — and
//   `SortedUsableValues` for the reference path.
//   Sorting compares canonical numeric values (`to_canonical_uint`, the
//   `Ord` of reduced `Fp`).
// - **Permuted rows** (per Action): `PermutedColumns`, the usable-row
//   permutation of one input/table pair with its equal-value runs, then
//   blinded into `PermutedLookup`.
//
// Two representations of the same field elements are in play, and they are
// used for different questions. Membership and probing (`TupleIndex`,
// `RawValueMap`) reduce loose residues before hashing and comparing their
// unique Montgomery limbs. A hit or miss agrees with a comparison of canonical
// encodings without converting out of Montgomery form. Ordering
// (`TableOrder`, `SortedUsableValues`) uses the **canonical** numeric value,
// which requires the reduction out of Montgomery form. Neither may stand in
// for the other: Montgomery limbs do not order, and canonical order is not a
// hash key here.
// ----------------------------------------------------------------------------

/// One lookup's prepared table side. Table expressions are fixed-only (pinned
/// by `lookup_table_sides_are_fixed_only_with_prepared_indices`), so both
/// forms are witness-independent: per-proof θ-compression Horner-folds the
/// full-domain component vectors, and preflight membership probes the exact
/// distinct usable-row tuple index instead of rebuilding a tuple set.
///
/// Phase: component tuples (fixed, process lifetime).
pub(super) struct PreparedTableSide {
    /// Per table expression, its value on every base-domain row.
    pub(super) components: Vec<Vec<Fp>>,
    /// Distinct usable-row tuples, indexed on their reduced Montgomery limbs.
    pub(super) tuples: TupleIndex,
}

/// Open-addressed exact-match index of one table side's distinct, uncompressed
/// usable-row tuples, keyed on each component's reduced Montgomery limbs, with
/// each tuple's identity (its first-seen order), representative row, and
/// usable-row multiplicity, and every usable row's identity.
///
/// A membership probe reduces each component before hashing its Montgomery
/// limbs and confirms with component-wise reduced field equality. Equivalent
/// loose representations therefore have the same hash and identity, without
/// converting each component to its canonical byte encoding. The θ-compressed
/// values have a separate index in [`RawValueMap`].
pub(in crate::native) struct TupleIndex {
    pub(super) arity: usize,
    /// Distinct tuples, `arity` consecutive components each, in identity
    /// (first-seen row) order.
    pub(super) tuples: Vec<Fp>,
    /// Each identity's first usable row.
    pub(super) representatives: Vec<u16>,
    /// Each identity's number of usable rows.
    pub(super) counts: Vec<u16>,
    /// Each usable row's identity.
    pub(super) row_ids: Vec<u16>,
    pub(super) mask: usize,
    /// Identity plus one; zero marks an empty slot.
    pub(super) slots: Vec<u32>,
}

impl TupleIndex {
    /// Indexes the distinct tuples formed by rows `0..rows` of `components`.
    pub(super) fn build(components: &[Vec<Fp>], rows: usize) -> Self {
        let arity = components.len();
        let capacity = (rows * 2).next_power_of_two().max(8);
        let mask = capacity - 1;
        let mut slots = alloc::vec![ 0u32; capacity];
        let mut tuples = Vec::with_capacity(rows * arity);
        let mut representatives = Vec::with_capacity(rows);
        let mut counts = Vec::with_capacity(rows);
        let mut row_ids = Vec::with_capacity(rows);
        for row in 0..rows {
            let mut slot = hash_tuple(components.iter().map(|column| &column[row])) as usize & mask;
            let id = loop {
                match slots[slot] {
                    0 => {
                        let id = tuples.len() / arity;
                        slots[slot] = id as u32 + 1;
                        tuples.extend(components.iter().map(|column| column[row]));
                        representatives.push(row as u16);
                        counts.push(0);
                        break id;
                    }
                    occupied => {
                        let id = occupied as usize - 1;
                        if tuples[id * arity..][..arity]
                            .iter()
                            .zip(components)
                            .all(|(stored, column)| (stored).reduce() == (column[row]).reduce())
                        {
                            break id;
                        }
                    }
                }
                slot = (slot + 1) & mask;
            };
            counts[id] += 1;
            row_ids.push(id as u16);
        }
        Self {
            arity,
            tuples,
            representatives,
            counts,
            row_ids,
            mask,
            slots,
        }
    }

    /// Components per tuple.
    pub(in crate::native) fn arity(&self) -> usize {
        self.arity
    }

    /// Number of distinct tuples indexed.
    pub(in crate::native) fn len(&self) -> usize {
        self.tuples.len() / self.arity
    }

    /// The components of tuple `id`, or `None` for an unknown identity.
    pub(in crate::native) fn tuple(&self, id: u16) -> Option<&[Fp]> {
        let start = usize::from(id) * self.arity;
        self.tuples.get(start..start + self.arity)
    }

    /// Each identity's first usable row.
    pub(super) fn representatives(&self) -> &[u16] {
        &self.representatives
    }

    /// Each identity's number of usable rows.
    pub(super) fn counts(&self) -> &[u16] {
        &self.counts
    }

    /// Each usable row's identity, row-ascending.
    pub(super) fn row_ids(&self) -> &[u16] {
        &self.row_ids
    }

    /// The identity of `tuple` (`arity` components) if it is one of the
    /// indexed table tuples: the same reduced hash and component-wise field
    /// equality as [`Self::find_row`], for a tuple formed in registers.
    pub(in crate::native) fn find_tuple(&self, tuple: &[Fp]) -> Option<u16> {
        debug_assert_eq!(tuple.len(), self.arity);
        let mut slot = hash_tuple(tuple.iter()) as usize & self.mask;
        loop {
            match self.slots[slot] {
                0 => return None,
                occupied => {
                    let id = occupied as usize - 1;
                    if self.tuples[id * self.arity..][..self.arity]
                        .iter()
                        .zip(tuple)
                        .all(|(left, right)| left.reduce() == right.reduce())
                    {
                        return Some(id as u16);
                    }
                }
            }
            slot = (slot + 1) & self.mask;
        }
    }

    /// The identity of row `row` of `inputs` — one value vector per input
    /// expression, `arity` of them — if it is one of the indexed table tuples.
    pub(in crate::native) fn find_row(&self, inputs: &[Vec<Fp>], row: usize) -> Option<u16> {
        debug_assert_eq!(inputs.len(), self.arity);
        let mut slot = hash_tuple(inputs.iter().map(|column| &column[row])) as usize & self.mask;
        loop {
            match self.slots[slot] {
                0 => return None,
                occupied => {
                    let id = occupied as usize - 1;
                    if self.tuples[id * self.arity..][..self.arity]
                        .iter()
                        .zip(inputs)
                        .all(|(stored, column)| (stored).reduce() == (column[row]).reduce())
                    {
                        return Some(id as u16);
                    }
                }
            }
            slot = (slot + 1) & self.mask;
        }
    }
}

pub(crate) struct LookupPreparation {
    sources: Vec<usize>,
    unique_sources: Vec<usize>,
    source_positions: Vec<usize>,
    consumer_counts: Vec<usize>,
    table_kernels: Vec<LookupKernelGroup>,
    pub(super) sides: Vec<Option<Arc<PreparedTableSide>>>,
    pub(super) tables: Vec<Option<Arc<PreparedLookupTable>>>,
}
impl LookupPreparation {
    pub(crate) fn sources(&self) -> &[usize] {
        &self.sources
    }
    pub(crate) fn new(fixed_values: &[[Fp; N]]) -> Result<Self, Error> {
        let sources = table_sources();
        let unique_sources = sources
            .iter()
            .enumerate()
            .filter_map(|(index, &source)| (index == source).then_some(index))
            .collect::<Vec<_>>();
        let source_positions = sources
            .iter()
            .map(|source| {
                unique_sources
                    .iter()
                    .position(|unique| unique == source)
                    .expect("table source")
            })
            .collect::<Vec<_>>();
        let mut consumer_counts = alloc::vec![0; unique_sources.len()];
        for &position in &source_positions {
            consumer_counts[position] += 1;
        }
        let sides = prepare_unique_tables(&sources, |index| {
            prepare_table_side(fixed_values, &generated_expressions::LOOKUPS[index])
        });
        let tables = prepare_unique_tables(&sources, |index| {
            Some(prepare_lookup_table(sides.get(index)?.as_deref()?))
        });
        let table_kernels = unique_sources
            .iter()
            .map(|&index| {
                resolve_lookup_kernel_group(
                    generated_expressions::LOOKUPS,
                    generated_expressions::LOOKUPS[index].tables(),
                )
                .filter(|group| !group.as_slice().iter().any(|kernel| kernel.reads_advice()))
                .ok_or(Error::InternalInvariant)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            table_kernels,
            sources,
            unique_sources,
            source_positions,
            consumer_counts,
            sides,
            tables,
        })
    }

    /// Table topology is fixed at preparation. Only theta changes per proof;
    /// each residue writes directly into its final destination.
    pub(super) fn compress_cosets(
        &self,
        theta: Fp,
        target: &FixedTarget,
        execution: Execution<'_>,
    ) -> Result<Vec<ExtendedCoset>, Error> {
        let fixed: [_; FIXED_COLUMNS] =
            core::array::from_fn(|column| target.fixed_polynomials().cosets().column(column));
        self.table_kernels
            .iter()
            .map(|group| {
                let mut values = execution.buffer(EXTENDED_N, false);
                for (residue, output) in values.chunks_exact_mut(N).enumerate() {
                    compress_kernel_rows(
                        group.as_slice(),
                        &theta,
                        &[],
                        &fixed,
                        RowWindow {
                            residue,
                            k_offset: 0,
                            rows: N,
                        },
                        output,
                    )?;
                }
                ExtendedCoset::from_flat(values)
                    .ok_or_else(|| invariant::failed(Invariant::ExtendedDomainLength))
            })
            .collect()
    }
}

fn prepare_table_side(
    fixed_values: &[[Fp; N]],
    lookup: &LookupExpressionRanges,
) -> Option<PreparedTableSide> {
    let mut components = Vec::with_capacity(lookup.tables().len());
    for program in lookup.tables().indices() {
        let mut evaluation = crate::native::compiled_expressions::program(program)
            .ok()?
            .full
            .bind_fixed(fixed_values)
            .ok()?;
        let column = (0..N).map(|row| evaluation.evaluate(row)).collect();
        components.push(column);
    }
    let tuples = TupleIndex::build(&components, USABLE_ROWS_END);
    Some(PreparedTableSide { components, tuples })
}

/// Preflight's membership view of one prepared table side, or `None` when the
/// target's table expressions are not fixed-only.
pub(in crate::native) fn prepared_lookup_table_tuples(
    target: &FixedTarget,
    lookup_index: usize,
) -> Option<&TupleIndex> {
    Some(
        &target
            .lookup_preparation()
            .sides
            .get(lookup_index)?
            .as_ref()?
            .tuples,
    )
}

fn prepare_lookup_table(side: &PreparedTableSide) -> PreparedLookupTable {
    let tuple_index = &side.tuples;
    if let [column] = side.components.as_slice() {
        let mut sorted: Vec<_> = column[..USABLE_ROWS_END]
            .iter()
            .map(|value| (value.to_canonical_uint(), *value))
            .collect();
        sorted.sort_unstable_by_key(|entry| entry.0);
        let mut entries: Vec<(Fp, u16)> = Vec::with_capacity(sorted.len());
        for (_, value) in sorted {
            if let Some((previous, count)) = entries.last_mut()
                && (previous).reduce() == (value).reduce()
            {
                *count += 1;
            } else {
                entries.push((value, 1));
            }
        }
        let value_probe = build_value_map(&entries);
        // Every identity's single component is a table value, so it has an
        // entry; an impossible miss maps to an out-of-range entry the
        // consumers reject.
        let entry_of_id = (0..tuple_index.len())
            .map(|id| {
                tuple_index
                    .tuple(id as u16)
                    .and_then(|tuple| probe_value_map(&value_probe, &entries, &tuple[0]))
                    .map_or(u16::MAX, |entry| entry as u16)
            })
            .collect();
        return PreparedLookupTable::Static {
            order: TableOrder {
                entries: entries.into(),
            },
            probe: value_probe,
            entry_of_id,
        };
    }
    // Identity order: `distinct[id]` is tuple `id`'s representative row and
    // multiplicity, so a preflight identity indexes it directly.
    let distinct = tuple_index
        .representatives()
        .iter()
        .zip(tuple_index.counts())
        .map(|(&row, &count)| (row, count))
        .collect();
    PreparedLookupTable::Distinct { distinct }
}

/// Ascending compressed-value order of one lookup table: `(compressed value,
/// usable-row occurrences)` sorted by canonical representation. The values
/// are distinct by construction — `prepared_table_access` refuses a table
/// whose compressed distinct tuples collide — so an entry index identifies a
/// compressed value exactly.
///
/// Phase: canonical order (per proof; process lifetime only for the
/// single-expression `Static` tables, whose compression is θ-independent).
pub(super) struct TableOrder {
    pub(super) entries: Buffer<(Fp, u16)>,
}

/// Open-addressed exact-match map from θ-compressed table values to
/// [`TableOrder`] entry indices. These indices name compressed values;
/// [`TupleIndex`] identities name uncompressed component tuples.
///
/// Keys hash by reduced Montgomery limbs, and every probe confirms with
/// reduced field equality. Equivalent loose representations therefore agree
/// with the reference scan.
pub(super) struct RawValueMap {
    pub(super) mask: usize,
    /// Entry index plus one; zero marks an empty slot.
    pub(super) slots: Buffer<u32>,
}

fn hash_value(value: &Fp) -> u64 {
    hash_tuple(core::iter::once(value))
}

/// Hashes a tuple by reduced Montgomery limbs so equal values share a key.
fn hash_tuple<'a>(components: impl Iterator<Item = &'a Fp>) -> u64 {
    const MIX: u64 = 0x9e37_79b9_7f4a_7c15;
    components
        .flat_map(|value| value.reduce().montgomery_limbs())
        .fold(0u64, |hash, limb| {
            (hash ^ limb).wrapping_mul(MIX).rotate_left(23)
        })
}

pub(super) fn build_value_map(entries: &[(Fp, u16)]) -> RawValueMap {
    let capacity = (entries.len() * 4).next_power_of_two().max(8);
    build_value_map_in(entries, alloc::vec![0u32; capacity].into())
}

fn build_value_map_in(entries: &[(Fp, u16)], mut slots: Buffer<u32>) -> RawValueMap {
    let mask = slots.len() - 1;
    for (index, (value, _)) in entries.iter().enumerate() {
        let mut slot = hash_value(value) as usize & mask;
        while slots[slot] != 0 {
            slot = (slot + 1) & mask;
        }
        slots[slot] = index as u32 + 1;
    }
    RawValueMap { mask, slots }
}

fn probe_value_map(map: &RawValueMap, entries: &[(Fp, u16)], value: &Fp) -> Option<usize> {
    let mut slot = hash_value(value) as usize & map.mask;
    loop {
        match map.slots[slot] {
            0 => return None,
            occupied => {
                let index = occupied as usize - 1;
                if (entries[index].0).reduce() == (value).reduce() {
                    return Some(index);
                }
            }
        }
        slot = (slot + 1) & map.mask;
    }
}

/// One prepared lookup table's per-proof access: prepared order and probe map
/// borrowed for single-expression tables, or derived from the compressed
/// column for multi-expression tables.
pub(super) enum TableAccess {
    Static(Arc<PreparedLookupTable>),
    /// Canonical order, compressed-value probe, and tuple-identity-to-entry map.
    PerProof(TableOrder, RawValueMap, Buffer<u16>),
}

impl TableAccess {
    /// The ascending order, the value probe, and each tuple identity's entry
    /// index in that order.
    pub(super) fn parts(&self) -> (&TableOrder, &RawValueMap, &[u16]) {
        match self {
            Self::Static(table) => match table.as_ref() {
                PreparedLookupTable::Static {
                    order,
                    probe: value_probe,
                    entry_of_id,
                } => (order, value_probe, entry_of_id),
                _ => unreachable!("static table access"),
            },
            Self::PerProof(order, value_probe, entry_of_id) => (order, value_probe, entry_of_id),
        }
    }
}

/// Resolves one lookup's table access for this proof, or `None` when the
/// table is unprepared or two distinct tuples collide after θ-compression
/// (the counting order would be ambiguous relative to the reference sort, so
/// that proof falls back to it).
fn prepared_table_access_in(
    target: &FixedTarget,
    lookup_index: usize,
    compressed_table: &[Fp],
    scratch: &LookupWorkspace,
) -> Option<TableAccess> {
    match target
        .lookup_preparation()
        .tables
        .get(lookup_index)?
        .as_deref()?
    {
        PreparedLookupTable::Static { .. } => Some(TableAccess::Static(Arc::clone(
            target
                .lookup_preparation()
                .tables
                .get(lookup_index)?
                .as_ref()?,
        ))),
        PreparedLookupTable::Distinct { distinct } => {
            let mut keyed = scratch
                .keys
                .take(distinct.len(), LookupWorkspace::empty_key(), false);
            keyed.clear();
            keyed.extend(
                distinct
                    .iter()
                    .enumerate()
                    .map(|(tuple_id, &(row, multiplicity))| {
                        let compressed_value = compressed_table[usize::from(row)];
                        (
                            compressed_value.to_canonical_uint(),
                            compressed_value,
                            multiplicity,
                            tuple_id,
                        )
                    }),
            );
            keyed.sort_unstable_by_key(|(canonical_key, _, _, _)| *canonical_key);
            if keyed.windows(2).any(|pair| {
                let (left_canonical_key, _, _, _) = &pair[0];
                let (right_canonical_key, _, _, _) = &pair[1];
                *left_canonical_key == *right_canonical_key
            }) {
                return None;
            }
            let mut entry_of_id = scratch.indices.take(keyed.len(), 0, false);
            for (entry_index, &(_, _, _, tuple_id)) in keyed.iter().enumerate() {
                entry_of_id[tuple_id] = entry_index as u16;
            }
            let mut entries = scratch.entries.take(keyed.len(), (Fp::ZERO, 0), false);
            for (entry, &(_, compressed_value, multiplicity, _)) in
                entries.iter_mut().zip(keyed.iter())
            {
                *entry = (compressed_value, multiplicity);
            }
            drop(keyed);
            // Clear the pooled slots: zero marks an empty probe slot.
            let slots = scratch
                .slots
                .take((entries.len() * 4).next_power_of_two().max(8), 0, true);
            let value_probe = build_value_map_in(&entries, slots);
            Some(TableAccess::PerProof(
                TableOrder { entries },
                value_probe,
                entry_of_id,
            ))
        }
    }
}

/// Counts each table entry's occurrences among one Action's usable input
/// rows: a row carrying a preflight identity maps through `entry_of_id`
/// (its compressed value is the entry's value by construction); a patched
/// row — re-evaluated on the blinded columns — probes its value, failing as
/// the reference does when it is not a table value.
fn count_input_entries_in(
    order: &TableOrder,
    probe: &RawValueMap,
    entry_of_id: &[u16],
    ids: &[u16],
    compressed_input: &[Fp],
    scratch: &LookupWorkspace,
) -> Result<Buffer<u32>, Error> {
    if ids.len() != USABLE_ROWS_END || compressed_input.len() < USABLE_ROWS_END {
        return Err(Error::InternalInvariant);
    }
    let mut counts = scratch.counts.take(order.entries.len(), 0, true);
    let mut patched = patched_usable_rows().peekable();
    for (row, &id) in ids.iter().enumerate() {
        let entry = if patched.peek() == Some(&row) {
            patched.next();
            probe_value_map(probe, &order.entries, &compressed_input[row])
                .ok_or(Error::UnsatisfiedWitness)?
        } else {
            usize::from(
                *entry_of_id
                    .get(usize::from(id))
                    .ok_or(Error::InternalInvariant)?,
            )
        };
        *counts.get_mut(entry).ok_or(Error::InternalInvariant)? += 1;
    }
    Ok(counts)
}

fn reconstruct_permuted_in(
    order: &TableOrder,
    input_counts: &[u32],
    usable_rows: usize,
    execution: Execution<'_>,
    scratch: &LookupWorkspace,
) -> Result<PermutedColumns, Error> {
    if input_counts.len() != order.entries.len() {
        return Err(Error::InternalInvariant);
    }

    // Both columns receive their `N - usable_rows` blinding tail later, so
    // they are sized for `N` now and never grow.
    let mut permuted_input = execution.buffer(N, false);
    permuted_input.clear();
    let mut permuted_table = execution.buffer(usable_rows, false);
    let mut input_runs = scratch.runs.take(usable_rows, (0, Fp::ZERO), false);
    input_runs.clear();
    for ((value, _), input_count) in order.entries.iter().zip(input_counts) {
        if *input_count > 0 {
            let run_start = permuted_input.len();
            input_runs.push((run_start as u32, *value));
            permuted_table[run_start] = *value;
            permuted_input.resize(run_start + *input_count as usize, *value);
        }
    }
    if permuted_input.len() != usable_rows {
        return Err(Error::InternalInvariant);
    }
    // The reference walks leftover table values ascending while popping
    // repeated input rows from the back of an ascending list, so the k-th
    // largest leftover lands on the k-th smallest repeated row.
    let mut repeated = input_runs
        .iter()
        .enumerate()
        .flat_map(|(index, &(start, _))| {
            let end = input_runs
                .get(index + 1)
                .map_or(usable_rows, |&(start, _)| start as usize);
            start as usize + 1..end
        });
    for ((value, table_count), input_count) in order.entries.iter().zip(input_counts).rev() {
        let leftover = usize::from(*table_count) - usize::from(*input_count > 0);
        for _ in 0..leftover {
            let row = repeated.next().ok_or(Error::InternalInvariant)?;
            permuted_table[row] = *value;
        }
    }
    if repeated.next().is_some() {
        return Err(Error::InternalInvariant);
    }
    let table_runs = column_runs_in(&permuted_table, scratch);
    Ok(PermutedColumns {
        input: permuted_input,
        table: permuted_table,
        input_runs,
        table_runs,
    })
}

/// One lookup's reconstructed permuted columns over the usable rows, with
/// each column's ascending `(start row, value)` runs for interval commitment.
/// The input runs fall out of the reconstruction; the table column is
/// fragmented by the leftover rule (see `permuted_lookup_column_run_census`),
/// so its runs are extracted from the finished column.
///
/// Phase: permuted rows (per Action). Invariants established by both
/// constructors (`reconstruct_permuted_columns` and the reference
/// `permute_sorted_usable_values`): `input` is in canonical ascending order,
/// `table` is a permutation of the compressed table's usable rows, and on
/// every row `input[row] == table[row]` or `input[row] == input[row - 1]`.
pub(super) struct PermutedColumns {
    pub(super) input: Buffer<Fp>,
    pub(super) table: Buffer<Fp>,
    pub(super) input_runs: Buffer<(u32, Fp)>,
    pub(super) table_runs: Buffer<(u32, Fp)>,
}

fn column_runs_in(values: &[Fp], scratch: &LookupWorkspace) -> Buffer<(u32, Fp)> {
    let mut runs = scratch.runs.take(values.len(), (0, Fp::ZERO), false);
    runs.clear();
    for (row, value) in values.iter().enumerate() {
        if row == 0 || values[row - 1].reduce() != value.reduce() {
            runs.push((row as u32, *value));
        }
    }
    runs
}

#[cfg(test)]
mod certified_product_input_tests {
    use super::*;
    use crate::native::test_support::reduced_values;
    use alloc::vec;

    fn reconstructed_prefix(collision: bool) -> LookupPrefix {
        let mut tables = Vec::new();
        let lookups = core::array::from_fn(|lookup| {
            let low = if collision {
                <Fp>::ZERO
            } else {
                <Fp>::from_u64((10 * lookup + 1) as u64)
            };
            let high = if collision {
                <Fp>::ZERO
            } else {
                <Fp>::from_u64((10 * lookup + 2) as u64)
            };
            let mut input = vec![low; 700];
            input.resize(USABLE_ROWS_END, high);
            input.reverse();
            let mut table = vec![low; 1_000];
            table.resize(USABLE_ROWS_END, high);
            let (mut permuted_input, mut permuted_table) =
                permute_usable_values(input.clone(), table.clone()).unwrap();
            if !collision {
                let order = TableOrder {
                    entries: vec![(low, 1_000), (high, (USABLE_ROWS_END - 1_000) as u16)].into(),
                };
                let probe = build_value_map(&order.entries);
                let counts = count_input_values(&order, &probe, &input).unwrap();
                let counted =
                    reconstruct_permuted_columns(&order, &counts, USABLE_ROWS_END).unwrap();
                assert_eq!(
                    reduced_values(&counted.input),
                    reduced_values(&permuted_input)
                );
                assert_eq!(
                    reduced_values(&counted.table),
                    reduced_values(&permuted_table)
                );
                permuted_input = counted.input.to_vec();
                permuted_table = counted.table.to_vec();
            }
            for row in USABLE_ROWS_END..N {
                input.push(<Fp>::from_u64((100_000 + lookup * 100 + row) as u64));
                table.push(<Fp>::from_u64((200_000 + lookup * 100 + row) as u64));
                permuted_input.push(<Fp>::from_u64((300_000 + lookup * 100 + row) as u64));
                permuted_table.push(<Fp>::from_u64((400_000 + lookup * 100 + row) as u64));
            }
            tables.push(SharedPoly::new(table));
            PermutedLookup {
                compressed_input: SharedPoly::new(input),
                permuted_input: SharedPoly::new(permuted_input),
                permuted_table: SharedPoly::new(permuted_table),
                input_blind: <Fp>::ONE,
                table_blind: <Fp>::ONE,
                input_commitment: VestaPoint::IDENTITY,
                table_commitment: VestaPoint::IDENTITY,
            }
        });
        LookupPrefix {
            lookups: vec![lookups],
            compressed_tables: tables.try_into().ok().unwrap(),
            beta: <Fp>::ONE,
            gamma: <Fp>::ONE,
        }
    }

    #[test]
    fn certified_inputs_bind_exact_tables_after_counting_and_collision_sorting() {
        // Distinct prepared tuples that compress to zero must take the actual
        // sorted fallback rather than use an ambiguous counting order.
        let target = crate::test_codec::target();
        let collision_lookup = target.lookup_preparation().tables.iter().position(|table| {
            matches!(table.as_deref(), Some(PreparedLookupTable::Distinct { distinct }) if distinct.len() > 1)
        }).expect("target has a multi-tuple lookup");
        assert!(prepared_table_access(target, collision_lookup, &vec![<Fp>::ZERO; N]).is_none());

        for collision in [false, true] {
            let prefix = reconstructed_prefix(collision);
            let inputs = prefix.certified_product_inputs(0).unwrap();
            assert_eq!(inputs.len(), LOOKUPS_PER_ACTION);
            for (index, input) in inputs.enumerate() {
                let (permuted, table) = input.parts();
                assert_eq!(table.as_ptr(), prefix.compressed_tables[index].as_ptr());
                assert_eq!(
                    permuted.compressed_input.as_ptr(),
                    prefix.lookups[0][index].compressed_input.as_ptr()
                );
                assert_eq!(
                    permuted.permuted_input.as_ptr(),
                    prefix.lookups[0][index].permuted_input.as_ptr()
                );
                assert_eq!(
                    permuted.permuted_table.as_ptr(),
                    prefix.lookups[0][index].permuted_table.as_ptr()
                );
                for (original, rearranged) in [
                    (
                        &permuted.compressed_input[..USABLE_ROWS_END],
                        &permuted.permuted_input[..USABLE_ROWS_END],
                    ),
                    (
                        &table[..USABLE_ROWS_END],
                        &permuted.permuted_table[..USABLE_ROWS_END],
                    ),
                ] {
                    let mut original = original.iter().map(|x| x.to_bytes()).collect::<Vec<_>>();
                    let mut rearranged =
                        rearranged.iter().map(|x| x.to_bytes()).collect::<Vec<_>>();
                    original.sort_unstable();
                    rearranged.sort_unstable();
                    assert_eq!(original, rearranged);
                }
            }
        }
    }

    #[test]
    fn certified_inputs_reject_wrong_action_malformed_columns_and_drained_tables() {
        let mut prefix = reconstructed_prefix(false);
        assert!(matches!(
            prefix.certified_product_inputs(1),
            Err(Error::InternalInvariant)
        ));
        assert!(matches!(
            prefix.certified_product_inputs(usize::MAX),
            Err(Error::InternalInvariant)
        ));
        let short = || SharedPoly::new(vec![<Fp>::ZERO; N - 1]);
        let old = core::mem::replace(&mut prefix.lookups[0][1].compressed_input, short());
        assert!(matches!(
            prefix.certified_product_inputs(0),
            Err(Error::InternalInvariant)
        ));
        prefix.lookups[0][1].compressed_input = old;
        let old = core::mem::replace(&mut prefix.lookups[0][1].permuted_input, short());
        assert!(matches!(
            prefix.certified_product_inputs(0),
            Err(Error::InternalInvariant)
        ));
        prefix.lookups[0][1].permuted_input = old;
        let old = core::mem::replace(&mut prefix.lookups[0][1].permuted_table, short());
        assert!(matches!(
            prefix.certified_product_inputs(0),
            Err(Error::InternalInvariant)
        ));
        prefix.lookups[0][1].permuted_table = old;
        let old = core::mem::replace(&mut prefix.compressed_tables[1], short());
        assert!(matches!(
            prefix.certified_product_inputs(0),
            Err(Error::InternalInvariant)
        ));
        prefix.compressed_tables[1] = old;
        assert_eq!(
            prefix.certified_product_inputs(0).unwrap().len(),
            LOOKUPS_PER_ACTION
        );
        // Exactly the partial form reconstructed for later quotient windows.
        prefix.compressed_tables = core::array::from_fn(|_| SharedPoly::new(Vec::new()));
        assert!(matches!(
            prefix.certified_product_inputs(0),
            Err(Error::InternalInvariant)
        ));
    }
}
