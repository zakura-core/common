//! Dense witness assignment storage and rational finalization.
//!
//! Assignment support records positions, including explicit zeros. Gadgets
//! write values straight into the dense advice columns in synthesis order;
//! finalization divides the rational cells in place with one batched
//! inversion. The independent test oracle lives in `writer/shadow.rs`.

#[cfg(test)]
mod shadow;

#[cfg(test)]
use shadow::ShadowWriter;
#[cfg(test)]
pub(super) use shadow::{AssignedCell, AssignmentKind, batch_finalize_rationals};

use crate::Error;
use crate::native::field::Fp;
use crate::native::regions::REGION_STARTS;
use crate::native::target::{ADVICE_COLUMNS, N};
use crate::native::{buffer::Buffer, prover::AdviceMatrix};
use alloc::vec::Vec;

static EMBEDDED_ROW_MAP: RowMap = RowMap;

/// Absolute placement of every V1 synthesis region for the pinned circuit.
pub(crate) struct RowMap;

impl RowMap {
    pub(crate) fn load() -> &'static Self {
        &EMBEDDED_ROW_MAP
    }

    pub(crate) fn absolute_row(&self, region: usize, local_row: usize) -> Result<usize, Error> {
        REGION_STARTS
            .get(region)
            .and_then(|start| start.checked_add(local_row))
            .filter(|row| *row < N)
            .ok_or(Error::InternalInvariant)
    }

    #[cfg(test)]
    pub(crate) fn region_starts(&self) -> &[usize] {
        &REGION_STARTS
    }
}

/// Representation retained until rational assignments are finalized.
#[derive(Clone, Copy, Debug)]
pub(crate) enum AdviceValue {
    AssignedZero,
    Direct(Fp),
    Rational { numerator: Fp, denominator: Fp },
}

/// Words of the per-column assignment bitmask (`N` bits per column).
pub(crate) const ASSIGNED_WORDS_PER_COLUMN: usize = N / 64;

/// One deferred denominator. The numerators are already stored in their
/// dense cells; the entry records which cells the denominator's inverse
/// divides, and at which power, when `finish` runs its single batched
/// inversion. Cells are dense indices `column · N + row`.
pub(super) struct RationalEntry {
    denominator: Fp,
    uses: RationalUses,
}

/// The cells one deferred denominator serves (dense indices).
#[derive(Clone, Copy)]
enum RationalUses {
    /// One cell: `numerator / denominator`.
    Single(u32),
    /// Two numerator cells divided by the same denominator.
    Pair { first: u32, second: u32 },
    /// One incomplete double-and-add's three cells sharing the accumulator's `z`: the
    /// two slopes are `numerator / z` and the x-coordinate is `numerator / z²`,
    /// so one inverse of `z` (squared once for `x`) serves all three — two
    /// fewer independent denominators per round than entering each cell on its
    /// own, by the gadget's algebra rather than by any runtime equality test.
    IncompleteDoubleAndAdd {
        lambda_1: u32,
        lambda_2: u32,
        x: u32,
    },
}

/// Reservation hint for the per-Action rational log, sized just above the
/// grouped schedule's count of deferred denominators — one entry per
/// Sinsemilla word (two note commitments of `NOTE_COMMIT_WORDS`,
/// `MERKLE_DEPTH` levels of `MERKLE_WORDS`, and `COMMIT_IVK_WORDS`: 1,933
/// words), 251 variable-base rounds, one entry per intermediate fixed-window
/// coordinate pair, and the remaining single-cell rationals. Pinned against the
/// fixtures by `rational_log_reservation_covers_the_grouped_schedule` (no growth, and
/// not twice the count). A capacity hint only; correctness never depends on
/// it, and any valid witness may grow the log.
// Tuning knob (capacity hint): any value is valid; the only dependent is the
// vector's initial reservation.
pub(super) const RATIONAL_CAPACITY: usize = 4_096;

/// Minimal dense writer used by the fixed-purpose witness calculations.
///
/// # Support contract
///
/// The per-column bitmask `assigned` *is* the witness's assignment support,
/// and it is distinct from the dense columns:
///
/// - an **explicitly assigned zero** sets its bit and writes nothing (the
///   cell already holds zero);
/// - an **unassigned cell** sets no bit and keeps its zero, so the dense
///   matrix cannot tell the two apart — only the mask can;
/// - a **direct or rational value** sets its bit and writes the cell once
///   (the rational's numerator, divided in place in `finish`);
/// - a second write to a set bit, or a cell outside `ADVICE_COLUMNS × N`, is
///   rejected as an internal invariant.
///
/// The set of assigned positions is fixed by the circuit layout and the
/// gadgets, not by the witness values (pinned by
/// `advice_structural_support_census`), so it is structural support in the
/// sense the commitment paths need; the nonzero event list is not, since a
/// witness may assign zero anywhere in its support.
///
/// Assignments go straight into the ten zero-initialized dense columns the
/// advice matrix will own — the destinations are the cells themselves, so
/// there is no per-proof event record to append and later scatter; a flat
/// per-column bitmask preserves the exact bounds and double-write rejection
/// of the former `AssignedCell` staging matrix and doubles as the witness's
/// support mask (assignment positions are witness-independent — pinned by
/// `advice_structural_support_census`). Rational cells hold their numerator
/// immediately while deferring the denominator to one batched inversion in
/// `finish`, which divides the cells in place (zero denominators are still
/// detected there, after all writes and before any cell is modified, so error
/// ordering on invalid witnesses is unchanged). Under `cfg(test)` an optional
/// shadow replays every write through the former enum-cell writer and asserts
/// agreement, including on error outcomes.
pub(crate) struct WitnessWriter<'a> {
    pub(super) target: &'a crate::native::target::FixedTarget,
    pub(super) execution: crate::native::worker::Execution<'a>,
    pub(super) columns: [Buffer<Fp>; ADVICE_COLUMNS],
    pub(super) assigned: [u64; ADVICE_COLUMNS * ASSIGNED_WORDS_PER_COLUMN],
    pub(super) rationals: Vec<RationalEntry>,
    #[cfg(test)]
    shadow: Option<ShadowWriter>,
}

impl<'a> WitnessWriter<'a> {
    pub(crate) fn new(
        target: &'a crate::native::target::FixedTarget,
        execution: crate::native::worker::Execution<'a>,
    ) -> Self {
        // The rational log's entry count is witness-dependent (a cell direct
        // for one witness may be rational for another), so the buffer is
        // declared growing and the reservation stays a hint.
        let mut rationals = Vec::new();
        rationals.reserve_exact(RATIONAL_CAPACITY);
        Self {
            target,
            execution,
            columns: core::array::from_fn(|_| execution.buffer(N, true)),
            assigned: [0; ADVICE_COLUMNS * ASSIGNED_WORDS_PER_COLUMN],
            rationals,
            #[cfg(test)]
            shadow: None,
        }
    }

    /// Writer whose every write and finalization is checked against the
    /// former enum-cell staging writer.
    #[cfg(test)]
    pub(super) fn with_shadow() -> Self {
        Self {
            shadow: Some(ShadowWriter::new()),
            ..Self::new(crate::test_codec::target(), crate::test_codec::execution())
        }
    }

    /// Whether this writer carries the shadow oracle (tests only; always
    /// false in production builds).
    pub(super) fn shadowed(&self) -> bool {
        #[cfg(test)]
        {
            self.shadow.is_some()
        }
        #[cfg(not(test))]
        {
            false
        }
    }

    /// A writer for one concurrent gadget chain of an Action: fresh
    /// columns, support and rational log, carrying the shadow oracle when
    /// `shadowed`. Its assignments return through [`Self::absorb`].
    pub(super) fn chain_writer(
        target: &'a crate::native::target::FixedTarget,
        execution: crate::native::worker::Execution<'a>,
        shadowed: bool,
    ) -> Self {
        // Distinct purposes from the Action writer's: these buffers are born
        // and released inside the witness stage (the inventory contract pins
        // the Action writer's columns to the multi-opening stage), and the
        // columns are collected fresh rather than cloned from a seed column.
        let mut rationals = Vec::new();
        rationals.reserve_exact(RATIONAL_CAPACITY);
        let columns = core::array::from_fn(|_| execution.buffer(N, true));
        #[cfg(test)]
        let shadow = shadowed.then(ShadowWriter::new);
        #[cfg(not(test))]
        let _ = shadowed;
        Self {
            target,
            execution,
            columns,
            assigned: [0; ADVICE_COLUMNS * ASSIGNED_WORDS_PER_COLUMN],
            rationals,
            #[cfg(test)]
            shadow,
        }
    }

    /// Merges a chain writer's assignments into this writer: the supports
    /// must be disjoint (an overlap is the double write the serial schedule
    /// would have rejected), every assigned cell is copied — direct values
    /// and rational numerators alike — and the chain's deferred denominators
    /// append to this writer's log, so `finish` divides them in the one
    /// batched inversion as before. Values, support and the errors `finish`
    /// can raise are exactly the serial writer's.
    pub(super) fn absorb(&mut self, chain: Self) -> Result<(), Error> {
        let Self {
            columns,
            assigned,
            rationals,
            #[cfg(test)]
            shadow,
            ..
        } = chain;
        for (column, values) in columns.iter().enumerate() {
            for word in 0..ASSIGNED_WORDS_PER_COLUMN {
                let index = column * ASSIGNED_WORDS_PER_COLUMN + word;
                let bits = assigned[index];
                if bits == 0 {
                    continue;
                }
                if self.assigned[index] & bits != 0 {
                    return Err(Error::InternalInvariant);
                }
                self.assigned[index] |= bits;
                let mut remaining = bits;
                while remaining != 0 {
                    let row = word * 64 + remaining.trailing_zeros() as usize;
                    self.columns[column][row] = values[row];
                    remaining &= remaining - 1;
                }
            }
        }
        self.rationals.extend(rationals);
        #[cfg(test)]
        if let (Some(mine), Some(mut theirs)) = (self.shadow.as_mut(), shadow) {
            for (column, cells) in theirs.cells.iter_mut().enumerate() {
                for (row, cell) in cells.iter_mut().enumerate() {
                    if matches!(cell, AssignedCell::Unassigned) {
                        continue;
                    }
                    let cell = core::mem::replace(cell, AssignedCell::Unassigned);
                    let mine = &mut mine.cells[column][row];
                    assert!(
                        matches!(mine, AssignedCell::Unassigned),
                        "chain writers overlap at column {column}, row {row}"
                    );
                    *mine = cell;
                }
            }
        }
        Ok(())
    }

    pub(crate) fn write_advice(
        &mut self,
        column: usize,
        row: usize,
        value: AdviceValue,
    ) -> Result<(), Error> {
        #[cfg(test)]
        let shadow_result = self
            .shadow
            .as_mut()
            .map(|shadow| shadow.write_advice(column, row, value));

        let result = self.write_event(column, row, value);
        #[cfg(test)]
        if let Some(shadow_result) = shadow_result {
            assert_eq!(
                result, shadow_result,
                "event write diverged from the shadow oracle at column {column}, row {row}"
            );
        }
        result
    }

    /// Claims one cell of the support: bounds and double-write rejection.
    pub(super) fn claim_cell(&mut self, column: usize, row: usize) -> Result<(), Error> {
        if column >= ADVICE_COLUMNS || row >= N {
            return Err(Error::InternalInvariant);
        }
        let word = &mut self.assigned[column * ASSIGNED_WORDS_PER_COLUMN + row / 64];
        let bit = 1 << (row % 64);
        if *word & bit != 0 {
            return Err(Error::InternalInvariant);
        }
        *word |= bit;
        Ok(())
    }

    pub(super) fn write_event(
        &mut self,
        column: usize,
        row: usize,
        value: AdviceValue,
    ) -> Result<(), Error> {
        self.claim_cell(column, row)?;
        match value {
            AdviceValue::AssignedZero => {}
            AdviceValue::Direct(value) => self.columns[column][row] = value,
            AdviceValue::Rational {
                numerator,
                denominator,
            } => {
                self.rationals.push(RationalEntry {
                    denominator,
                    uses: RationalUses::Single(dense_index(column, row)),
                });
                self.columns[column][row] = numerator;
            }
        }
        Ok(())
    }

    /// Writes two numerator cells sharing one deferred denominator.
    ///
    /// Cells are claimed in array order. A zero denominator is rejected during
    /// finalization; the test shadow receives two independent rational cells.
    pub(crate) fn write_rational_pair(
        &mut self,
        cells: [(usize, usize); 2],
        numerators: [Fp; 2],
        denominator: Fp,
    ) -> Result<(), Error> {
        #[cfg(test)]
        let shadow_result = self.shadow.as_mut().map(|shadow| {
            cells
                .iter()
                .zip(numerators)
                .try_for_each(|(&(column, row), numerator)| {
                    shadow.write_advice(
                        column,
                        row,
                        AdviceValue::Rational {
                            numerator,
                            denominator,
                        },
                    )
                })
        });

        let result = (|| {
            for (&(column, row), numerator) in cells.iter().zip(numerators) {
                self.claim_cell(column, row)?;
                self.columns[column][row] = numerator;
            }
            let [first, second] = cells.map(|(column, row)| dense_index(column, row));
            self.rationals.push(RationalEntry {
                denominator,
                uses: RationalUses::Pair { first, second },
            });
            Ok(())
        })();
        #[cfg(test)]
        if let Some(shadow_result) = shadow_result {
            assert_eq!(
                result, shadow_result,
                "rational pair write diverged from the shadow oracle at {cells:?}"
            );
        }
        result
    }

    /// Writes one incomplete double-and-add's three rational cells — the two slopes
    /// over `z` and the x-coordinate over `z²` — as three numerator cells
    /// sharing one deferred denominator entry. Cell order: `λ₁`, `λ₂`, `x`.
    /// Under `cfg(test)` the shadow oracle still receives three independent
    /// per-cell rationals, so it stays independent of the sharing.
    pub(crate) fn write_incomplete_double_and_add(
        &mut self,
        cells: [(usize, usize); 3],
        numerators: [Fp; 3],
        z: Fp,
    ) -> Result<(), Error> {
        #[cfg(test)]
        let shadow_result = self.shadow.as_mut().map(|shadow| {
            let denominators = [z, z, z.square()];
            cells.iter().zip(numerators).zip(denominators).try_for_each(
                |((&(column, row), numerator), denominator)| {
                    shadow.write_advice(
                        column,
                        row,
                        AdviceValue::Rational {
                            numerator,
                            denominator,
                        },
                    )
                },
            )
        });

        let result = (|| {
            for (&(column, row), numerator) in cells.iter().zip(numerators) {
                self.claim_cell(column, row)?;
                self.columns[column][row] = numerator;
            }
            let [lambda_1, lambda_2, x] = cells.map(|(column, row)| dense_index(column, row));
            self.rationals.push(RationalEntry {
                denominator: z,
                uses: RationalUses::IncompleteDoubleAndAdd {
                    lambda_1,
                    lambda_2,
                    x,
                },
            });
            Ok(())
        })();
        #[cfg(test)]
        if let Some(shadow_result) = shadow_result {
            assert_eq!(
                result, shadow_result,
                "shared-denominator word write diverged from the shadow oracle at {cells:?}"
            );
        }
        result
    }

    pub(crate) fn write_region_advice(
        &mut self,
        row_map: &RowMap,
        column: usize,
        region: usize,
        local_row: usize,
        value: AdviceValue,
    ) -> Result<(), Error> {
        self.write_advice(column, row_map.absolute_row(region, local_row)?, value)
    }

    pub(super) fn finish(self) -> Result<NativeWitness, Error> {
        #[cfg(test)]
        let shadow_result = self.shadow.map(ShadowWriter::finish);

        let mut columns = self.columns;
        let result = finalize_rational_cells(self.execution, &mut columns, &self.rationals);

        #[cfg(test)]
        if let Some(shadow_result) = shadow_result {
            match (&shadow_result, &result) {
                (Ok(shadow_columns), Ok(())) => {
                    for (column, (shadow_column, dense_column)) in
                        shadow_columns.iter().zip(&columns).enumerate()
                    {
                        for (row, (shadow_value, dense_value)) in
                            shadow_column.iter().zip(dense_column).enumerate()
                        {
                            assert_eq!(
                                (shadow_value).reduce(),
                                (dense_value).reduce(),
                                "event finalize diverged from the shadow oracle at column {column}, row {row}"
                            );
                        }
                    }
                }
                (Err(shadow_error), Err(event_error)) => assert_eq!(
                    shadow_error, event_error,
                    "event finalize error diverged from the shadow oracle"
                ),
                _ => panic!(
                    "dense finalize diverged from the shadow oracle: shadow ok = {}, dense ok = {}",
                    shadow_result.is_ok(),
                    result.is_ok()
                ),
            }
        }

        result?;
        Ok(NativeWitness {
            columns,
            support: self.assigned,
        })
    }

    #[cfg(test)]
    pub(super) fn assignment_kind(&self, column: usize, row: usize) -> Option<AssignmentKind> {
        self.shadow
            .as_ref()
            .expect("assignment-kind introspection requires the shadow oracle")
            .kind(column, row)
    }
}

/// Prefix-product lanes in the rational finalize passes. Both passes are
/// serial multiplication chains (a few thousand entries per Action, see
/// [`RATIONAL_CAPACITY`]), so their cost is
/// multiplier latency, not throughput; interleaving four independent chains
/// recovers the pipeline while still spending a single field inversion.
const RATIONAL_LANES: usize = 4;

// Kernel shape, not a tuning knob: `finalize_rational_cells` combines the
// lane products pairwise and unfolds them in code written for exactly four
// lanes, so another value would silently break the recovery schedule.
const _: () = assert!(
    RATIONAL_LANES == 4,
    "the rational finalizer is a fixed four-lane kernel"
);

/// The dense cell index of `(column, row)`, as the rational log records it.
#[inline(always)]
fn dense_index(column: usize, row: usize) -> u32 {
    (column * N + row) as u32
}

/// Divides every deferred rational cell by its denominator with one field
/// inversion, in chronological write order. Zero denominators reject the
/// witness before any cell is modified, exactly like the former enum-cell
/// finalize pass.
///
/// # Policy, schedule, and scratch
///
/// **Zero-rejecting:** a zero denominator is an unsatisfiable witness
/// (`Error::UnsatisfiedWitness`), detected in the forward pass before any
/// event is touched, so a rejected witness leaves the log unmodified. This is
/// a different contract from the prover's zero-preserving batch inverter and
/// is deliberately not shared with it.
///
/// Four independent lanes take the denominators round-robin by write index
/// ([`RATIONAL_LANES`], a fixed kernel shape: the pairwise recovery below is
/// written for exactly four products). Each lane's exclusive prefix products
/// go to pooled scratch (one entry per rational); the four lane products
/// combine pairwise into one inversion, the pairwise unfold yields the four
/// lane inverses, and the backward pass
/// recovers each denominator's inverse as `lane_inverse · prefix` while
/// folding the denominator back into the lane. With no rationals the pass
/// leaves the columns untouched without inverting. Exact arithmetic: every
/// quotient equals the independent `numerator · denominator⁻¹`.
fn finalize_rational_cells(
    execution: crate::native::worker::Execution<'_>,
    columns: &mut [Buffer<Fp>],
    rationals: &[RationalEntry],
) -> Result<(), Error> {
    let mut products = [<Fp>::ONE; RATIONAL_LANES];
    let mut prefixes = execution.buffer(rationals.len(), false);
    for (index, entry) in rationals.iter().enumerate() {
        if entry.denominator.is_zero() {
            return Err(Error::UnsatisfiedWitness);
        }
        let lane = index % RATIONAL_LANES;
        prefixes[index] = products[lane];
        products[lane] = products[lane].mul(&entry.denominator);
    }
    if rationals.is_empty() {
        return Ok(());
    }

    let pair_low = products[0].mul(&products[1]);
    let pair_high = products[2].mul(&products[3]);
    let combined_inverse = pair_low
        .mul(&pair_high)
        .invert()
        .ok_or(Error::InternalInvariant)?;
    let inverse_low = combined_inverse.mul(&pair_high);
    let inverse_high = combined_inverse.mul(&pair_low);
    let mut inverses = [
        inverse_low.mul(&products[1]),
        inverse_low.mul(&products[0]),
        inverse_high.mul(&products[3]),
        inverse_high.mul(&products[2]),
    ];

    for (index, (entry, prefix)) in rationals.iter().zip(&prefixes).enumerate().rev() {
        let lane = index % RATIONAL_LANES;
        let denominator_inverse = inverses[lane].mul(prefix);
        inverses[lane] = inverses[lane].mul(&entry.denominator);
        let mut divide = |cell: u32, factor: &Fp| -> Result<(), Error> {
            let cell = cell as usize;
            let value = columns
                .get_mut(cell / N)
                .and_then(|column| column.get_mut(cell % N))
                .ok_or(Error::InternalInvariant)?;
            *value = value.mul(factor);
            Ok(())
        };
        match entry.uses {
            RationalUses::Single(event) => divide(event, &denominator_inverse)?,
            RationalUses::Pair { first, second } => {
                divide(first, &denominator_inverse)?;
                divide(second, &denominator_inverse)?;
            }
            RationalUses::IncompleteDoubleAndAdd {
                lambda_1,
                lambda_2,
                x,
            } => {
                divide(lambda_1, &denominator_inverse)?;
                divide(lambda_2, &denominator_inverse)?;
                divide(x, &denominator_inverse.square())?;
            }
        }
    }
    Ok(())
}

/// One finalized Action witness: the dense advice columns and their support.
///
/// The retained `support` mask is the writer's assignment bitmask above: the
/// authoritative support, independent of which assigned values happen to be
/// zero. Every unassigned cell holds zero, and `into_matrix` hands the mask to
/// the [`AdviceMatrix`] beside the dense columns, so a commitment path may
/// consult the support instead of scanning for zeros; it must still commit
/// every blinding row, which lies outside the support by contract.
pub(crate) struct NativeWitness {
    pub(super) columns: [Buffer<Fp>; ADVICE_COLUMNS],
    /// The writer's assignment bitmask: the structural support
    /// (`ASSIGNED_WORDS_PER_COLUMN` words per column, bit `row % 64` of word
    /// `row / 64`), carried to the advice matrix for the commitment paths.
    pub(super) support: [u64; ADVICE_COLUMNS * ASSIGNED_WORDS_PER_COLUMN],
}

impl NativeWitness {
    /// The dense advice matrix, carrying the assignment support beside it.
    pub(crate) fn into_matrix(self) -> Result<AdviceMatrix, Error> {
        AdviceMatrix::from_columns_with_support(self.columns, self.support)
    }

    #[cfg(test)]
    pub(super) fn support_bit(&self, column: usize, row: usize) -> bool {
        self.support[column * ASSIGNED_WORDS_PER_COLUMN + row / 64] & (1 << (row % 64)) != 0
    }
}
