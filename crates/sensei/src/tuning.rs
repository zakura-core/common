//! Sensei's source-editable preparation and memory policy. Rebuild after editing.
//!
//! `Embed` adds read-only artifact pages to the executable. `WarmUp` computes
//! and retains the same payload on the heap. `OnDemand` retains no table and
//! computes its contributions while executing the operation. Payload sizes
//! below exclude allocator overhead, temporary work, and executable code.
//!
//! The build script and runtime read this same file. There are no caller or
//! environment overrides. Udon's `sqrt-table-large` is required in Cargo.toml
//! (about 58 KiB of additional static tables before linker elimination).
//!
//! SRS points, canonical circuit inputs, and structured window commitment
//! bases remain embedded. Sparse permutation schedules, copy classes, gate
//! active rows, and lookup suffix multiples (0.375 MiB) are prepared during
//! warmup. Embedded SRS records contain only `(x, y)`; warmup caches their
//! endomorphism coordinates. Commitment expansions have independent policies
//! below, with checked retained-memory ceilings.

// Both compilation contexts intentionally use only part of this inventory;
// alternatives also need to compile when no current setting selects them.
#![allow(dead_code)]

pub(crate) use sensei_shared::commitment_tables::Preparation;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OptionalPreparation {
    Embed,
    WarmUp,
    OnDemand,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum WorkspaceRetention {
    Discard,
    RetainOne,
}

/// 0.39 MiB; warmup otherwise reconstructs points and square roots.
pub(crate) const WINDOW_TABLES: Preparation = Preparation::Embed;
/// 1.81 MiB; warmup interpolates 29 fixed columns.
pub(crate) const FIXED_COEFFICIENTS: Preparation = Preparation::WarmUp;
/// 0.94 MiB; warmup interpolates 15 sigma columns.
pub(crate) const SIGMA_COEFFICIENTS: Preparation = Preparation::WarmUp;
/// 14.5 MiB; warmup expands fixed columns into residue-major cosets.
pub(crate) const FIXED_COSETS: Preparation = Preparation::WarmUp;
/// 7.5 MiB; warmup expands sigma columns into residue-major cosets.
pub(crate) const SIGMA_COSETS: Preparation = Preparation::WarmUp;
/// 25 MiB; on-demand preparation shares each row across all Actions.
pub(crate) const GATE_SELECTORS: OptionalPreparation = OptionalPreparation::WarmUp;
/// 1.5 MiB of forward/inverse twiddles and inverse finish scales.
pub(crate) const FFT_TABLES: OptionalPreparation = OptionalPreparation::WarmUp;
/// 0.94 MiB; independent of the FFT table choice.
pub(crate) const EXPANSION_SCALES: OptionalPreparation = OptionalPreparation::WarmUp;
/// 0.625 MiB of instance interpolation coefficients.
pub(crate) const INSTANCE_BASES: Preparation = Preparation::WarmUp;
/// 1.5 MiB of boundary cosets.
pub(crate) const BOUNDARIES: Preparation = Preparation::WarmUp;
/// Prover scratch is reused within one proving call. Discard releases it after
/// success or failure; prepared data and workers remain alive. Allocators may
/// retain pages. Verifier scratch has its own bounded retention policy below.
pub(crate) const WORKSPACE: WorkspaceRetention = WorkspaceRetention::Discard;

// Per-operation task budgets within the configured worker pool. Each
// operation requests at most its cap of concurrent tasks; the pool's worker
// count bounds them all. The minimum-work floors below still apply within a
// cap, so a small request never fans out merely because workers are
// available. A cap bounds one call's tasks, not the pool's threads:
// concurrent calls still overlap across the whole pool.
//
// Neither a 16-core M-series sweep nor a 16-core/32-thread Intel sweep (both
// 2026-11-10) found a cap worth defaulting. Capping folds, the final MSM, or
// proving at the Intel part's 16 physical cores inside its 32-worker pool was
// 20-60% slower than the full pool: the capped tasks land on SMT siblings
// while the pool's idle workers spin, so a smaller pool (`configure_workers`)
// is the only effective SMT lever, and work-shaped limits such as
// VERIFY_MSM_SLICE_POINTS are what let 32 workers match 16.
/// A per-operation task cap, resolved by the executor against its pool.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TaskCap {
    /// The full pool budget.
    Pool,
    /// An absolute task count; zero is treated as one.
    Fixed(usize),
}
/// Task cap for the proof pipeline. Preparation and warmup keep the full pool.
pub(crate) const PROVING_TASK_CAP: TaskCap = TaskCap::Pool;
/// Task cap for verification proof folding.
pub(crate) const VERIFY_FOLD_TASK_CAP: TaskCap = TaskCap::Pool;
/// Task cap for the final verification equation's MSM.
pub(crate) const VERIFY_MSM_TASK_CAP: TaskCap = TaskCap::Pool;
/// Final-equation transcript points per MSM input slice. The batch's
/// transcript commitments enter the final MSM as independent slices of at
/// least this many points (never more slices than the MSM task budget), so
/// their window tasks shorten with the batch instead of one input's window
/// count bounding the whole MSM's parallelism. Intel anchors (i9-7960X,
/// 64 two-Action proofs): as one Booth(11) input, the 4,928 points expose
/// twelve window tasks of about 2.6 ms, the MSM's critical path; four slices
/// cut the final MSM from 3.4 to 3.0 ms at 16 workers and from 4.5 to 2.8 ms
/// at 32, and shrink the retained workspace from 25.8 MiB to 6.6 MiB (12.3
/// MiB at 32 workers). Slicing a 16-proof batch's 1,232 points costs 4-9%,
/// so the floor sits above it.
pub(crate) const VERIFY_MSM_SLICE_POINTS: usize = 1024;
/// Minimum Actions of proof-folding work per verification chunk before an
/// additional chunk is cut; a batch below one floor folds on the calling
/// thread without entering the pool's scheduler. Folding one two-Action proof
/// costs ~0.35 ms against ~50 µs of dispatch (M-series measurement), so the
/// floor stays low: it serializes only single-proof and all-single-Action
/// pairs, never a batch whose proofs each carry two or more Actions.
pub(crate) const VERIFY_FOLD_MIN_ACTIONS: usize = 2;
/// Minimum final-equation MSM terms per requested task. A small batch asks
/// for fewer workers instead of slicing its terms thinner; a one-proof batch
/// carries about 2,200 terms, so this floor requests about sixteen tasks for
/// it on pools that large. Intel anchors (i9-7960X): sixteen tasks verify a
/// one-proof batch in 1.73 ms at 16 workers against 2.15 ms with eight
/// (the previous floor of 256 terms, the M-series small-batch optimum at
/// the time; pending revalidation there) and 3.1 ms with four; a 16-proof
/// batch gains 11% at 16 and 32 workers, and an 8-worker pool is unchanged.
pub(crate) const VERIFY_MSM_MIN_TERMS: usize = 128;

// Bounded idle verification scratch, retained across calls. Each verification
// call leases per-chunk equation scratch and one final-MSM workspace, and
// returns them — on success and on error — to process-wide pools whose slot
// counts the functions below derive from the pool's budgets. A returned item
// whose retained capacity exceeds its byte ceiling is dropped instead, so
// retained memory never exceeds slots × MAX_BYTES per pool (reported as
// `VerificationPlan::max_idle_bytes`). Unwinding drops the active scratch.
// Concurrent calls beyond the slot counts allocate fresh scratch and discard
// it, so a node's admission bound should not exceed the workspace slots.
// Measured anchors (two-Action proofs, sliced final MSM): a 64-proof batch
// retains fifteen chunk equations of about 0.14 MiB, a 0.7 MiB combined
// equation (the first chunk's, reserved once at the batch's size), and a
// 6.6 MiB workspace at 16 workers (31 chunks of about 0.1 MiB and 12.3 MiB
// at 32 workers); only a batch of more than about 420 proofs exceeds the
// equation ceiling with its combined equation.
/// Idle equation-scratch entries: two batches' worth of fold chunks at the
/// resolved fold budget, within this range, so one batch's chunks always
/// return to the pool and an overlapping second batch usually does.
pub(crate) const VERIFIER_EQUATION_SLOTS: core::ops::RangeInclusive<usize> = 16..=64;
pub(crate) fn verifier_equation_slots(fold_budget: usize) -> usize {
    (2 * fold_budget).clamp(
        *VERIFIER_EQUATION_SLOTS.start(),
        *VERIFIER_EQUATION_SLOTS.end(),
    )
}
/// Per-entry retained-capacity ceiling for pooled equation scratch.
pub(crate) const VERIFIER_EQUATION_MAX_BYTES: usize = 4 << 20;
/// Idle final-MSM workspaces: the concurrently verifying batches the pools
/// serve without allocating one, one slot per
/// `VERIFIER_WORKSPACE_WORKERS_PER_SLOT` workers within this range.
/// `warm_up_verifier_scratch` reports the result as admission control's
/// upper bound, not a target: the last slots buy little. Intel anchors
/// (i9-7960X, 64 two-Action proofs, proofs only): against one batch at a
/// time, 2 / 4 / 8 in-flight batches verify about 16% / 28% / 30% more
/// proofs per second on 32 workers, 9% / 15% / 16% more on 16 workers
/// (whose peak resident memory nearly triples from four to eight, past its
/// slots), and 3% / 7% / 7% more on 8 workers.
pub(crate) const VERIFIER_WORKSPACE_SLOTS: core::ops::RangeInclusive<usize> = 4..=8;
pub(crate) const VERIFIER_WORKSPACE_WORKERS_PER_SLOT: usize = 4;
pub(crate) fn verifier_workspace_slots(workers: usize) -> usize {
    (workers / VERIFIER_WORKSPACE_WORKERS_PER_SLOT).clamp(
        *VERIFIER_WORKSPACE_SLOTS.start(),
        *VERIFIER_WORKSPACE_SLOTS.end(),
    )
}
/// Per-entry retained-capacity ceiling for pooled final-MSM workspaces.
pub(crate) const VERIFIER_WORKSPACE_MAX_BYTES: usize = 48 << 20;

// Shared SRS acceleration: both roles use these tables and preparation policies.
// The SRS/prover expansions have explicit memory ceilings in COMMITMENT_TABLES.
use sensei_shared::commitment_tables::{BankPolicy, Config, FixedPolicy, FoldingPolicy, SrsTable};
pub(crate) const COEFFICIENT_TABLE: SrsTable = SrsTable::Alpha6;
pub(crate) const LAGRANGE_TABLE: SrsTable = SrsTable::None;
pub(crate) const COEFFICIENT_PREPARATION: Preparation = Preparation::WarmUp;
pub(crate) const LAGRANGE_PREPARATION: Preparation = Preparation::WarmUp;
/// The verifier's 77 distinct fixed/sigma commitments are prepared separately at runtime.
/// Equal-width SRS and VK banks share their residue codebook.
pub(crate) const VERIFIER_FIXED_ALPHA_WIDTH: u8 = 6;
const _: () = assert!(VERIFIER_FIXED_ALPHA_WIDTH >= 5 && VERIFIER_FIXED_ALPHA_WIDTH <= 7);
pub(crate) const FIXED_WIDTHS: [u32; 4] = [8, 8, 4, 4]; // W, U, G₀, H.
pub(crate) const FIXED_PREPARATION: [Preparation; 4] = [Preparation::WarmUp; 4];
pub(crate) const SPARSE_MASK: bool = true;
pub(crate) const SPARSE_MASK_WIDTH: u32 = 4;
pub(crate) const SPARSE_MASK_PREPARATION: Preparation = Preparation::WarmUp;
/// The verifier's doubling-free instance commitment bank: ten Lagrange
/// generators at width 4 cost about 245 KiB, prepared at warmup outside the
/// embedded-section layout (and outside COMMITMENT_TABLES' byte accounting).
pub(crate) const INSTANCE_FIXED_WIDTH: u32 = 4;
pub(crate) const JOINT_FIXED_SUM: bool = false;
/// Reuses coefficient α6 odd layers; zero disables the shared wNAF fold.
pub(crate) const IPA_FOLDING_WIDTH: u8 = 6;
pub(crate) const IPA_FOLDING_REUSE_ALPHA: bool = true;
pub(crate) const IPA_FOLDING_PREPARATION: Preparation = Preparation::WarmUp;
pub(crate) const IPA_FOLD_ENDS: [usize; 3] = [3, 6, 11]; // Candidates [4, 7, 11], [4, 8, 11].
pub(crate) const IPA_COMPACT_FOLDED: bool = true;
pub(crate) const COMMITMENT_TABLES: Config = Config {
    srs: [
        BankPolicy {
            table: COEFFICIENT_TABLE,
            preparation: COEFFICIENT_PREPARATION,
            max_bytes: 16 << 20,
        },
        BankPolicy {
            table: LAGRANGE_TABLE,
            preparation: LAGRANGE_PREPARATION,
            max_bytes: 16 << 20,
        },
    ],
    fixed: [
        FixedPolicy {
            width: FIXED_WIDTHS[0],
            preparation: FIXED_PREPARATION[0],
        },
        FixedPolicy {
            width: FIXED_WIDTHS[1],
            preparation: FIXED_PREPARATION[1],
        },
        FixedPolicy {
            width: FIXED_WIDTHS[2],
            preparation: FIXED_PREPARATION[2],
        },
        FixedPolicy {
            width: FIXED_WIDTHS[3],
            preparation: FIXED_PREPARATION[3],
        },
    ],
    sparse: if SPARSE_MASK {
        Some(FixedPolicy {
            width: SPARSE_MASK_WIDTH,
            preparation: SPARSE_MASK_PREPARATION,
        })
    } else {
        None
    },
    folding: if IPA_FOLDING_WIDTH == 0 {
        None
    } else {
        Some(FoldingPolicy {
            width: IPA_FOLDING_WIDTH,
            reuse_alpha: IPA_FOLDING_REUSE_ALPHA,
            preparation: IPA_FOLDING_PREPARATION,
        })
    },
    max_bytes: 32 << 20,
};
const _: () = COMMITMENT_TABLES.validate();
