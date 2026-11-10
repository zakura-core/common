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
// count bounds them all, and `usize::MAX` leaves an operation at the full
// pool budget. The minimum-work floors below still apply within a cap, so a
// small request never fans out merely because workers are available.
// A 16-core M-series sweep (2026-11-10) found no cap worth defaulting:
// proving and both verification phases were flat or improving through 16
// workers. Platforms whose optima differ (for example SMT machines) can cap
// an operation here without resizing the pool.
/// Task cap for the proof pipeline. Preparation and warmup keep the full pool.
pub(crate) const PROVING_TASK_CAP: usize = usize::MAX;
/// Task cap for verification proof folding.
pub(crate) const VERIFY_FOLD_TASK_CAP: usize = usize::MAX;
/// Task cap for the final verification equation's MSM.
pub(crate) const VERIFY_MSM_TASK_CAP: usize = usize::MAX;
/// Minimum Actions of proof-folding work per verification chunk before an
/// additional chunk is cut; a batch below one floor folds on the calling
/// thread without entering the pool's scheduler. Folding one two-Action proof
/// costs ~0.35 ms against ~50 µs of dispatch (M-series measurement), so the
/// floor stays low: it serializes only single-proof and all-single-Action
/// pairs, never a batch whose proofs each carry two or more Actions.
pub(crate) const VERIFY_FOLD_MIN_ACTIONS: usize = 2;
/// Minimum final-equation MSM terms per requested task. A small batch asks
/// for fewer workers instead of slicing its terms thinner; a one-proof batch
/// carries about 2,200 terms, so this floor requests roughly eight tasks for
/// it (the measured small-batch optimum; pending revalidation on x86_64).
pub(crate) const VERIFY_MSM_MIN_TERMS: usize = 256;

// Bounded idle verification scratch, retained across calls. Each verification
// call leases per-chunk equation scratch and one final-MSM workspace, and
// returns them — on success and on error — to process-wide pools holding at
// most SLOTS entries each. A returned item whose retained capacity exceeds
// its byte ceiling is dropped instead, so retained memory never exceeds
// SLOTS × MAX_BYTES per pool. Unwinding drops the active scratch. Concurrent
// calls beyond the slot counts allocate fresh scratch and discard it.
// Measured anchors (two-Action proofs): a 64-proof batch retains sixteen
// chunk equations of ≤0.7 MiB and a 25.8 MiB workspace; a 256-proof batch's
// workspace is 41.4 MiB, and only its merged combined equation exceeds the
// equation ceiling.
/// Idle equation-scratch entries; sized for one pool's worth of fold chunks.
pub(crate) const VERIFIER_EQUATION_SLOTS: usize = 16;
/// Per-entry retained-capacity ceiling for pooled equation scratch.
pub(crate) const VERIFIER_EQUATION_MAX_BYTES: usize = 4 << 20;
/// Idle final-MSM workspaces; one per concurrently verifying batch.
pub(crate) const VERIFIER_WORKSPACE_SLOTS: usize = 4;
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
