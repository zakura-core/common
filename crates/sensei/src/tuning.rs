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
/// Scratch is reused within a proving or verification call. Discard releases it
/// after success or failure; prepared data and workers remain alive. Allocators
/// may retain pages.
pub(crate) const WORKSPACE: WorkspaceRetention = WorkspaceRetention::Discard;

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
