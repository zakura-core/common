//! Fixed-base multiplication parameters, region schedule, and window tables.
//!
//! [`FixedBase`] selects a pinned generator and its per-window interpolation
//! parameters. [`FIXED_BASE_REGIONS`] lists the seven gadget instances in
//! window-table order. Region IDs are resolved through
//! [`crate::regions::REGION_STARTS`] to obtain absolute circuit rows.
//!
//! `windows.rs` contains the shared point construction; `z_values.rs` contains
//! the pinned parameter-search results. Both the host generator and the prover
//! use these definitions when constructing window tables at build time or
//! during prover preparation.

mod root_signs;
mod windows;
mod z_values;

use udon::curve::PallasAffine;

// Group the fixed-base generators here; all domain generators are defined
// together in the generators module.
pub use crate::generators::{
    COMMIT_IVK_M_GENERATOR, COMMIT_IVK_R_GENERATOR, MERKLE_CRH_M_GENERATOR,
    NOTE_COMMIT_M_GENERATOR, NOTE_COMMIT_R_GENERATOR, NULLIFIER_K_GENERATOR,
    SPEND_AUTH_G_GENERATOR, VALUE_COMMIT_R_GENERATOR, VALUE_COMMIT_V_GENERATOR,
};
pub use windows::{
    build_fixed_base_window_tables, fixed_base_window_candidates, fixed_window_bases,
};
use z_values::{
    COMMIT_IVK_R_Z, NOTE_COMMIT_R_Z, NULLIFIER_K_Z, SPEND_AUTH_G_Z, VALUE_COMMIT_R_Z,
    VALUE_COMMIT_V_Z,
};

/// Window width, in bits, of every fixed-base multiplication.
pub const FIXED_BASE_WINDOW_BITS: usize = 3;
/// Number of digit values per fixed-base window.
pub const FIXED_BASE_WINDOW_SIZE: u64 = 1 << FIXED_BASE_WINDOW_BITS;
/// Window count of a short (64-bit magnitude) fixed-base multiplication.
pub const SHORT_SCALAR_WINDOWS: usize = 22;
/// Window count of a full-width fixed-base multiplication.
pub const FULL_SCALAR_WINDOWS: usize = 85;
/// The fixed column holding each window's interpolation parameter `z`.
/// This parameter supplies `u² = y + z`; scalar running sums are advice values.
pub const FIXED_BASE_Z_COLUMN: usize = 11;

/// One of the pinned circuit's fixed multiplication bases.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FixedBase {
    /// The value-commitment value base.
    ValueCommitV,
    /// The value-commitment blinding base.
    ValueCommitR,
    /// The spend-authorization base.
    SpendAuthG,
    /// The commit-ivk blinding base.
    CommitIvkR,
    /// The nullifier base.
    NullifierK,
    /// The note-commitment blinding base.
    NoteCommitR,
}

impl FixedBase {
    /// The base's pinned generator point.
    pub const fn generator(self) -> PallasAffine {
        match self {
            Self::ValueCommitV => VALUE_COMMIT_V_GENERATOR,
            Self::ValueCommitR => VALUE_COMMIT_R_GENERATOR,
            Self::SpendAuthG => SPEND_AUTH_G_GENERATOR,
            Self::CommitIvkR => COMMIT_IVK_R_GENERATOR,
            Self::NullifierK => NULLIFIER_K_GENERATOR,
            Self::NoteCommitR => NOTE_COMMIT_R_GENERATOR,
        }
    }

    /// The pinned per-window interpolation parameters `z` of this base:
    /// search outputs of the original Orchard parameter generation, chosen so
    /// that for every candidate window point `(x, y)`, `y + z` is square (its
    /// root is the interpolation value `u`) and `z − y` is not. Table
    /// construction uses these values directly and returns `None` if a
    /// required square root is unavailable.
    pub const fn z_column(self) -> &'static [u64] {
        match self {
            Self::ValueCommitV => &VALUE_COMMIT_V_Z,
            Self::ValueCommitR => &VALUE_COMMIT_R_Z,
            Self::SpendAuthG => &SPEND_AUTH_G_Z,
            Self::CommitIvkR => &COMMIT_IVK_R_Z,
            Self::NullifierK => &NULLIFIER_K_Z,
            Self::NoteCommitR => &NOTE_COMMIT_R_Z,
        }
    }
}

/// `(region ID, fixed base, window count)` of each fixed-base multiplication.
///
/// The ID names the gadget's incomplete-addition region in
/// [`crate::regions::REGION_STARTS`]. Window `w` occupies absolute row
/// `REGION_STARTS[region] + w`. Entries follow the witness builder's gadget
/// order: value-commitment magnitude and blind, nullifier, spend authorization,
/// incoming viewing-key blind, then the old and new note-commitment blinds.
/// This is also the order of the flat window-table artifact.
pub const FIXED_BASE_REGIONS: [(usize, FixedBase, usize); 7] = [
    (266, FixedBase::ValueCommitV, SHORT_SCALAR_WINDOWS),
    (268, FixedBase::ValueCommitR, FULL_SCALAR_WINDOWS),
    (275, FixedBase::NullifierK, FULL_SCALAR_WINDOWS),
    (280, FixedBase::SpendAuthG, FULL_SCALAR_WINDOWS),
    (290, FixedBase::CommitIvkR, FULL_SCALAR_WINDOWS),
    (328, FixedBase::NoteCommitR, FULL_SCALAR_WINDOWS),
    (375, FixedBase::NoteCommitR, FULL_SCALAR_WINDOWS),
];

/// Total window count across every entry of [`FIXED_BASE_REGIONS`]: the row
/// count of the flat window table.
pub const FIXED_BASE_TOTAL_WINDOWS: usize = fixed_base_window_offset(FIXED_BASE_REGIONS.len());

/// Start of one [`FIXED_BASE_REGIONS`] slot's windows within the flat window
/// table (the prefix sum of the preceding slots' window counts).
///
/// `slot` indexes the seven-entry schedule, not the synthesis-region table.
/// Passing `FIXED_BASE_REGIONS.len()` returns the total window count.
///
/// # Panics
///
/// Panics if `slot > FIXED_BASE_REGIONS.len()`.
pub const fn fixed_base_window_offset(slot: usize) -> usize {
    let mut offset = 0;
    let mut index = 0;
    while index < slot {
        offset += FIXED_BASE_REGIONS[index].2;
        index += 1;
    }
    offset
}
