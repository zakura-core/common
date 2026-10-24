//! Generator for the fixed-base window-table artifact.
//!
//! The table is a pure function of the pinned fixed bases, the frozen region
//! layout, and the pinned running-sum values — all circuit-description
//! source — so it is baked at build time through the same `sensei-shared`
//! construction the prover runs at load when the artifact is not embedded.
//! Precomputing it removes candidate-point construction and a Tonelli–Shanks
//! square root per window digit from process initialization.
//!
//! Each record holds Pallas `x`, `y`, and the chosen `u` with `u² = y + z`.
//! Windows are concatenated in the circuit's fixed-base schedule order,
//! with eight digit entries per window. Vesta commitment contributions for
//! those values are generated separately in `points::window_bases`.

use bento::bytes_of_slice;
use sensei_shared::{
    WindowTableEntry,
    fixed_bases::{
        FIXED_BASE_TOTAL_WINDOWS, FIXED_BASE_WINDOW_SIZE, build_fixed_base_window_tables,
    },
};

use crate::{Error, context::Context};

pub(crate) type WindowTables = Vec<[WindowTableEntry; FIXED_BASE_WINDOW_SIZE as usize]>;

/// Constructs the joint window entries used by the table and commitment encoders.
pub(crate) fn build() -> Result<WindowTables, Error> {
    let table = build_fixed_base_window_tables()
        .ok_or_else(|| Error::new("window-table construction failed on the pinned inputs"))?;
    if table.len() != FIXED_BASE_TOTAL_WINDOWS {
        return Err(Error::new("window table has unexpected dimensions"));
    }
    Ok(table)
}

/// Serializes the shared window entries without rebuilding their points or roots.
pub(crate) fn generate(context: &Context<'_>) -> Result<Vec<u8>, Error> {
    Ok(bytes_of_slice(context.window_tables()?).to_vec())
}
