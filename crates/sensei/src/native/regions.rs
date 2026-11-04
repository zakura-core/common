//! Witness region roles and public-input order owned by the prover.

use sensei_shared::regions::FROZEN_REGION_COUNT;
pub(crate) use sensei_shared::regions::REGION_STARTS;

/// The frozen schedule of the circuit's Sinsemilla hashes, shared by the
/// witness writer (`write_sinsemilla_hash` and its callers) and the advice
/// commitment path that transposes each hash's running sums onto weighted
/// generators: both derive rows, columns, and piece widths from these
/// constants, so the writer and the committer agree by construction.
pub mod sinsemilla_hashes;

/// The fixed-base multiplication gadgets' window footprint, shared by the
/// writer (`write_fixed_incomplete_region`) and the advice commitment path
/// that replaces each window's `x` cell with a selected precomputed point:
/// window `w` of a region in `FIXED_BASE_REGIONS` sits at local row `w`, with
/// its selected `(x, y, u)` in columns `X_COLUMN`, `Y_COLUMN`, `U_COLUMN` and
/// its scalar cell in `SCALAR_COLUMN`.
pub mod fixed_base_windows {
    use alloc::vec::Vec;
    use sensei_shared::fixed_bases::{FIXED_BASE_REGIONS, FIXED_BASE_TOTAL_WINDOWS};

    use super::REGION_STARTS;

    /// The advice column of each window's selected `x`.
    pub const X_COLUMN: usize = 0;
    /// The advice column of each window's selected `y`.
    pub const Y_COLUMN: usize = 1;
    /// The advice column of each window's scalar (digit or running sum).
    pub const SCALAR_COLUMN: usize = 4;
    /// The advice column of each window's interpolation value `u`.
    pub const U_COLUMN: usize = 5;

    /// Every window's absolute row, flat in `FIXED_BASE_REGIONS` order (the
    /// order of the flat window table and the `x`-base artifact).
    pub fn window_rows() -> Vec<usize> {
        let mut rows = Vec::with_capacity(FIXED_BASE_TOTAL_WINDOWS);
        for (region, _, window_count) in FIXED_BASE_REGIONS {
            let start = REGION_STARTS[region];
            rows.extend(start..start + window_count);
        }
        debug_assert_eq!(rows.len(), FIXED_BASE_TOTAL_WINDOWS);
        rows
    }
}

/// The running-sum streams of the short and base-field fixed-base
/// multipliers, shared by their writers (`write_short_fixed_mul`,
/// `write_base_field_fixed_mul`) and the advice commitment path that
/// transposes them onto three-bit word bases: each stream writes
/// `W + 1` running sums `z_0..z_W` (the final cell a strict zero) into
/// `fixed_base_windows::SCALAR_COLUMN` at local rows `0..=W` of its
/// window region. The five full multipliers write digits there instead and
/// are not streams.
pub mod fixed_base_running_sums {
    use alloc::vec::Vec;
    use core::ops::Range;

    use sensei_shared::fixed_bases::{
        FIXED_BASE_WINDOW_BITS, FULL_SCALAR_WINDOWS, SHORT_SCALAR_WINDOWS,
    };

    use super::{REGION_STARTS, fixed_base_windows::SCALAR_COLUMN, roles};

    /// Bits per running-sum word (one fixed-base window).
    pub const WORD_BITS: usize = FIXED_BASE_WINDOW_BITS;
    /// `(window region, window count)` of every running-sum stream: the
    /// `[v] ValueCommitV` short multiplier and the `[nk] NullifierK`
    /// base-field multiplier.
    pub const STREAMS: [(usize, usize); 2] = [
        (roles::VALUE_COMMIT_V.0, SHORT_SCALAR_WINDOWS),
        (275, FULL_SCALAR_WINDOWS),
    ];
    /// Streams per Action.
    pub const PIECE_COUNT: usize = STREAMS.len();
    /// Running-sum cells per Action across both streams.
    pub const WORD_COUNT: usize = STREAMS[0].1 + 1 + STREAMS[1].1 + 1;

    /// Whether `(region, windows)` is one of the scheduled streams.
    pub fn is_stream(region: usize, windows: usize) -> bool {
        STREAMS.contains(&(region, windows))
    }

    /// Every stream as `(column, absolute rows of `z_0..z_W`)`.
    pub fn pieces() -> Vec<(usize, Range<usize>)> {
        STREAMS
            .iter()
            .map(|&(region, windows)| {
                let start = REGION_STARTS[region];
                (SCALAR_COLUMN, start..start + windows + 1)
            })
            .collect()
    }
}

/// The ten-bit range-check and canonicity running-sum streams written by
/// `write_running_sum` through its scheduled wrapper, shared with the advice
/// commitment path that transposes them onto ten-bit word bases: each
/// stream writes `n + 1` cells `z_0..z_n` into column `COLUMN` at local rows
/// `0..=n` of its region, `z_n` being the final sum (a strict zero for the
/// two 25-word streams, an arbitrary quotient otherwise; the transform
/// carries it exactly as a remainder term).
pub mod range_running_sums;

/// The advice cells the writer assigns the same nonzero constant on every
/// valid witness, derived from the writer's own expressions: the
/// cross-address relation rows' ones, the Poseidon initial-state `2^65`
/// cells, the Merkle layer numbers, the short-range-check inverses `2^-b`,
/// and the Sinsemilla initial `x` coordinates. Zero constants are omitted:
/// a zero cell already costs the commitment nothing. The advice commitment
/// replaces each column's constant cells by one precomputed offset point.
pub mod constant_cells;

/// The variable-base scalar multiplication gadget's frozen footprint, shared
/// by its writer (`write_variable_base_mul`) and the advice commitment path
/// that folds its repeated input coordinates: both derive the same rows from
/// these constants, so the writer and the committer agree by construction
/// rather than by census.
pub mod variable_base_mul;

/// Semantic roles of the regions the prover's witness orchestration addresses
/// directly, by frozen region number.
///
/// These name *which* region a value lands in; a region's row and column
/// footprint is a property of the gadget that writes it and is pinned from
/// the actual assignments (the prover's `witness_layout_footprints` test),
/// never inferred from the next region's start — starts alone do not make
/// regions disjoint or contiguous. Gadgets with many regions (Sinsemilla,
/// Merkle layers, the ECC chains) are addressed through their own schedules
/// and are not listed here.
pub mod roles {

    /// Top-level inputs, one region each: the value sits at local row 0
    /// (column 0 for a scalar; columns 0 and 1 for a point's `x`, `y`).
    pub const PSI_OLD: usize = 0;
    /// See [`PSI_OLD`].
    pub const RHO_OLD: usize = 1;
    /// See [`PSI_OLD`] (point).
    pub const CM_OLD: usize = 2;
    /// See [`PSI_OLD`] (point).
    pub const G_D_OLD: usize = 3;
    /// See [`PSI_OLD`] (point).
    pub const AK: usize = 4;
    /// See [`PSI_OLD`].
    pub const NK: usize = 5;
    /// See [`PSI_OLD`].
    pub const V_OLD: usize = 6;
    /// See [`PSI_OLD`].
    pub const V_NEW: usize = 7;

    /// Value commitment group: the signed value's magnitude and sign (column
    /// 9, local row 0 of each), then the two fixed-base multiplication region
    /// pairs (`[v] ValueCommitV`, `[rcv] ValueCommitR`).
    pub const VALUE_MAGNITUDE: usize = 264;
    /// See [`VALUE_MAGNITUDE`].
    pub const VALUE_SIGN: usize = 265;
    /// See [`VALUE_MAGNITUDE`]: `(windows region, running-sum region)`.
    pub const VALUE_COMMIT_V: (usize, usize) = (266, 267);
    /// See [`VALUE_MAGNITUDE`]: `(windows region, running-sum region)`.
    pub const VALUE_COMMIT_R: (usize, usize) = (268, 269);
    /// The complete addition of the value and blinding terms into `cv_net`.
    pub const VALUE_COMMIT_ADDITION: usize = 270;
    /// The `[alpha] SpendAuthG` multiplication: `(windows, final addition)`.
    pub const SPEND_AUTH_G: (usize, usize) = (280, 281);
    /// The complete addition of `[alpha] SpendAuthG` and `ak` into `rk`.
    pub const RK_ADDITION: usize = 282;
    /// The `[rivk] CommitIvkR` fixed-base multiplication region pair.
    pub const COMMIT_IVK_R: (usize, usize) = (290, 291);
    /// The complete addition of the `commit_ivk` hash and its blinding term.
    pub const COMMIT_IVK_ADDITION: usize = 293;
    /// The old note's `pk_d` point (columns 0 and 1, local row 0).
    pub const PK_D_OLD: usize = 301;
    /// The first region of the old note's message decomposition.
    pub const NOTE_DECOMPOSITION_OLD: usize = 303;
    /// The old note's `[rcm] NoteCommitR`: `(windows, final addition)`.
    pub const NOTE_COMMIT_R_OLD: (usize, usize) = (328, 329);
    /// The complete addition of the old note's hash and blinding term.
    pub const NOTE_COMMIT_ADDITION_OLD: usize = 331;
    /// The new note's `g_d` point (columns 0 and 1, local row 0).
    pub const G_D_NEW: usize = 347;
    /// The new note's `pk_d` point (columns 0 and 1, local row 0).
    pub const PK_D_NEW: usize = 348;
    /// The new note's `psi` (column 0, local row 0).
    pub const PSI_NEW: usize = 349;
    /// The first region of the new note's message decomposition.
    pub const NOTE_DECOMPOSITION_NEW: usize = 350;
    /// The new note's `[rcm] NoteCommitR`: `(windows, final addition)`.
    pub const NOTE_COMMIT_R_NEW: (usize, usize) = (375, 376);
    /// The complete addition of the new note's hash and blinding term.
    pub const NOTE_COMMIT_ADDITION_NEW: usize = 378;

    /// The statement row: one row whose columns 0..8 hold `v_old`, `v_new`,
    /// the value magnitude and sign, the Merkle root, and the public
    /// `anchor`, `enable_spend`, and `enable_output` (columns 0 through 7).
    pub const STATEMENT_ROW: usize = 393;
    /// The cross-address rows: four rows (old/new `g_d` and `pk_d`
    /// coordinates) across all ten columns, gated by
    /// `disable_cross_address`.
    pub const CROSS_ADDRESS_ROWS: usize = 394;
}

/// Positions of the public inputs in the instance column: the order the
/// public statement encodes them and the prover binds them.
pub(crate) use crate::public_input;

const _: () = {
    use roles::*;
    let listed = [
        PSI_OLD,
        RHO_OLD,
        CM_OLD,
        G_D_OLD,
        AK,
        NK,
        V_OLD,
        V_NEW,
        VALUE_MAGNITUDE,
        VALUE_SIGN,
        VALUE_COMMIT_V.0,
        VALUE_COMMIT_V.1,
        VALUE_COMMIT_R.0,
        VALUE_COMMIT_R.1,
        VALUE_COMMIT_ADDITION,
        SPEND_AUTH_G.0,
        SPEND_AUTH_G.1,
        RK_ADDITION,
        COMMIT_IVK_R.0,
        COMMIT_IVK_R.1,
        COMMIT_IVK_ADDITION,
        PK_D_OLD,
        NOTE_DECOMPOSITION_OLD,
        NOTE_COMMIT_R_OLD.0,
        NOTE_COMMIT_R_OLD.1,
        NOTE_COMMIT_ADDITION_OLD,
        G_D_NEW,
        PK_D_NEW,
        PSI_NEW,
        NOTE_DECOMPOSITION_NEW,
        NOTE_COMMIT_R_NEW.0,
        NOTE_COMMIT_R_NEW.1,
        NOTE_COMMIT_ADDITION_NEW,
        STATEMENT_ROW,
        CROSS_ADDRESS_ROWS,
    ];
    let mut index = 0;
    while index < listed.len() {
        assert!(listed[index] < FROZEN_REGION_COUNT);
        index += 1;
    }
    assert!(CROSS_ADDRESS_ROWS == FROZEN_REGION_COUNT - 1);
};
