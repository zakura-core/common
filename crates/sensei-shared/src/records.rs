//! The shared `Pod` record types of the embedded prover data.
//!
//! These types are the single description of each stored layout: the
//! host-side generators in `sensei-artifacts` construct values of them and serialize
//! with `bento::bytes_of`, and the prover embeds the resulting files and
//! reads them back zero-copy as the same types. Defining them below both
//! sides is what keeps the write and read views from ever drifting apart.
//! The `bento::Pod` derive supplies the implementations and the
//! compile-time no-padding proofs.
//!
//! Field-element-bearing records are stamped per stored form
//! (`udon::STORED_FORM`) from a field list written once, so a second at-rest
//! representation reuses the structure — fields, order, meaning — and differs
//! only in its element layouts. The one registered form today is
//! `mont-u64x4`, stamped over `udon`'s concrete point types; their layouts
//! are fixed in every compilation (a `bento::Pod` obligation), which is what
//! makes host-side generation of the stored bytes valid for any target using
//! this form.
//!
//! Keep field order, element types, and array lengths identical on the write
//! and read sides. These records describe implementation-owned artifacts, not
//! proof encodings or a general serialization format. `Pod` establishes the
//! memory-layout contract; generator validation and embedded-data digest tests
//! establish the meaning of the stored values.

use udon::curve::{PallasAffine, VestaAffine};

use crate::{N, generators::SINSEMILLA_TABLE_ROWS};

/// Sinsemilla generators stored independently of circuit dimensions and the SRS.
///
/// Uses [`PallasAffine`]'s in-memory Montgomery representation, not compressed
/// point encodings. This record provides a fixed layout; neither construction
/// through its public field nor [`bento::Pod`] embedding validates that the
/// points are the prescribed generators. Artifact producers establish that
/// invariant before storage.
#[repr(C)]
#[derive(Clone, Copy, bento::Pod)]
pub struct PrimitivePointsFile {
    /// The canonical Sinsemilla generator table, in message-word order.
    pub sinsemilla_generators: [PallasAffine; SINSEMILLA_TABLE_ROWS],
}

/// Proof commitment points shared by prover and verifier preparation.
///
/// Uses [`VestaAffine`]'s in-memory Montgomery representation. Array lengths
/// follow [`N`], the circuit domain size. Producers must supply the matching
/// SRS bases, their derived prefix sums, and the protocol's auxiliary points;
/// this record and [`bento::Pod`] embedding do not validate those relationships.
#[repr(C)]
#[derive(Clone, Copy, bento::Pod)]
pub struct SrsPointsFile {
    /// Coefficient-basis SRS generators.
    pub coefficient_bases: [VestaAffine; N],
    /// Lagrange-basis SRS generators.
    pub lagrange_bases: [VestaAffine; N],
    /// Prefix sums of `lagrange_bases`, then individual boundary/tail bases.
    ///
    /// At index `j - 1`, stores the sum of bases at indices `0..j` for
    /// `j` in `1..=crate::USABLE_ROWS_END`. Remaining indices store the original
    /// bases, starting at the boundary row [`crate::USABLE_ROWS_END`]. Every
    /// prefix must be nonidentity to admit this affine representation.
    pub lagrange_prefix_sums: [VestaAffine; N],
    /// Commitment blinding generator.
    pub blind_generator: VestaAffine,
    /// IPA auxiliary generator.
    pub ipa_generator: VestaAffine,
}

/// Fixed and permutation commitments in each supported Orchard verifying key.
pub const VK_COLUMN_COUNT: usize = crate::FIXED_COLUMNS + crate::PERMUTATION_COLUMN_COUNT;
/// Distinct commitments across the three pinned keys: 44 current, 30 NU6.2,
/// and three additional pre-NU6.2 permutation commitments.
pub const VERIFIER_POINT_COUNT: usize = 77;
/// Number of pinned circuit versions, in current, NU6.2, pre-NU6.2 order.
pub const VERIFIER_VERSION_COUNT: usize = 3;

/// Shared verifier point bank and each key's column-to-bank mapping.
///
/// Current-key points come first, retaining a contiguous current-only MSM.
/// Indices are `u32` for Udon's indexed MSM interface and a padding-free layout.
#[repr(C)]
#[derive(Clone, Copy, bento::Pod)]
pub struct VerifierCommitments {
    /// Each distinct default-blinded fixed or permutation commitment, once.
    pub points: [VestaAffine; VERIFIER_POINT_COUNT],
    /// Fixed columns followed by permutation columns for each key. Version
    /// order is post-NU6.3, fixed post-NU6.2, insecure pre-NU6.2.
    pub columns: [[u32; VK_COLUMN_COUNT]; VERIFIER_VERSION_COUNT],
}

/// Declares the fixed-base window-table entry record over one stored form's
/// field type; the field list lives only here, as in
/// `prepared_points_record!`.
macro_rules! window_table_record {
    (
        $(#[$attribute:meta])*
        $name:ident { field: $field:ty, }
    ) => {
        $(#[$attribute])*
        #[repr(C)]
        #[derive(Clone, Copy, bento::Pod)]
        pub struct $name {
            /// The window point's x coordinate.
            pub x: $field,
            /// The window point's y coordinate.
            pub y: $field,
            /// The interpolation witness `u = sqrt(y + z)` for the
            /// window's pinned interpolation parameter `z`.
            pub u: $field,
        }
    };
}

window_table_record! {
    /// One digit entry of a fixed-base window table, stored in the
    /// `mont-u64x4` in-memory Montgomery-limb representation so consuming it
    /// performs no field or curve arithmetic.
    ///
    /// Tables contain eight entries per window, ordered by digit; windows
    /// follow [`crate::fixed_bases::FIXED_BASE_REGIONS`] and each region's
    /// local window order.
    WindowTableEntry { field: udon::field::Fp, }
}

/// One sparse fixed-tuple assignment: tuple `tuple` fills the tuple
/// columns at row `row`. Representation-invariant: no field elements,
/// so no per-form stamping.
#[repr(C)]
#[derive(Clone, Copy, bento::Pod)]
pub struct RowAssignment {
    /// The absolute row the tuple is copied into, less than [`N`].
    pub row: u16,
    /// The dictionary index, less than [`crate::fixed_columns::FIXED_TUPLE_COUNT`].
    pub tuple: u16,
}

/// Declares the prepared-points record over one stored form's point types.
///
/// The field list lives only here; each stored form stamps it over its own
/// prepared point types, so two forms' records cannot drift structurally.
macro_rules! prepared_points_record {
    (
        $(#[$attribute:meta])*
        $name:ident {
            msm_base: $msm_base:ty,
            pallas_affine: $pallas_affine:ty,
            vesta_affine: $vesta_affine:ty,
        }
    ) => {
        $(#[$attribute])*
        #[repr(C)]
        #[derive(Clone, Copy, bento::Pod)]
        pub struct $name {
            /// Coefficient-basis SRS generators as affine points.
            pub coefficient_bases: [$msm_base; N],
            /// Lagrange-basis SRS generators as affine points.
            pub lagrange_bases: [$msm_base; N],
            /// The prefix and boundary/tail layout of
            /// [`SrsPointsFile::lagrange_prefix_sums`].
            pub lagrange_prefix_sums: [$msm_base; N],
            /// Sinsemilla lookup generators.
            pub sinsemilla_generators: [$pallas_affine; SINSEMILLA_TABLE_ROWS],
            /// Commitment blinding generator.
            pub blind_generator: $vesta_affine,
            /// IPA auxiliary generator.
            pub ipa_generator: $vesta_affine,
        }
    };
}

prepared_points_record! {
    /// Combined SRS and Sinsemilla affine point sets in `mont-u64x4` storage.
    ///
    /// Combines the contents of [`SrsPointsFile`] and [`PrimitivePointsFile`]
    /// in one record. Their representation and validation requirements apply
    /// here too. Consumers needing only one set can use the separate records.
    PreparedPointsFile {
        msm_base: VestaAffine,
        pallas_affine: PallasAffine,
        vesta_affine: VestaAffine,
    }
}
