//! Lazy preparation shared by the encoders in one emission.
//!
//! A standalone encoder gets a fresh context. Nothing survives an emission,
//! so another call observes changed raw inputs and releases all preparation.

use std::cell::OnceCell;

use sensei_shared::{N, fixed_columns::SINSEMILLA_TABLE_ROWS};
use udon::{
    curve::{PallasAffine, VestaAffine},
    field::Fp,
};

use crate::{
    Error, RawStore,
    fixed_base_tables::{self, WindowTables},
    fixed_columns::{self, SparseFixedRows},
    points::{self, window_bases::WindowMultipliers},
    polynomials::{coefficients, cosets, values},
    raw::{
        permutation,
        points::{COEFFICIENT_BASES, SINSEMILLA_GENERATORS, decode_points},
    },
};

type PreparationCache<T> = OnceCell<Result<T, Error>>;

/// Lazy preparation shared by the enabled encoders in one emission.
///
/// Each accessor retains its first returned `Result` in a `OnceCell`: successes
/// and failures remain until this context is dropped. A failed access returns
/// a new [`Error`] with the cached message without retrying preparation.
/// [`crate::emit_generated_with_commitment_tables`] shares one context across
/// enabled entries; each standalone [`crate::Artifact::generate`] call creates
/// a fresh context. [`RawStore`] itself does not cache reads.
///
/// The table names the caches each encoder requests; their upstream work is
/// shared through these chains (arrows run from prerequisite to derived cache):
///
/// - Raw SRS → `coefficient_bases` → `lagrange_bases` → `window_multipliers`
///   (prepared advice-row points for all three coordinate families).
/// - Raw Sinsemilla points → `sinsemilla_generators`; these plus `sparse_rows`
///   → `fixed_coefficients` → `fixed_cosets`.
/// - Raw permutation cells → `sigma_map` → `sigma_coefficients` → `sigma_cosets`.
/// - `sparse_rows` uses source window-row and constant recipes; `window_tables`
///   independently builds the joint x/y/u entries. Sparse rows do not request
///   the `window_tables` cache.
///
/// | Encoder ([`ArtifactId`](crate::ArtifactId)) | Requested caches |
/// | --- | --- |
/// | `PrimitivePoints` | [`sinsemilla_generators`](Self::sinsemilla_generators()) |
/// | `SrsPoints` | [`coefficient_bases`](Self::coefficient_bases()), [`lagrange_bases`](Self::lagrange_bases()) |
/// | `CommitmentTables` | None when `embedded_entries() == 0`; otherwise the same caches as `SrsPoints` |
/// | `Points` | `coefficient_bases`, `lagrange_bases`, `sinsemilla_generators` |
/// | `VerifierCommitments` | `coefficient_bases`, `fixed_coefficients`, `sigma_coefficients` |
/// | `FixedCoefficients` | [`fixed_coefficients`](Self::fixed_coefficients()) |
/// | `SigmaCoefficients` | [`sigma_coefficients`](Self::sigma_coefficients()) |
/// | `FixedCosets`, `GateSelectors` | [`fixed_cosets`](Self::fixed_cosets()) |
/// | `SigmaCosets` | [`sigma_cosets`](Self::sigma_cosets()) |
/// | `WindowTables` | [`window_tables`](Self::window_tables()) |
/// | `FixedWindow{X,Y,U}Bases` | `window_tables`, [`window_multipliers`](Self::window_multipliers()) |
/// | `FixedTuples`, `TupleAssignments` | [`sparse_rows`](Self::sparse_rows()) |
/// | `SigmaMap` | [`sigma_map`](Self::sigma_map()) |
/// | `InstanceBases`, `Boundaries` | None; these polynomial-basis encoders ignore the context |
/// | `FftTables`, `ExpansionScales` | None; these encoders ignore the context |
///
/// Only the named caches are retained. Dense fixed/sigma evaluations are
/// temporary inputs to coefficient preparation. SRS prefix sums are rebuilt by
/// `SrsPoints`, `Points`, and nonempty `CommitmentTables`; current verifier
/// commitments and decoded historical keys are local to `VerifierCommitments`.
/// Final x/y/u products, selectors, expanded commitment tables, and encoded
/// bytes are also built per encoder, so their failures are not context-cached.
pub(crate) struct Context<'a> {
    pub(crate) raw: &'a RawStore,
    pub(crate) commitment_tables: sensei_shared::commitment_tables::Config,
    coefficient_bases: PreparationCache<Vec<VestaAffine>>,
    lagrange_bases: PreparationCache<Vec<VestaAffine>>,
    sinsemilla_generators: PreparationCache<Vec<PallasAffine>>,
    sigma_map: PreparationCache<Vec<[u16; N]>>,
    window_tables: PreparationCache<WindowTables>,
    window_multipliers: PreparationCache<WindowMultipliers>,
    sparse_rows: PreparationCache<SparseFixedRows>,
    fixed_coefficients: PreparationCache<Vec<[Fp; N]>>,
    sigma_coefficients: PreparationCache<Vec<[Fp; N]>>,
    fixed_cosets: PreparationCache<Vec<Vec<Fp>>>,
    sigma_cosets: PreparationCache<Vec<Vec<Fp>>>,
}

fn prepared<T>(
    cell: &PreparationCache<T>,
    build: impl FnOnce() -> Result<T, Error>,
) -> Result<&T, Error> {
    cell.get_or_init(build)
        .as_ref()
        .map_err(|error| Error::new(error.to_string()))
}

impl<'a> Context<'a> {
    pub(crate) fn new(raw: &'a RawStore) -> Self {
        Self::with_commitment_tables(raw, sensei_shared::commitment_tables::DEFAULT)
    }

    pub(crate) fn with_commitment_tables(
        raw: &'a RawStore,
        commitment_tables: sensei_shared::commitment_tables::Config,
    ) -> Self {
        Self {
            raw,
            commitment_tables,
            coefficient_bases: OnceCell::new(),
            lagrange_bases: OnceCell::new(),
            sinsemilla_generators: OnceCell::new(),
            sigma_map: OnceCell::new(),
            window_tables: OnceCell::new(),
            window_multipliers: OnceCell::new(),
            sparse_rows: OnceCell::new(),
            fixed_coefficients: OnceCell::new(),
            sigma_coefficients: OnceCell::new(),
            fixed_cosets: OnceCell::new(),
            sigma_cosets: OnceCell::new(),
        }
    }

    pub(crate) fn coefficient_bases(&self) -> Result<&[VestaAffine], Error> {
        prepared(&self.coefficient_bases, || {
            decode_points(self.raw, COEFFICIENT_BASES, N)
        })
        .map(Vec::as_slice)
    }

    pub(crate) fn lagrange_bases(&self) -> Result<&[VestaAffine], Error> {
        prepared(&self.lagrange_bases, || {
            points::srs::lagrange_srs(self.coefficient_bases()?)
        })
        .map(Vec::as_slice)
    }

    pub(crate) fn window_tables(&self) -> Result<&WindowTables, Error> {
        prepared(&self.window_tables, fixed_base_tables::build)
    }

    pub(crate) fn sinsemilla_generators(&self) -> Result<&[PallasAffine], Error> {
        prepared(&self.sinsemilla_generators, || {
            decode_points(self.raw, SINSEMILLA_GENERATORS, SINSEMILLA_TABLE_ROWS)
        })
        .map(Vec::as_slice)
    }

    pub(crate) fn sigma_map(&self) -> Result<&[[u16; N]], Error> {
        prepared(&self.sigma_map, || permutation::sigma_map(self.raw)).map(Vec::as_slice)
    }

    pub(crate) fn window_multipliers(&self) -> Result<&WindowMultipliers, Error> {
        prepared(&self.window_multipliers, || {
            WindowMultipliers::new(self.lagrange_bases()?)
        })
    }

    pub(crate) fn sparse_rows(&self) -> Result<&SparseFixedRows, Error> {
        prepared(&self.sparse_rows, fixed_columns::sparse_fixed_rows)
    }

    pub(crate) fn fixed_coefficients(&self) -> Result<&[[Fp; N]], Error> {
        prepared(&self.fixed_coefficients, || {
            coefficients::interpolate(values::fixed_columns(self)?)
        })
        .map(Vec::as_slice)
    }

    pub(crate) fn sigma_coefficients(&self) -> Result<&[[Fp; N]], Error> {
        prepared(&self.sigma_coefficients, || {
            coefficients::interpolate(values::sigma_columns(self)?)
        })
        .map(Vec::as_slice)
    }

    pub(crate) fn fixed_cosets(&self) -> Result<&[Vec<Fp>], Error> {
        prepared(&self.fixed_cosets, || {
            cosets::expand_coefficients(self.fixed_coefficients()?)
        })
        .map(Vec::as_slice)
    }

    pub(crate) fn sigma_cosets(&self) -> Result<&[Vec<Fp>], Error> {
        prepared(&self.sigma_cosets, || {
            cosets::expand_coefficients(self.sigma_coefficients()?)
        })
        .map(Vec::as_slice)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn primitive_and_srs_preparation_are_independent() {
        let raw = RawStore::new(concat!(env!("CARGO_MANIFEST_DIR"), "/../sensei/data"));
        let primitive = Context::new(&raw);
        crate::points::primitive_points(&primitive).unwrap();
        assert!(primitive.sinsemilla_generators.get().is_some());
        assert!(primitive.coefficient_bases.get().is_none());
        assert!(primitive.lagrange_bases.get().is_none());
        assert!(primitive.fixed_cosets.get().is_none());
        let srs = Context::new(&raw);
        crate::points::srs_points(&srs).unwrap();
        assert!(srs.lagrange_bases.get().is_some());
        assert!(srs.sinsemilla_generators.get().is_none());
        assert!(srs.fixed_coefficients.get().is_none());
    }

    /// Exercise every dial, including disabled artifacts, against the public
    /// independent encoders. Shared preparation must preserve exact stored bytes.
    #[test]
    #[cfg_attr(
        debug_assertions,
        ignore = "unoptimized generation is slow; run with --release"
    )]
    fn shared_preparation_matches_independent_encoders() {
        let raw = RawStore::new(concat!(env!("CARGO_MANIFEST_DIR"), "/../sensei/data"));
        let context = Context::new(&raw);
        assert_eq!(crate::ARTIFACTS.len(), crate::registry::ENCODERS.len());
        for (artifact, encode) in crate::ARTIFACTS.iter().zip(crate::registry::ENCODERS) {
            let name = artifact.file_name();
            let shared = encode(&context).unwrap_or_else(|error| panic!("shared {name}: {error}"));
            let independent = (artifact.generate)(&raw)
                .unwrap_or_else(|error| panic!("independent {name}: {error}"));
            assert_eq!(shared, independent, "shared preparation changed {name}");
        }
    }
}
