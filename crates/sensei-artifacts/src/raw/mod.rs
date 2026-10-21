//! Canonical file inventory, filesystem reads, and format-specific validation.
//!
//! Raw records contain canonical coordinates or integer cell indices, never
//! the prover's prepared field representation. Decoders validate the complete
//! input before downstream generators reconstruct or transform its values.

use std::{fs, io, path::PathBuf};

use crate::Error;

pub(crate) mod permutation;
pub(crate) mod points;

/// The canonical raw inputs under `data/raw/`: the only checked-in data
/// files, deliberately independent of the prover's at-rest representation.
pub static RAW_INPUTS: &[&str] = &[
    points::COEFFICIENT_BASES,
    points::SINSEMILLA_GENERATORS,
    points::VERIFIER_FIXED,
    points::VERIFIER_INSECURE,
    permutation::SIGMA_MAP,
];

/// Read access to the canonical raw inputs under `data/raw/`.
///
/// This is a directory handle, without caching: each [`Self::bytes`] call
/// reads the named file anew. Format validation belongs to the encoders'
/// decoders, so constructing a store does not read or validate any input.
pub struct RawStore {
    root: PathBuf,
}

impl RawStore {
    /// A store over `data_dir/raw` for the prover's `data/` directory.
    pub fn new(data_dir: impl Into<PathBuf>) -> Self {
        Self {
            root: data_dir.into().join("raw"),
        }
    }

    /// The directory the raw inputs live in.
    pub fn root(&self) -> &std::path::Path {
        &self.root
    }

    /// Reads one raw input file, without decoding its contents.
    ///
    /// Registered names are listed in [`RAW_INPUTS`]. Read failures include
    /// the input path in the returned error.
    pub fn bytes(&self, name: &str) -> Result<Vec<u8>, Error> {
        let path = self.root.join(name);
        fs::read(&path).map_err(|error: io::Error| {
            Error::new(format!("reading raw input {}: {error}", path.display()))
        })
    }
}
