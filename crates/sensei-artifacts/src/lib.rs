//! Host-side generators for Sensei's embedded primitive and proof data.
//!
//! This crate turns circuit recipes and the canonical raw inputs under
//! `crates/sensei/data/raw/` into prepared artifact bytes. It runs on the host
//! as a build dependency of Sensei, whose `build.rs` writes selected payloads
//! into `OUT_DIR` for the target's `bento` embedding declarations. This crate
//! is never part of the target binary.
//!
//! `crates/sensei/artifact_selection.rs` selects registry entries using Cargo
//! features and Sensei's source-selected preparation policy. Primitive points
//! are embedded even without either proof role; verifier-only builds also
//! select SRS points, verifier commitments, and any embedded commitment tables.
//! Prover builds select additional circuit data.
//!
//! [`generate`] runs an individual encoder by its full file name, including
//! when that artifact is not selected for embedding. It and [`emit_generated`]
//! use the shared [`DEFAULT`](sensei_shared::commitment_tables::DEFAULT)
//! commitment-table policy. Sensei's `build.rs` instead calls
//! [`emit_generated_with_commitment_tables`] with `tuning::COMMITMENT_TABLES`.
//! Policy is not encoded in the artifact name: the same commitment-table file
//! name can hold different bytes under different policies. Under the default
//! policy its payload is legitimately empty because no sections are embedded.
//!
//! [`ARTIFACTS`] describes those encoders, and [`RAW_INPUTS`] lists their file
//! inputs. Sensei also generates complete selector rows separately in its build
//! script; see [`ArtifactId::GateSelectors`] for the two selector layouts.
//! All public entry points remain at this crate's root; internal modules
//! separate raw decoding, reconstruction, transforms, and output.
//!
//! The [`sensei_shared`] crate map owns the circuit recipe and record-layout
//! descriptions. [Sensei's crate map](../zakura_sensei/index.html#crate-map)
//! leads to the target's standalone primitives, signatures, and native proof
//! runtime. Code generation is a separate host path in
//! [`sensei-macros`](../zakura_sensei_macros/index.html): it consumes those
//! shared recipes rather than these serialized artifacts.
//!
//! Nothing the generators produce is checked into the repository: the
//! checked-in [`RAW_INPUTS`] hold representation-free encodings
//! (canonical little-endian field bytes and index maps), and the generated pods
//! hold Sensei's at-rest in-memory forms, which are a property of the
//! current implementation and its stored form ([`udon::STORED_FORM`]), not of
//! the protocol. The registry is keyed by (artifact, stored form):
//! field-element-bearing entries name the form they encode and carry its
//! descriptor in their file names. The registry also supplies the consumer's
//! paths for registered artifacts through [`render_artifact_paths`].
//! Udon's stored representation has the same fixed layout on every supported
//! target, so host generation also supports cross-compilation without reading
//! target pointer width or choosing a different form.
//!
//! Raw decoders check record counts, canonical coordinates and curve membership
//! for points, and length, range and bijectivity for the permutation map.
//! These checks establish well-formedness of the supplied bytes; they do not
//! authenticate them as the inputs for the intended circuit.
//!
//! Generators encode into **fixed-layout** record types whose layouts are
//! identical in every compilation per `bento`'s `Pod` contract.
//!
//! Generated payloads must be **deterministic** relative to the raw bytes,
//! circuit recipes, stored representation, and supplied commitment-table policy,
//! with no map-iteration order, thread scheduling, time, or environment influence
//! on their bytes. This crate's determinism test regenerates every registered
//! artifact twice under the default policy. Sensei's digest tests pin baseline
//! artifact contents; configured-policy comparisons must use the same policy
//! and feature selection.
//!
//! ```no_run
//! use zakura_sensei_artifacts as sensei_artifacts;
//! use sensei_artifacts::{RawStore, ArtifactId, emit_generated};
//! use std::path::Path;
//!
//! # fn main() -> Result<(), sensei_artifacts::Error> {
//! // Pass the data directory, not its raw/ child. The output directory must exist.
//! let raw = RawStore::new("crates/sensei/data");
//! let files = emit_generated(&raw, Path::new("generated"), &[ArtifactId::Points])?;
//! # let _ = files;
//! # Ok(())
//! # }
//! ```
#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]
// Preserve the imported `chunks_exact` code, as in Udon. The pinned
// toolchain's Clippy predates this lint (introduced in 1.98).
#![allow(unknown_lints)]
#![allow(clippy::chunks_exact_to_as_chunks)]

mod commitment_tables;
mod context;
mod domain;
mod error;
mod fft;
mod fixed_base_tables;
mod fixed_columns;
mod output;
mod points;
mod polynomials;
mod raw;
mod registry;

pub use error::Error;
pub use output::{
    ARTIFACT_PATHS_FILE, emit_generated, emit_generated_with_commitment_tables,
    render_artifact_paths,
};
pub use raw::{RAW_INPUTS, RawStore};
pub use registry::{
    ARTIFACTS, Artifact, ArtifactDomain, ArtifactId, Generator, artifact, generate,
};

/// Reduces stored Montgomery representatives in place, retaining the loose type.
/// This fixes the limbs written to artifacts without converting to canonical bytes.
fn normalize_stored_montgomery(values: &mut [udon::field::Fp]) {
    for value in values {
        *value = value.reduce().into_loose();
    }
}
