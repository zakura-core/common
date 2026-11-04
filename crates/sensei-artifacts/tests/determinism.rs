//! Fail-closed determinism gate for the generators.
//!
//! Generators must be pure functions of the raw bytes and their registry
//! entry's stored form — no map-iteration order, thread scheduling, time, or
//! environment influence on the output. Each registered artifact is generated
//! twice and the outputs compared byte for byte, so accidental nondeterminism
//! fails the ordinary test suite. The prover's digest tests pin the exact bytes.
#![forbid(unsafe_code)]

use sensei_artifacts::{ARTIFACTS, RAW_INPUTS, RawStore};
use zakura_sensei_artifacts as sensei_artifacts;

/// The prover's `data/` directory (this crate lives at `crates/sensei-artifacts`).
fn raw_store() -> RawStore {
    RawStore::new(concat!(env!("CARGO_MANIFEST_DIR"), "/../sensei/data"))
}

/// Every registered raw input is present and readable.
#[test]
fn raw_inputs_are_present() {
    let raw = raw_store();
    for name in RAW_INPUTS {
        raw.bytes(name)
            .unwrap_or_else(|error| panic!("raw input `{name}`: {error}"));
    }
}

/// Every artifact generates identical bytes across two independent runs.
#[cfg_attr(
    debug_assertions,
    ignore = "unoptimized generation is slow; run with --release"
)]
#[test]
fn generators_are_deterministic() {
    let raw = raw_store();
    for artifact in ARTIFACTS {
        let name = artifact.file_name();
        let first = sensei_artifacts::generate(&name, &raw)
            .unwrap_or_else(|error| panic!("generating `{name}`: {error}"));
        let second = sensei_artifacts::generate(&name, &raw)
            .unwrap_or_else(|error| panic!("regenerating `{name}`: {error}"));
        assert_eq!(first, second, "`{name}` is nondeterministic across runs");
    }
}
