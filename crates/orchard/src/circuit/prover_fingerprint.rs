//! Complete prover captures using the same synthetic Actions as the verifier fixtures.
//!
//! Each test compares the captured proof and final RNG position with an uncaptured
//! execution before exporting. The capture is a finite execution anchor, not a
//! proof of Rust/Lean equivalence or of a private randomness distribution.
//!
//! Export one or two Actions using `ORCHARD_LEAN_SINGLE_PROVER_OUT` or
//! `ORCHARD_LEAN_MULTI_PROVER_OUT` and the corresponding exact test name:
//! `cargo test --release -p zakura-orchard --features prover-fingerprint --lib
//! circuit::prover_fingerprint::prover_capture -- --exact` (append `_two_actions`
//! to the test name for two Actions). Use `RAYON_NUM_THREADS=1` for the pinned
//! deterministic fixture profile. Neither command requires `verifier-fingerprint`.

use halo2_proofs::plonk::prover_fingerprint::ProverCapture;

use super::{
    OrchardCircuitVersion,
    fixtures::{build_fixture_bundle, fixture_rng},
};

/// Existing verifier fixture's public one-Action seed (ASCII `S`).
const SINGLE_SEED: u8 = 0x53;
/// Existing verifier fixture's public two-Action seed (ASCII `M`).
const MULTI_SEED: u8 = 0x4d;

fn capture_fixture(seed: u8, actions: u8, output_var: &str) {
    let keys = crate::cached_test_keys(OrchardCircuitVersion::PostNu6_3);
    let pk = keys.proving_key();
    let vk = keys.verifying_key();
    let mut rng = fixture_rng(seed);
    let capture = ProverCapture::start();
    let bundle = build_fixture_bundle(&mut rng, pk, actions);
    let bytes = capture.finish();
    assert!(bundle.verify_proof(vk).is_ok());

    let mut baseline_rng = fixture_rng(seed);
    let baseline = build_fixture_bundle(&mut baseline_rng, pk, actions);
    assert_eq!(
        bundle.authorization().proof().0,
        baseline.authorization().proof().0
    );
    assert_eq!(rng.get_word_pos(), baseline_rng.get_word_pos());

    if let Some(path) = std::env::var_os(output_var) {
        std::fs::write(path, bytes).expect("the requested fixture output is writable");
    }
}

/// Export one complete real prover call with `ORCHARD_LEAN_SINGLE_PROVER_OUT`.
#[test]
fn prover_capture() {
    capture_fixture(SINGLE_SEED, 1, "ORCHARD_LEAN_SINGLE_PROVER_OUT");
}

/// Export a complete two-Action call with `ORCHARD_LEAN_MULTI_PROVER_OUT`.
#[test]
fn prover_capture_two_actions() {
    capture_fixture(MULTI_SEED, 2, "ORCHARD_LEAN_MULTI_PROVER_OUT");
}
