//! Complete prover captures using the same synthetic Actions as the verifier fixtures.
//!
//! Each test compares the captured proof and final RNG position with an uncaptured
//! execution through the production `Proof::create` before exporting. Recording
//! wrappers are installed only here. The capture is a finite execution anchor,
//! not a proof of Rust/Lean equivalence or of a private randomness distribution.
//!
//! Export Lean source for one or two Actions using `ORCHARD_LEAN_SINGLE_PROVER_OUT` or
//! `ORCHARD_LEAN_MULTI_PROVER_OUT` and the corresponding exact test name:
//! `cargo test --release -p zakura-orchard --features prover-fingerprint --lib
//! circuit::prover_fingerprint::prover_capture -- --exact` (append `_two_actions`
//! to the test name for two Actions). Use `RAYON_NUM_THREADS=1` for the pinned
//! deterministic fixture profile. Neither command requires `verifier-fingerprint`.

use alloc::vec::Vec;

use halo2_proofs::{
    plonk::{
        self,
        prover_fingerprint::{
            ProverCapture, RecordingRng, RecordingTranscript, dump_vesta_lean_prover_fixture,
            record_error,
        },
    },
    transcript::{Blake2bWrite, Challenge255},
};
use pasta_curves::vesta;
use rand::Rng;

#[cfg(feature = "multicore")]
use super::CircuitWithPreparedMerklePath;
use super::{
    Circuit, Instance, OrchardCircuitVersion, Proof, ProvingKey,
    fixtures::{build_unproven_fixture_bundle, fixture_rng},
};
use crate::BenchmarkCircuitWitnesses as _;

/// Existing verifier fixture's public one-Action seed (ASCII `S`).
const SINGLE_SEED: u8 = 0x53;
/// Existing verifier fixture's public two-Action seed (ASCII `M`).
const MULTI_SEED: u8 = 0x4d;

fn record_proof<C: plonk::Circuit<vesta::Scalar> + Sync>(
    pk: &ProvingKey,
    circuits: &[C],
    instances: &[&[&[vesta::Scalar]]],
    rng: impl Rng,
) -> Result<Proof, plonk::Error>
where
    C::Config: Send,
{
    let mut transcript = RecordingTranscript::new(
        Blake2bWrite::<_, vesta::Affine, Challenge255<_>>::init(vec![]),
    );
    plonk::create_proof(
        &pk.params,
        &pk.pk,
        circuits,
        instances,
        RecordingRng::new(rng),
        &mut transcript,
    )
    .inspect_err(record_error)?;
    Ok(Proof(transcript.finalize()))
}

fn capture_proof(
    pk: &ProvingKey,
    circuits: &[Circuit],
    instances: &[Instance],
    rng: impl Rng,
) -> Result<Proof, plonk::Error> {
    let instances: Vec<_> = instances.iter().map(Instance::to_halo2_instance).collect();
    let instances: Vec<Vec<_>> = instances
        .iter()
        .map(|instance| instance.iter().map(|column| &column[..]).collect())
        .collect();
    let instances: Vec<_> = instances.iter().map(|instance| &instance[..]).collect();

    // Follow Proof::create's Merkle preparation choice. Keep this orchestration
    // in fixture tooling and check proof bytes and RNG position against that
    // uninstrumented entry point below.
    #[cfg(feature = "multicore")]
    if maybe_rayon::current_thread_index().is_none()
        && (circuits.len() == 1 || circuits.len() < maybe_rayon::current_num_threads())
    {
        let circuits: Vec<_> = circuits
            .iter()
            .map(CircuitWithPreparedMerklePath::new)
            .collect();
        return record_proof(pk, &circuits, &instances, rng);
    }

    record_proof(pk, circuits, &instances, rng)
}

fn capture_fixture(seed: u8, actions: u8, output_var: &str, namespace: &str) {
    let keys = crate::cached_test_keys(OrchardCircuitVersion::PostNu6_3);
    let pk = keys.proving_key();
    let vk = keys.verifying_key();
    let mut rng = fixture_rng(seed);
    let bundle = build_unproven_fixture_bundle(&mut rng, actions);
    let instances = bundle.to_instances();
    let mut baseline_rng = rng.clone();

    let capture = ProverCapture::start();
    let proof = capture_proof(pk, bundle.benchmark_circuits(), &instances, &mut rng).unwrap();
    let bytes = capture.finish();
    assert!(proof.verify(vk, &instances).is_ok());

    let baseline = bundle
        .authorization()
        .create_proof(pk, &instances, &mut baseline_rng)
        .unwrap();
    assert_eq!(proof.0, baseline.0);
    assert_eq!(rng.get_word_pos(), baseline_rng.get_word_pos());

    let fixture = dump_vesta_lean_prover_fixture(namespace, &bytes, &proof.0)
        .expect("the complete successful capture exports to Lean");
    if let Some(path) = std::env::var_os(output_var) {
        std::fs::write(path, fixture).expect("the requested fixture output is writable");
    }
}

/// Export one complete real prover call with `ORCHARD_LEAN_SINGLE_PROVER_OUT`.
#[test]
fn prover_capture() {
    capture_fixture(
        SINGLE_SEED,
        1,
        "ORCHARD_LEAN_SINGLE_PROVER_OUT",
        "Zcash.Snark.Fixtures.Prover.SingleAction",
    );
}

/// Export a complete two-Action call with `ORCHARD_LEAN_MULTI_PROVER_OUT`.
#[test]
fn prover_capture_two_actions() {
    capture_fixture(
        MULTI_SEED,
        2,
        "ORCHARD_LEAN_MULTI_PROVER_OUT",
        "Zcash.Snark.Fixtures.Prover.MultiAction",
    );
}
