//! Manual timing harness: end-to-end Ironwood bundle batch validation —
//! real proofs, real RedPallas signatures, [`BatchValidator`] exactly as a
//! node runs it — across proof batch sizes and worker counts.
//!
//! ```text
//! cargo test --release -p zakura-orchard --features circuit \
//!     --test ironwood_batch_timings -- --ignored --nocapture
//! ```
//!
//! Set `IRONWOOD_ARM=1` to prepare the verifying key for batch validation
//! (`VerifyingKey::prepare_batch_validation`) before timing; without it the
//! verifier's final identity test runs through the unprepared MSM path.

use std::time::Instant;

use rand::{SeedableRng, rngs::StdRng};

use orchard::{
    Bundle,
    bundle::{BatchValidator, BundleVersion},
    circuit::{OrchardCircuitVersion, ProvingKey, VerifyingKey},
};

#[path = "../benches/support/mod.rs"]
mod payment_support;

use payment_support::payment_fixture_with_index;

const BATCH_SIZES: [usize; 7] = [1, 2, 4, 8, 16, 32, 64];
const THREADS: [usize; 3] = [1, 8, 32];
const FIXTURE_ACTION_COUNTS: [usize; 3] = [1, 2, 4];
const PAYMENT_ACTIONS: usize = 2;
const PROOF_SEED_DOMAIN: u8 = 0x50;
const SIGNATURE_SEED_DOMAIN: u8 = 0x51;
const SIGHASH_DOMAIN: u8 = 0xa5;

fn median(mut samples: Vec<f64>) -> f64 {
    samples.sort_by(f64::total_cmp);
    samples[samples.len() / 2]
}

fn indexed_rng(domain: u8, index: u64) -> StdRng {
    let mut seed = [domain; 32];
    seed[..8].copy_from_slice(&index.to_le_bytes());
    StdRng::from_seed(seed)
}

#[test]
fn ironwood_payment_fixtures_are_valid() {
    for action_count in FIXTURE_ACTION_COUNTS {
        let fixture = payment_fixture_with_index(
            action_count,
            u64::try_from(action_count).expect("Action count fits into u64"),
        );
        assert_eq!(
            fixture.bundle().bundle_version(),
            BundleVersion::ironwood_v3(),
        );
        assert_eq!(
            fixture.bundle().circuit_version(),
            OrchardCircuitVersion::PostNu6_3,
        );
        assert_eq!(fixture.bundle().actions().len(), action_count);
    }
}

/// Builds one distinct two-Action Ironwood payment with real spends, outputs,
/// proof, and signatures, plus the sighash it was authorized for.
fn ironwood_bundle(
    pk: &ProvingKey,
    index: u64,
) -> (Bundle<orchard::bundle::Authorized, i64>, [u8; 32]) {
    let mut sighash = [SIGHASH_DOMAIN; 32];
    sighash[..8].copy_from_slice(&index.to_le_bytes());

    let fixture = payment_fixture_with_index(PAYMENT_ACTIONS, index);
    assert_eq!(
        fixture.bundle().circuit_version(),
        OrchardCircuitVersion::PostNu6_3,
    );
    let (bundle, spend_authorizing_key) = fixture.into_bundle_and_signing_key();
    let proven = bundle
        .create_proof(pk, indexed_rng(PROOF_SEED_DOMAIN, index))
        .expect("proving succeeds");
    let authorized = proven
        .apply_signatures(
            indexed_rng(SIGNATURE_SEED_DOMAIN, index),
            sighash,
            &[spend_authorizing_key],
        )
        .expect("the payment spend is authorized");
    (authorized, sighash)
}

#[test]
#[ignore = "manual timing harness; see the module docs"]
fn ironwood_batch_validation_timings() {
    let version = OrchardCircuitVersion::PostNu6_3;

    let start = Instant::now();
    let vk = VerifyingKey::build(version);
    let pk = ProvingKey::build(version);
    println!(
        "ironwood keys built in {:.1}s",
        start.elapsed().as_secs_f64()
    );

    let max_batch = *BATCH_SIZES.last().unwrap();
    let start = Instant::now();
    let corpus: Vec<_> = (0..u64::try_from(max_batch).expect("batch size fits into u64"))
        .map(|index| ironwood_bundle(&pk, index))
        .collect();
    println!(
        "{} two-Action ironwood payments proven in {:.1}s",
        corpus.len(),
        start.elapsed().as_secs_f64()
    );

    // [branch-only-begin]
    let mode = if std::env::var_os("IRONWOOD_ARM").is_some() {
        let start = Instant::now();
        let armed = vk.prepare_batch_validation();
        println!(
            "verifying key prepared (armed={armed}) in {:.3}s",
            start.elapsed().as_secs_f64()
        );
        "prepared"
    } else {
        "unarmed"
    };
    // [branch-only-end]

    for threads in THREADS {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build()
            .expect("bench thread pool must build");
        pool.install(|| {
            for batch in BATCH_SIZES {
                let iters = (192 / batch).clamp(5, 31) | 1;
                let mut samples = Vec::with_capacity(iters);
                for round in 0..iters {
                    let start = Instant::now();
                    let mut validator = BatchValidator::new(&vk);
                    for (bundle, sighash) in &corpus[..batch] {
                        validator
                            .add_bundle(bundle, *sighash)
                            .expect("the key supports ironwood bundles");
                    }
                    let round = u8::try_from(round).expect("sample round fits into u8");
                    let valid = validator.validate(StdRng::from_seed([round; 32]));
                    samples.push(start.elapsed().as_secs_f64() * 1e3);
                    assert!(valid, "the corpus must validate");
                }
                let ms = median(samples);
                println!(
                    "ironwood mode={mode} threads={threads:>2} batch={batch:>3} \
                     validate={ms:>9.3}ms per-bundle={:>8.3}ms",
                    ms / batch as f64
                );
            }
        });
    }
}
