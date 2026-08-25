//! Manual timing harness: end-to-end Ironwood bundle batch validation —
//! real proofs, real RedPallas signatures, [`BatchValidator`] exactly as a
//! node runs it — across proof batch sizes and worker counts.
//!
//! ```text
//! cargo test --release -p orchard --test ironwood_batch_timings -- \
//!     --ignored --nocapture
//! ```
//!
//! Set `IRONWOOD_ARM=1` to prepare the verifying key for batch validation
//! (`VerifyingKey::prepare_batch_validation`) before timing; without it the
//! verifier's final identity test runs through the unprepared MSM path.

use std::time::Instant;

use rand::{rngs::StdRng, SeedableRng};

use orchard::{
    builder::{Builder, BundleType},
    bundle::{BatchValidator, BundleVersion, Flags},
    circuit::{OrchardCircuitVersion, ProvingKey, VerifyingKey},
    keys::{FullViewingKey, Scope, SpendingKey},
    value::NoteValue,
    Anchor, Bundle,
};

const BATCH_SIZES: [usize; 7] = [1, 2, 4, 8, 16, 32, 64];
const THREADS: [usize; 3] = [1, 8, 32];
const MEMO_SIZE: usize = 512;

fn median(mut samples: Vec<f64>) -> f64 {
    samples.sort_by(f64::total_cmp);
    samples[samples.len() / 2]
}

/// Builds one distinct single-action Ironwood coinbase bundle with a real
/// proof and real signatures, plus the sighash it was authorized for.
fn ironwood_bundle(
    pk: &ProvingKey,
    index: u64,
) -> (Bundle<orchard::bundle::Authorized, i64>, [u8; 32]) {
    let sk = SpendingKey::from_bytes([7; 32]).unwrap();
    let recipient = FullViewingKey::from(&sk).address_at(0u32, Scope::External);
    let mut memo = [0u8; MEMO_SIZE];
    memo[..8].copy_from_slice(&index.to_le_bytes());
    let mut seed = [0x42u8; 32];
    seed[..8].copy_from_slice(&index.to_le_bytes());
    let mut sighash = [0xA5u8; 32];
    sighash[..8].copy_from_slice(&index.to_le_bytes());

    let mut builder = Builder::new(
        BundleType::Coinbase,
        BundleVersion::ironwood_v3(),
        Flags::SPENDS_DISABLED,
        Anchor::from_bytes([0; 32]).unwrap(),
    )
    .unwrap();
    builder
        .add_output(None, recipient, NoteValue::from_raw(10 + index), memo)
        .unwrap();
    let bundle: Bundle<_, i64> = builder
        .build(&mut StdRng::from_seed(seed))
        .unwrap()
        .expect("one output produces a bundle")
        .0;
    let proven = bundle
        .create_proof(pk, StdRng::from_seed(seed))
        .expect("proving succeeds");
    let authorized = proven
        .apply_signatures(StdRng::from_seed(seed), sighash, &[])
        .expect("coinbase bundles need no spend authorizations");
    (authorized, sighash)
}

#[test]
#[ignore = "manual timing harness; see the module docs"]
fn ironwood_batch_validation_timings() {
    let probe = {
        let mut builder = Builder::new(
            BundleType::Coinbase,
            BundleVersion::ironwood_v3(),
            Flags::SPENDS_DISABLED,
            Anchor::from_bytes([0; 32]).unwrap(),
        )
        .unwrap();
        let sk = SpendingKey::from_bytes([7; 32]).unwrap();
        let recipient = FullViewingKey::from(&sk).address_at(0u32, Scope::External);
        builder
            .add_output(None, recipient, NoteValue::from_raw(10), [0; MEMO_SIZE])
            .unwrap();
        let bundle: Bundle<_, i64> = builder
            .build(&mut StdRng::from_seed([1; 32]))
            .unwrap()
            .unwrap()
            .0;
        bundle.circuit_version()
    };
    assert_eq!(
        probe,
        OrchardCircuitVersion::PostNu6_3,
        "ironwood bundles prove under the post-NU6.3 circuit"
    );

    let start = Instant::now();
    let vk = VerifyingKey::build(probe);
    let pk = ProvingKey::build(probe);
    println!(
        "ironwood keys built in {:.1}s",
        start.elapsed().as_secs_f64()
    );

    let max_batch = *BATCH_SIZES.last().unwrap();
    let start = Instant::now();
    let corpus: Vec<_> = (0..max_batch as u64)
        .map(|index| ironwood_bundle(&pk, index))
        .collect();
    println!(
        "{} single-action ironwood bundles proven in {:.1}s",
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
                    let valid = validator.validate(StdRng::from_seed([round as u8; 32]));
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
