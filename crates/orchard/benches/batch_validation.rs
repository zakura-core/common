//! Whole-batch Orchard validation latency, throughput, and cold-call cost for
//! one backend, over a corpus of distinct two-Action payments.
//!
//! The target compiles once per backend (`backend-halo2` by default, or
//! `backend-sensei` with the default features disabled) and measures exactly
//! what a node's batch verifier runs: `BatchValidator::new`, `add_bundle` for
//! every bundle, and `validate`, so proofs and RedPallas signatures are both
//! included. Worker counts come from `RAYON_NUM_THREADS`, which sizes the
//! global pool used by Halo2 and Orchard's own fan-out, and Sensei's private
//! pool. Pin with `taskset` to choose physical cores.
//!
//! Modes (first argument): `isolated`, `concurrent`, `cold`. Settings:
//! `BATCH_CORPUS` bundles proven up front (64), `BATCH_BUNDLES` batch sizes
//! (`1,16,64`), `BATCH_REPS` (50), `BATCH_WARMUP` untimed calls (5),
//! `BATCH_CONCURRENT` thread counts (`1,2,4,8`), `BATCH_SECONDS` per
//! concurrent cell (6). One line per measurement goes to stdout; progress
//! goes to stderr.

use std::{
    sync::atomic::{AtomicBool, Ordering},
    time::{Duration, Instant},
};

use orchard::{
    Bundle,
    bundle::{Authorized, BatchValidator},
    circuit::{OrchardCircuitVersion, ProvingKey, VerifyingKey},
};
use rand::{SeedableRng, rngs::StdRng};

mod support;

const VERSION: OrchardCircuitVersion = OrchardCircuitVersion::PostNu6_3;
const ACTIONS_PER_BUNDLE: usize = 2;
const PROOF_SEED_DOMAIN: u8 = 0x51;
const SIGNATURE_SEED_DOMAIN: u8 = 0x52;
const VALIDATION_SEED_DOMAIN: u8 = 0x53;

type Corpus = Vec<(Bundle<Authorized, i64>, [u8; 32])>;

fn backend() -> &'static str {
    if cfg!(feature = "backend-sensei") {
        "sensei"
    } else {
        "halo2"
    }
}

fn setting(name: &str, default: usize) -> usize {
    std::env::var(name)
        .ok()
        .map(|value| value.parse().expect("positive integer setting"))
        .unwrap_or(default)
}

fn list_setting(name: &str, default: &[usize]) -> Vec<usize> {
    std::env::var(name)
        .ok()
        .map(|value| {
            value
                .split(',')
                .map(|item| item.trim().parse().expect("integer list"))
                .collect()
        })
        .unwrap_or_else(|| default.to_vec())
}

fn seeded(domain: u8, index: u64) -> StdRng {
    let mut seed = [domain; 32];
    seed[..8].copy_from_slice(&index.to_le_bytes());
    StdRng::from_seed(seed)
}

fn status_field(name: &str) -> Option<u64> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    status
        .lines()
        .find_map(|line| line.strip_prefix(name))
        .and_then(|value| value.trim().trim_end_matches("kB").trim().parse().ok())
}

fn peak_rss_kib() -> Option<u64> {
    status_field("VmHWM:")
}

fn rss_kib() -> Option<u64> {
    status_field("VmRSS:")
}

fn os_threads() -> Option<u64> {
    status_field("Threads:")
}

fn build_corpus(pk: &ProvingKey, count: usize) -> Corpus {
    (0..count)
        .map(|index| {
            let fixture = support::payment_fixture_with_index(ACTIONS_PER_BUNDLE, index as u64);
            let (bundle, signing_key) = fixture.into_bundle_and_signing_key();
            let sighash = [index as u8; 32];
            let proven = bundle
                .create_proof(pk, seeded(PROOF_SEED_DOMAIN, index as u64))
                .expect("corpus proof");
            let authorized = proven
                .apply_signatures(
                    seeded(SIGNATURE_SEED_DOMAIN, index as u64),
                    sighash,
                    &[signing_key],
                )
                .expect("corpus signatures");
            if index % 16 == 15 {
                eprintln!("[{}] proven {} / {count}", backend(), index + 1);
            }
            (authorized, sighash)
        })
        .collect()
}

/// One batch validation: admission (`add_bundle`) and `validate` timed
/// separately. Returns `(admission, validation)`.
fn validate(
    vk: &VerifyingKey,
    batch: &[(Bundle<Authorized, i64>, [u8; 32])],
    round: u64,
) -> (Duration, Duration) {
    let started = Instant::now();
    let mut validator = BatchValidator::new(vk);
    for (bundle, sighash) in batch {
        validator
            .add_bundle(bundle, *sighash)
            .expect("the key supports these bundles");
    }
    let admitted = started.elapsed();
    let started = Instant::now();
    assert!(validator.validate(seeded(VALIDATION_SEED_DOMAIN, round)));
    (admitted, started.elapsed())
}

fn median(values: &mut [u128]) -> u128 {
    values.sort_unstable();
    values[values.len() / 2]
}

fn p90(values: &mut [u128]) -> u128 {
    values.sort_unstable();
    values[values.len() * 9 / 10]
}

fn mode_isolated(vk: &VerifyingKey, corpus: &Corpus) {
    let reps = setting("BATCH_REPS", 50);
    let warmup = setting("BATCH_WARMUP", 5);
    for bundles in list_setting("BATCH_BUNDLES", &[1, 16, 64]) {
        assert!(
            bundles <= corpus.len(),
            "BATCH_BUNDLES exceeds BATCH_CORPUS"
        );
        let batch = &corpus[..bundles];
        for round in 0..warmup {
            validate(vk, batch, round as u64);
        }
        let mut admission = Vec::with_capacity(reps);
        let mut validation = Vec::with_capacity(reps);
        let mut total = Vec::with_capacity(reps);
        for round in 0..reps {
            let (admitted, validated) = validate(vk, batch, (warmup + round) as u64);
            admission.push(admitted.as_nanos());
            validation.push(validated.as_nanos());
            total.push((admitted + validated).as_nanos());
        }
        println!(
            "BATCH_ISOLATED backend={} workers={} bundles={bundles} actions={} reps={reps} \
             add_ns={} validate_ns={} validate_p90_ns={} total_ns={} total_p90_ns={}",
            backend(),
            rayon::current_num_threads(),
            bundles * ACTIONS_PER_BUNDLE,
            median(&mut admission),
            median(&mut validation),
            p90(&mut validation),
            median(&mut total),
            p90(&mut total),
        );
    }
}

fn mode_concurrent(vk: &VerifyingKey, corpus: &Corpus) {
    let bundles = setting("BATCH_SIZE", 64).min(corpus.len());
    let seconds = setting("BATCH_SECONDS", 6) as f64;
    let batch = &corpus[..bundles];
    validate(vk, batch, 0);
    for threads in list_setting("BATCH_CONCURRENT", &[1, 2, 4, 8]) {
        let stop = AtomicBool::new(false);
        let started = Instant::now();
        let per_thread: Vec<Vec<u128>> = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..threads)
                .map(|thread| {
                    let stop = &stop;
                    scope.spawn(move || {
                        let mut latencies = Vec::new();
                        let mut round = (thread as u64) << 32;
                        while !stop.load(Ordering::Relaxed) {
                            round += 1;
                            let (admitted, validated) = validate(vk, batch, round);
                            latencies.push((admitted + validated).as_nanos());
                        }
                        latencies
                    })
                })
                .collect();
            std::thread::sleep(Duration::from_secs_f64(seconds));
            stop.store(true, Ordering::Relaxed);
            handles
                .into_iter()
                .map(|handle| handle.join().expect("worker thread"))
                .collect()
        });
        let elapsed = started.elapsed().as_secs_f64();
        let batches: usize = per_thread.iter().map(Vec::len).sum();
        let mut latencies: Vec<u128> = per_thread.into_iter().flatten().collect();
        println!(
            "BATCH_CONCURRENT backend={} workers={} threads={threads} bundles={bundles} \
             batches={batches} elapsed_s={elapsed:.2} actions_per_s={:.0} latency_ns={} \
             latency_p90_ns={} rss_kib={:?} peak_rss_kib={:?} os_threads={:?}",
            backend(),
            rayon::current_num_threads(),
            (batches * bundles * ACTIONS_PER_BUNDLE) as f64 / elapsed,
            median(&mut latencies),
            p90(&mut latencies),
            rss_kib(),
            peak_rss_kib(),
            os_threads(),
        );
    }
}

fn mode_cold(vk: &VerifyingKey, corpus: &Corpus) {
    let bundles = setting("BATCH_SIZE", 64).min(corpus.len());
    let batch = &corpus[..bundles];
    let started = Instant::now();
    let prepared = vk.prepare_batch_validation();
    let prepare = started.elapsed();
    let (first_add, first) = validate(vk, batch, 1);
    let (second_add, second) = validate(vk, batch, 2);
    println!(
        "BATCH_COLD backend={} workers={} bundles={bundles} prepared={prepared} prepare_ns={} \
         first_ns={} second_ns={} rss_kib={:?} peak_rss_kib={:?}",
        backend(),
        rayon::current_num_threads(),
        prepare.as_nanos(),
        (first_add + first).as_nanos(),
        (second_add + second).as_nanos(),
        rss_kib(),
        peak_rss_kib(),
    );
}

fn main() {
    let mode = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "isolated".to_string());
    let corpus_size = setting("BATCH_CORPUS", 64);
    let started = Instant::now();
    let pk = ProvingKey::build(VERSION).expect("current circuit supports proving");
    let vk = VerifyingKey::build(VERSION);
    eprintln!(
        "[{}] keys built in {:.1?}; workers={} os_threads={:?}",
        backend(),
        started.elapsed(),
        rayon::current_num_threads(),
        os_threads(),
    );
    let started = Instant::now();
    let corpus = build_corpus(&pk, corpus_size);
    eprintln!(
        "[{}] {corpus_size} x {ACTIONS_PER_BUNDLE}-Action bundles proven in {:.1?}",
        backend(),
        started.elapsed()
    );
    match mode.as_str() {
        "isolated" => {
            vk.prepare_batch_validation();
            mode_isolated(&vk, &corpus);
        }
        "concurrent" => {
            vk.prepare_batch_validation();
            mode_concurrent(&vk, &corpus);
        }
        "cold" => mode_cold(&vk, &corpus),
        other => panic!("unknown mode {other}; use isolated, concurrent, or cold"),
    }
    eprintln!(
        "[{}] done; os_threads={:?} peak_rss_kib={:?}",
        backend(),
        os_threads(),
        peak_rss_kib()
    );
}
