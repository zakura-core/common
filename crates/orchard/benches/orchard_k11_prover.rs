use std::time::Duration;

use criterion::{BatchSize, Criterion, SamplingMode, black_box, criterion_group, criterion_main};
use orchard::{
    Anchor, Bundle, Proof,
    builder::{Builder, BundleType, UnauthorizedBundle},
    bundle::{BundleVersion, Flags},
    circuit::{Instance, OrchardCircuitVersion, ProvingKey, VerifyingKey},
    keys::{FullViewingKey, Scope, SpendingKey},
    value::NoteValue,
};
use rand::{SeedableRng, rngs::StdRng};

const STEADY_ACTION_COUNTS: [usize; 3] = [1, 2, 4];
const FIRST_AFTER_BUILD_AND_PREPARE_ACTION_COUNTS: [usize; 2] = [1, 4];
const FIXTURE_ADDRESS_INDEX: u32 = 0;
const FIXTURE_NOTE_VALUE: u64 = 10;
/// The Orchard builder API fixes memo fields at 512 bytes.
const FIXTURE_MEMO_SIZE: usize = 512;
const FIXTURE_MEMO: [u8; FIXTURE_MEMO_SIZE] = [0; FIXTURE_MEMO_SIZE];
const FIXTURE_SPENDING_KEY: [u8; 32] = [7; 32];
const FIXTURE_ANCHOR: [u8; 32] = [0; 32];
const FIXTURE_SEED: [u8; 32] = [0x42; 32];
const PREFLIGHT_PROOF_SEED_DOMAIN: u8 = 0x24;
const STEADY_PROOF_SEED_DOMAIN: u8 = 0x25;
const FIRST_AFTER_PREPARE_PROOF_SEED_DOMAIN: u8 = 0x26;
const PREFLIGHT_PROOF_COUNT: u64 = 2;

const BENCHMARK_SAMPLES: usize = 10;
const WARMUP_SECONDS: u64 = 2;
const MEASUREMENT_SECONDS: u64 = 15;
// One thread remains the default for comparable benchmark history. Set this
// and `RAYON_NUM_THREADS` to the same value to measure multicore proving.
const DEFAULT_BENCHMARK_THREADS: &str = "1";
const BENCHMARK_THREADS_ENV: &str = "ORCHARD_K11_PROVER_THREADS";

struct ProverFixture {
    bundle: UnauthorizedBundle<i64>,
    instances: Vec<Instance>,
}

fn prover_fixture(action_count: usize) -> ProverFixture {
    let sk = SpendingKey::from_bytes(FIXTURE_SPENDING_KEY).unwrap();
    let recipient = FullViewingKey::from(&sk).address_at(FIXTURE_ADDRESS_INDEX, Scope::External);
    let mut fixture_rng = StdRng::from_seed(FIXTURE_SEED);
    let mut builder = Builder::new(
        BundleType::Coinbase,
        BundleVersion::orchard_v2(),
        Flags::SPENDS_DISABLED,
        Anchor::from_bytes(FIXTURE_ANCHOR).unwrap(),
    )
    .unwrap();
    for _ in 0..action_count {
        builder
            .add_output(
                None,
                recipient,
                NoteValue::from_raw(FIXTURE_NOTE_VALUE),
                FIXTURE_MEMO,
            )
            .unwrap();
    }
    let bundle: Bundle<_, i64> = builder
        .build(&mut fixture_rng)
        .unwrap()
        .expect("at least one output produces an Orchard bundle")
        .0;
    assert_eq!(bundle.actions().len(), action_count);
    let instances = bundle
        .actions()
        .iter()
        .map(|action| action.to_instance(*bundle.flags(), *bundle.anchor()))
        .collect();

    ProverFixture { bundle, instances }
}

fn benchmark_name(action_count: usize) -> &'static str {
    match action_count {
        1 => "prove-1-action",
        2 => "prove-2-actions",
        4 => "prove-4-actions",
        _ => unreachable!("the benchmark action counts are fixed"),
    }
}

fn proof_rng(domain: u8, action_count: usize, proof_index: u64) -> StdRng {
    let mut seed = [domain; 32];
    let action_count = u64::try_from(action_count).expect("Action count fits into u64");
    seed[..8].copy_from_slice(&action_count.to_le_bytes());
    seed[8..16].copy_from_slice(&proof_index.to_le_bytes());
    StdRng::from_seed(seed)
}

fn build_prepared_key(version: OrchardCircuitVersion) -> ProvingKey {
    let pk = ProvingKey::build(version);
    assert!(
        pk.prepare_proving(),
        "first-after-prepare benchmarks require prepared commitment tables",
    );
    pk
}

fn orchard_k11_prover(c: &mut Criterion) {
    let expected_threads = std::env::var(BENCHMARK_THREADS_ENV)
        .unwrap_or_else(|_| DEFAULT_BENCHMARK_THREADS.to_owned());
    assert_eq!(
        std::env::var("RAYON_NUM_THREADS").ok().as_deref(),
        Some(expected_threads.as_str()),
        "set RAYON_NUM_THREADS to {expected_threads}",
    );

    // Orchard fixes its Action circuit size at k = 11. This shared key is
    // deliberately prepared and warmed before the steady-state routines.
    let version = OrchardCircuitVersion::FixedPostNu6_2;
    let vk = VerifyingKey::build(version);
    let pk = ProvingKey::build(version);
    // Keep the one-time table build outside the timed proving routine.
    #[cfg(any(feature = "multicore", feature = "orbits"))]
    assert!(pk.prepare_proving(), "Pasta commitment tables must prepare",);

    let fixtures =
        STEADY_ACTION_COUNTS.map(|action_count| (action_count, prover_fixture(action_count)));

    // These preflights intentionally make the historical throughput cases
    // steady-state with respect to all proving-key caches.
    for (action_count, fixture) in &fixtures {
        let mut previous_proof: Option<Proof> = None;
        // Check each exact fixture and retained-state path outside the timed
        // region with two distinct sets of transcript challenges.
        for proof_index in 0..PREFLIGHT_PROOF_COUNT {
            let proof = fixture
                .bundle
                .authorization()
                .create_proof(
                    &pk,
                    &fixture.instances,
                    proof_rng(PREFLIGHT_PROOF_SEED_DOMAIN, *action_count, proof_index),
                )
                .unwrap();
            proof
                .verify(&vk, &fixture.instances)
                .expect("each benchmark preflight proof must verify");
            if let Some(previous_proof) = &previous_proof {
                assert_ne!(
                    proof.as_ref(),
                    previous_proof.as_ref(),
                    "distinct proof seeds must produce distinct proofs",
                );
            }
            previous_proof = Some(proof);
        }
    }

    // Preserve the historical group ID used by baseline directories and
    // result parsers. Its cases are deliberately steady-state.
    let mut steady = c.benchmark_group("orchard-k11");
    steady.sample_size(BENCHMARK_SAMPLES);
    steady.sampling_mode(SamplingMode::Flat);
    steady.warm_up_time(Duration::from_secs(WARMUP_SECONDS));
    steady.measurement_time(Duration::from_secs(MEASUREMENT_SECONDS));
    for (action_count, fixture) in &fixtures {
        steady.bench_function(benchmark_name(*action_count), |bencher| {
            let mut proof_index = 0;
            bencher.iter_batched(
                || {
                    let proof_rng = proof_rng(STEADY_PROOF_SEED_DOMAIN, *action_count, proof_index);
                    proof_index += 1;
                    proof_rng
                },
                |proof_rng| {
                    black_box(
                        fixture
                            .bundle
                            .authorization()
                            .create_proof(&pk, &fixture.instances, proof_rng)
                            .unwrap(),
                    )
                },
                BatchSize::SmallInput,
            )
        });
    }
    steady.finish();

    let mut first_after_prepare = c.benchmark_group("orchard-k11-first-after-build-and-prepare");
    first_after_prepare.sample_size(BENCHMARK_SAMPLES);
    first_after_prepare.sampling_mode(SamplingMode::Flat);
    first_after_prepare.warm_up_time(Duration::from_secs(WARMUP_SECONDS));
    first_after_prepare.measurement_time(Duration::from_secs(MEASUREMENT_SECONDS));
    for (action_count, fixture) in fixtures.iter().filter(|(action_count, _)| {
        FIRST_AFTER_BUILD_AND_PREPARE_ACTION_COUNTS.contains(action_count)
    }) {
        first_after_prepare.bench_function(benchmark_name(*action_count), |bencher| {
            let mut proof_index = 0;
            bencher.iter_batched_ref(
                || {
                    let proof_rng = proof_rng(
                        FIRST_AFTER_PREPARE_PROOF_SEED_DOMAIN,
                        *action_count,
                        proof_index,
                    );
                    proof_index += 1;
                    (build_prepared_key(version), proof_rng)
                },
                |(pk, proof_rng)| {
                    black_box(
                        fixture
                            .bundle
                            .authorization()
                            .create_proof(pk, &fixture.instances, proof_rng)
                            .unwrap(),
                    )
                },
                BatchSize::PerIteration,
            )
        });
    }
    first_after_prepare.finish();
}

criterion_group!(benches, orchard_k11_prover);
criterion_main!(benches);
