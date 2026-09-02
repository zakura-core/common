#[macro_use]
extern crate criterion;

use criterion::{BenchmarkId, Criterion};

#[cfg(unix)]
use pprof::criterion::{Output, PProfProfiler};

use orchard::circuit::{OrchardCircuitVersion, ProvingKey, VerifyingKey};
use rand::rng;

mod support;

use support::payment_fixture;

fn criterion_benchmark(c: &mut Criterion) {
    let version = OrchardCircuitVersion::PostNu6_3;
    let vk = VerifyingKey::build(version);
    let pk = ProvingKey::build(version);
    let action_counts = 1..=4;

    {
        let mut group = c.benchmark_group("ironwood-payment-proving");
        group.sample_size(10);
        for action_count in action_counts.clone() {
            let fixture = payment_fixture(action_count);
            group.bench_function(BenchmarkId::from_parameter(action_count), |b| {
                b.iter(|| {
                    fixture
                        .bundle()
                        .authorization()
                        .create_proof(&pk, fixture.instances(), rng())
                        .unwrap()
                });
            });
        }
    }

    {
        let mut group = c.benchmark_group("ironwood-payment-verifying");
        for action_count in action_counts {
            let fixture = payment_fixture(action_count);
            let proof = fixture
                .bundle()
                .authorization()
                .create_proof(&pk, fixture.instances(), rng())
                .unwrap();
            assert!(proof.verify(&vk, fixture.instances()).is_ok());
            group.bench_function(BenchmarkId::from_parameter(action_count), |b| {
                b.iter(|| proof.verify(&vk, fixture.instances()));
            });
        }
    }
}

#[cfg(unix)]
criterion_group! {
    name = benches;
    config = Criterion::default().with_profiler(PProfProfiler::new(100, Output::Flamegraph(None)));
    targets = criterion_benchmark
}
#[cfg(windows)]
criterion_group! {
    name = benches;
    config = Criterion::default();
    targets = criterion_benchmark
}
criterion_main!(benches);
