use std::time::{Duration, Instant};

use criterion::{Criterion, SamplingMode, black_box, criterion_group, criterion_main};
use orchard::circuit::{OrchardCircuitVersion, ProvingKey};

const BENCHMARK_SAMPLES: usize = 10;
const WARMUP_SECONDS: u64 = 2;
const MEASUREMENT_SECONDS: u64 = 15;

fn post_nu6_3_k11_keygen(criterion: &mut Criterion) {
    let version = OrchardCircuitVersion::PostNu6_3;
    let mut group = criterion.benchmark_group("post-nu6-3-k11-keygen");
    group.sample_size(BENCHMARK_SAMPLES);
    group.sampling_mode(SamplingMode::Flat);
    group.warm_up_time(Duration::from_secs(WARMUP_SECONDS));
    group.measurement_time(Duration::from_secs(MEASUREMENT_SECONDS));
    group.bench_function("build-proving-key", |bencher| {
        bencher.iter_custom(|iterations| {
            let mut measured = Duration::ZERO;
            for _ in 0..iterations {
                let start = Instant::now();
                let proving_key = ProvingKey::build(version);
                measured += start.elapsed();
                black_box(&proving_key);
                drop(proving_key);
            }
            measured
        });
    });
    group.finish();
}

criterion_group!(benches, post_nu6_3_k11_keygen);
criterion_main!(benches);
