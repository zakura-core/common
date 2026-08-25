use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use pasta_curves::{deferred::DeferredField, Fp, Fq};
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;

const SEED: [u8; 16] = [
    0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc, 0xe5,
];

fn benchmark_field<F: DeferredField>(criterion: &mut Criterion, field_name: &str) {
    let mut group = criterion.benchmark_group(format!("{field_name}/deferred-inner-product"));
    let mut rng = XorShiftRng::from_seed(SEED);

    for len in [4, 16, 64] {
        let lhs = (0..len).map(|_| F::random(&mut rng)).collect::<Vec<_>>();
        let rhs = (0..len).map(|_| F::random(&mut rng)).collect::<Vec<_>>();

        group.throughput(Throughput::Elements(len));
        group.bench_with_input(BenchmarkId::from_parameter(len), &len, |bencher, _| {
            bencher.iter(|| {
                let mut accumulator = F::Accumulator::default();
                for (lhs, rhs) in lhs.iter().zip(&rhs) {
                    F::mul_accumulate(&mut accumulator, black_box(lhs), black_box(rhs));
                }
                black_box(F::reduce(accumulator))
            });
        });
    }
}

fn benchmark_deferred(criterion: &mut Criterion) {
    benchmark_field::<Fp>(criterion, "Fp");
    benchmark_field::<Fq>(criterion, "Fq");
}

criterion_group!(benches, benchmark_deferred);
criterion_main!(benches);
