///! Benchmarks for the Fp field.
use criterion::{criterion_group, criterion_main, Bencher, Criterion};

use rand::SeedableRng;
use rand_xorshift::XorShiftRng;

use ff::{Field, PrimeField};
use pasta_curves::Fp;

fn criterion_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("Fp");

    group.bench_function("double", bench_fp_double);
    group.bench_function("add_assign", bench_fp_add_assign);
    group.bench_function("sub_assign", bench_fp_sub_assign);
    group.bench_function("mul_assign", bench_fp_mul_assign);
    group.bench_function("square", bench_fp_square);
    group.bench_function("invert", bench_fp_invert);
    group.bench_function("neg", bench_fp_neg);
    group.bench_function("sqrt", bench_fp_sqrt);
    group.bench_function("to_repr", bench_fp_to_repr);
    group.bench_function("from_repr", bench_fp_from_repr);
    group.bench_function("mul_chain/64", bench_fp_mul_chain);
    group.bench_function("mul_indep/4", bench_fp_mul_indep_4);
    group.bench_function("mul_indep/8", bench_fp_mul_indep_8);
    group.bench_function("square_chain/64", bench_fp_square_chain);
    group.bench_function("add_chain/64", bench_fp_add_chain);
    group.bench_function("pow_vartime_p_minus_2", bench_fp_pow_vartime_p_minus_2);
}

fn bench_fp_double(b: &mut Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<Fp> = (0..SAMPLES).map(|_| Fp::random(&mut rng)).collect();

    let mut count = 0;
    b.iter(|| {
        let mut tmp = v[count];
        tmp = tmp.double();
        count = (count + 1) % SAMPLES;
        tmp
    });
}

fn bench_fp_add_assign(b: &mut Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<(Fp, Fp)> = (0..SAMPLES)
        .map(|_| (Fp::random(&mut rng), Fp::random(&mut rng)))
        .collect();

    let mut count = 0;
    b.iter(|| {
        let mut tmp = v[count].0;
        tmp += &v[count].1;
        count = (count + 1) % SAMPLES;
        tmp
    });
}

fn bench_fp_sub_assign(b: &mut Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<(Fp, Fp)> = (0..SAMPLES)
        .map(|_| (Fp::random(&mut rng), Fp::random(&mut rng)))
        .collect();

    let mut count = 0;
    b.iter(|| {
        let mut tmp = v[count].0;
        tmp -= &v[count].1;
        count = (count + 1) % SAMPLES;
        tmp
    });
}

fn bench_fp_mul_assign(b: &mut Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<(Fp, Fp)> = (0..SAMPLES)
        .map(|_| (Fp::random(&mut rng), Fp::random(&mut rng)))
        .collect();

    let mut count = 0;
    b.iter(|| {
        let mut tmp = v[count].0;
        tmp *= &v[count].1;
        count = (count + 1) % SAMPLES;
        tmp
    });
}

fn bench_fp_square(b: &mut Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<Fp> = (0..SAMPLES).map(|_| Fp::random(&mut rng)).collect();

    let mut count = 0;
    b.iter(|| {
        let mut tmp = v[count];
        tmp = tmp.square();
        count = (count + 1) % SAMPLES;
        tmp
    });
}

fn bench_fp_invert(b: &mut Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<Fp> = (0..SAMPLES).map(|_| Fp::random(&mut rng)).collect();

    // The unit-test instrumentation is compiled out of bench builds; sanity-
    // check the production codegen of the divstep inversion once per run.
    assert_eq!(v[0] * v[0].invert().unwrap(), Fp::ONE);

    let mut count = 0;
    b.iter(|| {
        count = (count + 1) % SAMPLES;
        v[count].invert()
    });
}

fn bench_fp_neg(b: &mut Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<Fp> = (0..SAMPLES).map(|_| Fp::random(&mut rng)).collect();

    let mut count = 0;
    b.iter(|| {
        let mut tmp = v[count];
        tmp = tmp.neg();
        count = (count + 1) % SAMPLES;
        tmp
    });
}

fn bench_fp_sqrt(b: &mut Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<Fp> = (0..SAMPLES)
        .map(|_| {
            let tmp = Fp::random(&mut rng);
            tmp.square()
        })
        .collect();

    let mut count = 0;
    b.iter(|| {
        count = (count + 1) % SAMPLES;
        v[count].sqrt()
    });
}

fn bench_fp_to_repr(b: &mut Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<Fp> = (0..SAMPLES).map(|_| Fp::random(&mut rng)).collect();

    let mut count = 0;
    b.iter(|| {
        count = (count + 1) % SAMPLES;
        v[count].to_repr()
    });
}

fn bench_fp_from_repr(b: &mut Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<<Fp as PrimeField>::Repr> = (0..SAMPLES)
        .map(|_| Fp::random(&mut rng).to_repr())
        .collect();

    let mut count = 0;
    b.iter(|| {
        count = (count + 1) % SAMPLES;
        Fp::from_repr(v[count])
    });
}

/// 64 data-dependent multiplications per iteration: each product feeds the
/// next, so this isolates multiplication latency (where serial reduction
/// rounds hurt) rather than throughput.
fn bench_fp_mul_chain(b: &mut Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<Fp> = (0..SAMPLES).map(|_| Fp::random(&mut rng)).collect();
    let chain: Vec<Fp> = (0..64).map(|_| Fp::random(&mut rng)).collect();

    let mut count = 0;
    b.iter(|| {
        let mut tmp = v[count];
        for x in &chain {
            tmp *= x;
        }
        count = (count + 1) % SAMPLES;
        tmp
    });
}

/// Four independent multiplications per iteration (no product feeds another):
/// exposes how much instruction-level parallelism the representation allows.
fn bench_fp_mul_indep_4(b: &mut Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<(Fp, Fp)> = (0..SAMPLES)
        .map(|_| (Fp::random(&mut rng), Fp::random(&mut rng)))
        .collect();

    let mut count = 0;
    b.iter(|| {
        let i = count * 4;
        let r0 = v[i].0 * v[i].1;
        let r1 = v[i + 1].0 * v[i + 1].1;
        let r2 = v[i + 2].0 * v[i + 2].1;
        let r3 = v[i + 3].0 * v[i + 3].1;
        count = (count + 1) % (SAMPLES / 4);
        [r0, r1, r2, r3]
    });
}

/// Eight independent multiplications per iteration.
fn bench_fp_mul_indep_8(b: &mut Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<(Fp, Fp)> = (0..SAMPLES)
        .map(|_| (Fp::random(&mut rng), Fp::random(&mut rng)))
        .collect();

    let mut count = 0;
    b.iter(|| {
        let i = count * 8;
        let r0 = v[i].0 * v[i].1;
        let r1 = v[i + 1].0 * v[i + 1].1;
        let r2 = v[i + 2].0 * v[i + 2].1;
        let r3 = v[i + 3].0 * v[i + 3].1;
        let r4 = v[i + 4].0 * v[i + 4].1;
        let r5 = v[i + 5].0 * v[i + 5].1;
        let r6 = v[i + 6].0 * v[i + 6].1;
        let r7 = v[i + 7].0 * v[i + 7].1;
        count = (count + 1) % (SAMPLES / 8);
        [r0, r1, r2, r3, r4, r5, r6, r7]
    });
}

/// 64 data-dependent squarings per iteration: squaring latency, the risk case
/// where raw multiplication gets cheaper but reduction stays the same.
fn bench_fp_square_chain(b: &mut Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<Fp> = (0..SAMPLES).map(|_| Fp::random(&mut rng)).collect();

    let mut count = 0;
    b.iter(|| {
        let mut tmp = v[count];
        for _ in 0..64 {
            tmp = tmp.square();
        }
        count = (count + 1) % SAMPLES;
        tmp
    });
}

/// 64 data-dependent additions per iteration: isolates the per-add
/// normalization cost (modulus subtraction vs. lattice correction).
fn bench_fp_add_chain(b: &mut Bencher) {
    const SAMPLES: usize = 1000;

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<Fp> = (0..SAMPLES).map(|_| Fp::random(&mut rng)).collect();
    let chain: Vec<Fp> = (0..64).map(|_| Fp::random(&mut rng)).collect();

    let mut count = 0;
    b.iter(|| {
        let mut tmp = v[count];
        for x in &chain {
            tmp += x;
        }
        count = (count + 1) % SAMPLES;
        tmp
    });
}

/// `pow_vartime` with the Fermat exponent `p - 2`: ~250 squarings fused into
/// `sqr_n_mul` runs plus ~125 multiplications — the real exponentiation-chain
/// workload behind sqrt-style addition chains, and the cost floor of a
/// Fermat inversion.
fn bench_fp_pow_vartime_p_minus_2(b: &mut Bencher) {
    const SAMPLES: usize = 1000;

    /// p - 2, little-endian limbs.
    const EXP: [u64; 4] = [
        0x992d30ecffffffff,
        0x224698fc094cf91b,
        0x0000000000000000,
        0x4000000000000000,
    ];

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let v: Vec<Fp> = (0..SAMPLES).map(|_| Fp::random(&mut rng)).collect();

    let mut count = 0;
    b.iter(|| {
        count = (count + 1) % SAMPLES;
        v[count].pow_vartime(EXP)
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
