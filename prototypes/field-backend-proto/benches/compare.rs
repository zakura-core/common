//! Head-to-head comparison of the prototype Fp backends.
//!
//! Everything runs in one binary so measurements are adjacent and share
//! machine state. Field benchmarks run a serial dependency chain (the shape
//! that dominates scalar-multiplication ladders); doubling benchmarks run a
//! serial chain of Jacobian doublings.

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use ff::Field;
use group::Group;
use pasta_curves::{pallas, Fp};

use field_backend_proto::{double_jacobian, mul_ffi, sqr_ffi, to_mont, Limbs, R1};
#[cfg(feature = "v1")]
use field_backend_proto::v1;
#[cfg(feature = "v2")]
use field_backend_proto::v2;
#[cfg(feature = "v3")]
use field_backend_proto::v3;

/// Field-op chain length per measured iteration.
const CHAIN: usize = 512;

fn fp_from(v: u64) -> Fp {
    Fp::from(v)
}

fn sample_mont() -> (Limbs, Limbs) {
    // Fixed, arbitrary canonical values (same for every variant).
    let a = to_mont(&[0x1234_5678_9abc_def0, 0x0fed_cba9_8765_4321, 0x0011_2233_4455_6677, 0x0aab_bccd_deef_f001]);
    let b = to_mont(&[0x0123_4567_89ab_cdef, 0x1122_3344_5566_7788, 0x99aa_bbcc_ddee_ff00, 0x0f00_ba51_1ab5_ba5e]);
    (a, b)
}

fn bench_field_mul(c: &mut Criterion) {
    let mut g = c.benchmark_group("field_mul_serial");
    let (a, b) = sample_mont();

    g.bench_function(BenchmarkId::new("now", "portable_inline"), |bch| {
        // The inherent const-fn portable path used by today's point formulas
        // when the asm feature is off (and by pow chains before PR #65).
        let fa = fp_from(12345);
        let fb = fp_from(67890);
        bch.iter(|| {
            let mut x = fa;
            for _ in 0..CHAIN {
                x = Fp::mul(&x, &fb);
            }
            x
        })
    });

    g.bench_function(BenchmarkId::new("now", "ffi_asm"), |bch| {
        bch.iter(|| {
            let mut x = a;
            for _ in 0..CHAIN {
                x = mul_ffi(&x, &b);
            }
            x
        })
    });

    #[cfg(feature = "v1")]
    g.bench_function(BenchmarkId::new("v1", "sparse_portable"), |bch| {
        bch.iter(|| {
            let mut x = a;
            for _ in 0..CHAIN {
                x = v1::mul(&x, &b);
            }
            x
        })
    });

    #[cfg(feature = "v2")]
    g.bench_function(BenchmarkId::new("v2", "inline_asm"), |bch| {
        bch.iter(|| {
            let mut x = a;
            for _ in 0..CHAIN {
                x = v2::mul(&x, &b);
            }
            x
        })
    });

    g.finish();
}

fn bench_field_sqr(c: &mut Criterion) {
    let mut g = c.benchmark_group("field_sqr_serial");
    let (a, _) = sample_mont();

    g.bench_function(BenchmarkId::new("now", "portable_inline"), |bch| {
        let fa = fp_from(12345);
        bch.iter(|| {
            let mut x = fa;
            for _ in 0..CHAIN {
                x = Fp::square(&x);
            }
            x
        })
    });

    g.bench_function(BenchmarkId::new("now", "ffi_asm"), |bch| {
        bch.iter(|| {
            let mut x = a;
            for _ in 0..CHAIN {
                x = sqr_ffi(&x);
            }
            x
        })
    });

    #[cfg(feature = "v1")]
    g.bench_function(BenchmarkId::new("v1", "sparse_portable"), |bch| {
        bch.iter(|| {
            let mut x = a;
            for _ in 0..CHAIN {
                x = v1::sqr(&x);
            }
            x
        })
    });

    #[cfg(feature = "v2")]
    g.bench_function(BenchmarkId::new("v2", "inline_asm"), |bch| {
        bch.iter(|| {
            let mut x = a;
            for _ in 0..CHAIN {
                x = v2::sqr(&x);
            }
            x
        })
    });

    g.finish();
}

/// Doublings per measured iteration.
const DOUBLES: usize = 128;

fn generator_xyz() -> [u64; 12] {
    use group::prime::PrimeCurveAffine;
    use pasta_curves::arithmetic::CurveAffine;
    use ff::PrimeField;
    let g = pallas::Affine::generator();
    let coords = g.coordinates().unwrap();
    let mut limbs = |f: &Fp| -> Limbs {
        let repr = f.to_repr();
        let mut l = [0u64; 4];
        for i in 0..4 {
            l[i] = u64::from_le_bytes(repr[8 * i..8 * i + 8].try_into().unwrap());
        }
        to_mont(&l)
    };
    let mut xyz = [0u64; 12];
    xyz[0..4].copy_from_slice(&limbs(coords.x()));
    xyz[4..8].copy_from_slice(&limbs(coords.y()));
    xyz[8..12].copy_from_slice(&R1);
    xyz
}

fn bench_double(c: &mut Criterion) {
    let mut g = c.benchmark_group("jacobian_double_serial");
    let xyz0 = generator_xyz();

    g.bench_function(BenchmarkId::new("now", "pasta_point"), |bch| {
        let p = pallas::Point::generator();
        bch.iter(|| {
            let mut q = p;
            for _ in 0..DOUBLES {
                q = q.double();
            }
            q
        })
    });

    g.bench_function(BenchmarkId::new("now", "ffi_asm_composed"), |bch| {
        bch.iter(|| {
            let mut xyz = xyz0;
            let (mut x, mut y, mut z): (Limbs, Limbs, Limbs) = (
                xyz[0..4].try_into().unwrap(),
                xyz[4..8].try_into().unwrap(),
                xyz[8..12].try_into().unwrap(),
            );
            for _ in 0..DOUBLES {
                double_jacobian(&mut x, &mut y, &mut z, mul_ffi, sqr_ffi);
            }
            xyz[0..4].copy_from_slice(&x);
            xyz
        })
    });

    #[cfg(feature = "v1")]
    g.bench_function(BenchmarkId::new("v1", "sparse_composed"), |bch| {
        bch.iter(|| {
            let mut xyz = xyz0;
            let (mut x, mut y, mut z): (Limbs, Limbs, Limbs) = (
                xyz[0..4].try_into().unwrap(),
                xyz[4..8].try_into().unwrap(),
                xyz[8..12].try_into().unwrap(),
            );
            for _ in 0..DOUBLES {
                double_jacobian(&mut x, &mut y, &mut z, v1::mul, v1::sqr);
            }
            xyz[0..4].copy_from_slice(&x);
            xyz
        })
    });

    #[cfg(feature = "v2")]
    g.bench_function(BenchmarkId::new("v2", "inline_asm_composed"), |bch| {
        bch.iter(|| {
            let mut xyz = xyz0;
            let (mut x, mut y, mut z): (Limbs, Limbs, Limbs) = (
                xyz[0..4].try_into().unwrap(),
                xyz[4..8].try_into().unwrap(),
                xyz[8..12].try_into().unwrap(),
            );
            for _ in 0..DOUBLES {
                double_jacobian(&mut x, &mut y, &mut z, v2::mul, v2::sqr);
            }
            xyz[0..4].copy_from_slice(&x);
            xyz
        })
    });

    #[cfg(feature = "v3")]
    g.bench_function(BenchmarkId::new("v3", "fused_asm_n1_calls"), |bch| {
        // One FFI call per doubling: the ladder's worst case (no runs).
        bch.iter(|| {
            let mut xyz = xyz0;
            for _ in 0..DOUBLES {
                v3::double_n(&mut xyz, 1);
            }
            xyz
        })
    });

    #[cfg(feature = "v3")]
    g.bench_function(BenchmarkId::new("v3", "fused_asm_one_call"), |bch| {
        // A single fused call: the fully-amortized bound.
        bch.iter(|| {
            let mut xyz = xyz0;
            v3::double_n(&mut xyz, DOUBLES);
            xyz
        })
    });

    g.finish();
}

criterion_group!(benches, bench_field_mul, bench_field_sqr, bench_double);
criterion_main!(benches);
