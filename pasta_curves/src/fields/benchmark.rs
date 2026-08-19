//! Manual microbenchmarks for private field backend operations.

use std::hint::black_box;
use std::time::Instant;
use std::vec::Vec;

use super::{DifferenceOfProducts, Fp, Fq};

const ITERATIONS: usize = 1_000_000;
const SAMPLES: usize = 15;
const WARMUPS: usize = 3;

fn measure_eager<F: DifferenceOfProducts>(a: F, b: F, c: F, d: F) -> u128 {
    let start = Instant::now();
    let mut output = F::ZERO;
    for _ in 0..ITERATIONS {
        output = black_box(black_box(a) * black_box(b) - black_box(c) * black_box(d));
    }
    black_box(output);
    start.elapsed().as_nanos()
}

fn measure_fused<F: DifferenceOfProducts>(a: F, b: F, c: F, d: F) -> u128 {
    let start = Instant::now();
    let mut output = F::ZERO;
    for _ in 0..ITERATIONS {
        output = black_box(F::difference_of_products(
            black_box(a),
            black_box(b),
            black_box(c),
            black_box(d),
        ));
    }
    black_box(output);
    start.elapsed().as_nanos()
}

fn samples<F: DifferenceOfProducts>(
    measure: fn(F, F, F, F) -> u128,
    a: F,
    b: F,
    c: F,
    d: F,
) -> Vec<u128> {
    (0..SAMPLES).map(|_| measure(a, b, c, d)).collect()
}

fn benchmark<F: DifferenceOfProducts>(label: &str, a: F, b: F, c: F, d: F) {
    assert!(
        a * b - c * d == F::difference_of_products(a, b, c, d),
        "benchmark implementations differ"
    );

    for _ in 0..WARMUPS {
        black_box(measure_eager(a, b, c, d));
        black_box(measure_fused(a, b, c, d));
    }

    let eager_1 = samples(measure_eager::<F>, a, b, c, d);
    let fused_1 = samples(measure_fused::<F>, a, b, c, d);
    let fused_2 = samples(measure_fused::<F>, a, b, c, d);
    let eager_2 = samples(measure_eager::<F>, a, b, c, d);

    println!("PRODUCT_DIFFERENCE field={label} iterations={ITERATIONS} eager_1={eager_1:?}");
    println!("PRODUCT_DIFFERENCE field={label} iterations={ITERATIONS} fused_1={fused_1:?}");
    println!("PRODUCT_DIFFERENCE field={label} iterations={ITERATIONS} fused_2={fused_2:?}");
    println!("PRODUCT_DIFFERENCE field={label} iterations={ITERATIONS} eager_2={eager_2:?}");
}

#[test]
#[ignore = "manual single-core performance benchmark"]
fn difference_of_products() {
    benchmark(
        "Fp",
        Fp::from_raw([1, 2, 3, 4]),
        Fp::from_raw([5, 6, 7, 8]),
        Fp::from_raw([9, 10, 11, 12]),
        Fp::from_raw([13, 14, 15, 16]),
    );
    benchmark(
        "Fq",
        Fq::from_raw([17, 18, 19, 20]),
        Fq::from_raw([21, 22, 23, 24]),
        Fq::from_raw([25, 26, 27, 28]),
        Fq::from_raw([29, 30, 31, 32]),
    );
}
