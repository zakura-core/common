//! Measures `is_valid_solution` on a Zcash mainnet block header.
//!
//! Run with `cargo bench -p zakura-equihash --bench verify`. Pass `-- --once`
//! to collect one sample for interleaved control/candidate measurements.

use std::{hint::black_box, time::Instant};

include!("../src/test_vectors/zcash.rs");

const VERIFICATIONS: u32 = 2_000;

fn main() {
    let header = hex::decode(MAINNET_415000_HEADER).unwrap();
    let nonce = hex::decode(MAINNET_415000_NONCE).unwrap();
    let solution = hex::decode(MAINNET_415000_SOLUTION).unwrap();
    let mut invalid = solution.clone();
    // Changes one index, so an early collision check fails.
    invalid[700] ^= 1;

    let samples = if std::env::args().any(|arg| arg == "--once") {
        1
    } else {
        15
    };
    let verify = |solution: &[u8]| {
        equihash::is_valid_solution(200, 9, black_box(&header), &nonce, black_box(solution))
    };
    verify(&solution).expect("block 415000 is valid");
    verify(&invalid).expect_err("mutated solution is invalid");

    println!("sample,case,ns_per_verification");
    for sample in 0..samples {
        for (case, solution) in [("valid", &solution), ("invalid", &invalid)] {
            let start = Instant::now();
            for _ in 0..VERIFICATIONS {
                let _ = black_box(verify(solution));
            }
            let elapsed = start.elapsed().as_nanos() / u128::from(VERIFICATIONS);
            println!("{sample},{case},{elapsed}");
        }
    }
}
