//! Measures complete CPU solver runs for four fixed nonces.
//!
//! Run with `cargo bench -p zakura-equihash --features solver --bench solver`.
//! Pass `-- --once` to collect one sample for interleaved control/candidate
//! measurements. Construction, solving, compression, and cleanup are timed;
//! solution verification and fingerprints are computed outside the timer.

use std::{hint::black_box, time::Instant};

const INPUT: &[u8] = b"Equihash is an asymmetric PoW based on the Generalised Birthday problem.";
const N: u32 = 200;
const K: u32 = 9;

fn main() {
    let samples = if std::env::args().any(|arg| arg == "--once") {
        1
    } else {
        7
    };
    println!("sample,nonce,elapsed_ns,solutions,fingerprint");
    for sample in 0..samples {
        for nonce_index in 0..4u32 {
            let mut nonce = [0u8; 32];
            nonce[..4].copy_from_slice(&nonce_index.to_le_bytes());
            let mut next_nonce = Some(nonce);
            let start = Instant::now();
            let solutions = equihash::tromp::solve_200_9(black_box(INPUT), || next_nonce.take());
            let elapsed = start.elapsed().as_nanos();
            let mut fingerprint = blake2b_simd::State::new();
            for solution in &solutions {
                equihash::is_valid_solution(N, K, INPUT, &nonce, solution)
                    .expect("solver returned an invalid solution");
                fingerprint.update(solution);
            }
            println!(
                "{sample},{nonce_index},{elapsed},{},{}",
                solutions.len(),
                hex::encode(fingerprint.finalize().as_bytes()),
            );
        }
    }
}
