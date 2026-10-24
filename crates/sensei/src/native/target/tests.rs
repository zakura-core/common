//! Target contract tests, grouped by the invariant they check.
//!
//! Artifact pins and representation checks retain their independent expectations;
//! layout censuses, instance/domain transforms, and commitment equivalence live
//! in their own children. The ignored preparation benchmarks stay here to keep
//! their existing libtest paths and printed measurement tokens.

mod artifacts;
mod commitments;
mod instance;
mod layout;
mod representation;

use std::{hint::black_box, time::Instant};

use crate::native::field::Fp;

use super::{BLINDING_FACTORS, FixedTarget, N, boundary_polynomial};

/// Measures explicit preparation, including FFT and fixed-base tables.
#[test]
#[ignore = "manual preparation benchmark"]
fn measure_target_initialization() {
    let started = Instant::now();
    black_box(
        FixedTarget::build(
            crate::native::srs::PreparedSrs::fresh_for_test(),
            crate::test_codec::execution(),
        )
        .unwrap(),
    );
    eprintln!("SENSEI_T_INIT_NS={}", started.elapsed().as_nanos());
}

#[test]
#[ignore = "manual boundary preparation benchmark"]
fn measure_boundary_derivation() {
    for _ in 0..10 {
        let started = Instant::now();
        black_box(super::Boundaries::derive().unwrap());
        eprintln!("SENSEI_BOUNDARY_DIRECT_NS={}", started.elapsed().as_nanos());
        let started = Instant::now();
        let l_0 = boundary_polynomial([0]).unwrap();
        let l_last = boundary_polynomial([super::USABLE_ROWS_END]).unwrap();
        let mut active = boundary_polynomial((N - BLINDING_FACTORS)..N).unwrap();
        for (value, last) in active.iter_mut().zip(&l_last) {
            *value = <Fp>::ONE.sub(&last.add(value));
        }
        black_box((l_0, l_last, active));
        eprintln!("SENSEI_BOUNDARY_FFT_NS={}", started.elapsed().as_nanos());
    }
}
