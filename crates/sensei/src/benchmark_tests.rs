//! Ignored warm-proof probes used by the repository benchmark harness.
//!
//! Every repetition replays its own fixture tape and checks both proof bytes
//! and tape exhaustion. Keep this module test-only: these tapes contain private
//! fixture randomness, and the harness selects these tests by their module path.

use alloc::vec::Vec;
use std::{hint::black_box, time::Instant};

use super::{RandomSource, RandomnessError, create_proof, warm_up};
use crate::test_codec::{FIXTURES, Fixture, decode_iwpr};

/// Timing-probe variant of the shared `test_codec::TapeRng`: the tape is
/// decoded to `u64`s up front so measured repetitions replay it without
/// per-draw byte decoding.
struct ReplayRng<'a> {
    tape: &'a [u64],
    cursor: usize,
}

impl RandomSource for ReplayRng<'_> {
    fn next_u64(&mut self) -> Result<u64, RandomnessError> {
        let value = self.tape.get(self.cursor).copied().ok_or(RandomnessError)?;
        self.cursor += 1;
        Ok(value)
    }
}

#[test]
#[ignore = "manual warm-proof benchmark; run this test alone in a fresh process"]
fn measure_warm_one_action_proof() {
    measure_warm_proof(&FIXTURES[0]);
}

#[test]
#[ignore = "manual warm-proof benchmark; run this test alone in a fresh process"]
fn measure_warm_two_action_proof() {
    measure_warm_proof(&FIXTURES[1]);
}

fn measure_warm_proof(fixture: &Fixture) {
    let request = decode_iwpr(fixture.request).unwrap();
    warm_up();
    let expected_proof = fixture.proof;
    let tape = fixture
        .tape
        .chunks_exact(size_of::<u64>())
        .map(|bytes| u64::from_le_bytes(bytes.try_into().unwrap()))
        .collect::<Vec<_>>();
    assert_eq!(tape.len() * size_of::<u64>(), fixture.tape.len());
    assert_eq!(tape.len(), fixture.rng_words);

    let mut priming_rng = ReplayRng {
        tape: &tape,
        cursor: 0,
    };
    assert_eq!(
        create_proof(&request, &mut priming_rng).unwrap(),
        expected_proof
    );
    assert_eq!(priming_rng.cursor, tape.len());
    crate::native::benchmark_resources();

    let repetitions = std::env::var("SENSEI_BENCH_REPETITIONS")
        .map_or(Ok(1), |value| value.parse::<usize>())
        .expect("SENSEI_BENCH_REPETITIONS must be a positive integer");
    assert!(repetitions > 0);
    for repetition in 0..repetitions {
        let mut measured_rng = ReplayRng {
            tape: &tape,
            cursor: 0,
        };
        let attribute_stages = std::env::var_os("SENSEI_STAGE_TIMING").is_some()
            || std::env::var_os("SENSEI_BENCH_REPETITIONS").is_some();
        if attribute_stages {
            crate::native::stage_timing::enable();
        }
        let started = Instant::now();
        let proof = black_box(create_proof(&request, &mut measured_rng).unwrap());
        let elapsed = started.elapsed();

        let stage_timings = attribute_stages.then(|| {
            crate::native::stage_timing::take().expect("measured proof must record stage timings")
        });
        let quotient_timings = attribute_stages.then(|| {
            crate::native::stage_timing::take_quotient()
                .expect("measured proof must record quotient timings")
        });
        let witness_timings = attribute_stages.then(|| {
            crate::native::stage_timing::take_witness()
                .expect("measured proof must record witness timings")
        });

        assert_eq!(proof, expected_proof);
        assert_eq!(measured_rng.cursor, tape.len());
        eprintln!("SENSEI_T_REPETITION={repetition}");
        eprintln!("SENSEI_T_WARM_NS={}", elapsed.as_nanos());
        if let Some(stage_timings) = stage_timings {
            eprintln!(
                "SENSEI_PIPELINE ipa_early_rounds={}",
                stage_timings.ipa_early_rounds
            );
            let values = format_metric_line(
                crate::native::stage_timing::NAMES
                    .into_iter()
                    .zip(stage_timings.elapsed_ns)
                    .chain(core::iter::once((
                        "product_arguments.prepare",
                        stage_timings.product_prepare_ns,
                    )))
                    .chain(
                        crate::native::stage_timing::IPA_PHASE_NAMES
                            .into_iter()
                            .zip(stage_timings.ipa_ns),
                    ),
            );
            eprintln!("SENSEI_T_STAGE_NS {values}");
        }
        if let Some(quotient_timings) = quotient_timings {
            let [fold, inverse, piece] = quotient_timings.early_consumers;
            eprintln!(
                "SENSEI_PIPELINE early_fold={fold} early_inverse={inverse} early_piece_msm={piece}"
            );
            let values = format_metric_line(
                crate::native::stage_timing::QUOTIENT_NAMES
                    .into_iter()
                    .zip(quotient_timings.elapsed_ns),
            );
            eprintln!(
                "SENSEI_T_QUOTIENT_NS {values} fold_work={}",
                quotient_timings.fold_work_ns
            );
        }
        if let Some(witness_timings) = witness_timings {
            let values = format_metric_line(
                crate::native::stage_timing::WITNESS_NAMES
                    .into_iter()
                    .zip(witness_timings.elapsed_ns),
            );
            eprintln!("SENSEI_T_WITNESS_NS {values}");
        }
    }
}

fn format_metric_line(metrics: impl Iterator<Item = (&'static str, u128)>) -> String {
    metrics
        .map(|(name, elapsed_ns)| format!("{name}={elapsed_ns}"))
        .collect::<Vec<_>>()
        .join(" ")
}
