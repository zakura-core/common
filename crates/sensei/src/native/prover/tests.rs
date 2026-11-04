//! Stage-specific differential checks and independent prover references.
//!
//! Shared setup is limited to the fixture bytes and their randomness replay.

use alloc::vec::Vec;

use self::lookup::lookup_commitment_fixtures;

mod allocation;
mod ipa;
mod lookup;
mod lookup_compression;
mod opening;
mod prefix;
mod products;
mod quotient;

const ONE_ACTION_FIXTURE: &[u8] = crate::test_codec::FIXTURES[0].request;
const TWO_ACTION_FIXTURE: &[u8] = crate::test_codec::FIXTURES[1].request;

/// Draws the full labeled randomness schedule from a committed golden
/// tape, for tests that drive individual prover stages.
fn randomness_from_tape(
    tape_bytes: &[u8],
    action_count: usize,
) -> crate::native::randomness::ProvingRandomness {
    struct Replay<'a> {
        tape: &'a [u64],
        cursor: usize,
    }
    impl crate::RandomSource for Replay<'_> {
        fn next_u64(&mut self) -> Result<u64, crate::RandomnessError> {
            let value = self
                .tape
                .get(self.cursor)
                .copied()
                .ok_or(crate::RandomnessError)?;
            self.cursor += 1;
            Ok(value)
        }
    }
    let tape = tape_bytes
        .chunks_exact(8)
        .map(|bytes| u64::from_le_bytes(bytes.try_into().unwrap()))
        .collect::<Vec<_>>();
    let mut rng = Replay {
        tape: &tape,
        cursor: 0,
    };
    let randomness =
        crate::native::randomness::ProvingRandomness::sample(&mut rng, action_count).unwrap();
    assert_eq!(rng.cursor, tape.len());
    randomness
}

// Keep the actual benchmark registration at its established libtest path.
#[test]
#[ignore = "manual lookup recipe benchmark and support census"]
fn measure_lookup_commitment_recipes() {
    use crate::resource_tests::PoolExecutor;
    use udon::exec::TaskBudget;

    let workers =
        std::env::var("SENSEI_BENCH_WORKERS").map_or(16, |value| value.parse::<usize>().unwrap());
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(workers)
        .build()
        .unwrap();
    let executor = PoolExecutor(&pool);
    let execution =
        crate::native::worker::Execution::new(&executor, TaskBudget::new(workers).unwrap());
    pool.install(|| lookup_commitment_fixtures(None, true, execution));
}
