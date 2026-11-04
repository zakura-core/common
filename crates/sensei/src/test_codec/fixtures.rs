//! Committed unit fixture corpus and frozen proof/RNG expectations.

/// One committed fixture: the IWPR request, its private RNG tape, the
/// independent proof oracle, and the frozen tape length in `u64` words.
/// Test-only material — never logged, never reused as real proving randomness.
pub(crate) struct Fixture {
    pub(crate) actions: usize,
    pub(crate) request: &'static [u8],
    pub(crate) tape: &'static [u8],
    pub(crate) proof: &'static [u8],
    pub(crate) rng_words: usize,
}

/// The committed fixture corpus with its frozen RNG consumption schedule
/// (1,552 `u64`s for one Action, 2,736 for two). Every in-crate consumer
/// shares this table; only the public-API golden harness keeps its own
/// deliberately independent copy.
pub(crate) const FIXTURES: [Fixture; 2] = [
    Fixture {
        actions: 1,
        request: include_bytes!("../../tests/fixtures/one-action.iwpr"),
        tape: include_bytes!("../../tests/fixtures/golden/one-action.rng-u64s-le"),
        proof: include_bytes!("../../tests/fixtures/golden/one-action.proof"),
        rng_words: 1_552,
    },
    Fixture {
        actions: 2,
        request: include_bytes!("../../tests/fixtures/two-action.iwpr"),
        tape: include_bytes!("../../tests/fixtures/golden/two-action.rng-u64s-le"),
        proof: include_bytes!("../../tests/fixtures/golden/two-action.proof"),
        rng_words: 2_736,
    },
];
