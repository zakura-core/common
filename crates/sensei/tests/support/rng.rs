//! Deterministic randomness for verifier batch tests.

use zakura_sensei::{RandomSource, RandomnessError};

/// A reproducible SplitMix64 generator for verifier batch tests.
///
/// This is not a cryptographically secure randomness source. Use it only with
/// synthetic test data.
pub struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    pub fn new(seed: u64) -> Self {
        Self { state: seed }
    }
}

impl RandomSource for SplitMix64 {
    fn next_u64(&mut self) -> Result<u64, RandomnessError> {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut output = self.state;
        output = (output ^ (output >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        output = (output ^ (output >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        Ok(output ^ (output >> 31))
    }
}
