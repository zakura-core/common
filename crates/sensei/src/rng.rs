/// Indicates that a caller-supplied randomness source could not produce a value.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RandomnessError;

/// Cryptographically secure randomness for proofs, signatures, and batch checks.
///
/// Successful calls must return independent, uniformly distributed values from
/// a cryptographically secure random number generator. Predictable or reused
/// values can compromise zero knowledge, expose signing keys, or allow invalid
/// batches to verify. Batch weights must be fresh and independent of all
/// submitted proofs or signatures.
///
/// The source remains caller-owned and is borrowed for each operation. Calls
/// to [`Self::next_u64`] occur on the calling thread, even when proof work uses
/// worker threads; neither [`Send`] nor [`Sync`] is required. No reference to
/// the source is retained after the operation.
///
/// A returned [`RandomnessError`] becomes the consuming API's `RngFailure`
/// error. Panics propagate to the caller instead of becoming `RngFailure`.
/// Errors never restore the source's state: earlier draws remain consumed.
/// The order of validation and sampling depends on the consuming API.
pub trait RandomSource {
    /// Returns the next random value, or an error if one is unavailable.
    fn next_u64(&mut self) -> Result<u64, RandomnessError>;
}

impl<F> RandomSource for F
where
    F: FnMut() -> Result<u64, RandomnessError>,
{
    fn next_u64(&mut self) -> Result<u64, RandomnessError> {
        self()
    }
}

#[cfg(any(feature = "prover", feature = "verifier"))]
pub(crate) fn sample_fp(rng: &mut dyn RandomSource) -> Result<udon::field::Fp, crate::Error> {
    let mut bytes = [0; 64];
    for chunk in bytes.chunks_exact_mut(8) {
        chunk.copy_from_slice(
            &rng.next_u64()
                .map_err(|_| crate::Error::RngFailure)?
                .to_le_bytes(),
        );
    }
    Ok(<udon::field::Fp>::from_bytes_reduced(&bytes))
}

#[cfg(test)]
mod tests {
    use super::{RandomSource, RandomnessError};
    use std::prelude::v1::*;

    #[test]
    fn closures_forward_values_and_errors() {
        let mut values = [Ok(4), Ok(8), Err(RandomnessError)].into_iter();
        let mut source = || values.next().unwrap();

        assert_eq!(source.next_u64(), Ok(4));
        assert_eq!(source.next_u64(), Ok(8));
        assert_eq!(source.next_u64(), Err(RandomnessError));
    }
}
