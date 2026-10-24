use core::fmt;

/// An error from input validation, proof preparation, creation, or verification.
///
/// [`Self::InvalidInput`], [`Self::InvalidStatement`],
/// [`Self::UnsatisfiedWitness`], and [`Self::InvalidProof`] describe rejected
/// inputs; fresh randomness does not repair them. [`Self::RetryRandomness`]
/// requests a retry with fresh draws. [`Self::InternalInvariant`] signals an
/// implementation failure to report.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Error {
    /// The request has an unsupported shape or contains an invalid encoding.
    InvalidInput,
    /// The public statement does not agree with the private witness.
    InvalidStatement,
    /// The private witness does not satisfy the Ironwood Action circuit.
    UnsatisfiedWitness,
    /// The proof does not verify for the supplied statements.
    ///
    /// Includes malformed transcript contents and unusable transcript-derived
    /// challenges: fresh verification weights cannot change that transcript.
    InvalidProof,
    /// The caller-supplied randomness source returned [`crate::RandomnessError`].
    ///
    /// Earlier draws remain consumed. Source panics propagate rather than
    /// becoming this error; see [`crate::RandomSource`].
    RngFailure,
    /// A negligible random event requires retrying with fresh randomness.
    ///
    /// For proving, retry the same request with fresh draws. For proof batch
    /// verification, retry the same batch with fresh weights; its proofs need
    /// not be regenerated. This error does not establish whether the inputs
    /// are valid.
    RetryRandomness,
    /// Sensei encountered an unexpected internal failure.
    ///
    /// Report this as an implementation failure. It is neither a routine
    /// randomness retry nor a conclusion that the input is invalid.
    /// For example, a prepared circuit shape or internal buffer contract failed;
    /// this does not establish a failed statement relation or circuit constraint.
    InternalInvariant,
}

impl fmt::Display for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::InvalidInput => "invalid proof input",
            Self::InvalidStatement => "public statement does not match the witness",
            Self::UnsatisfiedWitness => "witness does not satisfy the fixed circuit",
            Self::InvalidProof => "invalid proof",
            Self::RngFailure => "randomness source failed",
            Self::RetryRandomness => "fresh randomness is required",
            Self::InternalInvariant => "internal proof invariant failed",
        })
    }
}

impl core::error::Error for Error {}
