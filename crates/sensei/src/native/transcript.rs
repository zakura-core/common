//! Pinned transcript and proof-byte encoding for the fixed target.
//!
//! This implements the historical `halo2-blake2b-transcript-v1` transcript and
//! `halo2-blake2b-write-v1` proof encoding without introducing a Halo 2
//! dependency. Blake2b-512 is personalized with `Halo2-Transcript`, and the
//! scalar, point, and challenge domain prefixes below are absorbed in
//! production order.
//!
//! Common and proof points are absorbed as canonical affine `x || y`; proof
//! points are separately emitted in the 32-byte compressed format. Scalars are
//! absorbed as canonical 32-byte representations; only proof scalars are also
//! emitted. A challenge squeeze absorbs its prefix, finalizes a clone of the
//! hash state, and reduces the 64-byte digest into [`Fp`] without reabsorbing the
//! challenge.
//!
//! The [transcript correspondence](super::protocol#transcript-correspondence)
//! identifies common inputs, version-specific key and instance selection, and
//! proof messages. The verifier reader rejects truncation and requires complete
//! consumption of the slice it receives. Before that reader is constructed,
//! `crate::VerificationRequest::new` rejects a short proof for every version and
//! rejects trailing bytes for NU6.2 and later. For historical pre-NU6.2 proofs,
//! it instead lends only the expected prefix to the reader, leaving any suffix
//! ignored without changing the caller's bytes.
//!
//! The prover stages drive this exact challenge order:
//!
//! ```text
//! theta, beta, gamma, y, x, x_1, x_2, x_3, x_4, xi, z, u_0 ... u_10
//! ```
//!
//! Committed RNG tapes and proof bytes freeze these rules together with the
//! exact blinding-draw order for the golden corpus.

#[cfg(any(test, feature = "prover"))]
use alloc::vec::Vec;
use blake2b_simd::{Params as Blake2bParams, State as Blake2bState};

use super::{
    curve::VestaPoint,
    field::{Fp, PastaField},
};

// Protocol facts: the transcript's domain-separation prefixes, pinned by the
// golden proofs.
const PREFIX_CHALLENGE: u8 = 0;
const PREFIX_POINT: u8 = 1;
const PREFIX_SCALAR: u8 = 2;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TranscriptError {
    IdentityPoint,
}

/// The fixed `halo2-blake2b-write-v1` transcript used by the target.
pub(crate) struct Transcript {
    state: Blake2bState,
    #[cfg(any(test, feature = "prover"))]
    proof: Vec<u8>,
}

impl Transcript {
    /// A transcript whose proof buffer is reserved once, up front. The
    /// buffer is sized: construction declares the complete proof extent.
    pub(crate) fn with_proof_capacity(proof_capacity: usize) -> Self {
        #[cfg(not(any(test, feature = "prover")))]
        let _ = proof_capacity;
        Self {
            state: Blake2bParams::new()
                .hash_length(64)
                .personal(b"Halo2-Transcript")
                .to_state(),
            #[cfg(any(test, feature = "prover"))]
            proof: Vec::with_capacity(proof_capacity),
        }
    }

    /// Absorbs a common point without emitting proof bytes.
    pub(crate) fn common_point(&mut self, point: &VestaPoint) -> Result<(), TranscriptError> {
        self.absorb_point(point)
    }

    /// Absorbs a proof point and emits its production compressed encoding.
    ///
    /// The coordinates are serialized once: the absorbed uncompressed
    /// `x || y` bytes also provide the compressed emission (`x` with the
    /// parity of `y` in the top bit, which is always clear in a canonical
    /// sub-2^255 encoding).
    #[cfg(any(test, feature = "prover"))]
    pub(crate) fn write_point(&mut self, point: &VestaPoint) -> Result<(), TranscriptError> {
        let Some((x, y)) = point.coordinates() else {
            return Err(TranscriptError::IdentityPoint);
        };
        let x_bytes = x.to_bytes();
        let y_bytes = y.to_bytes();
        self.state.update(&[PREFIX_POINT]);
        self.state.update(&x_bytes);
        self.state.update(&y_bytes);
        let mut compressed = x_bytes;
        compressed[31] |= (y_bytes[0] & 1) << 7;
        self.proof.extend_from_slice(&compressed);
        Ok(())
    }

    /// Absorbs a common scalar without emitting proof bytes.
    pub(crate) fn common_scalar(&mut self, scalar: &Fp) {
        self.absorb_scalar(scalar);
    }

    /// Absorbs and emits a canonical scalar, serialized once.
    #[cfg(any(test, feature = "prover"))]
    pub(crate) fn write_scalar(&mut self, scalar: &Fp) {
        let bytes = scalar.to_bytes();
        self.state.update(&[PREFIX_SCALAR]);
        self.state.update(&bytes);
        self.proof.extend_from_slice(&bytes);
    }

    /// Domain-separates and derives a challenge without reabsorbing it.
    pub(crate) fn squeeze_challenge(&mut self) -> Fp {
        self.state.update(&[PREFIX_CHALLENGE]);
        let digest = self.state.clone().finalize();
        PastaField::from_bytes_reduced(digest.as_bytes())
    }

    #[cfg(test)]
    pub(crate) fn proof(&self) -> &[u8] {
        &self.proof
    }

    /// Consumes the transcript, returning the proof bytes without a copy.
    #[cfg(feature = "prover")]
    pub(crate) fn into_proof(self) -> Vec<u8> {
        self.proof
    }

    fn absorb_point(&mut self, point: &VestaPoint) -> Result<(), TranscriptError> {
        let Some((x, y)) = point.coordinates() else {
            return Err(TranscriptError::IdentityPoint);
        };
        self.state.update(&[PREFIX_POINT]);
        self.state.update(&x.to_bytes());
        self.state.update(&y.to_bytes());
        Ok(())
    }

    fn absorb_scalar(&mut self, scalar: &Fp) {
        self.state.update(&[PREFIX_SCALAR]);
        self.state.update(&scalar.to_bytes());
    }
}

/// Borrowed, checked reader using exactly the writer's common-input hashing.
/// The writer's zero-capacity output remains empty, so this allocates no buffer.
#[cfg(feature = "verifier")]
pub(crate) struct Reader<'a> {
    transcript: Transcript,
    remaining: &'a [u8],
    #[cfg(test)]
    pub(crate) challenges: Vec<[u8; 32]>,
}
#[cfg(feature = "verifier")]
impl<'a> Reader<'a> {
    pub(crate) fn new(proof: &'a [u8]) -> Self {
        Self {
            transcript: Transcript::with_proof_capacity(0),
            remaining: proof,
            #[cfg(test)]
            challenges: Vec::new(),
        }
    }
    pub(crate) fn common_scalar(&mut self, scalar: &Fp) {
        self.transcript.common_scalar(scalar);
    }
    pub(crate) fn common_point(&mut self, point: &VestaPoint) -> Result<(), crate::Error> {
        // Even a common point reconstructed from statements belongs to this
        // fixed verification transcript; new batch weights cannot repair it.
        self.transcript
            .common_point(point)
            .map_err(|_| crate::Error::InvalidProof)
    }
    fn encoding(&mut self) -> Result<[u8; 32], crate::Error> {
        let (bytes, rest) = self
            .remaining
            .split_at_checked(32)
            .ok_or(crate::Error::InvalidProof)?;
        self.remaining = rest;
        Ok(bytes.try_into().expect("fixed encoding width"))
    }
    pub(crate) fn point(&mut self) -> Result<super::curve::VestaAffine, crate::Error> {
        let point = VestaPoint::from_bytes(self.encoding()?).ok_or(crate::Error::InvalidProof)?;
        self.common_point(&point)?;
        point.as_affine().copied().ok_or(crate::Error::InvalidProof)
    }
    pub(crate) fn scalar(&mut self) -> Result<Fp, crate::Error> {
        let value = Fp::from_bytes(self.encoding()?).ok_or(crate::Error::InvalidProof)?;
        self.common_scalar(&value);
        Ok(value)
    }
    pub(crate) fn scalars<const N: usize>(&mut self) -> Result<[Fp; N], crate::Error> {
        let mut values = [Fp::ZERO; N];
        for value in &mut values {
            *value = self.scalar()?;
        }
        Ok(values)
    }
    pub(crate) fn challenge(&mut self) -> Fp {
        let challenge = self.transcript.squeeze_challenge();
        #[cfg(test)]
        self.challenges.push(challenge.to_bytes());
        challenge
    }
    pub(crate) fn finish(self) -> Result<(), crate::Error> {
        if self.remaining.is_empty() {
            Ok(())
        } else {
            Err(crate::Error::InvalidProof)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Transcript, TranscriptError};
    use crate::native::{curve::VestaPoint, field::Fp};
    use std::prelude::v1::*;

    #[test]
    fn transcript_is_deterministic_and_domain_separated() {
        fn exercise(common_scalar: u64) -> ([u8; 32], [u8; 32], Vec<u8>) {
            let generator = VestaPoint::GENERATOR;
            let mut transcript = Transcript::with_proof_capacity(96);
            transcript
                .common_point(&generator.mul_projective(&<Fp>::from_u64(2)).to_point())
                .unwrap();
            transcript.common_scalar(&<Fp>::from_u64(common_scalar));
            transcript
                .write_point(&generator.mul_projective(&<Fp>::from_u64(3)).to_point())
                .unwrap();
            transcript.write_scalar(&<Fp>::from_u64(11));
            let first = transcript.squeeze_challenge().to_bytes();
            transcript
                .write_point(&generator.mul_projective(&<Fp>::from_u64(5)).to_point())
                .unwrap();
            let second = transcript.squeeze_challenge().to_bytes();
            (first, second, transcript.proof().to_vec())
        }

        assert_eq!(exercise(7), exercise(7));
        assert_ne!(exercise(7).0, exercise(13).0);
    }

    #[test]
    fn common_values_do_not_enter_proof_and_writes_are_canonical() {
        let generator = VestaPoint::GENERATOR;
        let scalar = <Fp>::from_u64(19);
        let mut transcript = Transcript::with_proof_capacity(96);
        transcript.common_point(&generator).unwrap();
        transcript.common_scalar(&scalar);
        assert!(transcript.proof().is_empty());

        transcript.write_point(&generator).unwrap();
        transcript.write_scalar(&scalar);
        assert_eq!(transcript.proof().len(), 64);
        assert_eq!(&transcript.proof()[..32], &generator.to_bytes());
        assert_eq!(&transcript.proof()[32..], &scalar.to_bytes());
    }

    #[test]
    fn identity_points_fail_without_emitting_proof_bytes() {
        let mut transcript = Transcript::with_proof_capacity(96);
        assert_eq!(
            transcript.common_point(&VestaPoint::IDENTITY),
            Err(TranscriptError::IdentityPoint)
        );
        assert_eq!(
            transcript.write_point(&VestaPoint::IDENTITY),
            Err(TranscriptError::IdentityPoint)
        );
        assert!(transcript.proof().is_empty());
    }
}
