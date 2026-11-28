use blake2b_simd::Hash as Blake2bHash;
use core::fmt;

use super::{
    Authorization, TransactionData, TxDigests, TxVersion, sighash_v4::v4_signature_hash,
    sighash_v5::v5_signature_hash, sighash_v7::v7_signature_hash, v7,
};
use ::sapling::bundle::GrothProofBytes;

use super::sighash_v6::v6_signature_hash;

/// The signature whose digest is being computed.
pub enum SignableInput<'a> {
    /// A Sapling or Orchard signature in a transaction before v7, which signs the
    /// transaction-wide digest with `SIGHASH_ALL`.
    Shielded,
    /// A signature on a transparent input.
    Transparent(transparent::sighash::SignableInput<'a>),
    /// A Sapling, Orchard, or Ironwood signature in a v7 transaction, which commits to the
    /// bundle containing it and to its position there.
    V7Shielded {
        /// The bundle containing the signature.
        bundle_type: v7::ShieldedBundleType,
        /// Which signature in the bundle it is.
        signature: v7::ShieldedSignature,
    },
}

impl SignableInput<'_> {
    pub fn hash_type(&self) -> u8 {
        match self {
            SignableInput::Shielded | SignableInput::V7Shielded { .. } => {
                ::transparent::sighash::SIGHASH_ALL
            }
            SignableInput::Transparent(input) => input.hash_type().encode(),
        }
    }
}

/// An error in computing a signature digest.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum SighashError {
    /// The signable input describes a signature of another transaction version: a
    /// [`SignableInput::V7Shielded`] signature in a transaction before v7, or a
    /// [`SignableInput::Shielded`] signature in a v7 transaction.
    SignerVersionMismatch,
    /// A v7 signature with a transparent sighash type other than `SIGHASH_ALL`, which
    /// sighash variant 0 does not support.
    UnsupportedHashType(u8),
    /// The signature's input, spend, or action is not in its bundle, or its position does
    /// not fit in the two bytes the v7 signature context allots to it.
    IndexOutOfRange,
    /// The transaction has no bundle of the type whose signature is requested.
    MissingBundle(v7::ShieldedBundleType),
    /// The transaction's transparent authorizing context does not describe one spent
    /// output per input, or the signer's spent output differs from it.
    SpentOutputMismatch,
    /// The transaction digests lack the parts of a v7 transaction, which
    /// [`TxIdDigester`](super::txid::TxIdDigester) computes for every v7 transaction.
    MissingV7Digests,
}

impl fmt::Display for SighashError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SignerVersionMismatch => {
                write!(f, "the signature belongs to another transaction version")
            }
            Self::UnsupportedHashType(t) => {
                write!(f, "v7 signatures cannot use sighash type {t:#04x}")
            }
            Self::IndexOutOfRange => write!(f, "the signed input is not in the transaction"),
            Self::MissingBundle(bundle) => {
                write!(f, "the transaction has no {bundle:?} bundle to sign")
            }
            Self::SpentOutputMismatch => {
                write!(f, "the spent outputs do not match the transparent inputs")
            }
            Self::MissingV7Digests => write!(f, "the digests lack the v7 transaction parts"),
        }
    }
}

impl core::error::Error for SighashError {}

pub struct SignatureHash(pub(super) Blake2bHash);

pub use super::sighash_v7::{V7ShieldedSighashes, V7SignatureHashes};

impl AsRef<[u8; 32]> for SignatureHash {
    fn as_ref(&self) -> &[u8; 32] {
        self.0.as_ref().try_into().unwrap()
    }
}

/// Computes the signature hash for an input to a transaction, given
/// the full data of the transaction, the input being signed, and the
/// set of precomputed hashes produced in the construction of the
/// transaction ID.
///
/// For several v7 signatures on the same transaction, use [`V7SignatureHashes`]
/// to reuse the transaction ID and spent-output commitments.
///
/// Returns an error if `signable_input` cannot be signed in this transaction: see
/// [`SighashError`]. Before v7, only [`SignableInput::V7Shielded`] is rejected.
pub fn signature_hash<
    TA: ::transparent::sighash::TransparentAuthorizingContext,
    SA: sapling::bundle::Authorization<SpendProof = GrothProofBytes, OutputProof = GrothProofBytes>,
    A: Authorization<SaplingAuth = SA, TransparentAuth = TA>,
>(
    tx: &TransactionData<A>,
    signable_input: &SignableInput,
    txid_parts: &TxDigests<Blake2bHash>,
) -> Result<SignatureHash, SighashError> {
    if tx.version != TxVersion::V7 && matches!(signable_input, SignableInput::V7Shielded { .. }) {
        return Err(SighashError::SignerVersionMismatch);
    }
    Ok(SignatureHash(match tx.version {
        TxVersion::Sprout(_) | TxVersion::V3 | TxVersion::V4 => {
            v4_signature_hash(tx, signable_input)
        }

        TxVersion::V5 => v5_signature_hash(tx, signable_input, txid_parts),

        TxVersion::V6 => v6_signature_hash(tx, signable_input, txid_parts),

        TxVersion::V7 => return v7_signature_hash(tx, signable_input, txid_parts),
    }))
}
