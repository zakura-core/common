use alloc::boxed::Box;
use core::fmt;

use blake2b_simd::Hash as Blake2bHash;

use super::{
    Authorization, TransactionData, TxDigests, TxVersion,
    sighash_v4::{
        Zip143Digests, v4_signature_hash, v4_signature_hash_with_digests, zip143_digests,
    },
    sighash_v5::{
        TransparentInputsDigests, v5_signature_hash, v5_signature_hash_with_inputs_digests,
    },
    sighash_v6::v6_signature_hash_with_inputs_digests,
    txid::TxIdDigester,
};
use ::sapling::bundle::GrothProofBytes;
use ::transparent::sighash::TransparentAuthorizingContext;

use super::sighash_v6::v6_signature_hash;

pub enum SignableInput<'a> {
    Shielded,
    Transparent(transparent::sighash::SignableInput<'a>),
}

impl SignableInput<'_> {
    pub fn hash_type(&self) -> u8 {
        match self {
            SignableInput::Shielded => ::transparent::sighash::SIGHASH_ALL,
            SignableInput::Transparent(input) => input.hash_type().encode(),
        }
    }
}

pub struct SignatureHash(Blake2bHash);

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
/// This rehashes data shared by every input of the transaction on each call. To compute
/// the signature hashes of several inputs of one transaction, use
/// [`PrecomputedSighashData`].
pub fn signature_hash<
    TA: ::transparent::sighash::TransparentAuthorizingContext,
    SA: sapling::bundle::Authorization<SpendProof = GrothProofBytes, OutputProof = GrothProofBytes>,
    A: Authorization<SaplingAuth = SA, TransparentAuth = TA>,
>(
    tx: &TransactionData<A>,
    signable_input: &SignableInput,
    txid_parts: &TxDigests<Blake2bHash>,
) -> SignatureHash {
    SignatureHash(match tx.version {
        TxVersion::Sprout(_) | TxVersion::V3 | TxVersion::V4 => {
            v4_signature_hash(tx, signable_input)
        }

        TxVersion::V5 => v5_signature_hash(tx, signable_input, txid_parts),

        TxVersion::V6 => v6_signature_hash(tx, signable_input, txid_parts),
    })
}

/// The digests of a transaction that its signature hashes share, in the form its
/// version's signature hash algorithm uses.
#[derive(Clone, Debug)]
enum SharedDigests {
    /// [ZIP 143] and [ZIP 243] digests, for transactions of version 4 and earlier.
    ///
    /// [ZIP 143]: https://zips.z.cash/zip-0143
    /// [ZIP 243]: https://zips.z.cash/zip-0243
    Zip143(Zip143Digests),
    /// [ZIP 244] digests, for transactions of version 5 and later.
    ///
    /// [ZIP 244]: https://zips.z.cash/zip-0244
    Zip244 {
        txid_parts: TxDigests<Blake2bHash>,
        /// `Some` exactly when the transaction has non-coinbase transparent inputs.
        transparent_inputs: Option<TransparentInputsDigests>,
    },
}

/// A transaction, together with the digests of its data that the signature hash of every
/// input of the transaction shares.
///
/// Computing a value of this type takes time linear in the size of the transaction. Given
/// it, [`PrecomputedSighashData::signature_hash`] computes the signature hash of an input
/// without rehashing the transaction's inputs and outputs, so computing the signature
/// hashes of all inputs of a transaction takes linear time in total.
///
/// The transaction is owned and cannot be modified, so the digests always match it. To
/// change the transaction, take it back with [`PrecomputedSighashData::into_tx`] and
/// compute new digests for the changed transaction.
pub struct PrecomputedSighashData<A: Authorization> {
    tx: TransactionData<A>,
    digests: SharedDigests,
}

impl<A: Authorization> fmt::Debug for PrecomputedSighashData<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PrecomputedSighashData")
            .field("version", &self.tx.version)
            .field("consensus_branch_id", &self.tx.consensus_branch_id)
            .field("digests", &self.digests)
            .finish_non_exhaustive()
    }
}

impl<TA, SA, A> PrecomputedSighashData<A>
where
    TA: TransparentAuthorizingContext,
    SA: sapling::bundle::Authorization<SpendProof = GrothProofBytes, OutputProof = GrothProofBytes>,
    A: Authorization<SaplingAuth = SA, TransparentAuth = TA>,
{
    /// Computes the shared signature hash digests of `tx`.
    pub fn new(tx: TransactionData<A>) -> Self {
        match tx.version {
            TxVersion::Sprout(_) | TxVersion::V3 | TxVersion::V4 => {
                let digests = SharedDigests::Zip143(zip143_digests(&tx));
                PrecomputedSighashData { tx, digests }
            }
            TxVersion::V5 | TxVersion::V6 => Self::new_zip244_unchecked(tx),
        }
    }
}

impl<TA, A> PrecomputedSighashData<A>
where
    TA: TransparentAuthorizingContext,
    A: Authorization<TransparentAuth = TA>,
{
    /// Computes the shared signature hash digests of `tx`, which must be of version 5 or
    /// later.
    ///
    /// Unlike [`PrecomputedSighashData::new`], this does not require the Sapling proofs of
    /// `tx` to be available, because [ZIP 244] signature hashes do not commit to them.
    ///
    /// Returns [`Zip244Error::NotZip244`] holding `tx` unchanged if `tx` is of version 4
    /// or earlier.
    ///
    /// [ZIP 244]: https://zips.z.cash/zip-0244
    pub fn new_zip244(tx: TransactionData<A>) -> Result<Self, Zip244Error<A>> {
        match tx.version {
            TxVersion::Sprout(_) | TxVersion::V3 | TxVersion::V4 => {
                Err(Zip244Error::NotZip244(Box::new(tx)))
            }
            TxVersion::V5 | TxVersion::V6 => Ok(Self::new_zip244_unchecked(tx)),
        }
    }

    /// Computes the [ZIP 244] digests of `tx`, whose version the caller has checked.
    ///
    /// [ZIP 244]: https://zips.z.cash/zip-0244
    fn new_zip244_unchecked(tx: TransactionData<A>) -> Self {
        let txid_parts = tx.digest(TxIdDigester);
        let transparent_inputs = tx
            .transparent_bundle
            .as_ref()
            .and_then(TransparentInputsDigests::for_bundle);
        PrecomputedSighashData {
            tx,
            digests: SharedDigests::Zip244 {
                txid_parts,
                transparent_inputs,
            },
        }
    }

    /// Returns the transaction.
    pub fn tx(&self) -> &TransactionData<A> {
        &self.tx
    }

    /// Returns the transaction, discarding the digests.
    pub fn into_tx(self) -> TransactionData<A> {
        self.tx
    }

    /// Computes the signature hash for an input to the transaction.
    ///
    /// The result is the same as that of [`signature_hash`] for the transaction.
    ///
    /// # Panics
    ///
    /// Panics if the transaction is a pre-Overwinter transaction, or if it is of version 4
    /// or earlier and `signable_input` is a transparent input but the transaction has no
    /// transparent bundle.
    pub fn signature_hash(&self, signable_input: &SignableInput) -> SignatureHash {
        SignatureHash(match &self.digests {
            SharedDigests::Zip143(digests) => {
                v4_signature_hash_with_digests(&self.tx, signable_input, digests)
            }
            SharedDigests::Zip244 {
                txid_parts,
                transparent_inputs,
            } => match self.tx.version {
                TxVersion::V6 => v6_signature_hash_with_inputs_digests(
                    &self.tx,
                    signable_input,
                    txid_parts,
                    transparent_inputs.as_ref(),
                ),
                TxVersion::V5 => v5_signature_hash_with_inputs_digests(
                    &self.tx,
                    signable_input,
                    txid_parts,
                    transparent_inputs.as_ref(),
                ),
                TxVersion::Sprout(_) | TxVersion::V3 | TxVersion::V4 => {
                    unreachable!("ZIP 244 digests are only computed for v5 and later")
                }
            },
        })
    }
}

/// An error returned by [`PrecomputedSighashData::new_zip244`].
#[non_exhaustive]
pub enum Zip244Error<A: Authorization> {
    /// The transaction is of version 4 or earlier, so its signature hashes are not
    /// [ZIP 244] signature hashes. This holds the transaction, unchanged.
    ///
    /// [ZIP 244]: https://zips.z.cash/zip-0244
    NotZip244(Box<TransactionData<A>>),
}

impl<A: Authorization> fmt::Debug for Zip244Error<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Zip244Error::NotZip244(tx) => f
                .debug_struct("NotZip244")
                .field("version", &tx.version)
                .finish_non_exhaustive(),
        }
    }
}

impl<A: Authorization> fmt::Display for Zip244Error<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Zip244Error::NotZip244(tx) => write!(
                f,
                "transaction version {:?} does not use ZIP 244 signature hashes",
                tx.version
            ),
        }
    }
}

impl<A: Authorization> core::error::Error for Zip244Error<A> {}
