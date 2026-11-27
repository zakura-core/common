//! The bundle-agnostic levels of the ZIP 248 transaction identifier and authorizing
//! data commitment.
//!
//! Each bundle type defines its own `bundle_effects_digest` and `bundle_auth_digest`;
//! the functions here combine them with the header and value pool delta map.
//! [`Envelope::txid_with_bundle_digests`] and [`Envelope::auth_digest_with_bundle_digests`]
//! take every bundle's digest from the caller. [`Envelope::txid`] and
//! [`Envelope::auth_digest`] compute the digests of the registered bundles from their
//! payloads, and the caller supplies the others.

use alloc::vec::Vec;
use core::fmt;

use blake2b_simd::{Hash as Blake2bHash, Params, State};
use corez::io::{self, Write};

use super::{
    bundle_digests::{self, InvalidPayload},
    envelope::{BundleData, Envelope, Header, MapKind, ValuePoolDelta, write_bundle_id},
    registry::BundleId,
};
use crate::{
    encoding::StateWrite,
    transaction::txid::{
        ZCASH_AUTH_PERSONALIZATION_PREFIX, ZCASH_HEADERS_HASH_PERSONALIZATION,
        ZCASH_TX_PERSONALIZATION_PREFIX,
    },
};
use zcash_protocol::TxId;

/// T.2 `value_pool_deltas_digest`.
const VALUE_POOL_DELTAS_PERSONALIZATION: &[u8; 16] = b"ZTxIdVPDeltaHash";
/// T.3 `effects_bundles_digest`.
const EFFECTS_BUNDLES_PERSONALIZATION: &[u8; 16] = b"ZTxIdEffBnd_Hash";
/// A.1 `auth_bundles_digest`.
const AUTH_BUNDLES_PERSONALIZATION: &[u8; 16] = b"ZTxAuthBnd__Hash";

pub(crate) fn hasher(personalization: &[u8; 16]) -> StateWrite {
    StateWrite(state(personalization))
}

fn state(personalization: &[u8; 16]) -> State {
    Params::new()
        .hash_length(32)
        .personal(personalization)
        .to_state()
}

fn branch_personalization(prefix: &[u8; 12], consensus_branch_id: u32) -> [u8; 16] {
    let mut personalization = [0; 16];
    personalization[..12].copy_from_slice(prefix);
    personalization[12..].copy_from_slice(&consensus_branch_id.to_le_bytes());
    personalization
}

/// T.1: `header_digest`.
pub(crate) fn header_digest(header: &Header) -> Blake2bHash {
    let mut h = hasher(ZCASH_HEADERS_HASH_PERSONALIZATION);
    header.write(&mut h).unwrap();
    h.finalize()
}

/// T.2: `value_pool_deltas_digest`, over the entries of `mValuePoolDeltas` in encoding
/// order.
pub(crate) fn value_pool_deltas_digest<'a>(
    deltas: impl IntoIterator<Item = &'a ValuePoolDelta>,
) -> Blake2bHash {
    let mut h = hasher(VALUE_POOL_DELTAS_PERSONALIZATION);
    for delta in deltas {
        delta.write(&mut h).unwrap();
    }
    h.finalize()
}

/// T.3: `effects_bundles_digest`, over each effecting bundle's identifier and
/// `bundle_effects_digest`, in encoding order.
pub(crate) fn effects_bundles_digest(
    bundle_effects_digests: impl IntoIterator<Item = (BundleId, [u8; 32])>,
) -> Blake2bHash {
    tagged_digests(EFFECTS_BUNDLES_PERSONALIZATION, bundle_effects_digests)
}

/// A.1: `auth_bundles_digest`, over each authorizing bundle's identifier and
/// `bundle_auth_digest`, in encoding order.
pub(crate) fn auth_bundles_digest(
    bundle_auth_digests: impl IntoIterator<Item = (BundleId, [u8; 32])>,
) -> Blake2bHash {
    tagged_digests(AUTH_BUNDLES_PERSONALIZATION, bundle_auth_digests)
}

fn tagged_digests(
    personalization: &[u8; 16],
    digests: impl IntoIterator<Item = (BundleId, [u8; 32])>,
) -> Blake2bHash {
    let mut h = hasher(personalization);
    for (id, digest) in digests {
        write_bundle_id(&mut h, id).unwrap();
        h.write_all(&digest).unwrap();
    }
    h.finalize()
}

/// `txid_digest`: the root of the v7 transaction identifier tree.
pub(crate) fn txid_digest(
    consensus_branch_id: u32,
    header_digest: Blake2bHash,
    value_pool_deltas_digest: Blake2bHash,
    effects_bundles_digest: Blake2bHash,
) -> Blake2bHash {
    let mut h = state(&branch_personalization(
        ZCASH_TX_PERSONALIZATION_PREFIX,
        consensus_branch_id,
    ));
    h.update(header_digest.as_bytes());
    h.update(value_pool_deltas_digest.as_bytes());
    h.update(effects_bundles_digest.as_bytes());
    h.finalize()
}

/// `auth_digest`: the root of the v7 authorizing data commitment.
pub(crate) fn auth_digest(
    consensus_branch_id: u32,
    auth_bundles_digest: Blake2bHash,
) -> Blake2bHash {
    let mut h = state(&branch_personalization(
        ZCASH_AUTH_PERSONALIZATION_PREFIX,
        consensus_branch_id,
    ));
    h.update(auth_bundles_digest.as_bytes());
    h.finalize()
}

impl Envelope {
    /// Computes the transaction identifier.
    ///
    /// The identifier commits only to effecting data, so this reads only the header, the
    /// value pool deltas, and `mEffectBundles`. It computes the `bundle_effects_digest` of
    /// each entry whose pair the registry gives an effecting encoding, by decoding its
    /// payload as that encoding. `opaque_effects_digest` supplies the digest of every
    /// other entry: one whose pair is not registered, or is registered without an
    /// effecting encoding. A wallet that does not understand such a bundle obtains its
    /// digest from elsewhere, as described in ZIP 248's "Implications for Wallets".
    ///
    /// Each registered payload is decoded with the field decoders of the typed layer, so
    /// beyond being consumed exactly it must pass the checks those decoders make:
    ///
    /// - a transparent, Sapling, Orchard or Ironwood bundle is not empty;
    /// - each transparent output value is in {0 .. `MAX_MONEY`};
    /// - the coinbase `blockHeight` is in {1 .. 499999999}, `blockSubsidy` and
    ///   `lockboxValue` are at most `MAX_MONEY`, `lockboxValue` is at most
    ///   `blockSubsidy`, `coinbaseData` is at most 94 bytes, and the miner signals are in
    ///   strictly ascending order;
    /// - the Sapling `cmu` and `rk`, and the Orchard and Ironwood `nullifier`, `cmx`,
    ///   `cv` and `rk`, are canonical encodings of field elements or valid points.
    ///
    /// These are not all ZIP 248 parsing rules, but a transaction that breaks one is
    /// invalid in every epoch. Everything else is left to full validators: the consensus
    /// branch ID need not be known or valid for v7 (the envelope only requires it to be
    /// nonzero), nor an Orchard or Ironwood flag byte permitted by that branch's bundle
    /// version; a registered pair need not be active, or permitted in the other maps;
    /// the authorizing data may be absent; and the bundle-local rules that relate bundles
    /// to each other, such as a value pool delta needing its effecting bundle, are not
    /// checked. So unlike [`Transaction::read`], this identifies every envelope whose
    /// registered effecting payloads pass those decoders.
    ///
    /// Returns [`DigestError::MissingDigest`] if a needed digest is not supplied, and
    /// [`DigestError::InvalidPayload`] if a registered payload does not decode.
    ///
    /// [`Transaction::read`]: crate::transaction::Transaction::read
    pub fn txid(
        &self,
        opaque_effects_digest: impl Fn(BundleId) -> Option<[u8; 32]>,
    ) -> Result<TxId, DigestError> {
        self.txid_with_bundle_digests(|effect| {
            bundle_digest(
                effect.bundle,
                bundle_digests::effects_digest(effect),
                &opaque_effects_digest,
            )
        })
    }

    /// Computes the authorizing data commitment.
    ///
    /// As [`Envelope::txid`] does for effecting data, this computes the
    /// `bundle_auth_digest` of each entry of `mAuthBundles` whose pair the registry gives
    /// an authorizing encoding, and `opaque_auth_digest` supplies the digest of every
    /// other entry. It decodes such an entry together with its effecting entry, which
    /// gives the number of signatures and proofs, so both payloads must decode, the
    /// effecting one with the checks [`Envelope::txid`] lists. The authorizing payload
    /// must also have a canonical Sapling or Orchard anchor, and a `sighashInfo` of at
    /// least one byte for each signature. Each `sighashInfo` is hashed as its field
    /// encoding, whatever sighash variant it selects, and an Orchard or Ironwood proof is
    /// hashed whatever its length; full validators check both.
    pub fn auth_digest(
        &self,
        opaque_auth_digest: impl Fn(BundleId) -> Option<[u8; 32]>,
    ) -> Result<Blake2bHash, DigestError> {
        self.auth_digest_with_bundle_digests(|auth| {
            let effect = self
                .effect_bundle(auth.bundle.bundle_type)
                .expect("the parsing rules give every authorizing entry an effecting entry");
            bundle_digest(
                auth.bundle,
                bundle_digests::auth_digest(effect, auth),
                &opaque_auth_digest,
            )
        })
    }

    /// Computes the transaction identifier from the `bundle_effects_digest` that
    /// `bundle_effects_digest` returns for each effecting bundle.
    ///
    /// This needs no knowledge of any bundle type or consensus branch, so it identifies
    /// any well-formed envelope, as ZIP 248's parsing rules promise, given the digests of
    /// its bundles.
    pub fn txid_with_bundle_digests<E>(
        &self,
        mut bundle_effects_digest: impl FnMut(&BundleData) -> Result<[u8; 32], E>,
    ) -> Result<TxId, E> {
        let effects = self
            .effect_bundles()
            .iter()
            .map(|bundle| Ok((bundle.bundle, bundle_effects_digest(bundle)?)))
            .collect::<Result<Vec<_>, E>>()?;
        let digest = txid_digest(
            self.header().consensus_branch_id,
            header_digest(self.header()),
            value_pool_deltas_digest(self.value_pool_deltas()),
            effects_bundles_digest(effects),
        );
        Ok(TxId::from_bytes(digest.as_bytes().try_into().expect(
            "the digest is configured with a 32-byte hash length",
        )))
    }

    /// Computes the authorizing data commitment from the `bundle_auth_digest` that
    /// `bundle_auth_digest` returns for each authorizing bundle.
    pub fn auth_digest_with_bundle_digests<E>(
        &self,
        mut bundle_auth_digest: impl FnMut(&BundleData) -> Result<[u8; 32], E>,
    ) -> Result<Blake2bHash, E> {
        let auths = self
            .auth_bundles()
            .iter()
            .map(|bundle| Ok((bundle.bundle, bundle_auth_digest(bundle)?)))
            .collect::<Result<Vec<_>, E>>()?;
        Ok(auth_digest(
            self.header().consensus_branch_id,
            auth_bundles_digest(auths),
        ))
    }
}

/// Returns the digest of `bundle`: the one computed from its payloads if the registry
/// gives its pair an encoding in that map, and the one the caller supplies otherwise.
fn bundle_digest(
    bundle: BundleId,
    registered: Option<Result<[u8; 32], InvalidPayload>>,
    opaque: impl Fn(BundleId) -> Option<[u8; 32]>,
) -> Result<[u8; 32], DigestError> {
    match registered {
        Some(digest) => {
            digest.map_err(
                |InvalidPayload { map, error }| DigestError::InvalidPayload { bundle, map, error },
            )
        }
        None => opaque(bundle).ok_or(DigestError::MissingDigest(bundle)),
    }
}

/// An error in computing the transaction identifier or authorizing data commitment of an
/// [`Envelope`].
#[derive(Debug)]
#[non_exhaustive]
pub enum DigestError {
    /// No digest was supplied for a bundle whose pair the registry gives no encoding in
    /// its map.
    MissingDigest(BundleId),
    /// The payload of a registered bundle does not decode as its registered encoding.
    InvalidPayload {
        /// The bundle whose digest was being computed.
        bundle: BundleId,
        /// The map of the payload that does not decode. The authorizing digest of a
        /// bundle also decodes its effecting payload.
        map: MapKind,
        /// The decoding error.
        error: io::Error,
    },
}

impl fmt::Display for DigestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingDigest(id) => write!(f, "no digest was supplied for bundle {id}"),
            Self::InvalidPayload { bundle, map, error } => {
                write!(
                    f,
                    "the {map:?} payload of bundle {bundle} does not decode: {error}"
                )
            }
        }
    }
}

impl core::error::Error for DigestError {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            Self::MissingDigest(_) => None,
            Self::InvalidPayload { error, .. } => Some(error),
        }
    }
}
