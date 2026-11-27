//! The bundle-agnostic levels of the ZIP 248 transaction identifier and authorizing
//! data commitment.
//!
//! Each bundle type defines its own `bundle_effects_digest` and `bundle_auth_digest`;
//! the functions here combine them with the header and value pool delta map.

use blake2b_simd::{Hash as Blake2bHash, Params, State};
use corez::io::Write;

use super::{
    envelope::{BundleData, Envelope, Header, ValuePoolDelta, write_bundle_id},
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
    /// `bundle_effects_digest` returns the `bundle_effects_digest` of each effecting
    /// bundle. A caller that does not understand a bundle can supply its digest from
    /// elsewhere, as described in ZIP 248's "Implications for Wallets".
    pub fn txid<E>(
        &self,
        mut bundle_effects_digest: impl FnMut(&BundleData) -> Result<[u8; 32], E>,
    ) -> Result<TxId, E> {
        let effects = self
            .effect_bundles()
            .iter()
            .map(|bundle| Ok((bundle.bundle, bundle_effects_digest(bundle)?)))
            .collect::<Result<alloc::vec::Vec<_>, E>>()?;
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

    /// Computes the authorizing data commitment.
    ///
    /// `bundle_auth_digest` returns the `bundle_auth_digest` of each authorizing bundle.
    pub fn auth_digest<E>(
        &self,
        mut bundle_auth_digest: impl FnMut(&BundleData) -> Result<[u8; 32], E>,
    ) -> Result<Blake2bHash, E> {
        let auths = self
            .auth_bundles()
            .iter()
            .map(|bundle| Ok((bundle.bundle, bundle_auth_digest(bundle)?)))
            .collect::<Result<alloc::vec::Vec<_>, E>>()?;
        Ok(auth_digest(
            self.header().consensus_branch_id,
            auth_bundles_digest(auths),
        ))
    }
}
