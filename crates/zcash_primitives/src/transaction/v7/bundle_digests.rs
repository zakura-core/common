//! The digests of the registered bundles of an [`Envelope`], computed from their
//! payloads alone.
//!
//! Each payload is decoded into the effecting or authorizing representation that the
//! typed layer decodes it into, and digested by the functions that
//! [`TxIdDigester`] and [`BlockTxCommitmentDigester`] use for a typed transaction, so
//! the two paths share one implementation of each bundle's digests.
//!
//! Each payload must be its bundle's encoding, consumed exactly, and pass the checks of
//! the typed field decoders, which [`Envelope::txid`] and [`Envelope::auth_digest`]
//! list. Unlike the typed layer, this accepts any `sighashInfo`, an effecting bundle
//! without its authorizing data, any consensus branch ID, and Orchard and Ironwood
//! flags that the bundle version of the branch would not permit, and it checks no
//! bundle-local rule that relates bundles to each other.
//!
//! [`Envelope`]: super::Envelope
//! [`Envelope::txid`]: super::Envelope::txid
//! [`Envelope::auth_digest`]: super::Envelope::auth_digest
//! [`TxIdDigester`]: crate::transaction::txid::TxIdDigester
//! [`BlockTxCommitmentDigester`]: crate::transaction::txid::BlockTxCommitmentDigester

use corez::io;

use blake2b_simd::Hash as Blake2bHash;
use orchard::ValuePool;

use super::{
    coinbase,
    envelope::{BundleData, MapKind},
    registry::BundleId,
    transparent,
};
use crate::transaction::{
    components::{orchard as orchard_serialization, sapling as sapling_serialization},
    txid::bytes32,
};

/// A registered bundle's payload that does not decode as its registered encoding.
pub(super) struct InvalidPayload {
    /// The map of the payload. An authorizing digest also decodes the effecting
    /// payload, for the counts it takes from it.
    pub(super) map: MapKind,
    pub(super) error: io::Error,
}

/// Returns the `bundle_effects_digest` of an entry of `mEffectBundles`, or `None` if the
/// registry defines no effecting encoding for its pair.
///
/// The pairs decoded here are exactly those the registry permits in `mEffectBundles`, as
/// a test checks, so a pair the registry gains without a decoder takes a supplied digest
/// rather than failing.
pub(super) fn effects_digest(effect: &BundleData) -> Option<Result<[u8; 32], InvalidPayload>> {
    let digest = match effect.bundle {
        BundleId::TRANSPARENT => decode(effect, MapKind::EffectBundles, |r| {
            transparent::Effects::read(r).map(|effects| effects.effects_digest())
        }),
        BundleId::COINBASE => decode(
            effect,
            MapKind::EffectBundles,
            coinbase::encoded_effects_digest,
        ),
        BundleId::SAPLING => decode(effect, MapKind::EffectBundles, |r| {
            sapling_serialization::V7Effects::read(r).map(|effects| effects.effects_digest())
        }),
        BundleId::ORCHARD => orchard_effects(effect).map(|e| e.effects_digest(ValuePool::Orchard)),
        BundleId::IRONWOOD => {
            orchard_effects(effect).map(|e| e.effects_digest(ValuePool::Ironwood))
        }
        _ => return None,
    };
    Some(digest.map(|digest| bytes32(&digest)))
}

/// Returns the `bundle_auth_digest` of an entry of `mAuthBundles`, or `None` if the
/// registry defines no authorizing encoding for its pair.
///
/// `effect` is the entry of `mEffectBundles` for the same pair, which the parsing rules
/// require, and from which the authorizing data takes its numbers of signatures and
/// proofs. As for [`effects_digest`], the pairs decoded here are exactly those the
/// registry permits in `mAuthBundles`.
pub(super) fn auth_digest(
    effect: &BundleData,
    auth: &BundleData,
) -> Option<Result<[u8; 32], InvalidPayload>> {
    debug_assert_eq!(effect.bundle, auth.bundle);
    let digest = match auth.bundle {
        BundleId::TRANSPARENT => decode(effect, MapKind::EffectBundles, |r| {
            transparent::Effects::read(r)
        })
        .and_then(|effects| {
            decode(auth, MapKind::AuthBundles, |r| effects.read_auth(r))
                .map(|input_auth| transparent::auth_digest(&input_auth))
        }),
        BundleId::SAPLING => decode(effect, MapKind::EffectBundles, |r| {
            sapling_serialization::V7Effects::read(r)
        })
        .and_then(|effects| {
            decode(auth, MapKind::AuthBundles, |r| effects.read_auth(r))
                .map(|auth| auth.auth_digest())
        }),
        BundleId::ORCHARD => orchard_auth_digest(effect, auth, ValuePool::Orchard),
        BundleId::IRONWOOD => orchard_auth_digest(effect, auth, ValuePool::Ironwood),
        _ => return None,
    };
    Some(digest.map(|digest| bytes32(&digest)))
}

fn orchard_effects(
    effect: &BundleData,
) -> Result<orchard_serialization::V7Effects, InvalidPayload> {
    decode(effect, MapKind::EffectBundles, |r| {
        orchard_serialization::V7Effects::read(r)
    })
}

fn orchard_auth_digest(
    effect: &BundleData,
    auth: &BundleData,
    pool: ValuePool,
) -> Result<Blake2bHash, InvalidPayload> {
    let effects = orchard_effects(effect)?;
    decode(auth, MapKind::AuthBundles, |r| effects.read_auth(r)).map(|auth| auth.auth_digest(pool))
}

/// Decodes a payload, which `read` must consume exactly.
fn decode<T>(
    bundle: &BundleData,
    map: MapKind,
    read: impl FnOnce(&mut &[u8]) -> io::Result<T>,
) -> Result<T, InvalidPayload> {
    bundle
        .decode(read)
        .map_err(|error| InvalidPayload { map, error })
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use super::{auth_digest, effects_digest};
    use crate::transaction::v7::{BundleData, BundleId, BundleType, BundleVariant};

    /// A pair has a decoder in a map exactly when the registry permits it there, so the
    /// envelope digests never decode a pair the registry forbids, and never lack a
    /// decoder for one it permits.
    #[test]
    fn decoders_match_the_registry() {
        for bundle_type in 0..=255 {
            for variant in 0..3 {
                let bundle =
                    BundleId::new(BundleType::new(bundle_type), BundleVariant::new(variant));
                let empty = BundleData {
                    bundle,
                    data: Vec::new(),
                };
                let registration = bundle.registration();
                assert_eq!(
                    effects_digest(&empty).is_some(),
                    registration.is_some_and(|r| r.effecting),
                    "effecting decoder for {bundle}"
                );
                assert_eq!(
                    auth_digest(&empty, &empty).is_some(),
                    registration.is_some_and(|r| r.authorizing),
                    "authorizing decoder for {bundle}"
                );
            }
        }
    }
}
