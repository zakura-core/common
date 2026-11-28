//! The v7 extensible transaction format of [ZIP 248].
//!
//! The envelope layer is independent of any payment protocol. It defines the bundle
//! registry, the envelope encoding (common fields plus the value pool delta, effecting,
//! and authorizing maps, with opaque bundle payloads) and its parsing rules, and the
//! levels of the transaction identifier and authorizing data commitment that combine
//! per-bundle digests.
//!
//! The typed layer represents the bundles ZIP 248 registers in a
//! [`TransactionData`](super::TransactionData): the coinbase bundle and the value pool
//! deltas that no bundle carries as its value balance are its [`V7Fields`]. Every v7
//! [`Transaction`](super::Transaction) satisfies the ZIP 248 bundle-local rules
//! ([`BundleRuleError`]), except the rule that transparent signatures use `SIGHASH_ALL`,
//! which only script verification under `zcash_script`'s `Flags::SigHashAllOnly` can
//! check.
//!
//! [ZIP 248]: https://zips.z.cash/zip-0248

mod bundle_digests;
/// Largest block or expiry height representable in a typed v7 transaction.
pub(crate) const MAX_V7_HEIGHT: u32 = 499_999_999;

mod coinbase;
pub(crate) mod digest;
mod envelope;
mod fields;
mod registry;
mod rules;
pub(crate) mod sighash_info;
pub(crate) mod transaction;
pub(crate) mod transparent;

pub use coinbase::{CoinbaseBundle, CoinbaseError, MAX_COINBASE_DATA_LEN, MinerPoll, MinerSignal};
pub use digest::DigestError;
pub(crate) use envelope::write_bundle_id;
pub use envelope::{BundleData, Envelope, EnvelopeError, Header, MapKind, ValuePoolDelta};
pub(crate) use fields::{ShieldedBalances, value_pool_deltas};
pub use fields::{V7Fields, ValueDeltas};
pub use registry::{BundleId, BundleType, BundleVariant, Registration};
pub use rules::BundleRuleError;
pub(crate) use rules::conform;
pub use sighash_info::SIGHASH_INFO_V0;

/// A v7 bundle whose signatures each sign their own digest: the Sapling, Orchard, or
/// Ironwood bundle.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ShieldedBundleType {
    /// The Sapling bundle.
    Sapling,
    /// The Orchard bundle.
    Orchard,
    /// The Ironwood bundle.
    Ironwood,
}

impl From<ShieldedBundleType> for BundleType {
    fn from(bundle: ShieldedBundleType) -> Self {
        match bundle {
            ShieldedBundleType::Sapling => BundleType::SAPLING,
            ShieldedBundleType::Orchard => BundleType::ORCHARD,
            ShieldedBundleType::Ironwood => BundleType::IRONWOOD,
        }
    }
}

/// Which signature of a v7 Sapling, Orchard, or Ironwood bundle is being made or checked.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShieldedSignature {
    /// The spend authorization signature of the spend (Sapling) or action (Orchard and
    /// Ironwood) at `index` within its bundle.
    SpendAuth {
        /// The zero-based position of the spend or action within its bundle.
        index: usize,
    },
    /// The bundle's binding signature.
    Binding,
}

#[cfg(any(test, feature = "test-dependencies"))]
pub mod testing;

#[cfg(test)]
pub(crate) mod tests;
