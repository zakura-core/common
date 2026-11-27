//! The v7 extensible transaction format of [ZIP 248].
//!
//! This module is independent of any payment protocol. It defines the bundle registry,
//! the envelope encoding (common fields plus the value pool delta, effecting, and
//! authorizing maps, with opaque bundle payloads) and its parsing rules, and the levels
//! of the transaction identifier and authorizing data commitment that combine
//! per-bundle digests.
//!
//! [ZIP 248]: https://zips.z.cash/zip-0248

mod digest;
mod envelope;
mod registry;

pub use envelope::{BundleData, Envelope, EnvelopeError, Header, MapKind, ValuePoolDelta};
pub use registry::{BundleId, BundleType, BundleVariant, Registration};

#[cfg(test)]
mod tests;
