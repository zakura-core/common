//! Receiving and change key scopes used by note and key operations.

#[cfg(feature = "zip32")]
pub use zip32::Scope;

/// Whether key material is used for receiving funds or internal wallet operations.
#[cfg(not(feature = "zip32"))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Scope {
    /// Addresses for receiving funds.
    External,
    /// Addresses for change and other internal operations.
    Internal,
}
