//! Private identities for the internal contracts whose failure the public API
//! reports as [`Error::InternalInvariant`].
//!
//! The public error surface is one variant by design; it stays that way.
//! Inside the crate, a validated boundary names the contract it enforces
//! through [`failed`], which records that identity for the test harness and
//! returns the unchanged public error — so when a rewrite breaks proof parity,
//! an internal test can report *which* contract failed (wrong polynomial
//! domain, a missing query, an unexpected stage shape) without any golden
//! comparison. Only names and public structural dimensions are recorded:
//! never a witness value, a randomness tape, or proof bytes.
//!
//! These checks concern shapes and metadata supplied by circuit preparation
//! or an earlier internal stage. They do not test witness values for circuit
//! satisfaction: [`super::preflight`] reports those failures as
//! [`Error::UnsatisfiedWitness`], while [`super::witness`] uses
//! [`Error::InvalidStatement`] for public/private relation failures. Keep those
//! errors intact when propagating them; translating a structural failure into
//! an input rejection would hide a broken producer/consumer contract. The
//! [`Error`] docs describe caller recovery; [`super::prover`] explains the
//! separate transcript and randomness boundary.

use crate::Error;

/// The internal contract a validated boundary enforces.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Invariant {
    /// A base-domain column or polynomial did not have exactly `N` entries.
    BaseDomainLength,
    /// An extended-coset vector did not have exactly `EXTENDED_N` entries.
    ExtendedDomainLength,
    /// An Action's permutation products were not `PERMUTATION_SETS` in number.
    PermutationSetCount,
    /// An Action's lookup products were not one per circuit lookup.
    LookupCount,
    /// A test-oracle query index has no entry in its kind's query table.
    /// Production expression indices are checked during macro expansion.
    #[cfg(test)]
    MissingQuery,
    /// A queried column was absent or did not have the domain's row count.
    ColumnShape,
    /// The instance column was not column zero of `N` rows.
    InstanceColumnShape,
}

#[cfg(test)]
thread_local! {
    static LAST_FAILED: std::cell::Cell<Option<Invariant>> = const { std::cell::Cell::new(None) };
}

/// Records that `invariant` failed on this thread (test builds only) and
/// returns the public error every internal failure maps to.
#[cold]
pub(crate) fn failed(invariant: Invariant) -> Error {
    #[cfg(test)]
    LAST_FAILED.with(|last| last.set(Some(invariant)));
    #[cfg(not(test))]
    let _ = invariant;
    Error::InternalInvariant
}

/// Takes the identity of the last invariant that failed on this thread, for
/// tests localizing an `InternalInvariant`.
#[cfg(test)]
pub(crate) fn take_last_failed() -> Option<Invariant> {
    LAST_FAILED.with(|last| last.take())
}

#[cfg(test)]
mod tests {
    use super::{Invariant, failed, take_last_failed};
    use crate::Error;
    use std::prelude::v1::*;

    #[test]
    fn failed_invariants_are_named_for_tests_and_public_for_callers() {
        assert_eq!(take_last_failed(), None);
        assert_eq!(failed(Invariant::MissingQuery), Error::InternalInvariant);
        assert_eq!(take_last_failed(), Some(Invariant::MissingQuery));
        assert_eq!(take_last_failed(), None);
    }
}
