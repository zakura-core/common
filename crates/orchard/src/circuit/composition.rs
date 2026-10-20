//! Components for circuits that compose Orchard address, commitment, and nullifier relations.
//!
//! Enable `circuit-composition` to use this Halo2/Pallas-specific interface.
//! Voting proofs are one consumer; these components contain no governance policy.
//! Payment callers should use the ordinary builder and opaque proof APIs.
//! Cargo feature unification controls API availability, not access to secrets or
//! the footprint of a build that already enables proving.
//!
//! Callers must configure columns and tables, constrain claimed results, and bind
//! public inputs. These components do not establish chain membership, authenticate
//! an application session, or enforce authorization policy. Keep private witness
//! encodings secret and decode them only at the circuit boundary.
//!
//! Payment implementation types remain private:
//! ```compile_fail
//! use orchard::circuit::{Circuit, Config};
//! ```
//! Implementation modules remain private:
//! ```compile_fail
//! use orchard::{constants, spec};
//! use orchard::circuit::halo2;
//! ```
//! Ordinary payment types do not expose witness accessors:
//! ```compile_fail
//! use orchard::keys::FullViewingKey;
//! fn raw(fvk: &FullViewingKey) { fvk.nk(); }
//! ```
//! Raw authorization-key derivation remains private:
//! ```compile_fail
//! use orchard::keys::{SpendAuthorizingKey, SpendingKey};
//! fn raw(sk: &SpendingKey) { SpendAuthorizingKey::derive_inner(sk); }
//! ```

/// Typed witness adapters and their canonical encodings.
pub mod witness;

/// Constrains the incoming-viewing-key commitment for address ownership.
pub use super::halo2::commit_ivk::gadgets::commit_ivk;
/// Existing incoming-viewing-key commitment chip and column configuration.
pub use super::halo2::commit_ivk::{CommitIvkChip, CommitIvkConfig};
/// Existing addition chip used by the nullifier relation.
pub use super::halo2::gadget::add_chip::{AddChip, AddConfig};
/// Shared witness assignment and nullifier constraints, not authorization checks.
pub use super::halo2::gadget::{AddInstruction, assign_free_advice, derive_nullifier};
/// Constrains a note commitment to the supplied component witnesses.
pub use super::halo2::note_commit::gadgets::note_commit;
/// Existing note commitment chip and column configuration.
pub use super::halo2::note_commit::{NoteCommitChip, NoteCommitConfig};
/// Canonical spending-authorization base and its existing fixed-base tables.
pub use crate::constants::fixed_bases::spend_auth_g::{
    U as SPEND_AUTH_U, Z as SPEND_AUTH_Z, generator as spend_auth_generator,
};
/// Canonical protocol domains; callers must not substitute application domains.
pub use crate::constants::fixed_bases::{
    COMMIT_IVK_PERSONALIZATION, NOTE_COMMITMENT_PERSONALIZATION,
};
/// Orchard's fixed-base carrier types used by composition ECC chips.
pub use crate::constants::fixed_bases::{
    OrchardBaseFieldBases, OrchardFixedBases, OrchardFixedBasesFull,
};
/// Orchard's Sinsemilla domain selections and protocol bit lengths.
pub use crate::constants::{
    L_ORCHARD_BASE, L_VALUE, MERKLE_DEPTH_ORCHARD, OrchardCommitDomains, OrchardHashDomains,
};
