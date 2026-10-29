//! Orchard's Halo2 gadgets and typed witnesses for composing other circuits.
//!
//! Enable the default-off `circuit-composition` feature to use this module. It
//! selects the Halo2 backend and prover and deliberately exposes Halo2/Pallas
//! types; it is not a backend-independent proof interface. Payment callers
//! should use the builder and opaque proof APIs instead. For example, the
//! governance circuits in voting-circuits reuse Orchard's address-ownership,
//! note-commitment, and nullifier relations through this module. Cargo features
//! are additive across a dependency graph: this opt-in controls API
//! availability, not access to secrets or the size of a build that already
//! enables proving.
//!
//! These are the same gadgets and constants used by Orchard payments. A caller
//! must configure their columns/tables, constrain claimed results, and bind all
//! required public inputs. Gadget use alone does not establish chain
//! membership, freshness, or an application's authorization policy. Treat
//! private key/note components as secret witnesses, never public instances.
//! Obtain them from [`witness`] and decode their canonical encodings only at
//! the circuit boundary; do not implement competing Orchard derivations or
//! wire codecs downstream.
//!
//! The payment circuit remains private with this feature enabled:
//! ```compile_fail
//! use orchard::circuit::{Circuit, Config};
//! ```
//! Raw key extraction remains private:
//! ```compile_fail
//! use orchard::keys::{SpendAuthorizingKey, SpendingKey};
//! fn raw(sk: &SpendingKey) { SpendAuthorizingKey::derive_inner(sk); }
//! ```
//! Internal modules are not part of this composition API:
//! ```compile_fail
//! use orchard::{constants, spec};
//! use orchard::circuit::halo2;
//! ```
//! Payment key and address types gain no composition accessors:
//! ```compile_fail
//! fn raw(fvk: &orchard::keys::FullViewingKey) { fvk.nk(); }
//! ```
//! ```compile_fail
//! fn raw(address: &orchard::Address) { address.g_d(); }
//! ```
//! Typed witnesses do not expose raw field getters:
//! ```compile_fail
//! use orchard::circuit::composition::witness::NullifierKey;
//! fn raw(nk: &NullifierKey) { nk.inner(); }
//! ```

pub mod witness;

/// Constrains the incoming-viewing-key commitment used by address ownership.
pub use super::halo2::commit_ivk::gadgets::commit_ivk;
/// Existing incoming-viewing-key commitment chip and column configuration.
pub use super::halo2::commit_ivk::{CommitIvkChip, CommitIvkConfig};
/// Existing addition chip used by the nullifier relation.
pub use super::halo2::gadget::add_chip::{AddChip, AddConfig};
/// Shared witness assignment and nullifier constraints, not authorization checks.
pub use super::halo2::gadget::{AddInstruction, assign_free_advice, derive_nullifier};
/// Constrains a note commitment to the supplied typed-component witnesses.
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
/// Orchard's fixed-base carrier types used by composed ECC chips.
pub use crate::constants::fixed_bases::{
    OrchardBaseFieldBases, OrchardFixedBases, OrchardFixedBasesFull,
};
/// Orchard's Sinsemilla domain selections and protocol bit lengths.
pub use crate::constants::{
    L_ORCHARD_BASE, L_VALUE, MERKLE_DEPTH_ORCHARD, OrchardCommitDomains, OrchardHashDomains,
};
/// A canonically decoded nonidentity point, for addresses and synthetic notes.
pub use crate::spec::NonIdentityPallasPoint;

#[cfg(test)]
mod tests;
