//! Orchard components used to construct separate governance proofs in voting-circuits.
//!
//! Enable the default-off `voting` feature to use this interface. It selects the
//! Halo2 prover and deliberately exposes Halo2/Pallas types; this is not a
//! backend-independent proof interface. Payment callers should use the ordinary
//! builder and opaque proof APIs instead. Cargo features are additive across a
//! dependency graph: this opt-in controls API availability, not access to secrets
//! or the size of a build that already enables proving.
//!
//! These are the same gadgets and constants used by Orchard payments. A caller
//! must configure their columns/tables, constrain claimed results, and bind all
//! required public inputs. Gadget use alone does not authenticate a voting
//! session, establish chain membership, or prove an application's authorization
//! policy. Treat private key/note components as secret witnesses, never public
//! instances. Decode their owner-provided canonical encodings only at the circuit
//! boundary; do not implement competing Orchard wire codecs downstream.
//!
//! The payment circuit remains private even with voting enabled:
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
//! Typed components do not expose raw field getters:
//! ```compile_fail
//! use orchard::keys::FullViewingKey;
//! fn raw(fvk: &FullViewingKey) { fvk.nk().inner(); }
//! ```

/// Constrains the incoming-viewing-key commitment for voting address ownership.
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
/// Orchard's fixed-base carrier types used by voting's ECC chips.
pub use crate::constants::fixed_bases::{
    OrchardBaseFieldBases, OrchardFixedBases, OrchardFixedBasesFull,
};
/// Orchard's Sinsemilla domain selections and protocol bit lengths.
pub use crate::constants::{
    L_ORCHARD_BASE, L_VALUE, MERKLE_DEPTH_ORCHARD, OrchardCommitDomains, OrchardHashDomains,
};
/// A canonically decoded nonidentity point for synthetic governance components.
pub use crate::spec::NonIdentityPallasPoint;
