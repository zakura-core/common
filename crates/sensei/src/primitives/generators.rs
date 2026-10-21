//! Orchard's fixed generators and lazy multiplication tables.
//!
//! Tables follow the primitive [cache ownership](crate::primitives#lazy-data-and-ownership)
//! policy: retained on targets with pointer atomics, owned per access elsewhere.
//! These caches are separate from the signature-domain tables in [`crate::redpallas`].
use super::cache::Cache as OnceBox;
use super::{
    Fq,
    pallas::{Affine, Point},
    prepared::Generator,
};
use alloc::boxed::Box;
use sensei_shared::generators::*;

/// A fixed generator used by an Orchard protocol operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FixedGenerator {
    /// Incoming-viewing-key commitment randomness.
    CommitIvkR,
    /// Note commitment randomness.
    NoteCommitR,
    /// Nullifier derivation.
    NullifierK,
    /// Spend authorization.
    SpendAuthG,
    /// Value commitment randomness and binding signatures.
    ValueCommitR,
    /// Value commitment amount.
    ValueCommitV,
}
impl FixedGenerator {
    fn native(self) -> udon::curve::PallasAffine {
        match self {
            Self::CommitIvkR => COMMIT_IVK_R_GENERATOR,
            Self::NoteCommitR => NOTE_COMMIT_R_GENERATOR,
            Self::NullifierK => NULLIFIER_K_GENERATOR,
            Self::SpendAuthG => SPEND_AUTH_G_GENERATOR,
            Self::ValueCommitR => VALUE_COMMIT_R_GENERATOR,
            Self::ValueCommitV => VALUE_COMMIT_V_GENERATOR,
        }
    }
    /// Returns this generator in affine form without decoding or hashing.
    pub fn point(self) -> Affine {
        Affine::from_native(self.native().to_point())
    }
    /// Multiplies this generator using the module's lazy primitive tables.
    pub fn multiply(self, scalar: &Fq) -> Point {
        static TABLES: [OnceBox<Generator<udon::curve::Pallas>>; 6] = [const { OnceBox::new() }; 6];
        let table = TABLES[self as usize].get_or_init(|| Box::new(Generator::new(self.native())));
        Point::from_native(table.mul(&scalar.native()))
    }
}
