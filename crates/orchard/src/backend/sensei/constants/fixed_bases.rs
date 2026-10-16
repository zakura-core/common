//! Fixed protocol generators, owned and prepared by Sensei.

/// SWU hash-to-curve personalization for the spending key base point and
/// the nullifier base point K^Orchard
pub const ORCHARD_PERSONALIZATION: &str = "z.cash:Orchard";

/// SWU hash-to-curve personalization for the value commitment generator
pub const VALUE_COMMITMENT_PERSONALIZATION: &str = "z.cash:Orchard-cv";

/// SWU hash-to-curve value for the value commitment generator
pub const VALUE_COMMITMENT_V_BYTES: [u8; 1] = *b"v";

/// SWU hash-to-curve value for the value commitment generator
pub const VALUE_COMMITMENT_R_BYTES: [u8; 1] = *b"r";

/// SWU hash-to-curve personalization for the note commitment generator
pub const NOTE_COMMITMENT_PERSONALIZATION: &str = "z.cash:Orchard-NoteCommit";

/// SWU hash-to-curve personalization for the IVK commitment generator
pub const COMMIT_IVK_PERSONALIZATION: &str = "z.cash:Orchard-CommitIvk";

/// The `CommitIvkR` protocol generator.
pub mod commit_ivk_r {
    /// Returns the fixed affine generator without hashing or decoding.
    pub fn generator() -> sensei::primitives::pallas::Affine {
        sensei::primitives::generators::FixedGenerator::CommitIvkR.point()
    }
}
/// The `NoteCommitR` protocol generator.
pub mod note_commit_r {
    /// Returns the fixed affine generator without hashing or decoding.
    pub fn generator() -> sensei::primitives::pallas::Affine {
        sensei::primitives::generators::FixedGenerator::NoteCommitR.point()
    }
}
/// The `NullifierK` protocol generator.
pub mod nullifier_k {
    /// Returns the fixed affine generator without hashing or decoding.
    pub fn generator() -> sensei::primitives::pallas::Affine {
        sensei::primitives::generators::FixedGenerator::NullifierK.point()
    }
}
/// The `SpendAuthG` protocol generator.
pub mod spend_auth_g {
    /// Returns the fixed affine generator without hashing or decoding.
    pub fn generator() -> sensei::primitives::pallas::Affine {
        sensei::primitives::generators::FixedGenerator::SpendAuthG.point()
    }
}
/// The `ValueCommitR` protocol generator.
pub mod value_commit_r {
    /// Returns the fixed affine generator without hashing or decoding.
    pub fn generator() -> sensei::primitives::pallas::Affine {
        sensei::primitives::generators::FixedGenerator::ValueCommitR.point()
    }
}
/// The `ValueCommitV` protocol generator.
pub mod value_commit_v {
    /// Returns the fixed affine generator without hashing or decoding.
    pub fn generator() -> sensei::primitives::pallas::Affine {
        sensei::primitives::generators::FixedGenerator::ValueCommitV.point()
    }
}
