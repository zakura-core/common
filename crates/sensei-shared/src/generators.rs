//! Pinned Pallas generators for the Ironwood circuit.
//!
//! The six multiplication bases are selected by [`crate::fixed_bases::FixedBase`].
//! The three `M` generators are the initial accumulators `Q` of the Sinsemilla
//! hash domains. All coordinates are checked against the curve equation at
//! compile time and stored as ready [`PallasAffine`] values.
//!
//! The 1,024-point Sinsemilla lookup table is a separate raw input to
//! `sensei-artifacts`; it is not the set of domain generators declared here.

use udon::{curve::PallasAffine, fp_hex};

/// Number of Sinsemilla generators, one per ten-bit message word.
pub const SINSEMILLA_TABLE_ROWS: usize = 1 << 10;

macro_rules! pallas_points {
    ($($(#[$attribute:meta])* $name:ident: $x:literal, $y:literal;)+) => {
        $(
            $(#[$attribute])*
            pub const $name: PallasAffine =
                udon::pallas_affine!(fp_hex!($x), fp_hex!($y));
        )+
    };
}

// The pinned Orchard fixed bases, ready in the at-rest representation.
pallas_points! {
    /// Value-commitment value base `V`.
    VALUE_COMMIT_V_GENERATOR:
        "0x2f70597a8e3d0f42f7a86a704f9bb232fe04a37f2b5a7c8c2aa7bd6e3af94367",
        "0x2d0e5169311919af1e917f63136d6c421d9ea766a7ffe3dba413c47eaf5af28e";
    /// Value-commitment blinding base `R`.
    VALUE_COMMIT_R_GENERATOR:
        "0x07f444550fa409bb4f66235bea8d2048406ed745ee90802f0ec3c668883c5a91",
        "0x24136777af26628c21562cc9e46fb7c2279229f1f39281460e2f46c8a772d9ca";
    /// Spend-authorization base `G`.
    SPEND_AUTH_G_GENERATOR:
        "0x375523b328f1d6063b8d187c3e5f445f0c7f0ce37b70a10c8d1a7284b875c963",
        "0x1ad0357fdf1a66db7b10bcfcfed624fbdfc914fec005bdd84ce33e817b0c3bc9";
    /// Blinding base `R` for the incoming viewing-key commitment.
    COMMIT_IVK_R_GENERATOR:
        "0x25a22ccd5070134e1634290a4080894802957fe2d31aedc79823486e5ff8a118",
        "0x29cfd29966a2faebc2c890c4284b57946b4442fb1b58a6c73fe793b3e37fdda9";
    /// Nullifier base `K`.
    NULLIFIER_K_GENERATOR:
        "0x25e7aa169ca8198d2e375571faf4c9cf5e7eb192ccb5db9bd36f6aa7e447ca75",
        "0x155c1f851b1a3384880473442008ff755fe0a49ec1c1b4332db8dce21ae001cc";
    /// Initial Sinsemilla accumulator for the incoming viewing-key hash domain.
    COMMIT_IVK_M_GENERATOR:
        "0x05bc0cf14aa9c8117dcc81b85aa241fa421bcc245128a2326bcb2f92790f82f2",
        "0x1b014cf6d41abee6ef59074620de054b46c4351dc96da5f1be5ae5cecfaddebe";
    /// Note-commitment blinding base `R`, shared by the old and new notes.
    NOTE_COMMIT_R_GENERATOR:
        "0x26b206c328a94533cd239fab936f3df2239ec55cfc14a47c2c022c480ffc6e13",
        "0x3cde564b686dc04ca9541a2f2366e1c679c7c07823e0dcf6c34153c622cf37e3";
    /// Initial Sinsemilla accumulator for the note-commitment hash domain.
    NOTE_COMMIT_M_GENERATOR:
        "0x178007a056fbcd0df79ff2b479b0ed5dc5960f5afd46dd2a320eba0940a8745d",
        "0x32a058938ac670834ebec2d96ef4c92c8822128881db5e9e87270a5a7349ac63";
    /// Initial Sinsemilla accumulator for the Merkle-tree hash domain.
    MERKLE_CRH_M_GENERATOR:
        "0x1616d29663a818b9a00f365aef890e99c9beb955c08d1070f8b9c7f97f29c6a0",
        "0x358642a3e3af20992dc4f23e4fa35979e21c96ea0574159686e9aece25f2ea62";
}
