//! Typed access to Orchard components at an external circuit's witness boundary.
//!
//! Encoding a component does not authorize its disclosure. Nullifier keys, viewing
//! randomness, note randomness, and trapdoors are private material. Authorization
//! key encodings permit spending. Callers own the encoded bytes' lifetime and erasure.

use crate::backend::{ff::PrimeField, group::GroupEncoding, pallas};
use crate::{keys, note, spec, value::NoteValue};
use subtle::CtOption;

macro_rules! witness_adapter {
    ($(#[$doc:meta])* $name:ident, $inner:ty, $encode:expr) => {
        $(#[$doc])*
        #[derive(Clone)]
        pub struct $name($inner);

        impl core::fmt::Debug for $name {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.write_str(concat!(stringify!($name), "([redacted])"))
            }
        }

        impl $name {
            /// Returns the canonical encoding for decoding at the circuit boundary.
            pub fn to_bytes(&self) -> [u8; 32] {
                ($encode)(&self.0)
            }

            /// Writes one canonical component. The caller controls storage and secrecy.
            pub fn write(&self, mut writer: impl corez::io::Write) -> corez::io::Result<()> {
                writer.write_all(&self.to_bytes())
            }
        }
    };
}

witness_adapter!(
    /// Private nullifier-derivation material obtained from a full viewing key.
    #[derive(Copy)]
    NullifierDerivingKey,
    keys::NullifierDerivingKey,
    |key: &keys::NullifierDerivingKey| key.to_bytes()
);

impl From<&keys::FullViewingKey> for NullifierDerivingKey {
    fn from(key: &keys::FullViewingKey) -> Self {
        Self(*key.nk())
    }
}

witness_adapter!(
    /// Private randomness used to bind an incoming viewing key to a full viewing key.
    #[derive(Copy)]
    CommitIvkRandomness,
    keys::CommitIvkRandomness,
    |randomness: &keys::CommitIvkRandomness| randomness.inner().to_repr()
);

impl CommitIvkRandomness {
    /// Selects randomness for the same scope as the address being proven.
    pub fn from_viewing_key(key: &keys::FullViewingKey, scope: keys::Scope) -> Self {
        Self(key.rivk(scope))
    }
}

witness_adapter!(
    /// The canonical public spending-validation key used in address ownership.
    SpendValidatingKey,
    keys::SpendValidatingKey,
    |key: &keys::SpendValidatingKey| key.to_bytes()
);

impl From<&keys::SpendValidatingKey> for SpendValidatingKey {
    fn from(key: &keys::SpendValidatingKey) -> Self {
        Self(key.clone())
    }
}

witness_adapter!(
    /// The sign-corrected authorization key. Its encoding permits spending.
    ///
    /// Extract this separately from viewing material, only in the trusted signer.
    /// Never send these bytes to an untrusted proving service or public instance.
    SpendAuthorizingKey,
    keys::SpendAuthorizingKey,
    |key: &keys::SpendAuthorizingKey| key.to_bytes()
);

impl From<&keys::SpendAuthorizingKey> for SpendAuthorizingKey {
    fn from(key: &keys::SpendAuthorizingKey) -> Self {
        Self(key.clone())
    }
}

witness_adapter!(
    /// A canonically decoded nonidentity point used for address or synthetic components.
    #[derive(Copy, PartialEq, Eq)]
    NonIdentityPallasPoint,
    spec::NonIdentityPallasPoint,
    |point: &spec::NonIdentityPallasPoint| point.to_bytes()
);

impl NonIdentityPallasPoint {
    /// Obtains the diversified base of an Orchard address.
    pub fn diversified_base(address: &crate::Address) -> Self {
        Self(address.g_d())
    }

    /// Obtains the validated transmission point of an Orchard address.
    pub fn transmission_key(address: &crate::Address) -> Self {
        Self(address.pk_d().inner())
    }

    /// Obtains a point from an existing validated transmission key.
    pub fn from_transmission_key(key: &keys::DiversifiedTransmissionKey) -> Self {
        Self(key.inner())
    }

    /// Rejects invalid, noncanonical, and identity point encodings.
    pub fn from_bytes(bytes: &[u8; 32]) -> CtOption<Self> {
        spec::NonIdentityPallasPoint::from_bytes(bytes).map(Self)
    }

    /// Reads one canonical nonidentity point; rejects invalid and truncated input.
    pub fn read(mut reader: impl corez::io::Read) -> corez::io::Result<Self> {
        let mut bytes = [0; 32];
        reader.read_exact(&mut bytes)?;
        Self::from_bytes(&bytes).into_option().ok_or_else(|| {
            corez::io::Error::new(
                corez::io::ErrorKind::InvalidData,
                "invalid nonidentity point",
            )
        })
    }
}

witness_adapter!(
    /// The private note-randomness component bound into commitments and nullifiers.
    #[derive(Copy, PartialEq, Eq)]
    NotePsi,
    pallas::Base,
    |psi: &pallas::Base| psi.to_repr()
);

impl NotePsi {
    /// Uses Orchard's existing seed-and-rho derivation.
    pub fn derive(seed: &note::RandomSeed, rho: &note::Rho) -> Self {
        Self(seed.psi(rho))
    }

    /// Parses a canonical field encoding, rejecting encodings at or above the modulus.
    pub fn from_bytes(bytes: [u8; 32]) -> CtOption<Self> {
        pallas::Base::from_repr(bytes).map(Self)
    }

    /// Reads one canonical note component; rejects invalid and truncated input.
    pub fn read(mut reader: impl corez::io::Read) -> corez::io::Result<Self> {
        let mut bytes = [0; 32];
        reader.read_exact(&mut bytes)?;
        Self::from_bytes(bytes).into_option().ok_or_else(|| {
            corez::io::Error::new(
                corez::io::ErrorKind::InvalidData,
                "noncanonical note randomness",
            )
        })
    }
}

witness_adapter!(
    /// Private randomness for a note commitment.
    NoteCommitTrapdoor,
    note::commitment::NoteCommitTrapdoor,
    |trapdoor: &note::commitment::NoteCommitTrapdoor| trapdoor.inner().to_repr()
);

impl NoteCommitTrapdoor {
    /// Uses Orchard's existing V2 commitment-randomness derivation.
    pub fn derive_v2(seed: &note::RandomSeed, rho: &note::Rho) -> Self {
        Self(seed.rcm_v2(rho))
    }

    /// Uses Orchard's existing V3 derivation, including for synthetic components.
    ///
    /// Supply these same components to the commitment constraints. This does not
    /// establish address ownership, freshness, chain membership, or spendability.
    pub fn derive_v3(
        seed: &note::RandomSeed,
        rho: &note::Rho,
        g_d: &NonIdentityPallasPoint,
        pk_d: &NonIdentityPallasPoint,
        value: NoteValue,
        psi: &NotePsi,
    ) -> Self {
        Self(seed.rcm_v3(rho, &g_d.0, &pk_d.0, value.inner(), &psi.0))
    }
}

witness_adapter!(
    /// A complete note-commitment point, including the coordinate omitted on-chain.
    NoteCommitment,
    note::NoteCommitment,
    |commitment: &note::NoteCommitment| commitment.inner().to_bytes()
);

impl From<&note::NoteCommitment> for NoteCommitment {
    fn from(commitment: &note::NoteCommitment) -> Self {
        Self(commitment.clone())
    }
}
