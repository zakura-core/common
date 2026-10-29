//! Typed private witnesses derived by Orchard for composed circuits.
//!
//! Each adapter wraps a value that Orchard derives from an existing key, address,
//! or note and offers only its canonical encoding. Callers decode those bytes
//! into circuit values at their witness boundary. Every value here except
//! [`AddressPoints`] is private material: do not log, publish, or use it as a
//! public instance.
//!
//! Spending authorization is separate from viewing and note material: see
//! [`SpendAuthorization`], whose bytes permit spending.

use crate::backend::{ff::PrimeField, group::GroupEncoding, pallas};
use subtle::CtOption;

use crate::{
    Address,
    keys::{
        CommitIvkRandomness, FullViewingKey, NullifierDerivingKey, Scope, SpendAuthorizingKey,
        SpendValidatingKey,
    },
    note::{Note, NoteCommitment, RandomSeed, Rho, commitment::NoteCommitTrapdoor},
    spec::NonIdentityPallasPoint,
    value::NoteValue,
};

fn read_32(mut reader: impl corez::io::Read) -> corez::io::Result<[u8; 32]> {
    let mut bytes = [0; 32];
    reader.read_exact(&mut bytes)?;
    Ok(bytes)
}

/// The spend validating key `ak` of a full viewing key.
///
/// Its encoding is the x-coordinate of `ak`, whose ỹ is always 0.
#[derive(Clone, Debug)]
pub struct ValidatingKey(SpendValidatingKey);

impl ValidatingKey {
    /// Selects `ak` from a full viewing key.
    pub fn from_viewing_key(fvk: &FullViewingKey) -> Self {
        Self(fvk.clone().into())
    }

    /// Returns the canonical encoding of `ak`, a valid Pallas point encoding.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.to_bytes()
    }

    /// Writes the canonical encoding of `ak`.
    pub fn write(&self, mut writer: impl corez::io::Write) -> corez::io::Result<()> {
        writer.write_all(&self.to_bytes())
    }
}

impl From<&SpendValidatingKey> for ValidatingKey {
    fn from(ak: &SpendValidatingKey) -> Self {
        Self(ak.clone())
    }
}

/// The nullifier deriving key `nk` of a full viewing key.
///
/// This is private viewing material; do not log or publish it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NullifierKey(NullifierDerivingKey);

impl NullifierKey {
    /// Selects `nk` from a full viewing key.
    pub fn from_viewing_key(fvk: &FullViewingKey) -> Self {
        Self(*fvk.nk())
    }

    /// Returns the canonical base-field encoding of `nk`.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.to_bytes()
    }

    /// Writes the canonical base-field encoding of `nk`.
    pub fn write(&self, mut writer: impl corez::io::Write) -> corez::io::Result<()> {
        writer.write_all(&self.to_bytes())
    }
}

/// The randomness `rivk` that commits a full viewing key to its incoming
/// viewing key for one scope.
///
/// This is private viewing material; do not log or publish it. A proof of
/// address ownership must use the scope of the address being proven.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IvkCommitRandomness(CommitIvkRandomness);

impl IvkCommitRandomness {
    /// Selects `rivk` (external) or `rivk_internal` from a full viewing key.
    pub fn from_viewing_key(fvk: &FullViewingKey, scope: Scope) -> Self {
        Self(fvk.rivk(scope))
    }

    /// Returns the canonical scalar-field encoding of this randomness.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.inner().to_repr()
    }

    /// Writes the canonical scalar-field encoding of this randomness.
    pub fn write(&self, mut writer: impl corez::io::Write) -> corez::io::Result<()> {
        writer.write_all(&self.to_bytes())
    }
}

/// The diversified base `g_d` and transmission key `pk_d` of an address.
///
/// These points are part of the public address encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AddressPoints {
    g_d: NonIdentityPallasPoint,
    pk_d: NonIdentityPallasPoint,
}

impl AddressPoints {
    /// Derives `g_d` from the address's diversifier and selects its `pk_d`.
    pub fn from_address(address: &Address) -> Self {
        Self {
            g_d: address.g_d(),
            pk_d: address.pk_d().inner(),
        }
    }

    /// Returns the diversified base `g_d`.
    pub fn diversified_base(&self) -> NonIdentityPallasPoint {
        self.g_d
    }

    /// Returns the diversified transmission key `pk_d`.
    pub fn transmission_key(&self) -> NonIdentityPallasPoint {
        self.pk_d
    }
}

/// The note randomness `ψ` bound into Orchard nullifiers and note commitments.
///
/// This is private note material, not a public identifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NotePsi(pallas::Base);

impl NotePsi {
    /// Derives `ψ` from a note's random seed and `ρ`.
    pub fn derive(rseed: &RandomSeed, rho: &Rho) -> Self {
        Self(rseed.psi(rho))
    }

    /// Parses a canonical base-field encoding, rejecting encodings at or above
    /// the modulus.
    pub fn from_bytes(bytes: [u8; 32]) -> CtOption<Self> {
        pallas::Base::from_repr(bytes).map(Self)
    }

    /// Returns the canonical base-field encoding of `ψ`.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.to_repr()
    }

    /// Reads a canonical encoding, rejecting noncanonical and truncated input.
    pub fn read(reader: impl corez::io::Read) -> corez::io::Result<Self> {
        Self::from_bytes(read_32(reader)?)
            .into_option()
            .ok_or_else(|| {
                corez::io::Error::new(
                    corez::io::ErrorKind::InvalidData,
                    "noncanonical note randomness",
                )
            })
    }

    /// Writes the canonical base-field encoding of `ψ`.
    pub fn write(&self, mut writer: impl corez::io::Write) -> corez::io::Result<()> {
        writer.write_all(&self.to_bytes())
    }
}

/// The note commitment trapdoor `rcm`.
///
/// This is private note material; do not log or publish it.
#[derive(Clone, Debug)]
pub struct NoteTrapdoor(NoteCommitTrapdoor);

impl NoteTrapdoor {
    /// Derives the trapdoor of an existing note for its note version.
    pub fn from_note(note: &Note) -> Self {
        Self(note.rcm())
    }

    /// Derives the [ZIP 212] (V2) trapdoor from a random seed and `ρ`.
    ///
    /// [ZIP 212]: https://zips.z.cash/zip-0212
    pub fn derive_v2(rseed: &RandomSeed, rho: &Rho) -> Self {
        Self(rseed.rcm_v2(rho))
    }

    /// Derives the [ZIP 2005] (V3) trapdoor, which binds every note field.
    ///
    /// `g_d` and `pk_d` need not come from a diversified address, so composed
    /// circuits can commit to synthetic notes. The caller must supply the same
    /// components to the note commitment gadget. This derivation does not
    /// check address ownership, freshness, chain membership, or spendability.
    ///
    /// [ZIP 2005]: https://zips.z.cash/zip-2005
    pub fn derive_v3(
        rseed: &RandomSeed,
        rho: &Rho,
        g_d: &NonIdentityPallasPoint,
        pk_d: &NonIdentityPallasPoint,
        value: NoteValue,
        psi: &NotePsi,
    ) -> Self {
        Self(rseed.rcm_v3(rho, g_d, pk_d, value.inner(), &psi.0))
    }

    /// Returns the canonical scalar-field encoding of `rcm`.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.inner().to_repr()
    }

    /// Writes the canonical scalar-field encoding of `rcm`.
    pub fn write(&self, mut writer: impl corez::io::Write) -> corez::io::Result<()> {
        writer.write_all(&self.to_bytes())
    }
}

/// The full note commitment point `cm`, before x-coordinate extraction.
#[derive(Clone, Debug)]
pub struct NoteCommitmentPoint(NoteCommitment);

impl NoteCommitmentPoint {
    /// Returns the canonical Pallas point encoding of `cm`.
    ///
    /// This differs from the extracted commitment `cmx` published on-chain.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.inner().to_bytes()
    }

    /// Writes the canonical Pallas point encoding of `cm`.
    pub fn write(&self, mut writer: impl corez::io::Write) -> corez::io::Result<()> {
        writer.write_all(&self.to_bytes())
    }
}

impl From<&NoteCommitment> for NoteCommitmentPoint {
    fn from(cm: &NoteCommitment) -> Self {
        Self(cm.clone())
    }
}

/// The spend authorizing key `ask`, as a witness for a circuit that proves
/// spending authority.
///
/// Its bytes permit spending: protect them like the spending key. Encoding does
/// not log or persist them; callers own their lifetime and erasure.
#[derive(Clone, Debug)]
pub struct SpendAuthorization(SpendAuthorizingKey);

impl SpendAuthorization {
    /// Selects the spend authorizing key as a circuit witness.
    pub fn from_spend_authorizing_key(ask: &SpendAuthorizingKey) -> Self {
        Self(ask.clone())
    }

    /// Returns the canonical encoding of the sign-corrected scalar `ask`, the
    /// one whose validating key `[ask] G` matches the key's [`ValidatingKey`].
    ///
    /// These bytes permit spending.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.to_sign_corrected_bytes()
    }

    /// Writes the canonical encoding of the sign-corrected scalar `ask`.
    ///
    /// These bytes permit spending.
    pub fn write(&self, mut writer: impl corez::io::Write) -> corez::io::Result<()> {
        writer.write_all(&self.to_bytes())
    }
}
