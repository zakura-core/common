//! Note commitments and their trapdoors.
//!
//! A [`NoteCommitment`] is the Sinsemilla commitment to the contents of a
//! note, binding the diversified transmission key, note value, ρ, and ψ. Its
//! x-coordinate is exposed as [`ExtractedNoteCommitment`] (the value
//! appearing in the commitment tree), and its randomness is
//! [`NoteCommitTrapdoor`].

use crate::backend::pallas;
#[allow(unused_imports)]
use crate::backend::prelude::*;
use subtle::{ConstantTimeEq, CtOption};

use crate::{spec::extract_p, value::NoteValue};

/// The trapdoor for a note commitment.
#[derive(Clone, Debug)]
pub(crate) struct NoteCommitTrapdoor(pub(super) pallas::Scalar);

impl NoteCommitTrapdoor {
    /// Returns the inner scalar value.
    pub(crate) fn inner(&self) -> pallas::Scalar {
        self.0
    }
}

/// A commitment to a note.
#[derive(Clone, Debug)]
pub struct NoteCommitment(pub(super) pallas::Point);

impl NoteCommitment {
    /// Returns the inner Pallas curve point.
    pub(crate) fn inner(&self) -> pallas::Point {
        self.0
    }
}

impl NoteCommitment {
    /// $NoteCommit^Orchard$.
    ///
    /// Defined in [Zcash Protocol Spec § 5.4.8.4: Sinsemilla commitments][concretesinsemillacommit].
    ///
    /// [concretesinsemillacommit]: https://zips.z.cash/protocol/nu5.pdf#concretesinsemillacommit
    #[cfg(feature = "backend-sensei")]
    pub(super) fn derive(
        g_d: crate::spec::NonIdentityPallasPoint,
        pk_d: crate::spec::NonIdentityPallasPoint,
        v: NoteValue,
        rho: pallas::Base,
        psi: pallas::Base,
        rcm: NoteCommitTrapdoor,
    ) -> CtOption<Self> {
        sensei::primitives::protocol::note_commitment(
            g_d.backend(),
            pk_d.backend(),
            v.inner(),
            rho,
            psi,
            rcm.0,
        )
        .map(NoteCommitment)
    }
    #[cfg(feature = "backend-halo2")]
    pub(super) fn derive(
        g_d: crate::spec::NonIdentityPallasPoint,
        pk_d: crate::spec::NonIdentityPallasPoint,
        v: NoteValue,
        rho: pallas::Base,
        psi: pallas::Base,
        rcm: NoteCommitTrapdoor,
    ) -> CtOption<Self> {
        use crate::constants::L_ORCHARD_BASE;
        use bitvec::{array::BitArray, order::Lsb0};
        use core::iter;
        use legacy::*;
        let domain = note_commitment_domain();
        domain
            .commit(
                iter::empty()
                    .chain(BitArray::<_, Lsb0>::new(g_d.to_bytes()).iter().by_vals())
                    .chain(BitArray::<_, Lsb0>::new(pk_d.to_bytes()).iter().by_vals())
                    .chain(v.to_le_bits().iter().by_vals())
                    .chain(rho.to_le_bits().iter().by_vals().take(L_ORCHARD_BASE))
                    .chain(psi.to_le_bits().iter().by_vals().take(L_ORCHARD_BASE)),
                &rcm.0,
            )
            .map(NoteCommitment)
    }
}

/// The x-coordinate of the commitment to a note.
#[derive(Copy, Clone, Debug)]
pub struct ExtractedNoteCommitment(pub(super) pallas::Base);

impl ExtractedNoteCommitment {
    /// Deserialize the extracted note commitment from a byte array.
    ///
    /// This method enforces the [consensus rule][cmxcanon] that the
    /// byte representation of cmx MUST be canonical.
    ///
    /// [cmxcanon]: https://zips.z.cash/protocol/protocol.pdf#actionencodingandconsensus
    pub fn from_bytes(bytes: &[u8; 32]) -> CtOption<Self> {
        pallas::Base::from_repr(*bytes).map(ExtractedNoteCommitment)
    }

    /// Serialize the value commitment to its canonical byte representation.
    pub fn to_bytes(self) -> [u8; 32] {
        self.0.to_repr()
    }
}

impl From<NoteCommitment> for ExtractedNoteCommitment {
    fn from(cm: NoteCommitment) -> Self {
        ExtractedNoteCommitment(extract_p(&cm.0))
    }
}

impl ExtractedNoteCommitment {
    /// Returns the inner field element.
    pub(crate) fn inner(&self) -> pallas::Base {
        self.0
    }
}

impl From<&ExtractedNoteCommitment> for [u8; 32] {
    fn from(cmx: &ExtractedNoteCommitment) -> Self {
        cmx.to_bytes()
    }
}

impl ConstantTimeEq for ExtractedNoteCommitment {
    fn ct_eq(&self, other: &Self) -> subtle::Choice {
        self.0.ct_eq(&other.0)
    }
}

impl PartialEq for ExtractedNoteCommitment {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl Eq for ExtractedNoteCommitment {}

#[cfg(feature = "backend-halo2")]
mod legacy {

    use crate::once::OnceTable;

    use crate::constants::fixed_bases::NOTE_COMMITMENT_PERSONALIZATION;

    static NOTE_COMMITMENT_DOMAIN: OnceTable<crate::backend::sinsemilla::CommitDomain> =
        OnceTable::new();

    pub(super) fn note_commitment_domain() -> &'static crate::backend::sinsemilla::CommitDomain {
        NOTE_COMMITMENT_DOMAIN.get_or_init(|| {
            crate::backend::sinsemilla::CommitDomain::new(NOTE_COMMITMENT_PERSONALIZATION)
        })
    }
}
