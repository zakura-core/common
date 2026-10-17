use group::{GroupEncoding, ff::Field};
use rand_core::{CryptoRng, Rng};
use zcash_spec::PrfExpand;

use crate::keys::{ExpandedSpendingKey, FullViewingKey};

use super::{
    Diversifier, Nullifier, NullifierDerivingKey, PaymentAddress, keys::EphemeralSecretKey,
    value::NoteValue,
};

mod commitment;
pub use self::commitment::{ExtractedNoteCommitment, NoteCommitment};

pub(super) mod nullifier;

/// Enum for note randomness before and after [ZIP 212](https://zips.z.cash/zip-0212).
///
/// Before ZIP 212, the note commitment trapdoor `rcm` must be a scalar value.
/// After ZIP 212, the note randomness `rseed` is a 32-byte sequence, used to derive
/// both the note commitment trapdoor `rcm` and the ephemeral private key `esk`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Rseed {
    BeforeZip212(jubjub::Fr),
    AfterZip212([u8; 32]),
}

impl Rseed {
    /// Defined in [Zcash Protocol Spec § 4.7.2: Sending Notes (Sapling)][saplingsend].
    ///
    /// [saplingsend]: https://zips.z.cash/protocol/protocol.pdf#saplingsend
    pub(crate) fn rcm(&self) -> commitment::NoteCommitTrapdoor {
        commitment::NoteCommitTrapdoor(match self {
            Rseed::BeforeZip212(rcm) => *rcm,
            Rseed::AfterZip212(rseed) => {
                jubjub::Fr::from_bytes_wide(&PrfExpand::SAPLING_RCM.with(rseed))
            }
        })
    }
}

/// A discrete amount of funds received by an address.
#[derive(Clone, Debug)]
pub struct Note {
    /// The recipient of the funds.
    recipient: PaymentAddress,
    /// The value of this note.
    value: NoteValue,
    /// The seed randomness for various note components.
    rseed: Rseed,
}

impl PartialEq for Note {
    fn eq(&self, other: &Self) -> bool {
        // Notes are canonically defined by their commitments.
        self.cmu().eq(&other.cmu())
    }
}

impl Eq for Note {}

impl Note {
    /// Creates a note from its component parts.
    ///
    /// # Caveats
    ///
    /// This low-level constructor enforces that the provided arguments produce an
    /// internally valid `Note`. However, it allows notes to be constructed in a way that
    /// violates required security checks for note decryption, as specified in
    /// [Section 4.19] of the Zcash Protocol Specification. Users of this constructor
    /// should only call it with note components that have been fully validated by
    /// decrypting a received note according to [Section 4.19].
    ///
    /// [Section 4.19]: https://zips.z.cash/protocol/protocol.pdf#saplingandorchardinband
    pub fn from_parts(recipient: PaymentAddress, value: NoteValue, rseed: Rseed) -> Self {
        Note {
            recipient,
            value,
            rseed,
        }
    }

    /// Returns the recipient of this note.
    pub fn recipient(&self) -> PaymentAddress {
        self.recipient
    }

    /// Returns the value of this note.
    pub fn value(&self) -> NoteValue {
        self.value
    }

    /// Returns the rseed value of this note.
    pub fn rseed(&self) -> &Rseed {
        &self.rseed
    }

    /// Computes the note commitment, returning the full point.
    fn cm_full_point(&self) -> NoteCommitment {
        NoteCommitment::derive(
            self.recipient.g_d().to_bytes(),
            self.recipient.pk_d().to_bytes(),
            self.value,
            self.rseed.rcm(),
        )
    }

    /// Computes the nullifier given the nullifier deriving key and
    /// note position
    pub fn nf(&self, nk: &NullifierDerivingKey, position: u64) -> Nullifier {
        Nullifier::derive(nk, self.cm_full_point(), position)
    }

    /// Computes the note commitment
    pub fn cmu(&self) -> ExtractedNoteCommitment {
        self.cm_full_point().into()
    }

    /// Defined in [Zcash Protocol Spec § 4.7.2: Sending Notes (Sapling)][saplingsend].
    ///
    /// [saplingsend]: https://zips.z.cash/protocol/protocol.pdf#saplingsend
    pub fn rcm(&self) -> jubjub::Fr {
        self.rseed.rcm().0
    }

    /// Derives `esk` from the internal `Rseed` value, or generates a random value if this
    /// note was created with a v1 (i.e. pre-ZIP 212) note plaintext.
    pub fn generate_or_derive_esk<R: Rng + CryptoRng>(&self, rng: &mut R) -> EphemeralSecretKey {
        self.generate_or_derive_esk_internal(rng)
    }

    pub(crate) fn generate_or_derive_esk_internal<R: Rng>(
        &self,
        rng: &mut R,
    ) -> EphemeralSecretKey {
        match self.derive_esk() {
            None => EphemeralSecretKey(jubjub::Fr::random(rng)),
            Some(esk) => esk,
        }
    }

    /// Returns the derived `esk` if this note was created after ZIP 212 activated.
    pub(crate) fn derive_esk(&self) -> Option<EphemeralSecretKey> {
        match self.rseed {
            Rseed::BeforeZip212(_) => None,
            Rseed::AfterZip212(rseed) => Some(EphemeralSecretKey(jubjub::Fr::from_bytes_wide(
                &PrfExpand::SAPLING_ESK.with(&rseed),
            ))),
        }
    }

    /// Generates a dummy spent note.
    ///
    /// Defined in [Zcash Protocol Spec § 4.8.2: Dummy Notes (Sapling)][saplingdummynotes].
    ///
    /// [saplingdummynotes]: https://zips.z.cash/protocol/nu5.pdf#saplingdummynotes
    pub(crate) fn dummy<R: Rng>(mut rng: R) -> (ExpandedSpendingKey, FullViewingKey, Self) {
        let mut sk_bytes = [0; 32];
        rng.fill_bytes(&mut sk_bytes);

        let expanded = crate::keys::master_key_expansion(&sk_bytes);
        let expsk = ExpandedSpendingKey::from_spending_key(&expanded.as_bytes()[..32]);
        let fvk = FullViewingKey::from_expanded_spending_key(&expsk);
        // Dummy notes do not need a reproducible ZIP 32 address index.
        // Retry because not every Sapling diversifier is valid.
        let ivk = fvk.vk.ivk();
        let recipient = loop {
            let mut diversifier = Diversifier(Default::default());
            rng.fill_bytes(&mut diversifier.0);
            if let Some(recipient) = ivk.to_payment_address(diversifier) {
                break recipient;
            }
        };

        let mut rseed_bytes = [0; 32];
        rng.fill_bytes(&mut rseed_bytes);
        let rseed = Rseed::AfterZip212(rseed_bytes);

        let note = Note::from_parts(recipient, NoteValue::ZERO, rseed);

        (expsk, fvk, note)
    }
}

#[cfg(any(test, feature = "test-dependencies"))]
pub(super) mod testing {
    use proptest::{collection::vec, prelude::*};

    use super::{
        super::{testing::arb_payment_address, value::NoteValue},
        ExtractedNoteCommitment, Note, Rseed,
    };

    #[cfg(test)]
    pub(super) fn arb_dummy_note() -> impl Strategy<
        Value = (
            crate::keys::ExpandedSpendingKey,
            crate::keys::FullViewingKey,
            Note,
        ),
    > {
        use rand::{SeedableRng, rngs::StdRng};

        prop::array::uniform32(any::<u8>()).prop_map(|seed| Note::dummy(StdRng::from_seed(seed)))
    }

    prop_compose! {
        pub fn arb_note(value: NoteValue)(
            recipient in arb_payment_address(),
            rseed in prop::array::uniform32(prop::num::u8::ANY).prop_map(Rseed::AfterZip212)
        ) -> Note {
            Note {
                recipient,
                value,
                rseed
            }
        }
    }

    prop_compose! {
        pub(crate) fn arb_cmu()(
            cmu in vec(any::<u8>(), 64)
                .prop_map(|v| <[u8;64]>::try_from(v.as_slice()).unwrap())
                .prop_map(|v| bls12_381::Scalar::from_bytes_wide(&v)),
        ) -> ExtractedNoteCommitment {
            ExtractedNoteCommitment(cmu)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use rand_core::Rng;

    struct CountingRng {
        inner: rand::rngs::StdRng,
        consumed: usize,
    }

    impl CountingRng {
        fn new(seed: [u8; 32]) -> Self {
            use rand::SeedableRng;
            Self {
                inner: rand::rngs::StdRng::from_seed(seed),
                consumed: 0,
            }
        }
    }

    impl rand_core::TryRng for CountingRng {
        type Error = core::convert::Infallible;

        fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
            self.consumed += 4;
            Ok(self.inner.next_u32())
        }

        fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
            self.consumed += 8;
            Ok(self.inner.next_u64())
        }

        fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Self::Error> {
            self.consumed += dest.len();
            self.inner.fill_bytes(dest);
            Ok(())
        }
    }

    #[test]
    fn dummy_note_derivation_and_randomness_are_unchanged() {
        // Pin the key components, note contents, byte consumption, and following RNG word.
        for (seed, expected_digest, expected_consumed, expected_next) in [
            (
                0,
                [
                    41, 218, 228, 136, 208, 212, 88, 195, 115, 92, 245, 135, 95, 110, 148, 169,
                    158, 88, 190, 39, 10, 7, 195, 164, 90, 163, 1, 153, 243, 52, 195, 120,
                ],
                75,
                13252731160361427084,
            ),
            (
                1,
                [
                    80, 222, 41, 137, 135, 161, 238, 87, 159, 97, 83, 44, 55, 26, 90, 235, 73, 242,
                    19, 253, 241, 193, 97, 107, 128, 181, 30, 4, 36, 54, 219, 95,
                ],
                97,
                5790603339235468134,
            ),
            (
                90,
                [
                    37, 56, 194, 138, 186, 67, 253, 3, 44, 106, 220, 35, 50, 167, 23, 229, 103,
                    254, 35, 78, 246, 202, 154, 49, 81, 75, 110, 47, 145, 89, 215, 103,
                ],
                86,
                1661224483263062408,
            ),
            (
                255,
                [
                    129, 220, 116, 71, 84, 161, 163, 78, 90, 212, 167, 228, 217, 73, 167, 88, 28,
                    140, 94, 132, 29, 33, 79, 149, 187, 226, 153, 216, 31, 70, 156, 85,
                ],
                97,
                4758269131877494279,
            ),
        ] {
            let mut rng = CountingRng::new([seed; 32]);
            let (expsk, fvk, note) = Note::dummy(&mut rng);
            let mut hash = blake2b_simd::Params::new().hash_length(32).to_state();
            hash.update(&expsk.to_bytes());
            hash.update(&fvk.to_bytes());
            hash.update(&note.recipient().to_bytes());
            hash.update(&note.cmu().to_bytes());
            match note.rseed() {
                Rseed::AfterZip212(seed) => {
                    hash.update(seed);
                }
                _ => panic!("dummy notes use ZIP 212 randomness"),
            }
            let consumed = rng.consumed;
            let next = rng.next_u64();
            assert_eq!(hash.finalize().as_bytes(), expected_digest);
            assert_eq!(consumed, expected_consumed);
            assert_eq!(next, expected_next);
        }
    }

    proptest! {
        #[test]
        fn dummy_note_preserves_spend_inputs((expsk, fvk, note) in testing::arb_dummy_note()) {
            prop_assert_eq!(fvk.to_bytes(), FullViewingKey::from_expanded_spending_key(&expsk).to_bytes());
            prop_assert_eq!(note.value(), NoteValue::ZERO);
            prop_assert!(matches!(note.rseed(), Rseed::AfterZip212(_)));
            prop_assert_eq!(
                Some(note.recipient()),
                fvk.vk.ivk().to_payment_address(*note.recipient().diversifier())
            );
        }
    }
}
