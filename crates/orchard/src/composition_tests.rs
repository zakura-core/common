//! Native agreement and codec boundaries for governance witnesses.
use crate::backend::{
    ff::{Field, PrimeField},
    group::{Curve, GroupEncoding},
    pasta_curves::pallas,
};
use crate::{
    circuit::composition::{
        spend_auth_generator,
        witness::{self, NonIdentityPallasPoint, NoteCommitTrapdoor, NotePsi},
    },
    keys::{
        FullViewingKey, Scope, SpendAuthorizingKey, SpendValidatingKey, SpendingKey,
        testing::arb_spending_key,
    },
    note::{NoteVersion, testing::arb_note},
    primitives::redpallas::SpendAuthRandomizer,
    value::NoteValue,
};
use proptest::prelude::*;

proptest! {
    #[test]
    fn viewing_and_signing_witnesses_keep_canonical_material(sk in arb_spending_key()) {
        let ask = SpendAuthorizingKey::from(&sk);
        let zero = SpendAuthRandomizer::from_bytes(pallas::Scalar::ZERO.to_repr()).unwrap();
        let encoded: [u8; 32] = (&ask.randomize(&zero)).into();
        prop_assert_eq!(witness::SpendAuthorizingKey::from(&ask).to_bytes(), encoded);
        let fvk = FullViewingKey::from(&sk);
        prop_assert_eq!(witness::NullifierDerivingKey::from(&fvk).to_bytes(), fvk.nk().inner().to_repr());
        for scope in [Scope::External, Scope::Internal] {
            let rivk = fvk.rivk(scope);
            prop_assert_eq!(witness::CommitIvkRandomness::from_viewing_key(&fvk, scope).to_bytes(), rivk.inner().to_repr());
        }
        let mut encoded_stream = alloc::vec::Vec::new();
        witness::SpendAuthorizingKey::from(&ask).write(&mut encoded_stream).unwrap();
        prop_assert_eq!(encoded_stream, witness::SpendAuthorizingKey::from(&ask).to_bytes());
    }

    #[test]
    fn note_components_match_existing_derivations(
        note in prop_oneof![
            arb_note(NoteValue::ZERO, NoteVersion::V2),
            arb_note(NoteValue::from_raw(u64::MAX), NoteVersion::V2),
            arb_note(NoteValue::ZERO, NoteVersion::V3),
            arb_note(NoteValue::from_raw(1), NoteVersion::V3),
            arb_note(NoteValue::from_raw(u64::MAX), NoteVersion::V3),
        ]
    ) {
        let rho = note.rho();
        let seed = note.rseed();
        let psi = NotePsi::derive(seed, &rho);
        prop_assert_eq!(psi.to_bytes(), seed.psi(&rho).to_repr());
        let address = note.recipient();
        let gd = NonIdentityPallasPoint::diversified_base(&address);
        let pkd = NonIdentityPallasPoint::transmission_key(&address);
        prop_assert_eq!(pkd.to_bytes(), address.pk_d().inner().to_bytes());
        let trapdoor = match note.version() {
            NoteVersion::V2 => NoteCommitTrapdoor::derive_v2(seed, &rho),
            NoteVersion::V3 => NoteCommitTrapdoor::derive_v3(seed, &rho, &gd, &pkd, note.value(), &psi),
        };
        prop_assert_eq!(trapdoor.to_bytes(), note.rcm().inner().to_repr());
        prop_assert_eq!(witness::NoteCommitment::from(&note.commitment()).to_bytes(), note.commitment().inner().to_bytes());
        let mut bytes = alloc::vec::Vec::new();
        psi.write(&mut bytes).unwrap();
        prop_assert_eq!(NotePsi::read(bytes.as_slice()).unwrap(), psi);

        // Synthetic governance bases deliberately need not be diversified addresses.
        let synthetic_gd = NonIdentityPallasPoint::from_bytes(&spend_auth_generator().to_bytes()).unwrap();
        let synthetic_pkd = NonIdentityPallasPoint::from_bytes(&(spend_auth_generator() * pallas::Scalar::from(2)).to_bytes()).unwrap();
        let typed = NoteCommitTrapdoor::derive_v3(seed, &rho, &synthetic_gd, &synthetic_pkd, note.value(), &psi);
        let native = seed.rcm_v3(&rho, &crate::spec::NonIdentityPallasPoint::from_bytes(&synthetic_gd.to_bytes()).unwrap(), &crate::spec::NonIdentityPallasPoint::from_bytes(&synthetic_pkd.to_bytes()).unwrap(), note.value().inner(), &seed.psi(&rho));
        prop_assert_eq!(typed.to_bytes(), native.inner().to_repr());
    }

    #[test]
    fn canonical_parsers_agree_with_the_protocol_fields(bytes in any::<[u8; 32]>()) {
        let field = pallas::Base::from_repr(bytes);
        let parsed = NotePsi::from_bytes(bytes);
        prop_assert_eq!(bool::from(parsed.is_some()), bool::from(field.is_some()));
        if bool::from(parsed.is_some()) { prop_assert_eq!(parsed.unwrap().to_bytes(), bytes); }
        let point = pallas::Point::from_bytes(&bytes);
        let parsed = NonIdentityPallasPoint::from_bytes(&bytes);
        use crate::backend::group::Group;
        let expected = point.map(|p| !p.is_identity()).unwrap_or(subtle::Choice::from(0));
        prop_assert_eq!(bool::from(parsed.is_some()), bool::from(expected));
    }
}

#[test]
fn frozen_keys_cover_both_sign_correction_outcomes() {
    let mut seen = [false; 2];
    for vector in crate::test_vectors::keys::test_vectors() {
        let sk = SpendingKey::from_bytes(vector.sk).unwrap();
        let raw = SpendAuthorizingKey::derive_inner(&sk);
        let negated = ((spend_auth_generator() * raw).to_affine().to_bytes()[31] >> 7) as usize;
        seen[negated] = true;
        let ask = SpendAuthorizingKey::from(&sk);
        assert_eq!(
            witness::SpendAuthorizingKey::from(&ask).to_bytes(),
            vector.ask
        );
        let scalar =
            pallas::Scalar::from_repr(witness::SpendAuthorizingKey::from(&ask).to_bytes()).unwrap();
        assert_eq!(
            (spend_auth_generator() * scalar).to_affine().to_bytes(),
            vector.ak
        );
        assert_eq!(
            witness::SpendValidatingKey::from(&SpendValidatingKey::from(&ask)).to_bytes(),
            vector.ak
        );
        let zero = SpendAuthRandomizer::from_bytes(pallas::Scalar::ZERO.to_repr()).unwrap();
        let signing = ask.randomize(&zero);
        let verification = crate::primitives::redpallas::VerificationKey::from(&signing);
        let signature = signing.sign(
            &mut crate::rng_compat::OsRng,
            b"composition witness agreement",
        );
        verification
            .verify(b"composition witness agreement", &signature)
            .unwrap();
        assert!(
            verification
                .verify(b"altered composition witness", &signature)
                .is_err()
        );
    }
    assert_eq!(
        seen,
        [true, true],
        "fixed vectors must exercise both sign corrections"
    );
}

fn successor(mut bytes: [u8; 32]) -> [u8; 32] {
    for byte in &mut bytes {
        let (next, carry) = byte.overflowing_add(1);
        *byte = next;
        if !carry {
            break;
        }
    }
    bytes
}

#[test]
fn canonical_boundaries_and_truncated_streams_are_rejected() {
    use crate::backend::group::Group;
    let base_max = (-pallas::Base::ONE).to_repr();
    assert!(bool::from(NotePsi::from_bytes(base_max).is_some()));
    for bytes in [
        successor(base_max),
        successor(successor(base_max)),
        [u8::MAX; 32],
    ] {
        assert!(bool::from(NotePsi::from_bytes(bytes).is_none()));
        assert_eq!(
            NotePsi::read(bytes.as_slice()).unwrap_err().kind(),
            corez::io::ErrorKind::InvalidData
        );
    }
    let scalar_max = (-pallas::Scalar::ONE).to_repr();
    assert!(bool::from(
        SpendAuthRandomizer::from_bytes(scalar_max).is_some()
    ));
    assert!(bool::from(
        SpendAuthRandomizer::from_bytes(successor(scalar_max)).is_none()
    ));
    for bytes in [pallas::Point::identity().to_bytes(), [u8::MAX; 32]] {
        assert!(bool::from(
            NonIdentityPallasPoint::from_bytes(&bytes).is_none()
        ));
        assert_eq!(
            NonIdentityPallasPoint::read(bytes.as_slice())
                .unwrap_err()
                .kind(),
            corez::io::ErrorKind::InvalidData
        );
    }
    let point = NonIdentityPallasPoint::from_bytes(&spend_auth_generator().to_bytes()).unwrap();
    let mut encoded = alloc::vec::Vec::new();
    point.write(&mut encoded).unwrap();
    assert_eq!(
        NonIdentityPallasPoint::read(encoded.as_slice()).unwrap(),
        point
    );
    for len in 0..encoded.len() {
        assert_eq!(
            NonIdentityPallasPoint::read(&encoded[..len])
                .unwrap_err()
                .kind(),
            corez::io::ErrorKind::UnexpectedEof
        );
        assert_eq!(
            NotePsi::read(&encoded[..len]).unwrap_err().kind(),
            corez::io::ErrorKind::UnexpectedEof
        );
    }
}
