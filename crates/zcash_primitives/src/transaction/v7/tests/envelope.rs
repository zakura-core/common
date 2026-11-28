use alloc::vec;
use alloc::vec::Vec;
use core::convert::Infallible;
use core::num::NonZeroI64;

use proptest::prelude::*;

use super::super::{
    BundleData, BundleId, BundleType, BundleVariant, Envelope, EnvelopeError, Header, MapKind,
    ValuePoolDelta,
};

fn header() -> Header {
    Header {
        consensus_branch_id: 0xffff_fffe,
        lock_time: 0,
        expiry_height: 10,
    }
}

fn delta(bundle_type: u32, variant: u32, value: i64) -> ValuePoolDelta {
    ValuePoolDelta {
        bundle: BundleId::new(BundleType::new(bundle_type), BundleVariant::new(variant)),
        value: NonZeroI64::new(value).unwrap(),
    }
}

fn data(bundle_type: u32, variant: u32, payload: &[u8]) -> BundleData {
    BundleData {
        bundle: BundleId::new(BundleType::new(bundle_type), BundleVariant::new(variant)),
        data: payload.to_vec(),
    }
}

/// A vector with a transparent bundle and fee and NSM deltas. The encoding, transaction
/// identifier and authorizing data commitment below were computed independently with
/// Python's `hashlib.blake2b`.
const VECTOR_ENCODING: &str = "07000080f7fffffffeffffff000000000a000000030000e80300000000000005007cfcffffffffffff06009cffffffffffffff01000002aabb01000001cc";
const VECTOR_TXID: &str = "18938b66c74f2a837f11cdf59f4c34b166aec9fbaa96620cbfa641e184096113";
const VECTOR_AUTH_DIGEST: &str = "d200c7d8543d608840b0c6c140671b2c7f43045dfd6520afbf258e30e30ceeac";
const EMPTY_TXID: &str = "4fe76a22a1f5755eadf63422ab1e71510267f518f8fcbb496037d66bceb61101";
/// A second vector with two entries per digest map and a bundle type (253) whose
/// `compactSize` encoding takes three bytes.
const MULTI_ENCODING: &str = "07000080f7fffffffeffffff000000000a000000020200fbfffffffffffffffdfd000105000000000000000202000101fdfd00010001fdfd0001020203";
const MULTI_TXID: &str = "0d2f011d7e4410dd0ed04b115f0db1c14dbb3d63a72399c4b71090edd7c3d446";
const MULTI_AUTH_DIGEST: &str = "e9f307165879540f6654b55105694dc08fee1d7ace046c358419c742908c8dc2";

fn vector_envelope() -> Envelope {
    Envelope::new(
        header(),
        vec![delta(0, 0, 1000), delta(5, 0, -900), delta(6, 0, -100)],
        vec![data(0, 0, &[0xaa, 0xbb])],
        vec![data(0, 0, &[0xcc])],
    )
    .unwrap()
}

#[test]
fn encoding_matches_vector() {
    let envelope = vector_envelope();
    let mut encoded = vec![];
    envelope.write(&mut encoded).unwrap();
    assert_eq!(hex::encode(&encoded), VECTOR_ENCODING);
    assert_eq!(Envelope::read(&encoded[..]).unwrap(), envelope);
}

#[test]
fn digests_match_vector() {
    // The vector supplies opaque per-bundle digests, to check how the envelope combines
    // them whatever the payloads are.
    let envelope = vector_envelope();
    let txid = envelope
        .txid_with_bundle_digests(|_| Ok::<_, Infallible>([0x11; 32]))
        .unwrap();
    assert_eq!(hex::encode(txid.as_ref()), VECTOR_TXID);
    let auth = envelope
        .auth_digest_with_bundle_digests(|_| Ok::<_, Infallible>([0x22; 32]))
        .unwrap();
    assert_eq!(hex::encode(auth.as_bytes()), VECTOR_AUTH_DIGEST);

    let empty = Envelope::new(header(), vec![], vec![], vec![]).unwrap();
    let txid = empty
        .txid_with_bundle_digests(|_| -> Result<[u8; 32], Infallible> {
            unreachable!("no bundles")
        })
        .unwrap();
    assert_eq!(hex::encode(txid.as_ref()), EMPTY_TXID);
}

#[test]
fn multi_byte_identifiers_match_vector() {
    let envelope = Envelope::new(
        header(),
        vec![delta(2, 0, -5), delta(253, 1, 5)],
        vec![data(2, 0, &[1]), data(253, 1, &[])],
        vec![data(253, 1, &[2, 3])],
    )
    .unwrap();
    let mut encoded = vec![];
    envelope.write(&mut encoded).unwrap();
    assert_eq!(hex::encode(&encoded), MULTI_ENCODING);
    assert_eq!(Envelope::read(&encoded[..]).unwrap(), envelope);

    let txid = envelope
        .txid_with_bundle_digests(|b| {
            Ok::<_, Infallible>(if b.bundle.bundle_type == BundleType::SAPLING {
                [0x33; 32]
            } else {
                [0x44; 32]
            })
        })
        .unwrap();
    assert_eq!(hex::encode(txid.as_ref()), MULTI_TXID);
    let auth = envelope
        .auth_digest_with_bundle_digests(|_| Ok::<_, Infallible>([0x55; 32]))
        .unwrap();
    assert_eq!(hex::encode(auth.as_bytes()), MULTI_AUTH_DIGEST);
}

fn envelope_error(encoded: &[u8]) -> EnvelopeError {
    let error = Envelope::read(encoded).expect_err("the encoding is malformed");
    *error
        .get_ref()
        .and_then(|e| e.downcast_ref::<EnvelopeError>())
        .unwrap_or_else(|| panic!("expected an EnvelopeError, got {error:?}"))
}

#[test]
fn parsing_rules_reject_malformed_maps() {
    type Case = (
        Vec<ValuePoolDelta>,
        Vec<BundleData>,
        Vec<BundleData>,
        EnvelopeError,
    );
    let cases: Vec<Case> = vec![
        (
            vec![delta(5, 0, -1), delta(0, 0, 1)],
            vec![],
            vec![],
            EnvelopeError::UnorderedMap {
                map: MapKind::ValuePoolDeltas,
                bundle_type: BundleType::TRANSPARENT,
            },
        ),
        (
            vec![],
            vec![data(2, 0, &[]), data(2, 0, &[])],
            vec![],
            EnvelopeError::UnorderedMap {
                map: MapKind::EffectBundles,
                bundle_type: BundleType::SAPLING,
            },
        ),
        (
            vec![],
            vec![data(0, 0, &[]), data(3, 0, &[])],
            vec![data(3, 0, &[]), data(0, 0, &[])],
            EnvelopeError::UnorderedMap {
                map: MapKind::AuthBundles,
                bundle_type: BundleType::TRANSPARENT,
            },
        ),
        (
            vec![delta(3, 1, 7)],
            vec![data(3, 0, &[])],
            vec![],
            EnvelopeError::InconsistentVariant(BundleType::ORCHARD),
        ),
        (
            vec![],
            vec![data(3, 0, &[])],
            vec![data(3, 2, &[])],
            EnvelopeError::InconsistentVariant(BundleType::ORCHARD),
        ),
        (
            vec![],
            vec![data(0, 0, &[])],
            vec![data(2, 0, &[])],
            EnvelopeError::AuthWithoutEffect(BundleType::SAPLING),
        ),
    ];
    for (deltas, effects, auths, expected) in cases {
        assert_eq!(
            Envelope::new(header(), deltas, effects, auths),
            Err(expected)
        );
    }
}

#[test]
fn decoder_rejects_malformed_encodings() {
    let vector = hex::decode(VECTOR_ENCODING).unwrap();

    // The first value pool delta's value starts after the 20-byte header, the map count,
    // and the entry's type and variant.
    let mut encoded = vector.clone();
    encoded[23..31].copy_from_slice(&0i64.to_le_bytes());
    assert_eq!(
        envelope_error(&encoded),
        EnvelopeError::ZeroValuePoolDelta(BundleType::TRANSPARENT)
    );

    // The v6 version group ID, version 6 with the v7 group ID, and a cleared
    // fOverwintered bit.
    for (offset, field) in [(4, 0xD884_B698u32), (0, 0x8000_0006), (0, 0x0000_0007)] {
        let mut encoded = vector.clone();
        encoded[offset..offset + 4].copy_from_slice(&field.to_le_bytes());
        assert_eq!(envelope_error(&encoded), EnvelopeError::NotV7);
    }

    // Swapping the two value pool deltas' bundle types breaks the map order.
    let mut encoded = vector.clone();
    encoded[21] = 5;
    encoded[31] = 0;
    assert_eq!(
        envelope_error(&encoded),
        EnvelopeError::UnorderedMap {
            map: MapKind::ValuePoolDeltas,
            bundle_type: BundleType::TRANSPARENT,
        }
    );

    // A zero consensus branch ID, which follows the header and version group ID.
    let mut encoded = vector.clone();
    encoded[8..12].copy_from_slice(&0u32.to_le_bytes());
    assert_eq!(
        envelope_error(&encoded),
        EnvelopeError::ZeroConsensusBranchId
    );

    // A non-canonical compactSize bundle type.
    let mut encoded = vector[..21].to_vec();
    encoded.extend_from_slice(&[0xfd, 0x00, 0x00]);
    encoded.extend_from_slice(&vector[22..]);
    assert!(Envelope::read(&encoded[..]).is_err());

    // A payload longer than the remaining input.
    assert!(Envelope::read(&vector[..vector.len() - 1]).is_err());
}

#[test]
fn identifiers_must_round_trip_through_compact_size() {
    for too_large in [
        BundleId::new(BundleType::new(0x0200_0001), BundleVariant::V0),
        BundleId::new(BundleType::TRANSPARENT, BundleVariant::new(0x0200_0001)),
    ] {
        assert_eq!(
            Envelope::new(
                header(),
                vec![ValuePoolDelta {
                    bundle: too_large,
                    value: NonZeroI64::new(1).unwrap(),
                }],
                vec![],
                vec![],
            ),
            Err(EnvelopeError::IdOutOfRange(too_large))
        );
    }
}

#[test]
fn sparse_maps_align_by_bundle_type() {
    let deltas = vec![delta(1, 0, 1), delta(4, 2, -1), delta(9, 1, 1)];
    let effects = vec![data(2, 1, &[]), data(4, 2, &[]), data(7, 0, &[])];
    let mut auths = vec![data(4, 2, &[]), data(7, 0, &[])];
    assert!(Envelope::new(header(), deltas.clone(), effects.clone(), auths.clone()).is_ok());

    // After the effects run out, a matching delta alone cannot authorize a bundle.
    auths.push(data(9, 1, &[]));
    assert_eq!(
        Envelope::new(header(), deltas.clone(), effects.clone(), auths.clone()),
        Err(EnvelopeError::AuthWithoutEffect(BundleType::new(9)))
    );

    // The delta and authorization must agree on the variant even without an effect.
    auths.last_mut().unwrap().bundle.variant = BundleVariant::new(2);
    assert_eq!(
        Envelope::new(header(), deltas, effects, auths),
        Err(EnvelopeError::InconsistentVariant(BundleType::new(9)))
    );
}

#[test]
fn large_maps_are_checked_in_linear_time() {
    // About 100k entries per map, the order of what a 2 MB block allows. A quadratic
    // check would take minutes here.
    let n = 100_000;
    let effects: Vec<_> = (0..n).map(|t| data(t, 0, &[])).collect();
    let auths = effects.clone();
    let deltas: Vec<_> = (0..n).map(|t| delta(t, 0, 1)).collect();
    let envelope = Envelope::new(header(), deltas, effects, auths).unwrap();
    assert_eq!(envelope.value_pool_delta(BundleType::new(n - 1)), 1);
    assert!(envelope.auth_bundle(BundleType::new(n - 1)).is_some());
}

#[test]
fn unregistered_bundles_parse_opaquely() {
    let envelope = Envelope::new(
        header(),
        vec![delta(200, 9, 5)],
        vec![data(200, 9, &[1, 2, 3])],
        vec![data(200, 9, &[4])],
    )
    .unwrap();
    assert_eq!(
        BundleId::new(BundleType::new(200), BundleVariant::new(9)).registration(),
        None
    );
    let mut encoded = vec![];
    envelope.write(&mut encoded).unwrap();
    assert_eq!(Envelope::read(&encoded[..]).unwrap(), envelope);

    // Its digests need only the supplied digests of its bundles.
    assert_eq!(
        envelope.txid(|_| Some([0x11; 32])).unwrap(),
        envelope
            .txid_with_bundle_digests(|_| Ok::<_, Infallible>([0x11; 32]))
            .unwrap()
    );
    assert_eq!(
        envelope.auth_digest(|_| Some([0x22; 32])).unwrap(),
        envelope
            .auth_digest_with_bundle_digests(|_| Ok::<_, Infallible>([0x22; 32]))
            .unwrap()
    );
}

#[test]
fn payload_decoding_consumes_exactly_the_declared_length() {
    let bundle = data(0, 0, &[1, 2, 3]);
    let read_two = |r: &mut &[u8]| {
        let mut buf = [0; 2];
        corez::io::Read::read_exact(r, &mut buf)?;
        Ok(buf)
    };
    assert!(bundle.decode(read_two).is_err());
    assert_eq!(data(0, 0, &[1, 2]).decode(read_two).unwrap(), [1, 2]);
    let read_four = |r: &mut &[u8]| {
        let mut buf = [0; 4];
        corez::io::Read::read_exact(r, &mut buf)?;
        Ok(buf)
    };
    assert!(bundle.decode(read_four).is_err());
}

#[test]
fn coinbase_is_identified_by_any_coinbase_variant() {
    let coinbase = Envelope::new(header(), vec![], vec![data(1, 3, &[])], vec![]).unwrap();
    assert!(coinbase.is_coinbase());
    assert!(!vector_envelope().is_coinbase());
}

/// Applies the edit that `scenario` names to the envelope of a frozen typed vector.
fn edit_for_scenario(scenario: &str, envelope: Envelope) -> Envelope {
    fn auth(auths: &mut [BundleData], bundle_type: BundleType) -> &mut Vec<u8> {
        &mut auths
            .iter_mut()
            .find(|a| a.bundle.bundle_type == bundle_type)
            .unwrap()
            .data
    }
    let (mut header, deltas, effects, mut auths) = envelope.into_parts();
    match scenario {
        "Sapling effects without authorizing data" => {
            auths.retain(|a| a.bundle.bundle_type != BundleType::SAPLING)
        }
        "transparent inputs and Ironwood without authorizing data" => auths.clear(),
        // The first input's sighashInfo becomes [0x01, 0x01].
        "transparent input with sighash variant 1" => {
            auth(&mut auths, BundleType::TRANSPARENT)[1] = 1
        }
        // After the anchor and the proof of two actions, with its three-byte length.
        "Ironwood action with sighash variant 2" => {
            auth(&mut auths, BundleType::IRONWOOD)[32 + 3 + 2720 + 2 * 2272 + 1] = 2
        }
        // After the anchor, two spend proofs and two spend authorization signatures.
        "Sapling binding signature with associated data" => {
            let payload = auth(&mut auths, BundleType::SAPLING);
            let at = 32 + 2 * 192 + 2 * 66;
            payload[at] = 2;
            payload.insert(at + 2, 0xaa);
        }
        "unknown consensus branch ID" => header.consensus_branch_id = 0x7a6b_5c4d,
        _ => panic!("unknown scenario {scenario}"),
    }
    Envelope::new(header, deltas, effects, auths).unwrap()
}

/// The digests of an envelope that the typed layer rejects, for a reason that leaves
/// them defined, match the independent oracle.
#[test]
fn envelope_digests_match_the_oracle_where_typed_decoding_fails() {
    use super::{envelope_vectors::ENVELOPE_VECTORS, vectors::TEST_VECTORS};
    use crate::transaction::Transaction;
    use zcash_protocol::consensus::BranchId;

    assert_eq!(ENVELOPE_VECTORS.len(), 6);
    for ev in ENVELOPE_VECTORS {
        let base = &TEST_VECTORS[ev.base];
        let envelope = edit_for_scenario(
            ev.scenario,
            Envelope::read(&hex::decode(base.tx).unwrap()[..]).unwrap(),
        );
        let mut encoded = vec![];
        envelope.write(&mut encoded).unwrap();
        assert_eq!(hex::encode(&encoded), ev.tx, "{}", ev.scenario);
        assert!(
            Transaction::read(&encoded[..], BranchId::Nu7_1).is_err(),
            "{}",
            ev.scenario
        );

        let txid = envelope.txid(|_| None).unwrap();
        assert_eq!(hex::encode(txid.as_ref()), ev.txid, "{}", ev.scenario);
        let auth = envelope.auth_digest(|_| None).unwrap();
        assert_eq!(
            hex::encode(auth.as_bytes()),
            ev.auth_digest,
            "{}",
            ev.scenario
        );
        // The identifier commits to effecting data only, which only the branch edit
        // changes.
        if ev.scenario != "unknown consensus branch ID" {
            assert_eq!(ev.txid, base.txid, "{}", ev.scenario);
        }
    }
}

/// A registered pair in a map the registry gives it no encoding in has no digest the
/// envelope can compute, so the caller supplies it, as for an unregistered pair.
#[test]
fn registered_pairs_outside_their_maps_take_supplied_digests() {
    let fee = data(5, 0, &[1]);
    let envelope = Envelope::new(header(), vec![], vec![fee.clone()], vec![]).unwrap();
    assert_matches::assert_matches!(
        envelope.txid(|_| None),
        Err(super::super::DigestError::MissingDigest(BundleId::FEE))
    );
    assert_eq!(
        envelope
            .txid(|id| (id == BundleId::FEE).then_some([0x33; 32]))
            .unwrap(),
        envelope
            .txid_with_bundle_digests(|_| Ok::<_, Infallible>([0x33; 32]))
            .unwrap()
    );
}

fn arb_bundle_id(bundle_type: u32) -> impl Strategy<Value = BundleId> {
    (0u32..3).prop_map(move |v| BundleId::new(BundleType::new(bundle_type), BundleVariant::new(v)))
}

prop_compose! {
    /// Envelopes over random well-formed maps: one variant per type, every authorizing
    /// entry paired with an effecting one.
    fn arb_envelope()(
        types in proptest::collection::btree_map(
            0u32..300,
            (0u32..3, proptest::option::of(any::<i64>().prop_filter("nonzero", |v| *v != 0)), any::<bool>(), any::<bool>()),
            0..6,
        ),
        consensus_branch_id in 1u32..,
        lock_time in any::<u32>(),
        expiry_height in any::<u32>(),
        payload in proptest::collection::vec(any::<u8>(), 0..300),
    ) -> Envelope {
        let mut deltas = vec![];
        let mut effects = vec![];
        let mut auths = vec![];
        for (bundle_type, (variant, value, effect, auth)) in types {
            let bundle = BundleId::new(BundleType::new(bundle_type), BundleVariant::new(variant));
            if let Some(value) = value {
                deltas.push(ValuePoolDelta { bundle, value: NonZeroI64::new(value).unwrap() });
            }
            if effect || auth {
                effects.push(BundleData { bundle, data: payload.clone() });
            }
            if auth {
                auths.push(BundleData { bundle, data: payload[..payload.len() / 2].to_vec() });
            }
        }
        Envelope::new(
            Header { consensus_branch_id, lock_time, expiry_height },
            deltas,
            effects,
            auths,
        )
        .unwrap()
    }
}

proptest! {
    /// The encoding is canonical: whatever parses writes back to the same bytes, so the
    /// parsed fields that the transaction identifier hashes determine the encoding.
    #[test]
    fn parsing_arbitrary_bytes_is_canonical(
        maps in proptest::collection::vec(any::<u8>(), 0..200),
    ) {
        let mut encoded = hex::decode(VECTOR_ENCODING).unwrap()[..20].to_vec();
        encoded.extend_from_slice(&maps);
        if let Ok(envelope) = Envelope::read(&encoded[..]) {
            let mut written = vec![];
            envelope.write(&mut written).unwrap();
            prop_assert_eq!(&encoded[..written.len()], &written[..]);
        }
    }

    #[test]
    fn envelope_round_trips(envelope in arb_envelope()) {
        let mut encoded = vec![];
        envelope.write(&mut encoded).unwrap();
        prop_assert_eq!(Envelope::read(&encoded[..]).unwrap(), envelope);
    }

    #[test]
    fn bundle_ids_round_trip_through_compact_size(id in (0u32..=0x0200_0000).prop_flat_map(arb_bundle_id)) {
        let envelope = Envelope::new(
            header(),
            vec![ValuePoolDelta { bundle: id, value: NonZeroI64::new(-1).unwrap() }],
            vec![],
            vec![],
        )
        .unwrap();
        let mut encoded = vec![];
        envelope.write(&mut encoded).unwrap();
        prop_assert_eq!(Envelope::read(&encoded[..]).unwrap(), envelope);
    }
}
