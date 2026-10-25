//! Byte fixtures exported by the independent pre-migration Pasta implementation.

// Preserve the imported `chunks_exact` code, as in Udon. The pinned
// toolchain's Clippy predates this lint (introduced in 1.98).
#![allow(unknown_lints)]
#![allow(clippy::chunks_exact_to_as_chunks)]

use zakura_sensei::{
    Fp, Fq, NonIdentityPallasPoint,
    primitives::{
        agreement::{PreparedBase, PreparedScalar},
        pallas,
    },
};

fn corpus() -> Vec<[u8; 32]> {
    include_bytes!("fixtures/migration/primitives.bin")
        .chunks_exact(32)
        .map(|v| v.try_into().unwrap())
        .collect()
}
#[test]
fn native_fields_and_hash_to_curve_match_legacy() {
    let corpus = corpus();
    let mut expected = corpus[..64 * 8].iter();
    for seed in 0..64u64 {
        let wide =
            core::array::from_fn(|i| (seed.wrapping_mul(37).wrapping_add(i as u64 * 13)) as u8);
        let base = Fp::from_uniform_bytes(&wide);
        let scalar = Fq::from_uniform_bytes(&wide);
        for value in [
            base.to_bytes(),
            base.square().to_bytes(),
            base.invert().unwrap().to_bytes(),
            scalar.to_bytes(),
            (pallas::Point::generator() * scalar).to_bytes(),
        ] {
            assert_eq!(&value, expected.next().unwrap());
        }
        for domain in ["z.cash:Orchard-gd", "z.cash:SinsemillaQ", "z.cash:test"] {
            assert_eq!(
                &pallas::Point::hash_to_curve(domain)(&wide).to_bytes(),
                expected.next().unwrap()
            );
        }
    }
    assert!(expected.next().is_none());
}
#[test]
fn prepared_agreement_matches_legacy_across_live_thresholds() {
    let corpus = corpus();
    let agreement = &corpus[64 * 8..];
    let prepared = PreparedScalar::new(Fq::from_bytes(agreement[0]).unwrap());
    let rows: Vec<_> = agreement[1..].chunks_exact(3).collect();
    let native: Vec<_> = rows
        .iter()
        .map(|r| NonIdentityPallasPoint::from_bytes(r[0]).unwrap())
        .collect();
    let mut counts = vec![0, 1, 7, 8, 9, 31, 65, 127, 128, 129];
    counts.extend(32..=64);
    for n in counts {
        let tables = PreparedBase::batch(&native[..n]);
        let refs: Vec<_> = tables.iter().rev().collect();
        let actual = PreparedBase::multiply_batch(&refs, &prepared);
        for (actual, row) in actual.iter().zip(rows[..n].iter().rev()) {
            assert_eq!(actual.to_bytes(), row[1]);
        }
        // Independently prepared and repeated owners exercise the borrowed path.
        let single = PreparedBase::new(native[0]);
        let repeated = PreparedBase::multiply_batch(&vec![&single; n], &prepared);
        assert!(repeated.iter().all(|p| p.to_bytes() == rows[0][1]));
        assert_eq!(PreparedBase::TABLE_BYTES, 1024);
        let projective: Vec<_> = rows[..n]
            .iter()
            .map(|r| pallas::Point::from_bytes(&r[0]).unwrap().double())
            .collect();
        for (actual, row) in prepared
            .multiply_unprepared(&projective)
            .iter()
            .zip(&rows[..n])
        {
            assert_eq!(actual.to_bytes(), row[2]);
        }
    }
}

#[test]
fn prepared_agreement_debug_redacts_key_material() {
    let compact = "PreparedScalar { scalar: \"<redacted>\", schedule: \"<redacted>\" }";
    let pretty = concat!(
        "PreparedScalar {\n",
        "    scalar: \"<redacted>\",\n",
        "    schedule: \"<redacted>\",\n",
        "}",
    );
    for bytes in [[0; 32], [0x11; 32]] {
        let prepared = PreparedScalar::new(Fq::from_bytes(bytes).unwrap());
        let cloned = prepared.clone();
        for value in [&prepared, &cloned] {
            assert!(
                format!("{value:?}") == compact,
                "Debug must redact both the scalar and schedule",
            );
            assert!(
                format!("{value:#?}") == pretty,
                "pretty Debug must redact both the scalar and schedule",
            );
        }
    }
}

#[test]
fn independent_migration_fixtures_match_the_manifest() {
    use sha2::{Digest, Sha256};
    let manifest = include_str!("fixtures/migration/manifest.json");
    macro_rules! check {
        ($name:literal) => {{
            let digest = hex::encode(Sha256::digest(include_bytes!(concat!(
                "fixtures/migration/",
                $name
            ))));
            assert!(manifest.contains(&format!("\"{}\": \"{digest}\"", $name)));
        }};
    }
    check!("primitives.bin");
    check!("poseidon-permute.bin");
    check!("poseidon-hash.bin");
    check!("equations.bin");
    check!("current-3-0.instances");
    check!("current-3-0.proof");
    check!("current-3-1.instances");
    check!("current-3-1.proof");
    check!("current-65-1.instances");
    check!("current-65-1.proof");
    check!("current-128-1.instances");
    check!("current-128-1.proof");
}

#[test]
fn orchard_sinsemilla_q_generators_match_historical_coordinates() {
    use zakura_sensei::primitives::sinsemilla::HashDomain;
    // Affine coordinates recorded by the independent pre-migration Orchard
    // constants for each protocol Sinsemilla domain's Q generator.
    const PINNED: [(&str, [u8; 32], [u8; 32]); 3] = [
        (
            "z.cash:Orchard-NoteCommit-M",
            [
                93, 116, 168, 64, 9, 186, 14, 50, 42, 221, 70, 253, 90, 15, 150, 197, 93, 237, 176,
                121, 180, 242, 159, 247, 13, 205, 251, 86, 160, 7, 128, 23,
            ],
            [
                99, 172, 73, 115, 90, 10, 39, 135, 158, 94, 219, 129, 136, 18, 34, 136, 44, 201,
                244, 110, 217, 194, 190, 78, 131, 112, 198, 138, 147, 88, 160, 50,
            ],
        ),
        (
            "z.cash:Orchard-CommitIvk-M",
            [
                242, 130, 15, 121, 146, 47, 203, 107, 50, 162, 40, 81, 36, 204, 27, 66, 250, 65,
                162, 90, 184, 129, 204, 125, 17, 200, 169, 74, 241, 12, 188, 5,
            ],
            [
                190, 222, 173, 207, 206, 229, 90, 190, 241, 165, 109, 201, 29, 53, 196, 70, 75, 5,
                222, 32, 70, 7, 89, 239, 230, 190, 26, 212, 246, 76, 1, 27,
            ],
        ),
        (
            "z.cash:Orchard-MerkleCRH",
            [
                160, 198, 41, 127, 249, 199, 185, 248, 112, 16, 141, 192, 85, 185, 190, 201, 153,
                14, 137, 239, 90, 54, 15, 160, 185, 24, 168, 99, 150, 210, 22, 22,
            ],
            [
                98, 234, 242, 37, 206, 174, 233, 134, 150, 21, 116, 5, 234, 150, 28, 226, 121, 89,
                163, 79, 62, 242, 196, 45, 153, 32, 175, 227, 163, 66, 134, 53,
            ],
        ),
    ];
    for (domain, x, y) in PINNED {
        // Hashing the empty message returns the domain's Q generator.
        let q = HashDomain::new(domain)
            .hash_to_point(core::iter::empty())
            .unwrap()
            .to_affine();
        let coordinates = q.coordinates().unwrap();
        assert_eq!(coordinates.x(), &Fp::from_bytes(x).unwrap(), "{domain} x");
        assert_eq!(coordinates.y(), &Fp::from_bytes(y).unwrap(), "{domain} y");
    }
}

#[test]
fn orchard_poseidon_matches_independent_protocol_vectors() {
    use zakura_sensei::primitives::poseidon;
    for row in include_bytes!("fixtures/migration/poseidon-permute.bin").chunks_exact(6 * 32) {
        let words: Vec<[u8; 32]> = row
            .chunks_exact(32)
            .map(|v| v.try_into().unwrap())
            .collect();
        let mut state = core::array::from_fn(|i| Fp::from_bytes(words[i]).unwrap());
        poseidon::permute(&mut state);
        assert_eq!(state.map(Fp::to_bytes).as_slice(), &words[3..]);
    }
    for row in include_bytes!("fixtures/migration/poseidon-hash.bin").chunks_exact(3 * 32) {
        let input = core::array::from_fn(|i| {
            Fp::from_bytes(row[i * 32..(i + 1) * 32].try_into().unwrap()).unwrap()
        });
        assert_eq!(poseidon::hash(input).to_bytes().as_slice(), &row[64..]);
    }
}
