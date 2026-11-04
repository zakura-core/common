//! Independent public-input decoding of frozen legacy verifier fixtures.
//!
//! See "Oracle independence" in `crates/sensei/src/native/mod.rs` for the
//! distinction between this decoder and the archived equation/acceptance oracles.

// Preserve the imported `chunks_exact` code, as in Udon. The pinned
// toolchain's Clippy predates this lint (introduced in 1.98).
#![allow(unknown_lints)]
#![allow(clippy::chunks_exact_to_as_chunks)]
#![allow(dead_code)]

use zakura_sensei::primitives::pallas;
use zakura_sensei::{CircuitVersion, Fp, PublicStatement, VerificationRequest};

pub const VERSIONS: [CircuitVersion; 3] = [
    CircuitVersion::PostNu6_3,
    CircuitVersion::FixedPostNu6_2,
    CircuitVersion::InsecurePreNu6_2,
];
pub const FIELD_BYTES: usize = 32;
pub const LEGACY_ROWS: usize = 9;
pub const CURRENT_ROWS: usize = 10;
const IWPR_HEADER: usize = 44;
const IWPR_ACTION: usize = 1_844;

pub struct Fixture {
    pub version: CircuitVersion,
    pub statements: Vec<PublicStatement>,
    /// Decoded directly from independent fixture bytes, never Sensei's native conversion.
    pub instances: Vec<Vec<pallas::Base>>,
    pub proof: &'static [u8],
}
impl Fixture {
    pub fn request(&self) -> VerificationRequest<'_> {
        VerificationRequest::new(self.version, &self.statements, self.proof).unwrap()
    }
}

pub fn from_instances(
    version: CircuitVersion,
    instances: Vec<Vec<pallas::Base>>,
    proof: &'static [u8],
) -> Fixture {
    let statements = instances
        .iter()
        .map(|row| {
            let field = |i: usize| Fp::from_bytes(row[i].to_repr()).unwrap();
            let flag = |i: usize| {
                assert!(row[i] == pallas::Base::from(0) || row[i] == pallas::Base::from(1));
                row[i] == pallas::Base::from(1)
            };
            PublicStatement {
                anchor: field(0),
                cv_net: (field(1), field(2)),
                nf_old: field(3),
                rk: (field(4), field(5)),
                cmx: field(6),
                enable_spend: flag(7),
                enable_output: flag(8),
                disable_cross_address: row.len() == CURRENT_ROWS && flag(9),
            }
        })
        .collect();
    Fixture {
        version,
        statements,
        instances,
        proof,
    }
}

fn decode_rows(bytes: &[u8], rows: usize) -> Vec<Vec<pallas::Base>> {
    assert!(bytes.len().is_multiple_of(rows * FIELD_BYTES));
    bytes
        .chunks_exact(rows * FIELD_BYTES)
        .map(|row| {
            row.chunks_exact(FIELD_BYTES)
                .map(|v| pallas::Base::from_repr(v.try_into().unwrap()).unwrap())
                .collect()
        })
        .collect()
}

pub fn current(count: usize) -> Fixture {
    let (iwpr, proof): (&[u8], &'static [u8]) = match count {
        1 => (
            include_bytes!("../fixtures/one-action.iwpr"),
            include_bytes!("../fixtures/golden/one-action.proof"),
        ),
        2 => (
            include_bytes!("../fixtures/two-action.iwpr"),
            include_bytes!("../fixtures/golden/two-action.proof"),
        ),
        _ => panic!("current committed fixture count"),
    };
    assert_eq!(iwpr.len(), IWPR_HEADER + count * IWPR_ACTION);
    let instances = iwpr[IWPR_HEADER..]
        .chunks_exact(IWPR_ACTION)
        .map(|action| {
            decode_rows(&action[..CURRENT_ROWS * FIELD_BYTES], CURRENT_ROWS)
                .pop()
                .unwrap()
        })
        .collect();
    from_instances(CircuitVersion::PostNu6_3, instances, proof)
}

macro_rules! historical {
    ($version:expr, $stem:literal) => {
        from_instances(
            $version,
            decode_rows(
                include_bytes!(concat!("../fixtures/legacy/", $stem, ".instances")),
                LEGACY_ROWS,
            ),
            include_bytes!(concat!("../fixtures/legacy/", $stem, ".proof")),
        )
    };
}
pub fn historical(version: CircuitVersion, count: usize) -> Fixture {
    use CircuitVersion::*;
    match (version, count) {
        (FixedPostNu6_2, 1) => historical!(version, "fixed-1"),
        (FixedPostNu6_2, 2) => historical!(version, "fixed-2"),
        (FixedPostNu6_2, 3) => historical!(version, "fixed-3"),
        (FixedPostNu6_2, 65) => historical!(version, "fixed-65"),
        (FixedPostNu6_2, 128) => historical!(version, "fixed-128"),
        (InsecurePreNu6_2, 1) => historical!(version, "insecure-1"),
        (InsecurePreNu6_2, 2) => historical!(version, "insecure-2"),
        (InsecurePreNu6_2, 3) => historical!(version, "insecure-3"),
        (InsecurePreNu6_2, 65) => historical!(version, "insecure-65"),
        (InsecurePreNu6_2, 128) => historical!(version, "insecure-128"),
        _ => panic!("historical fixture count"),
    }
}
pub fn small(version: CircuitVersion, count: usize) -> Fixture {
    if version == CircuitVersion::PostNu6_3 {
        current(count)
    } else {
        historical(version, count)
    }
}
pub fn flags() -> [Fixture; 6] {
    use CircuitVersion::*;
    [
        historical!(FixedPostNu6_2, "fixed-flags-0"),
        historical!(FixedPostNu6_2, "fixed-flags-1"),
        historical!(FixedPostNu6_2, "fixed-flags-2"),
        historical!(InsecurePreNu6_2, "insecure-flags-0"),
        historical!(InsecurePreNu6_2, "insecure-flags-1"),
        historical!(InsecurePreNu6_2, "insecure-flags-2"),
    ]
}

/// Original Orchard fixtures store five canonical values, including compressed
/// cv/rk points, two flags (three for current), and the proof bytes.
pub fn original(version: CircuitVersion, restricted: bool) -> Fixture {
    use CircuitVersion::*;
    let bytes: &'static [u8] = match (version, restricted) {
        (InsecurePreNu6_2, false) => {
            include_bytes!("../../../orchard/src/circuit_data/circuit_proof_test_case_insecure.bin")
        }
        (FixedPostNu6_2, false) => {
            include_bytes!("../../../orchard/src/circuit_data/circuit_proof_test_case_fixed.bin")
        }
        (PostNu6_3, false) => include_bytes!(
            "../../../orchard/src/circuit_data/circuit_proof_test_case_post_nu6_3.bin"
        ),
        (PostNu6_3, true) => include_bytes!(
            "../../../orchard/src/circuit_data/circuit_proof_test_case_post_nu6_3_restricted.bin"
        ),
        _ => panic!("historical restriction"),
    };
    let word = |i| {
        bytes[i * FIELD_BYTES..(i + 1) * FIELD_BYTES]
            .try_into()
            .unwrap()
    };
    let field = |i| pallas::Base::from_repr(word(i)).unwrap();
    let coords = |i| {
        let point = pallas::Affine::from_bytes(word(i)).unwrap();
        Option::from(point.coordinates())
            .map_or([pallas::Base::from(0); 2], |c: pallas::Coordinates| {
                [*c.x(), *c.y()]
            })
    };
    let cv = coords(1);
    let rk = coords(3);
    let flags_offset = 5 * FIELD_BYTES;
    let flag_count = if version == PostNu6_3 { 3 } else { 2 };
    let mut row = vec![field(0), cv[0], cv[1], field(2), rk[0], rk[1], field(4)];
    row.extend(
        bytes[flags_offset..flags_offset + flag_count]
            .iter()
            .map(|&b| {
                assert!(b <= 1);
                pallas::Base::from(u64::from(b))
            }),
    );
    from_instances(version, vec![row], &bytes[flags_offset + flag_count..])
}

/// The historical pinned descriptions are metadata, not reconstructed circuits.
pub fn pinned_description(version: CircuitVersion) -> &'static str {
    // Share Orchard's authoritative fixtures instead of duplicating them here.
    // Sensei is unpublished; these relative paths intentionally depend on the
    // workspace's Orchard file layout.
    match version {
        CircuitVersion::PostNu6_3 => {
            include_str!("../../../orchard/src/circuit_data/circuit_description_post_nu6_3")
        }
        CircuitVersion::FixedPostNu6_2 => {
            include_str!("../../../orchard/src/circuit_data/circuit_description_fixed")
        }
        CircuitVersion::InsecurePreNu6_2 => {
            include_str!("../../../orchard/src/circuit_data/circuit_description_insecure")
        }
    }
}

/// Additional current proofs generated by the archived Halo2 implementation.
pub fn migrated_current(count: usize, restricted: bool) -> Fixture {
    let (rows, proof): (&[u8], &'static [u8]) = match (count, restricted) {
        (3, false) => (
            include_bytes!("../fixtures/migration/current-3-0.instances"),
            include_bytes!("../fixtures/migration/current-3-0.proof"),
        ),
        (3, true) => (
            include_bytes!("../fixtures/migration/current-3-1.instances"),
            include_bytes!("../fixtures/migration/current-3-1.proof"),
        ),
        (65, true) => (
            include_bytes!("../fixtures/migration/current-65-1.instances"),
            include_bytes!("../fixtures/migration/current-65-1.proof"),
        ),
        (128, true) => (
            include_bytes!("../fixtures/migration/current-128-1.instances"),
            include_bytes!("../fixtures/migration/current-128-1.proof"),
        ),
        _ => panic!("committed current fixture count and policy"),
    };
    from_instances(
        CircuitVersion::PostNu6_3,
        decode_rows(rows, CURRENT_ROWS),
        proof,
    )
}
