//! Byte-exact golden replay of the committed reference proofs.
//!
//! This harness compiles only against Sensei's public API, so it doubles as a
//! backwards-compatibility check on that surface: internals under `src/` may
//! change freely, but this file must keep compiling and its assertions must
//! keep passing. Its IWPR/1 fixture decoder (`tests/support/`) and tape-replay
//! randomness source are independent of the crate's internal test scaffolding,
//! deliberately sharing no code with the implementation.

// Preserve the imported `chunks_exact` code, as in Udon. The pinned
// toolchain's Clippy predates this lint (introduced in 1.98).
#![allow(unknown_lints)]
#![allow(clippy::chunks_exact_to_as_chunks)]

mod support;

use zakura_sensei as sensei;

use sensei::{Error, ProvingRequest, RandomSource, RandomnessError, create_proof};

use support::{HEADER_SIZE, decode_actions, decode_request};

struct ReplayRng<'a> {
    tape: &'a [u64],
    cursor: usize,
}

impl<'a> ReplayRng<'a> {
    fn new(tape: &'a [u64]) -> Self {
        Self { tape, cursor: 0 }
    }

    fn consumed(&self) -> usize {
        self.cursor
    }
}

impl RandomSource for ReplayRng<'_> {
    fn next_u64(&mut self) -> Result<u64, RandomnessError> {
        let value = self.tape.get(self.cursor).copied().ok_or(RandomnessError)?;
        self.cursor += 1;
        Ok(value)
    }
}

struct GoldenFixture {
    name: &'static str,
    request: &'static [u8],
    tape: &'static [u8],
    proof: &'static [u8],
    rng_calls: usize,
    proof_bytes: usize,
}

const GOLDEN_FIXTURES: [GoldenFixture; 2] = [
    GoldenFixture {
        name: "one-action",
        request: include_bytes!("fixtures/one-action.iwpr"),
        tape: include_bytes!("fixtures/golden/one-action.rng-u64s-le"),
        proof: include_bytes!("fixtures/golden/one-action.proof"),
        rng_calls: 1_552,
        proof_bytes: 4_992,
    },
    GoldenFixture {
        name: "two-action",
        request: include_bytes!("fixtures/two-action.iwpr"),
        tape: include_bytes!("fixtures/golden/two-action.rng-u64s-le"),
        proof: include_bytes!("fixtures/golden/two-action.proof"),
        rng_calls: 2_736,
        proof_bytes: 7_264,
    },
];

#[cfg_attr(debug_assertions, ignore = "exact proof generation requires --release")]
#[test]
fn native_prover_matches_committed_reference_goldens() {
    let selected = std::env::var_os("SENSEI_GOLDEN_FIXTURE");
    let mut fixtures_run = 0;
    for fixture in GOLDEN_FIXTURES {
        if selected.as_deref().is_some_and(|name| name != fixture.name) {
            continue;
        }
        fixtures_run += 1;
        assert_eq!(fixture.tape.len(), fixture.rng_calls * size_of::<u64>());
        assert_eq!(fixture.proof.len(), fixture.proof_bytes);

        let tape = fixture
            .tape
            .chunks_exact(size_of::<u64>())
            .map(|bytes| u64::from_le_bytes(bytes.try_into().unwrap()))
            .collect::<Vec<_>>();
        let expected_rng_calls = fixture.rng_calls;
        let request = decode_request(fixture.request).unwrap();
        let mut replay = ReplayRng::new(&tape);
        let proof = create_proof(&request, &mut replay).unwrap();

        assert_eq!(proof, fixture.proof);
        assert_eq!(replay.consumed(), expected_rng_calls);
        assert_eq!(replay.consumed(), tape.len());
    }
    assert!(
        fixtures_run != 0,
        "unknown SENSEI_GOLDEN_FIXTURE: {selected:?}"
    );
}

#[test]
fn harness_codec_is_strict() {
    const FIXTURE: &[u8] = include_bytes!("fixtures/one-action.iwpr");

    assert_eq!(decode_actions(FIXTURE).unwrap().len(), 1);
    assert_eq!(
        decode_request(&FIXTURE[..HEADER_SIZE]).err(),
        Some(Error::InvalidInput)
    );

    let mut trailing = FIXTURE.to_vec();
    trailing.push(0);
    assert_eq!(decode_request(&trailing).err(), Some(Error::InvalidInput));

    let mut wrong_target = FIXTURE.to_vec();
    wrong_target[8] ^= 1;
    assert_eq!(
        decode_request(&wrong_target).err(),
        Some(Error::InvalidInput)
    );
}

#[test]
fn public_request_construction_accepts_documented_shapes() {
    const FIXTURE: &[u8] = include_bytes!("fixtures/one-action.iwpr");

    assert_eq!(
        ProvingRequest::new(Vec::new()).err(),
        Some(Error::InvalidInput)
    );

    for count in [63, 64, 65, 128] {
        let actions = (0..count)
            .map(|_| {
                decode_actions(FIXTURE)
                    .unwrap()
                    .pop()
                    .expect("fixture holds one Action")
            })
            .collect::<Vec<_>>();
        ProvingRequest::new(actions).expect("representable nonempty requests are accepted");
    }
}
