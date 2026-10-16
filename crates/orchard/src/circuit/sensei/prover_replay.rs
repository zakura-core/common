//! Preserve the independently pinned Ironwood Lean execution anchors.
use super::{OrchardCircuitVersion, ProvingKey, VerifyingKey};
use core::{convert::Infallible, mem::size_of};
use rand::{Rng, SeedableRng, TryRng};
use rand_chacha::ChaCha20Rng;

/// Public seeds used by the historical one- and two-action captures.
const SINGLE_SEED: u8 = 0x53;
const MULTI_SEED: u8 = 0x4d;
/// Canonical byte width of the fixture's RNG seed.
const SEED_BYTES: usize = 32;

struct PinnedRng<'a> {
    inner: &'a mut ChaCha20Rng,
    remaining: &'static [u8],
}
impl TryRng for PinnedRng<'_> {
    type Error = Infallible;
    fn try_next_u32(&mut self) -> Result<u32, Infallible> {
        panic!("the pinned prover uses only next_u64");
    }
    fn try_next_u64(&mut self) -> Result<u64, Infallible> {
        let (word, rest) = self
            .remaining
            .split_first_chunk::<{ size_of::<u64>() }>()
            .expect("prover exceeded the pinned tape");
        let word = u64::from_le_bytes(*word);
        assert_eq!(self.inner.next_u64(), word, "fixture randomness changed");
        self.remaining = rest;
        Ok(word)
    }
    fn try_fill_bytes(&mut self, _: &mut [u8]) -> Result<(), Infallible> {
        panic!("the pinned prover uses only next_u64");
    }
}
#[test]
#[cfg_attr(debug_assertions, ignore = "exact proof replay requires --release")]
fn independently_pinned_lean_proofs_and_rng_tapes() {
    let version = OrchardCircuitVersion::PostNu6_3;
    let pk = ProvingKey::build(version).unwrap();
    let vk = VerifyingKey::build(version);
    for (seed, count, tape, expected) in [
        (
            SINGLE_SEED,
            1,
            include_bytes!("../prover_fingerprint/single-action.rng-u64s-le").as_slice(),
            include_bytes!("../prover_fingerprint/single-action.proof").as_slice(),
        ),
        (
            MULTI_SEED,
            2,
            include_bytes!("../prover_fingerprint/multi-action.rng-u64s-le").as_slice(),
            include_bytes!("../prover_fingerprint/multi-action.proof").as_slice(),
        ),
    ] {
        let mut rng = ChaCha20Rng::from_seed([seed; SEED_BYTES]);
        let bundle = crate::builder::testing::build_pinned_fixture_bundle(&mut rng, count);
        let instances = bundle.to_instances();
        let mut pinned = PinnedRng {
            inner: &mut rng,
            remaining: tape,
        };
        let proof = bundle
            .authorization()
            .create_proof(&pk, &instances, &mut pinned)
            .unwrap();
        assert!(
            pinned.remaining.is_empty(),
            "prover did not consume the complete tape"
        );
        assert_eq!(proof.as_ref(), expected);
        proof.verify(&vk, &instances).unwrap();
    }
}
