//! Deterministic real-bundle construction shared by the opt-in fingerprint exporters.

use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

use super::ProvingKey;
use crate::builder::{UnauthorizedBundle, testing::build_pinned_fixture_bundle};

pub(super) fn fixture_rng(seed: u8) -> ChaCha20Rng {
    ChaCha20Rng::from_seed([seed; 32])
}

pub(super) fn build_fixture_bundle(
    rng: &mut ChaCha20Rng,
    pk: &ProvingKey,
    num_actions: u8,
) -> crate::Bundle<crate::bundle::Authorized, i64> {
    build_unproven_fixture_bundle(rng, num_actions)
        .create_proof(pk, &mut *rng)
        .unwrap()
        .apply_signatures(&mut *rng, [0; 32], &[])
        .unwrap()
}

pub(super) fn build_unproven_fixture_bundle(
    rng: &mut ChaCha20Rng,
    num_actions: u8,
) -> UnauthorizedBundle<i64> {
    let bundle = build_pinned_fixture_bundle(rng, num_actions);
    assert_eq!(bundle.actions().len(), usize::from(num_actions));
    assert!(!bundle.flags().cross_address_enabled());

    bundle
}
