//! Deterministic real-bundle construction shared by the opt-in fingerprint exporters.

use incrementalmerkletree::Hashable;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

use super::ProvingKey;
use crate::{
    builder::{Builder, BundleType},
    bundle::BundleVersion,
    constants::MERKLE_DEPTH_ORCHARD,
    tree::MerkleHashOrchard,
};

pub(super) fn fixture_rng(seed: u8) -> ChaCha20Rng {
    ChaCha20Rng::from_seed([seed; 32])
}

pub(super) fn build_fixture_bundle(
    rng: &mut ChaCha20Rng,
    pk: &ProvingKey,
    num_actions: u8,
) -> crate::Bundle<crate::bundle::Authorized, i64> {
    let bundle_version = BundleVersion::orchard_v3();
    let builder = Builder::new(
        BundleType::Transactional {
            bundle_required: true,
            pad_to_minimum: Some(num_actions),
        },
        bundle_version,
        bundle_version.default_flags(),
        MerkleHashOrchard::empty_root((MERKLE_DEPTH_ORCHARD as u8).into()).into(),
    )
    .unwrap();
    let bundle = builder.build::<i64>(&mut *rng).unwrap().unwrap().0;
    assert_eq!(bundle.actions().len(), usize::from(num_actions));
    assert!(!bundle.flags().cross_address_enabled());

    bundle
        .create_proof(pk, &mut *rng)
        .unwrap()
        .apply_signatures(&mut *rng, [0; 32], &[])
        .unwrap()
}
