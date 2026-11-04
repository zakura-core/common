//! Dynamic proving across quotient windows, pinned to independently verified baseline proofs.
mod support;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;
use zakura_sensei::{
    CircuitVersion, ProvingRequest, VerificationRequest, create_proof, verify_proofs,
};

#[test]
#[cfg_attr(debug_assertions, ignore = "large proof generation requires --release")]
fn dynamic_proofs_match_independently_verified_baseline() {
    let action = support::decode_actions(include_bytes!("fixtures/one-action.iwpr"))
        .unwrap()
        .pop()
        .unwrap();
    // Distinct valid witnesses and public instances cross each window boundary.
    let mut actions = vec![action.clone()];
    actions.extend(support::decode_actions(include_bytes!("fixtures/two-action.iwpr")).unwrap());
    for count in [17, 65, 128] {
        let selected: Vec<_> = actions.iter().cycle().take(count).cloned().collect();
        let statements: Vec<_> = selected.iter().map(|a| a.statement.clone()).collect();
        let request = ProvingRequest::new(selected).unwrap();
        let mut rng = ChaCha20Rng::from_seed([count as u8; 32]);
        let mut draws = 0;
        let started = std::time::Instant::now();
        let proof = create_proof(&request, &mut || {
            draws += 1;
            Ok(rng.next_u64())
        })
        .unwrap();
        assert_eq!(draws, (148 * count + 46) * 8);
        assert_eq!(proof.len(), 2720 + 2272 * count);
        verify_proofs(
            &[VerificationRequest::new(CircuitVersion::PostNu6_3, &statements, &proof).unwrap()],
            &mut || Ok(rng.next_u64()),
        )
        .unwrap();
        use sha2::{Digest, Sha256};
        let digest = hex::encode(Sha256::digest(&proof));
        let manifest = include_str!("fixtures/migration/manifest.json");
        assert!(
            manifest.contains(&format!("\"large-{count}.proof\": \"{digest}\"")),
            "large proof compatibility: {count}"
        );
        eprintln!(
            "{count} actions: {} bytes, {:?}",
            proof.len(),
            started.elapsed()
        );
    }
    // Returning to the ordinary request path after the largest proof must work.
    let mut rng = ChaCha20Rng::from_seed([1; 32]);
    let statements = [action.statement.clone()];
    let request = ProvingRequest::new(vec![action]).unwrap();
    let proof = create_proof(&request, &mut || Ok(rng.next_u64())).unwrap();
    verify_proofs(
        &[VerificationRequest::new(CircuitVersion::PostNu6_3, &statements, &proof).unwrap()],
        &mut || Ok(rng.next_u64()),
    )
    .unwrap();
}
