//! Public API compatibility and shared worker checks.

mod support;

use sensei::{Error, Fp, Fq, Fr, NonIdentityPallasPoint, PallasPoint, ProvingRequest};
use sensei::{
    RandomSource, RandomnessError, SpendValidatingKey, VerificationRequest, create_proof,
    verify_proofs, warm_up, warm_up_prover, warm_up_verifier,
};
use std::cell::Cell;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::rc::Rc;
use std::sync::Barrier;
use zakura_sensei as sensei;

const REQUEST: &[u8] = include_bytes!("fixtures/one-action.iwpr");
const TAPE: &[u8] = include_bytes!("fixtures/golden/one-action.rng-u64s-le");
const PROOF: &[u8] = include_bytes!("fixtures/golden/one-action.proof");

#[test]
fn field_encoding_and_scalar_alias_are_preserved() {
    let _zero = Fp::from_bytes([0; 32]).unwrap();
    let _: Fr = Fq::from_bytes([0; 32]).unwrap();
}

#[test]
fn point_identity_acceptance_is_preserved() {
    assert!(PallasPoint::from_bytes([0; 32]).is_ok());
    assert!(matches!(
        NonIdentityPallasPoint::from_bytes([0; 32]),
        Err(Error::InvalidInput)
    ));
    assert!(matches!(
        SpendValidatingKey::from_bytes([0; 32]),
        Err(Error::InvalidInput)
    ));
}

#[test]
fn invalid_point_encodings_are_rejected() {
    assert!(matches!(
        PallasPoint::from_bytes([255; 32]),
        Err(Error::InvalidInput)
    ));
    assert!(matches!(
        NonIdentityPallasPoint::from_bytes([255; 32]),
        Err(Error::InvalidInput)
    ));
    assert!(matches!(
        SpendValidatingKey::from_bytes([255; 32]),
        Err(Error::InvalidInput)
    ));
}

#[test]
fn proving_request_preserves_identity_rules() {
    let zero = Fp::from_bytes([0; 32]).unwrap();
    let mut actions = support::decode_actions(REQUEST).unwrap();
    actions[0].statement.cv_net = (zero, zero);
    ProvingRequest::new(actions.clone()).expect("the value commitment may be the identity");
    actions[0].statement.rk = (zero, zero);
    assert!(matches!(
        ProvingRequest::new(actions),
        Err(Error::InvalidInput)
    ));
}

#[test]
fn proving_request_rejects_off_curve_value_commitments() {
    let zero = Fp::from_bytes([0; 32]).unwrap();
    let mut actions = support::decode_actions(REQUEST).unwrap();
    let mut one = [0; 32];
    one[0] = 1;
    actions[0].statement.cv_net = (zero, Fp::from_bytes(one).unwrap());
    assert!(matches!(
        ProvingRequest::new(actions),
        Err(Error::InvalidInput)
    ));
}

fn replay(request: &ProvingRequest, reentrant: bool) {
    // The original RandomSource accepts caller-local state without Send or
    // Sync. Keep this RNG on the caller even when proving uses worker threads.
    let cursor = Rc::new(Cell::new(0));
    let caller = std::thread::current().id();
    let mut rng = || {
        assert_eq!(std::thread::current().id(), caller);
        if reentrant && cursor.get() == 0 {
            warm_up();
            replay(request, false);
            let mut failed_rng = || Err(RandomnessError);
            assert_eq!(
                create_proof(request, &mut failed_rng),
                Err(Error::RngFailure)
            );
        }
        let offset = cursor.get();
        let word = TAPE.get(offset..offset + 8).ok_or(RandomnessError)?;
        cursor.set(offset + 8);
        Ok(u64::from_le_bytes(word.try_into().unwrap()))
    };
    assert_eq!(create_proof(request, &mut rng).unwrap(), PROOF);
    assert_eq!(cursor.get(), TAPE.len());
}

#[test]
#[cfg_attr(debug_assertions, ignore = "proof replay requires --release")]
fn initialization_concurrency_and_error_recovery_preserve_proofs() {
    let _: fn(&ProvingRequest, &mut dyn RandomSource) -> Result<Vec<u8>, Error> = create_proof;
    let _: fn() = warm_up;
    let _: fn() = warm_up_prover;
    let _: fn() = warm_up_verifier;
    let actions = support::decode_actions(REQUEST).unwrap();
    let statements: Vec<_> = actions
        .iter()
        .map(|action| action.statement.clone())
        .collect();
    let request = ProvingRequest::new(actions).unwrap();
    let verification =
        VerificationRequest::new(zakura_sensei::CircuitVersion::PostNu6_3, &statements, PROOF)
            .unwrap();

    // This integration-test process begins cold. Race warming and verification
    // with two proofs, then replay after repeated warming.
    let barrier = Barrier::new(5);
    std::thread::scope(|scope| {
        scope.spawn(|| {
            barrier.wait();
            warm_up_prover();
            warm_up_prover();
        });
        scope.spawn(|| {
            barrier.wait();
            warm_up_verifier();
            warm_up_verifier();
        });
        scope.spawn(|| {
            barrier.wait();
            assert_eq!(
                verify_proofs(&[verification], &mut || {
                    panic!("singleton must not consume randomness")
                }),
                Ok(())
            );
        });
        for _ in 0..2 {
            scope.spawn(|| {
                barrier.wait();
                replay(&request, false);
            });
        }
    });
    warm_up();
    warm_up_prover();
    warm_up_verifier();

    // Both failure paths leave later proofs usable. Reentrant randomness also
    // checks that an internal workspace lock is not held across caller code.
    let mut failed_rng = || Err(RandomnessError);
    assert_eq!(
        create_proof(&request, &mut failed_rng),
        Err(Error::RngFailure)
    );
    let mut panicking_rng = || -> Result<u64, RandomnessError> { panic!("test RNG panic") };
    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            create_proof(&request, &mut panicking_rng)
        }))
        .is_err()
    );
    replay(&request, true);
}
