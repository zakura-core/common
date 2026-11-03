#![cfg(feature = "alloc")]

use rand::rng as thread_rng;

use jubjub::AffinePoint;
use reddsa::*;

#[test]
fn spendauth_batch_verify() {
    let mut rng = thread_rng();
    let mut batch = batch::Verifier::<_, sapling::Binding>::new();
    for _ in 0..32 {
        let sk = SigningKey::<sapling::SpendAuth>::new(&mut rng);
        let vk = VerificationKey::from(&sk);
        let msg = b"BatchVerifyTest";
        let sig = sk.sign(&mut rng, &msg[..]);
        batch.queue(batch::Item::from_spendauth(vk.into(), sig, msg));
    }
    assert!(batch.verify(rng).is_ok());
}

#[test]
fn binding_batch_verify() {
    let mut rng = thread_rng();
    let mut batch = batch::Verifier::<sapling::SpendAuth, _>::new();
    for _ in 0..32 {
        let sk = SigningKey::<sapling::Binding>::new(&mut rng);
        let vk = VerificationKey::from(&sk);
        let msg = b"BatchVerifyTest";
        let sig = sk.sign(&mut rng, &msg[..]);
        batch.queue(batch::Item::from_binding(vk.into(), sig, msg));
    }
    assert!(batch.verify(rng).is_ok());
}

#[test]
fn alternating_batch_verify() {
    let mut rng = thread_rng();
    let mut batch = batch::Verifier::new();
    for i in 0..32 {
        let item = match i % 2 {
            0 => {
                let sk = SigningKey::<sapling::SpendAuth>::new(&mut rng);
                let vk = VerificationKey::from(&sk);
                let msg = b"BatchVerifyTest";
                let sig = sk.sign(&mut rng, &msg[..]);
                batch::Item::from_spendauth(vk.into(), sig, msg)
            }
            1 => {
                let sk = SigningKey::<sapling::Binding>::new(&mut rng);
                let vk = VerificationKey::from(&sk);
                let msg = b"BatchVerifyTest";
                let sig = sk.sign(&mut rng, &msg[..]);
                batch::Item::from_binding(vk.into(), sig, msg)
            }
            _ => unreachable!(),
        };
        batch.queue(item);
    }
    assert!(batch.verify(rng).is_ok());
}

#[test]
fn bad_batch_verify() {
    let mut rng = thread_rng();
    let bad_index = 4; // must be even
    let mut batch = batch::Verifier::new();
    let mut items = Vec::new();
    for i in 0..32 {
        let item = match i % 2 {
            0 => {
                let sk = SigningKey::<sapling::SpendAuth>::new(&mut rng);
                let vk = VerificationKey::from(&sk);
                let msg = b"BatchVerifyTest";
                let sig = if i != bad_index {
                    sk.sign(&mut rng, &msg[..])
                } else {
                    sk.sign(&mut rng, b"bad")
                };
                batch::Item::from_spendauth(vk.into(), sig, msg)
            }
            1 => {
                let sk = SigningKey::<sapling::Binding>::new(&mut rng);
                let vk = VerificationKey::from(&sk);
                let msg = b"BatchVerifyTest";
                let sig = sk.sign(&mut rng, &msg[..]);
                batch::Item::from_binding(vk.into(), sig, msg)
            }
            _ => unreachable!(),
        };
        items.push(item.clone());
        batch.queue(item);
    }
    assert!(batch.verify(rng).is_err());
    for (i, item) in items.drain(..).enumerate() {
        if i != bad_index {
            assert!(item.verify_single().is_ok());
        } else {
            assert!(item.verify_single().is_err());
        }
    }
}

#[test]
fn malformed_batch_encodings_preserve_errors() {
    let mut rng = thread_rng();
    let sk = SigningKey::<sapling::SpendAuth>::new(&mut rng);
    let vk_bytes = VerificationKey::from(&sk).into();
    let msg = b"BatchVerifyTest";
    let sig = sk.sign(&mut rng, msg);
    let malformed_vk = VerificationKeyBytes::from([0xff; 32]);

    let mut batch = batch::Verifier::<_, sapling::Binding>::new();
    batch.queue(batch::Item::from_spendauth(malformed_vk, sig, msg));
    assert_eq!(batch.verify(&mut rng), Err(Error::MalformedVerificationKey));

    let mut sig_bytes: [u8; 64] = sig.into();
    sig_bytes[..32].fill(0xff);
    let mut batch = batch::Verifier::<_, sapling::Binding>::new();
    batch.queue(batch::Item::from_spendauth(vk_bytes, sig_bytes.into(), msg));
    assert_eq!(batch.verify(&mut rng), Err(Error::InvalidSignature));

    sig_bytes[32..].fill(0xff);
    let mut batch = batch::Verifier::<sapling::SpendAuth, sapling::Binding>::new();
    batch.queue(batch::Item::from_spendauth(
        malformed_vk,
        sig_bytes.into(),
        msg,
    ));
    assert_eq!(batch.verify(&mut rng), Err(Error::InvalidSignature));

    let mut batch = batch::Verifier::<_, sapling::Binding>::new();
    batch.queue(batch::Item::from_spendauth(malformed_vk, sig, msg));
    batch.queue(batch::Item::from_spendauth(vk_bytes, sig_bytes.into(), msg));
    assert_eq!(batch.verify(&mut rng), Err(Error::MalformedVerificationKey));
}

#[test]
fn small_order_batch_key_is_accepted() {
    let identity = AffinePoint::identity().to_bytes();
    let mut sig_bytes = [0; 64];
    sig_bytes[..32].copy_from_slice(&identity);

    let mut batch = batch::Verifier::<sapling::SpendAuth, sapling::Binding>::new();
    batch.queue(batch::Item::from_spendauth(
        VerificationKeyBytes::from(identity),
        Signature::from(sig_bytes),
        b"BatchVerifyTest",
    ));
    assert_eq!(batch.verify(thread_rng()), Ok(()));
}

#[test]
fn single_signature_batches_verify() {
    let mut rng = thread_rng();
    let msg = b"BatchVerifyTest";

    let spend_sk = SigningKey::<sapling::SpendAuth>::new(&mut rng);
    let spend_vk = VerificationKey::from(&spend_sk).into();
    let spend_sig = spend_sk.sign(&mut rng, msg);
    let mut valid = batch::Verifier::<sapling::SpendAuth, sapling::Binding>::new();
    valid.queue(batch::Item::from_spendauth(spend_vk, spend_sig, msg));
    assert_eq!(valid.verify(&mut rng), Ok(()));
    let mut invalid = batch::Verifier::<sapling::SpendAuth, sapling::Binding>::new();
    invalid.queue(batch::Item::from_spendauth(spend_vk, spend_sig, b"wrong"));
    assert_eq!(invalid.verify(&mut rng), Err(Error::InvalidSignature));

    let binding_sk = SigningKey::<sapling::Binding>::new(&mut rng);
    let binding_vk = VerificationKey::from(&binding_sk).into();
    let binding_sig = binding_sk.sign(&mut rng, msg);
    let mut valid = batch::Verifier::<sapling::SpendAuth, sapling::Binding>::new();
    valid.queue(batch::Item::from_binding(binding_vk, binding_sig, msg));
    assert_eq!(valid.verify(&mut rng), Ok(()));
    let mut invalid = batch::Verifier::<sapling::SpendAuth, sapling::Binding>::new();
    invalid.queue(batch::Item::from_binding(binding_vk, binding_sig, b"wrong"));
    assert_eq!(invalid.verify(&mut rng), Err(Error::InvalidSignature));
}

#[test]
fn empty_batch_is_valid() {
    let batch = batch::Verifier::<sapling::SpendAuth, sapling::Binding>::new();
    assert_eq!(batch.verify(thread_rng()), Ok(()));
}

#[test]
#[cfg(any(feature = "pallas-pasta", feature = "pallas-sensei"))]
fn orchard_single_signature_batches_verify() {
    let mut rng = thread_rng();
    let msg = b"BatchVerifyTest";

    let spend_sk = SigningKey::<orchard::SpendAuth>::new(&mut rng);
    let spend_vk = VerificationKey::from(&spend_sk);
    let spend_sig = spend_sk.sign(&mut rng, msg);
    assert_eq!(spend_vk.verify(msg, &spend_sig), Ok(()));
    let mut valid = batch::Verifier::<orchard::SpendAuth, orchard::Binding>::new();
    valid.queue(batch::Item::from_spendauth(spend_vk.into(), spend_sig, msg));
    assert_eq!(valid.verify(&mut rng), Ok(()));

    let binding_sk = SigningKey::<orchard::Binding>::new(&mut rng);
    let binding_vk = VerificationKey::from(&binding_sk);
    let binding_sig = binding_sk.sign(&mut rng, msg);
    assert_eq!(binding_vk.verify(msg, &binding_sig), Ok(()));
    let mut invalid = batch::Verifier::<orchard::SpendAuth, orchard::Binding>::new();
    invalid.queue(batch::Item::from_binding(
        binding_vk.into(),
        binding_sig,
        b"wrong",
    ));
    assert_eq!(invalid.verify(&mut rng), Err(Error::InvalidSignature));
}

#[test]
fn cancelling_signature_errors_are_rejected() {
    // Shifting one signature's s by +1 and another's by -1 gives check errors
    // of -P and +P. They cancel if both signatures have weight 1, so only one
    // signature in the batch may have it.
    let mut rng = thread_rng();
    let shifted = |shift: jubjub::Scalar, rng: &mut _| {
        let sk = SigningKey::<sapling::SpendAuth>::new(&mut *rng);
        let vk = VerificationKey::from(&sk);
        let msg = b"BatchVerifyTest";
        let mut bytes: [u8; 64] = sk.sign(&mut *rng, msg).into();
        let s = jubjub::Scalar::from_bytes(bytes[32..].try_into().unwrap()).unwrap();
        bytes[32..].copy_from_slice(&(s + shift).to_bytes());
        batch::Item::<sapling::SpendAuth, sapling::Binding>::from_spendauth(
            vk.into(),
            bytes.into(),
            msg,
        )
    };
    for order in [[1u64, 0], [0, 1]] {
        let mut batch = batch::Verifier::new();
        for sign in order {
            let one = jubjub::Scalar::one();
            let shift = if sign == 1 { one } else { -one };
            batch.queue(shifted(shift, &mut rng));
        }
        assert_eq!(batch.verify(&mut rng), Err(Error::InvalidSignature));
    }
}

fn retained_keys<S, B>()
where
    S: SpendAuth,
    B: Binding<Scalar = S::Scalar, Point = S::Point>,
{
    let mut rng = thread_rng();
    let msg = b"RetainedBindingKeyTest";
    // Test each item as the failing signature, including the unit-weight item.
    for bad_index in core::iter::once(None).chain((0..8).map(Some)) {
        let mut batch = batch::Verifier::<S, B>::new();
        for i in 0..8 {
            let signed_msg: &[u8] = if bad_index == Some(i) { b"wrong" } else { msg };
            let item = if i % 4 < 2 {
                let sk = SigningKey::<S>::new(&mut rng);
                let vk = VerificationKey::from(&sk);
                let sig = sk.sign(&mut rng, signed_msg);
                if i % 4 == 0 {
                    batch::Item::from_spendauth(vk.into(), sig, msg)
                } else {
                    batch::Item::from_spendauth_key(vk, sig, msg)
                }
            } else {
                let sk = SigningKey::<B>::new(&mut rng);
                let vk = VerificationKey::from(&sk);
                let sig = sk.sign(&mut rng, signed_msg);
                if i % 4 == 3 {
                    batch::Item::from_binding_key(vk, sig, msg)
                } else {
                    batch::Item::from_binding(vk.into(), sig, msg)
                }
            };
            assert_eq!(item.clone().verify_single().is_ok(), bad_index != Some(i));
            // Also exercise the n = 1 path for each kind of item.
            let mut single = batch::Verifier::new();
            single.queue(item.clone());
            assert_eq!(single.verify(&mut rng).is_ok(), bad_index != Some(i));
            batch.queue(item);
        }
        assert_eq!(batch.verify(&mut rng).is_ok(), bad_index.is_none());
    }
}

#[test]
fn sapling_retained_binding_keys_verify() {
    retained_keys::<sapling::SpendAuth, sapling::Binding>();
}

#[test]
#[cfg(any(feature = "pallas-pasta", feature = "pallas-sensei"))]
fn orchard_retained_binding_keys_verify() {
    retained_keys::<orchard::SpendAuth, orchard::Binding>();
}

#[test]
fn retained_keys_preserve_malformed_encoding_errors() {
    let mut rng = thread_rng();
    let sk = SigningKey::<sapling::Binding>::new(&mut rng);
    let vk = VerificationKey::from(&sk);
    let msg = b"RetainedBindingKeyTest";
    let sig = sk.sign(&mut rng, msg);
    let valid = batch::Item::from_binding_key(vk, sig, msg);
    let malformed_vk = VerificationKeyBytes::from([0xff; 32]);
    let mut malformed_r: [u8; 64] = sig.into();
    malformed_r[..32].fill(0xff);
    let mut malformed_s: [u8; 64] = sig.into();
    malformed_s[32..].fill(0xff);
    let spend_sk = SigningKey::<sapling::SpendAuth>::new(&mut rng);
    let spend_vk = VerificationKey::from(&spend_sk);
    let spend_sig = spend_sk.sign(&mut rng, msg);
    let mut spend_r: [u8; 64] = spend_sig.into();
    spend_r[..32].fill(0xff);
    let mut spend_s: [u8; 64] = spend_sig.into();
    spend_s[32..].fill(0xff);
    let cases = [
        (
            batch::Item::from_spendauth_key(spend_vk, spend_r.into(), msg),
            Error::InvalidSignature,
        ),
        (
            batch::Item::from_spendauth_key(spend_vk, spend_s.into(), msg),
            Error::InvalidSignature,
        ),
        (
            batch::Item::from_binding(malformed_vk, sig, msg),
            Error::MalformedVerificationKey,
        ),
        (
            batch::Item::from_binding_key(vk, malformed_r.into(), msg),
            Error::InvalidSignature,
        ),
        (
            batch::Item::from_binding_key(vk, malformed_s.into(), msg),
            Error::InvalidSignature,
        ),
        (
            batch::Item::from_binding(malformed_vk, malformed_r.into(), msg),
            Error::InvalidSignature,
        ),
        (
            batch::Item::from_binding(malformed_vk, malformed_s.into(), msg),
            Error::InvalidSignature,
        ),
    ];
    for (bad, error) in cases {
        for index in 0..3 {
            let mut batch = batch::Verifier::<sapling::SpendAuth, sapling::Binding>::new();
            for i in 0..3 {
                batch.queue(if i == index {
                    bad.clone()
                } else {
                    valid.clone()
                });
            }
            assert_eq!(batch.verify(&mut rng), Err(error));
        }
    }
}
