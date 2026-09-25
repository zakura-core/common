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
