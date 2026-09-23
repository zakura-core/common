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
