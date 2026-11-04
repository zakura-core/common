use rand::rng as thread_rng;

use redjubjub::*;

#[test]
fn spendauth_batch_verify() {
    let mut rng = thread_rng();
    let mut batch = batch::Verifier::new();
    for _ in 0..32 {
        let sk = SigningKey::<SpendAuth>::new(&mut rng);
        let vk = VerificationKey::from(&sk);
        let msg = b"BatchVerifyTest";
        let sig = sk.sign(&mut rng, &msg[..]);
        batch.queue((vk.into(), sig, msg));
    }
    assert!(batch.verify(rng).is_ok());
}

#[test]
fn binding_batch_verify() {
    let mut rng = thread_rng();
    let mut batch = batch::Verifier::new();
    for i in 0..32 {
        let sk = SigningKey::<Binding>::new(&mut rng);
        let vk = VerificationKey::from(&sk);
        let msg = b"BatchVerifyTest";
        let sig = sk.sign(&mut rng, &msg[..]);
        if i % 2 == 0 {
            batch.queue(batch::Item::from_binding_key(vk, sig, msg));
        } else {
            batch.queue((vk.into(), sig, msg));
        }
    }
    assert!(batch.verify(rng).is_ok());
}

#[test]
fn retained_binding_key_rejects_wrong_message() {
    let mut rng = thread_rng();
    let sk = SigningKey::<Binding>::new(&mut rng);
    let vk = VerificationKey::from(&sk);
    let sig = sk.sign(&mut rng, b"message");
    let valid = batch::Item::from_binding_key(vk, sig, b"message");
    let invalid = batch::Item::from_binding_key(vk, sig, b"wrong");
    assert_eq!(valid.clone().verify_single(), Ok(()));
    assert_eq!(
        invalid.clone().verify_single(),
        Err(Error::InvalidSignature)
    );
    for (items, expected_valid) in [
        (vec![valid.clone()], true),
        (vec![valid, invalid.clone()], false),
        (vec![invalid], false),
    ] {
        let mut batch = batch::Verifier::new();
        for item in items {
            batch.queue(item);
        }
        assert_eq!(batch.verify(&mut rng).is_ok(), expected_valid);
    }
}

#[test]
fn alternating_batch_verify() {
    let mut rng = thread_rng();
    let mut batch = batch::Verifier::new();
    for i in 0..32 {
        let item: batch::Item = match i % 2 {
            0 => {
                let sk = SigningKey::<SpendAuth>::new(&mut rng);
                let vk = VerificationKey::from(&sk);
                let msg = b"BatchVerifyTest";
                let sig = sk.sign(&mut rng, &msg[..]);
                (vk.into(), sig, msg).into()
            }
            1 => {
                let sk = SigningKey::<Binding>::new(&mut rng);
                let vk = VerificationKey::from(&sk);
                let msg = b"BatchVerifyTest";
                let sig = sk.sign(&mut rng, &msg[..]);
                (vk.into(), sig, msg).into()
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
        let item: batch::Item = match i % 2 {
            0 => {
                let sk = SigningKey::<SpendAuth>::new(&mut rng);
                let vk = VerificationKey::from(&sk);
                let msg = b"BatchVerifyTest";
                let sig = if i != bad_index {
                    sk.sign(&mut rng, &msg[..])
                } else {
                    sk.sign(&mut rng, b"bad")
                };
                (vk.into(), sig, msg).into()
            }
            1 => {
                let sk = SigningKey::<Binding>::new(&mut rng);
                let vk = VerificationKey::from(&sk);
                let msg = b"BatchVerifyTest";
                let sig = sk.sign(&mut rng, &msg[..]);
                (vk.into(), sig, msg).into()
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
fn retained_spend_keys_preserve_verification_and_encoding_checks() {
    let mut rng = thread_rng();
    let sk = SigningKey::<SpendAuth>::new(&mut rng);
    let vk = VerificationKey::from(&sk);
    let msg = b"RetainedSpendTest";
    let sig = sk.sign(&mut rng, msg);
    let valid = batch::Item::from_spendauth_key(vk, sig, msg);
    let mut bad_r: [u8; 64] = sig.into();
    bad_r[..32].fill(0xff);
    let mut bad_s: [u8; 64] = sig.into();
    bad_s[32..].fill(0xff);
    let invalid = [
        batch::Item::from_spendauth_key(vk, sig, b"wrong"),
        batch::Item::from_spendauth_key(vk, bad_r.into(), msg),
        batch::Item::from_spendauth_key(vk, bad_s.into(), msg),
    ];
    assert_eq!(valid.clone().verify_single(), Ok(()));
    for bad in invalid {
        assert_eq!(bad.clone().verify_single(), Err(Error::InvalidSignature));
        for index in 0..3 {
            let mut batch = batch::Verifier::new();
            for i in 0..3 {
                batch.queue(if i == index {
                    bad.clone()
                } else {
                    valid.clone()
                });
            }
            assert_eq!(batch.verify(&mut rng), Err(Error::InvalidSignature));
        }
        let mut batch = batch::Verifier::new();
        batch.queue(bad);
        assert_eq!(batch.verify(&mut rng), Err(Error::InvalidSignature));
    }
    let mut mixed = batch::Verifier::new();
    mixed.queue(valid);
    mixed.queue((vk.into(), sig, msg));
    assert_eq!(mixed.verify(rng), Ok(()));
}
