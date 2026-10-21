// Preserve the imported `chunks_exact` code, as in Udon. The pinned
// toolchain's Clippy predates this lint (introduced in 1.98).
#![allow(unknown_lints)]
#![allow(clippy::chunks_exact_to_as_chunks)]

use zakura_sensei::{Fq, RandomnessError, redpallas::*};

const MESSAGE: &[u8] = b"Orchard preparation compatibility";

fn fixtures<T: SigType>(bytes: &[u8]) -> Vec<BatchItem> {
    bytes
        .chunks_exact(208)
        .map(|case| {
            let key = SigningKey::<T>::from_bytes(case[..32].try_into().unwrap()).unwrap();
            assert_eq!(key.to_bytes(), case[..32]);
            let vk = key.verification_key();
            assert_eq!(vk.to_bytes(), case[32..64]);
            assert_eq!(VerificationKey::<T>::from_bytes(vk.to_bytes()).unwrap(), vk);
            let mut words = case[64..144].chunks_exact(8);
            let signature = key
                .sign(
                    &mut || {
                        Ok(u64::from_le_bytes(
                            words.next().unwrap().try_into().unwrap(),
                        ))
                    },
                    MESSAGE,
                )
                .unwrap();
            assert!(words.next().is_none());
            assert_eq!(signature.to_bytes(), case[144..208]);
            vk.verify(MESSAGE, &signature).unwrap();
            if vk.to_bytes() != [0; 32] {
                assert_eq!(
                    vk.verify(b"changed message", &signature),
                    Err(Error::InvalidSignature)
                );
            }
            BatchItem::new(&vk, &signature, MESSAGE)
        })
        .collect()
}

#[test]
fn legacy_signatures_are_byte_exact_in_both_domains() {
    let mut items = fixtures::<SpendAuth>(include_bytes!("fixtures/redpallas-spend.bin"));
    items.extend(fixtures::<Binding>(include_bytes!(
        "fixtures/redpallas-binding.bin"
    )));
    let mut draws = 0;
    verify_batch(&items, &mut || {
        draws += 1;
        Ok(draws)
    })
    .unwrap();
    assert_eq!(draws, 2 * items.len() as u64);
    verify_batch(&[], &mut || panic!("empty batch needs no randomness")).unwrap();
    verify_batch(&items[..1], &mut || panic!("singleton needs no randomness")).unwrap();
    assert_eq!(
        verify_batch(&items, &mut || Ok(0)),
        Err(Error::RetryRandomness)
    );
    assert_eq!(
        verify_batch(&items, &mut || Err(RandomnessError)),
        Err(Error::RngFailure)
    );
    let wrong = Signature::<SpendAuth>::from_bytes([0; 64]);
    let key = SigningKey::<SpendAuth>::from_bytes({
        let mut b = [0; 32];
        b[0] = 1;
        b
    })
    .unwrap();
    items.push(BatchItem::new(&key.verification_key(), &wrong, MESSAGE));
    assert_eq!(
        verify_batch(&items, &mut || Ok(42)),
        Err(Error::InvalidSignature)
    );
}

#[test]
fn canonical_boundaries_randomization_and_randomness_errors() {
    assert_eq!(
        SigningKey::<SpendAuth>::from_bytes([255; 32]).unwrap_err(),
        Error::MalformedSigningKey
    );
    assert_eq!(
        VerificationKey::<Binding>::from_bytes([255; 32]).unwrap_err(),
        Error::MalformedVerificationKey
    );
    let zero = SigningKey::<SpendAuth>::from_bytes([0; 32]).unwrap();
    assert_eq!(zero.verification_key().to_bytes(), [0; 32]);
    let mut alpha = [0; 32];
    alpha[0] = 7;
    let alpha = Fq::from_bytes(alpha).unwrap();
    let key = zero.randomize(&alpha);
    assert_eq!(
        key.verification_key(),
        zero.verification_key().randomize(&alpha)
    );
    assert_eq!(key.to_bytes(), alpha.to_bytes());
    let signature = key.sign(&mut || Ok(123), MESSAGE).unwrap();
    key.verification_key().verify(MESSAGE, &signature).unwrap();
    assert_eq!(
        key.sign(&mut || Err(RandomnessError), MESSAGE).unwrap_err(),
        Error::RngFailure
    );
    for range in [0..32, 32..64] {
        let mut bytes = signature.to_bytes();
        bytes[range].fill(255);
        let signature = Signature::from_bytes(bytes);
        assert_eq!(signature.to_bytes(), bytes);
        assert_eq!(
            key.verification_key().verify(MESSAGE, &signature),
            Err(Error::InvalidSignature)
        );
        let item = BatchItem::new(&key.verification_key(), &signature, MESSAGE);
        assert_eq!(
            verify_batch(&[item.clone(), item], &mut || panic!("validate before RNG")),
            Err(Error::InvalidSignature)
        );
    }
    let binding =
        VerificationKey::<Binding>::from_bytes(key.verification_key().to_bytes()).unwrap();
    assert_eq!(
        binding.verify(MESSAGE, &Signature::from_bytes(signature.to_bytes())),
        Err(Error::InvalidSignature)
    );
}

#[test]
fn spend_randomization_matches_frozen_legacy_bytes() {
    for case in include_bytes!("fixtures/redpallas-randomization.bin").chunks_exact(160) {
        let sk = SigningKey::<SpendAuth>::from_bytes(case[..32].try_into().unwrap()).unwrap();
        let alpha = Fq::from_bytes(case[32..64].try_into().unwrap()).unwrap();
        assert_eq!(sk.randomize(&alpha).to_bytes(), case[64..96]);
        assert_eq!(sk.verification_key().to_bytes(), case[96..128]);
        assert_eq!(
            sk.verification_key().randomize(&alpha).to_bytes(),
            case[128..160]
        );
        assert_eq!(
            sk.randomize(&alpha).verification_key(),
            sk.verification_key().randomize(&alpha)
        );
    }
}

#[test]
fn key_sampling_and_failed_sources_obey_word_consumption() {
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;

    let mut reference = ChaCha20Rng::from_seed([19; 32]);
    let mut wide = [0; 64];
    reference.fill_bytes(&mut wide);
    let expected = zakura_sensei::Fq::from_uniform_bytes(&wide).to_bytes();
    let mut rng = ChaCha20Rng::from_seed([19; 32]);
    let mut draws = 0;
    let key = SigningKey::<SpendAuth>::new(&mut || {
        draws += 1;
        Ok(rng.next_u64())
    })
    .unwrap();
    assert_eq!(draws, 8);
    assert_eq!(key.to_bytes(), expected);

    for stop in [0, 3, 7] {
        let mut calls = 0;
        let result = SigningKey::<Binding>::new(&mut || {
            calls += 1;
            if calls > stop {
                Err(RandomnessError)
            } else {
                Ok(1)
            }
        });
        assert_eq!(result.unwrap_err(), Error::RngFailure);
        assert_eq!(calls, stop + 1);
    }
    let original = key.to_bytes();
    let mut calls = 0;
    let result = key.sign(
        &mut || {
            calls += 1;
            if calls == 5 {
                Err(RandomnessError)
            } else {
                Ok(1)
            }
        },
        MESSAGE,
    );
    assert_eq!(result.unwrap_err(), Error::RngFailure);
    assert_eq!(calls, 5);
    assert_eq!(key.to_bytes(), original);
}

#[test]
fn batch_item_outlives_its_inputs() {
    let item = {
        let mut scalar = [0; 32];
        scalar[0] = 7;
        let key = SigningKey::<SpendAuth>::from_bytes(scalar).unwrap();
        let message = String::from("owned verification inputs");
        let signature = key.sign(&mut || Ok(42), message.as_bytes()).unwrap();
        BatchItem::new(&key.verification_key(), &signature, message.as_bytes())
    };
    item.verify().unwrap();
    verify_batch(&[item], &mut || panic!("singleton consumes no randomness")).unwrap();
}
