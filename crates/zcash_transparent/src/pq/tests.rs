macro_rules! primitive_cases {
    ($name:ident, $algorithm:ident, $seed_bytes:literal, $public_bytes:literal, $signature_bytes:literal, $prefix:literal) => {
        mod $name {
            use super::super::$algorithm::*;

            // Public test material only. See test_vectors/README.md for provenance and reproduction.
            const SEED: &[u8; $seed_bytes] =
                include_bytes!(concat!("test_vectors/", $prefix, "_nist.seed"));
            const PUBLIC_KEY: &[u8; $public_bytes] =
                include_bytes!(concat!("test_vectors/", $prefix, "_nist.pk"));
            const SIGNATURE: &[u8; $signature_bytes] =
                include_bytes!(concat!("test_vectors/", $prefix, "_openssl.sig"));
            const MESSAGE: [u8; 32] = [42; 32];
            const CONTEXT: &[u8] = b"common/slh-dsa/test";

            #[test]
            fn key_generation_matches_nist() {
                assert_eq!(SigningKey::from_seed(SEED).public_key(), *PUBLIC_KEY);
            }

            #[test]
            fn signature_matches_openssl_and_verifies() {
                let key = SigningKey::from_seed(SEED);
                let signature = key.sign(&MESSAGE, CONTEXT).unwrap();
                assert_eq!(signature.len(), SIGNATURE_BYTES);
                assert!(signature == SIGNATURE, "signature differs from OpenSSL");
                assert!(verify(PUBLIC_KEY, &MESSAGE, CONTEXT, SIGNATURE).is_ok());
            }

            #[test]
            fn altered_message_key_context_and_signature_are_rejected() {
                assert!(verify(PUBLIC_KEY, &[43; 32], CONTEXT, SIGNATURE).is_err());
                for context in [b"".as_slice(), b"another context".as_slice()] {
                    assert!(verify(PUBLIC_KEY, &MESSAGE, context, SIGNATURE).is_err());
                }
                let other_key = SigningKey::from_seed(&[7; SEED_BYTES]).public_key();
                assert!(verify(&other_key, &MESSAGE, CONTEXT, SIGNATURE).is_err());
                for position in [0, PUBLIC_KEY_BYTES - 1] {
                    let mut key = *PUBLIC_KEY;
                    key[position] ^= 1;
                    assert!(verify(&key, &MESSAGE, CONTEXT, SIGNATURE).is_err());
                }
                // Alter the randomizer, FORS signature, and hypertree signature.
                for position in [0, PUBLIC_KEY_BYTES / 2, SIGNATURE_BYTES - 1] {
                    let mut signature = SIGNATURE.to_vec();
                    signature[position] ^= 1;
                    assert!(verify(PUBLIC_KEY, &MESSAGE, CONTEXT, &signature).is_err());
                }
            }

            #[test]
            fn truncated_and_extended_encodings_are_rejected() {
                for length in [0, 1, PUBLIC_KEY_BYTES - 1] {
                    assert!(verify(&PUBLIC_KEY[..length], &MESSAGE, CONTEXT, SIGNATURE).is_err());
                }
                let mut key = PUBLIC_KEY.to_vec();
                key.push(0);
                assert!(verify(&key, &MESSAGE, CONTEXT, SIGNATURE).is_err());

                for length in [0, 1, SIGNATURE_BYTES - 1] {
                    assert!(verify(PUBLIC_KEY, &MESSAGE, CONTEXT, &SIGNATURE[..length]).is_err());
                }
                let mut signature = SIGNATURE.to_vec();
                signature.push(0);
                assert!(verify(PUBLIC_KEY, &MESSAGE, CONTEXT, &signature).is_err());
            }

            #[test]
            fn empty_messages_and_context_boundaries_work_with_a_reusable_key() {
                let key = SigningKey::from_seed(SEED);
                for context in [b"".as_slice(), &[5; 255]] {
                    let signature = key.sign(b"", context).unwrap();
                    assert!(verify(PUBLIC_KEY, b"", context, &signature).is_ok());
                    assert!(verify(PUBLIC_KEY, b"changed", context, &signature).is_err());
                }
                assert!(key.sign(&MESSAGE, &[5; 256]).is_err());
                assert!(verify(PUBLIC_KEY, &MESSAGE, &[5; 256], SIGNATURE).is_err());
            }
        }
    };
}
primitive_cases!(sha2_128f, sha2_128f, 48, 32, 17088, "sha2_128f");
primitive_cases!(sha2_192s, sha2_192s, 72, 48, 16224, "sha2_192s");
