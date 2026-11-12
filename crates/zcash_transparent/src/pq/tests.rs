macro_rules! vectors {
    ($module:ident, $algorithm:ident, $prefix:literal) => {
        mod $module {
            use super::super::$algorithm::*;
            const SEED: &[u8; SEED_BYTES] = include_bytes!(concat!("vectors/", $prefix, ".seed"));
            const PUBLIC: &[u8; PUBLIC_KEY_BYTES] =
                include_bytes!(concat!("vectors/", $prefix, ".pk"));
            const SIGNATURE: &[u8; SIGNATURE_BYTES] =
                include_bytes!(concat!("vectors/", $prefix, ".sig"));
            const CONTEXT: &[u8] = b"common/native-slh/vector";
            #[test]
            fn nist_key_generation_and_independent_openssl_signature() {
                let key = SigningKey::from_seed(SEED);
                assert_eq!(key.public_key(), *PUBLIC);
                assert_eq!(key.sign(&[42; 32], CONTEXT).unwrap(), SIGNATURE);
                assert!(verify(PUBLIC, &[42; 32], CONTEXT, SIGNATURE).is_ok());
            }
            #[test]
            fn alterations_and_noncanonical_lengths_reject() {
                assert!(verify(PUBLIC, &[43; 32], CONTEXT, SIGNATURE).is_err());
                assert!(verify(PUBLIC, &[42; 32], b"other context", SIGNATURE).is_err());
                let mut changed = SIGNATURE.to_vec();
                changed[0] ^= 1;
                assert!(verify(PUBLIC, &[42; 32], CONTEXT, &changed).is_err());
                let mut key = PUBLIC.to_vec();
                key[0] ^= 1;
                assert!(verify(&key, &[42; 32], CONTEXT, SIGNATURE).is_err());
                for length in [0, 1, PUBLIC_KEY_BYTES - 1] {
                    assert!(verify(&PUBLIC[..length], &[42; 32], CONTEXT, SIGNATURE).is_err());
                }
                for length in [0, 1, SIGNATURE_BYTES - 1] {
                    assert!(verify(PUBLIC, &[42; 32], CONTEXT, &SIGNATURE[..length]).is_err());
                }
                let mut extended = SIGNATURE.to_vec();
                extended.push(0);
                assert!(verify(PUBLIC, &[42; 32], CONTEXT, &extended).is_err());
                let mut extended = PUBLIC.to_vec();
                extended.push(0);
                assert!(verify(&extended, &[42; 32], CONTEXT, SIGNATURE).is_err());
            }
            #[test]
            fn empty_messages_and_context_boundary() {
                let key = SigningKey::from_seed(SEED);
                for context in [b"".as_slice(), &[1; 255]] {
                    let signature = key.sign(&[], context).unwrap();
                    assert!(verify(PUBLIC, &[], context, &signature).is_ok());
                }
                assert!(key.sign(&[], &[0; 256]).is_err());
                assert!(verify(PUBLIC, &[], &[0; 256], SIGNATURE).is_err());
            }
        }
    };
}
vectors!(fast, sha2_128f, "128f");
vectors!(small, sha2_192s, "192s");
