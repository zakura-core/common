use alloc::{string::ToString, vec, vec::Vec};

use super::{
    Error, VALID_LENGTH, f4jumble, f4jumble_inv_mut, f4jumble_mut, g_personalization,
    h_personalization, test_vectors,
};

#[test]
fn personalizations_match_upstream() {
    assert_eq!(h_personalization(7), *b"UA_F4Jumble_H\x07\x00\x00");
    assert_eq!(g_personalization(7, 13), *b"UA_F4Jumble_G\x07\x0d\x00");
    assert_eq!(
        g_personalization(7, u16::MAX),
        *b"UA_F4Jumble_G\x07\xff\xff"
    );
}

#[test]
fn upstream_vectors_match_both_directions() {
    let mut cache = vec![0; test_vectors::MAX_VECTOR_LENGTH];
    for vector in test_vectors::TEST_VECTORS {
        let data = &mut cache[..vector.normal.len()];
        data.copy_from_slice(vector.normal);
        f4jumble_mut(data).unwrap();
        assert_eq!(data, vector.jumbled);
        f4jumble_inv_mut(data).unwrap();
        assert_eq!(data, vector.normal);

        assert_eq!(f4jumble(vector.normal).unwrap(), vector.jumbled);
    }
}

#[cfg(feature = "std")]
#[test]
fn upstream_long_vectors_match_both_directions() {
    for vector in super::test_vectors_long::TEST_VECTORS {
        let normal: Vec<u8> = (0..vector.length)
            .map(|i| u8::try_from(i % 256).expect("remainder fits in u8"))
            .collect();
        let mut jumbled = f4jumble(&normal).unwrap();
        assert_eq!(
            blake2b_simd::blake2b(&jumbled).as_bytes(),
            vector.jumbled_hash
        );
        f4jumble_inv_mut(&mut jumbled).unwrap();
        assert_eq!(jumbled, normal);
    }
}

#[test]
fn invalid_lengths_leave_input_unchanged() {
    for length in [0, 1, VALID_LENGTH.start() - 1, VALID_LENGTH.end() + 1] {
        let original = vec![7; length];
        let mut message = original.clone();
        assert!(matches!(
            f4jumble_mut(&mut message),
            Err(Error::InvalidLength)
        ));
        assert_eq!(message, original);
        assert!(matches!(
            f4jumble_inv_mut(&mut message),
            Err(Error::InvalidLength)
        ));
        assert_eq!(message, original);
        assert!(matches!(f4jumble(&message), Err(Error::InvalidLength)));
    }

    assert_eq!(
        Error::InvalidLength.to_string(),
        "Message length must be in interval (48..=4194368)"
    );
}

#[test]
fn roundtrips_length_and_block_boundaries() {
    for length in [
        *VALID_LENGTH.start(),
        VALID_LENGTH.start() + 1,
        63,
        64,
        65,
        127,
        128,
        129,
        191,
        192,
        193,
        VALID_LENGTH.end() - 1,
        *VALID_LENGTH.end(),
    ] {
        let original: Vec<u8> = (0..length)
            .map(|i| u8::try_from(i % 256).expect("remainder fits in u8"))
            .collect();
        let mut message = f4jumble(&original).unwrap();
        assert_eq!(message.len(), length);
        f4jumble_inv_mut(&mut message).unwrap();
        assert_eq!(message, original);
    }
}

#[cfg(feature = "std")]
mod prop {
    use super::*;
    use proptest::{collection::vec, prelude::*};

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(5))]

        #[test]
        fn upstream_full_length_range_roundtrip(message in vec(any::<u8>(), VALID_LENGTH)) {
            let mut jumbled = f4jumble(&message).unwrap();
            prop_assert_eq!(jumbled.len(), message.len());
            f4jumble_inv_mut(&mut jumbled).unwrap();
            prop_assert_eq!(jumbled, message);
        }
    }
}
