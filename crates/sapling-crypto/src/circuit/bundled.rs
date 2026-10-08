//! Canonical Sapling verification keys without proving parameters.

use std::sync::LazyLock;

use super::{OutputVerifyingKey, SpendVerifyingKey};

const SPEND_KEY: &[u8] = include_bytes!("bundled/spend.vk");
const OUTPUT_KEY: &[u8] = include_bytes!("bundled/output.vk");

static VERIFYING_KEYS: LazyLock<(SpendVerifyingKey, OutputVerifyingKey)> = LazyLock::new(|| {
    let spend = SpendVerifyingKey::read(SPEND_KEY)
        .expect("the canonical Sapling spend verifying key has a valid encoding");
    let output = OutputVerifyingKey::read(OUTPUT_KEY)
        .expect("the canonical Sapling output verifying key has a valid encoding");
    (spend, output)
});

/// Returns the canonical Sapling spend and output verifying keys.
///
/// Requires the `pinned-vk-only` feature. Only the verifying keys are
/// embedded; no proving parameters are bundled or loaded. The keys are shared
/// process-wide, including their lazy batch-verification precomputations.
///
/// This feature adds no dependency on `zakura-proofs` or the Wagyu parameter
/// packages. It does not disable proving dependencies independently selected
/// by another crate.
pub fn pinned_verifying_keys() -> &'static (SpendVerifyingKey, OutputVerifyingKey) {
    &VERIFYING_KEYS
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use super::*;

    #[test]
    fn bundled_keys_roundtrip_and_are_reused() {
        let keys = pinned_verifying_keys();
        assert!(std::ptr::eq(keys, pinned_verifying_keys()));
        let mut spend = Vec::new();
        keys.0.0.write(&mut spend).unwrap();
        assert_eq!(spend, SPEND_KEY);
        let mut output = Vec::new();
        keys.1.0.write(&mut output).unwrap();
        assert_eq!(output, OUTPUT_KEY);
    }

    #[test]
    fn readers_reject_truncated_keys() {
        assert!(SpendVerifyingKey::read(&SPEND_KEY[..SPEND_KEY.len() - 1]).is_err());
        assert!(OutputVerifyingKey::read(&OUTPUT_KEY[..OUTPUT_KEY.len() - 1]).is_err());
    }

    #[test]
    fn readers_bound_the_input_vector() {
        fn append_input(encoded_key: &[u8]) -> Vec<u8> {
            use super::super::{VERIFYING_KEY_FIXED_BYTES, VERIFYING_KEY_INPUT_BYTES};

            let length_bytes = std::mem::size_of::<u32>();
            let offset = usize::try_from(VERIFYING_KEY_FIXED_BYTES).unwrap() - length_bytes;
            let mut key = encoded_key.to_vec();
            let input_count =
                u32::from_be_bytes(key[offset..offset + length_bytes].try_into().unwrap());
            key[offset..offset + length_bytes].copy_from_slice(&(input_count + 1).to_be_bytes());
            let point_bytes = usize::try_from(VERIFYING_KEY_INPUT_BYTES).unwrap();
            key.extend_from_within(key.len() - point_bytes..);
            key
        }

        // An extra valid point must not extend the circuit's input vector.
        assert!(SpendVerifyingKey::read(append_input(SPEND_KEY).as_slice()).is_err());
        assert!(OutputVerifyingKey::read(append_input(OUTPUT_KEY).as_slice()).is_err());
    }

    #[test]
    fn readers_reject_invalid_points() {
        let mut spend = SPEND_KEY.to_vec();
        spend[0] = 0xff;
        assert!(SpendVerifyingKey::read(spend.as_slice()).is_err());
        let mut output = OUTPUT_KEY.to_vec();
        output[0] = 0xff;
        assert!(OutputVerifyingKey::read(output.as_slice()).is_err());
    }
}
