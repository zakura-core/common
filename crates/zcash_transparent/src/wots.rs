//! Experimental, disposable-key WOTS authorizations for regtest.
//!
//! Reconstructs the public key and checks its commitment; endpoints are not sent.
//! This is not a durable wallet:
//! recreating a key from saved seeds can bypass its consuming signing API.

use alloc::vec::Vec;
use sha2::{Digest, Sha256};
use zcash_protocol::constants::WOTS_KEY_COMMITMENT_DOMAIN;
use zcash_script::script::Code;

use crate::address::{Script, TransparentAddress};
pub use wots_plus::{MessageDigest, SigningKey, VerifyingKey};

/// Experimental opcode, invalid when executed without explicit activation.
pub const CHECKWOTS: u8 = 0xba;
/// Five signature pushes (2,158 bytes), public-seed push (33), and redeem push (35).
pub const WOTS_SCRIPT_SIG_SIZE: usize = 2226;
/// Serialized input size, including its CompactSize script length.
pub const WOTS_INPUT_SIZE: usize = 36 + 3 + WOTS_SCRIPT_SIG_SIZE + 4;
/// Experimental verification charge; not a production cost model.
pub const WOTS_SIGOP_COST: u32 = 100;

/// A WOTS-only P2SH redeem script: a key commitment followed by CHECKWOTS.
#[derive(Clone, Debug)]
pub struct RedeemScript([u8; 34]);

impl RedeemScript {
    /// Commits to the canonical full WOTS public key, with no alternative authorization.
    pub fn new(key: &VerifyingKey) -> Self {
        let mut bytes = [0; 34];
        bytes[0] = 32;
        bytes[1..33].copy_from_slice(&key_commitment(&key.to_bytes()));
        bytes[33] = CHECKWOTS;
        Self(bytes)
    }

    /// Recognizes only the exact WOTS-only template.
    pub fn parse(bytes: &[u8]) -> Option<Self> {
        let bytes: [u8; 34] = bytes.try_into().ok()?;
        (bytes[0] == 32 && bytes[33] == CHECKWOTS).then_some(Self(bytes))
    }

    /// Returns the canonical redeem script bytes.
    pub fn as_bytes(&self) -> &[u8; 34] {
        &self.0
    }

    /// Returns the P2SH address using the existing address representation.
    pub fn address(&self) -> TransparentAddress {
        use ripemd::Ripemd160;
        TransparentAddress::ScriptHash(Ripemd160::digest(Sha256::digest(self.0)).into())
    }

    /// Signs exactly once and returns the push-only WOTS script signature.
    /// The caller must supply the existing ZIP 244 ALL digest for this input.
    /// A mismatched key is rejected before signing.
    pub fn sign(&self, key: SigningKey, digest: [u8; 32]) -> Result<Script, &'static str> {
        let public_key = key.verifying_key();
        if key_commitment(&public_key.to_bytes()).as_slice() != &self.0[1..33] {
            return Err("the signing key does not match the redeem script");
        }
        let signature = key
            .sign_digest(&MessageDigest::from_bytes(digest))
            .to_bytes();
        let mut bytes = Vec::with_capacity(WOTS_SCRIPT_SIG_SIZE);
        for chunk in signature.chunks(512) {
            push(&mut bytes, chunk);
        }
        push(&mut bytes, public_key.public_seed().as_bytes());
        push(&mut bytes, &self.0);
        Ok(Script(Code(bytes)))
    }
}

/// Reconstructs the candidate key using RFC 8391 section 3.1.6 and authenticates
/// its canonical full encoding against the output's independently trusted commitment.
/// Reconstruction alone accepts any signature-shaped bytes; the binding SHA-256
/// commitment check is essential. The public seed is included in that commitment.
pub fn verify(digest: [u8; 32], signature: &[u8], public_seed: &[u8], commitment: &[u8]) -> bool {
    let Ok(public_seed): Result<[u8; 32], _> = public_seed.try_into() else {
        return false;
    };
    if commitment.len() != 32 {
        return false;
    }
    let Ok(signature) = wots_plus::Signature::try_from(signature) else {
        return false;
    };
    let candidate = VerifyingKey::recover_from_signature(
        &MessageDigest::from_bytes(digest),
        &signature,
        wots_plus::PublicSeed::from_bytes(public_seed),
    );
    key_commitment(&candidate.to_bytes()).as_slice() == commitment
}

/// Counts opcode occurrences, excluding bytes inside data pushes.
pub fn sigop_cost(code: &[u8]) -> u32 {
    Code(code.to_vec())
        .parse()
        .take_while(Result::is_ok)
        .filter(|op| {
            matches!(
                op,
                Ok(zcash_script::opcode::PossiblyBad::Bad(
                    zcash_script::opcode::Bad::Unknown(CHECKWOTS)
                ))
            )
        })
        .count()
        .try_into()
        .unwrap_or(u32::MAX)
        .saturating_mul(WOTS_SIGOP_COST)
}

fn key_commitment(key: &[u8]) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(WOTS_KEY_COMMITMENT_DOMAIN);
    hash.update(key);
    hash.finalize().into()
}

fn push(bytes: &mut Vec<u8>, value: &[u8]) {
    // Script push lengths are unsigned little-endian, not signed script numbers.
    // These are fixed-size authorization elements, never larger than 512 bytes.
    match value.len() {
        0..=75 => bytes.push(u8::try_from(value.len()).expect("direct pushes fit one byte")),
        76..=255 => {
            bytes.push(0x4c);
            bytes.push(u8::try_from(value.len()).expect("PUSHDATA1 lengths fit one byte"));
        }
        256..=512 => {
            bytes.push(0x4d);
            bytes.extend(
                u16::try_from(value.len())
                    .expect("chunks fit two bytes")
                    .to_le_bytes(),
            );
        }
        _ => unreachable!("all callers supply fixed-size authorization elements"),
    }
    bytes.extend_from_slice(value);
}

#[cfg(test)]
mod tests {
    use super::*;
    use zcash_script::{
        interpreter::{Flags, SignatureChecker},
        script::{self, Evaluable},
        signature,
    };

    struct Checker([u8; 32]);
    impl SignatureChecker for Checker {
        fn check_sig(&self, _: &signature::Decoded, _: &[u8], _: &script::Code) -> bool {
            false
        }
        fn check_lock_time(&self, _: i64) -> bool {
            false
        }
        fn check_wots(&self, signature: &[u8], key: &[u8], commitment: &[u8]) -> bool {
            verify(self.0, signature, key, commitment)
        }
    }
    fn signed() -> (RedeemScript, Script) {
        let key = SigningKey::from_seeds(
            wots_plus::SecretSeed::from_bytes([7; 32]),
            wots_plus::PublicSeed::from_bytes([9; 32]),
        )
        .unwrap();
        let redeem = RedeemScript::new(&key.verifying_key());
        let signature = redeem.sign(key, [4; 32]).unwrap();
        (redeem, signature)
    }
    fn evaluate(redeem: &RedeemScript, signature: &Script, flags: Flags, digest: [u8; 32]) -> bool {
        script::Raw::from_raw_parts(signature.0.to_bytes(), redeem.address().script().to_bytes())
            .eval(flags | Flags::P2SH, &Checker(digest))
            == Ok(true)
    }

    #[test]
    fn reconstructed_key_authorization_executes_only_with_explicit_activation() {
        let (redeem, signature) = signed();
        assert_eq!(signature.0.to_bytes().len(), WOTS_SCRIPT_SIG_SIZE);
        assert_eq!(WOTS_SCRIPT_SIG_SIZE, 2226);
        assert_eq!(WOTS_INPUT_SIZE, 2269);
        let values: Vec<_> = signature
            .0
            .parse()
            .map(|op| match op.unwrap() {
                zcash_script::opcode::PossiblyBad::Good(zcash_script::Opcode::PushValue(value)) => {
                    value.value()
                }
                _ => panic!("the authorization contains only data pushes"),
            })
            .collect();
        assert_eq!(
            values.iter().map(Vec::len).collect::<Vec<_>>(),
            [512, 512, 512, 512, 96, 32, 34]
        );
        assert_eq!(values[5], [9; 32]);
        assert!(!evaluate(&redeem, &signature, Flags::empty(), [4; 32]));
        assert!(evaluate(&redeem, &signature, Flags::CHECKWOTS, [4; 32]));
        assert!(!evaluate(&redeem, &signature, Flags::CHECKWOTS, [5; 32]));
    }

    #[test]
    fn former_full_key_encoding_and_wrong_raw_lengths_are_rejected() {
        let (redeem, script) = signed();
        let key = SigningKey::from_seeds(
            wots_plus::SecretSeed::from_bytes([7; 32]),
            wots_plus::PublicSeed::from_bytes([9; 32]),
        )
        .unwrap()
        .verifying_key();
        // Reuse the existing signature bytes, never sign a different message.
        let mut old = script.0.0[..2158].to_vec();
        for chunk in key.to_bytes().chunks(512) {
            push(&mut old, chunk);
        }
        push(&mut old, redeem.as_bytes());
        assert!(!evaluate(
            &redeem,
            &Script(Code(old)),
            Flags::CHECKWOTS,
            [4; 32]
        ));
        for size in [0, 31, 33, 2176] {
            assert!(!verify(
                [4; 32],
                &[0; 2144],
                &vec![9; size],
                &redeem.0[1..33]
            ));
        }
        for size in [0, 2143, 2145] {
            assert!(!verify([4; 32], &vec![0; size], &[9; 32], &redeem.0[1..33]));
        }
        for size in [0, 31, 33] {
            assert!(!verify([4; 32], &[0; 2144], &[9; 32], &vec![0; size]));
        }
    }

    #[test]
    fn altered_signatures_keys_commitments_and_chunk_lengths_fail() {
        let (redeem, signature) = signed();
        // First signature byte, first public-seed byte, and first push length.
        for index in [3, 2159, 1] {
            let mut changed = signature.clone();
            changed.0.0[index] ^= 1;
            assert!(!evaluate(&redeem, &changed, Flags::CHECKWOTS, [4; 32]));
        }
        let mut changed = redeem.clone();
        changed.0[1] ^= 1;
        let mut changed_signature = signature.clone();
        let redeem_start = changed_signature.0.0.len() - changed.as_bytes().len();
        changed_signature.0.0[redeem_start..].copy_from_slice(changed.as_bytes());
        assert!(!evaluate(
            &changed,
            &changed_signature,
            Flags::CHECKWOTS,
            [4; 32]
        ));
        let mut truncated = signature;
        truncated.0.0.truncate(100);
        assert!(!evaluate(&redeem, &truncated, Flags::CHECKWOTS, [4; 32]));
    }

    #[test]
    fn only_wots_authorization_is_present_in_the_template() {
        let (redeem, _) = signed();
        assert_eq!(redeem.as_bytes().len(), 34);
        assert_eq!(redeem.as_bytes()[0], 32);
        assert_eq!(redeem.as_bytes()[33], CHECKWOTS);
        let mut ec_attempt = Vec::new();
        push(&mut ec_attempt, &[1; 72]);
        push(&mut ec_attempt, &[2; 33]);
        push(&mut ec_attempt, redeem.as_bytes());
        assert!(!evaluate(
            &redeem,
            &Script(Code(ec_attempt)),
            Flags::CHECKWOTS,
            [4; 32]
        ));
        let mut former_template = vec![0x63, 0x76, 0xa9, 20];
        former_template.extend([3; 20]);
        former_template.extend([0x88, 0xac, 0x67, 32]);
        former_template.extend(&redeem.as_bytes()[1..33]);
        former_template.extend([CHECKWOTS, 0x68]);
        assert!(RedeemScript::parse(&former_template).is_none());
    }

    #[test]
    fn work_count_ignores_data_pushes_but_includes_unselected_branches() {
        let (redeem, _) = signed();
        assert_eq!(sigop_cost(redeem.as_bytes()), WOTS_SIGOP_COST);
        assert_eq!(sigop_cost(&[1, CHECKWOTS]), 0);
        assert_eq!(sigop_cost(&[0x63, CHECKWOTS, 0x67, CHECKWOTS, 0x68]), 200);
        assert!(RedeemScript::parse(redeem.as_bytes()).is_some());
        assert!(RedeemScript::parse(&[0; 34]).is_none());
    }
}
