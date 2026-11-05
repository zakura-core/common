mod sha2_128f {
    use super::super::*;
    use crate::pq::sha2_128f as crypto;
    const PARAMETERS: ParameterSet = ParameterSet::Sha2_128f;
    include!("cases.rs");
}
mod sha2_192s {
    use super::super::*;
    use crate::pq::sha2_192s as crypto;
    const PARAMETERS: ParameterSet = ParameterSet::Sha2_192s;
    include!("cases.rs");
}

#[test]
fn versions_bind_parameters_context_and_exact_encodings() {
    use super::*;
    use crate::pq::{ParameterSet, sha2_128f, sha2_192s};
    fn signed(set: ParameterSet, context: &[u8]) -> (Vec<u8>, Vec<u8>) {
        let (key, mut signature) = match set {
            ParameterSet::Sha2_128f => {
                let key = sha2_128f::SigningKey::from_seed(&[8; sha2_128f::SEED_BYTES]);
                (
                    key.public_key().to_vec(),
                    key.sign(&[42; 32], context).unwrap(),
                )
            }
            ParameterSet::Sha2_192s => {
                let key = sha2_192s::SigningKey::from_seed(&[8; sha2_192s::SEED_BYTES]);
                (
                    key.public_key().to_vec(),
                    key.sign(&[42; 32], context).unwrap(),
                )
            }
        };
        signature.push(1);
        (key, signature)
    }
    fn push(value: &[u8]) -> Vec<u8> {
        let mut bytes = vec![0x4d];
        bytes.extend(u16::try_from(value.len()).unwrap().to_le_bytes());
        bytes.extend(value);
        bytes
    }
    fn spend(redeem: &Code, signature: &[u8]) -> script::Raw {
        let mut input = push(signature);
        input.extend(push(&redeem.0));
        let output: crate::address::Script =
            crate::address::TransparentAddress::ScriptHash(hash160::hash(&redeem.0))
                .script()
                .into();
        script::Raw::from_raw_parts(input, output.0.0)
    }
    let flags = Flags::P2SH | Flags::CHECKLOCKTIMEVERIFY;
    let signatures = [ParameterSet::Sha2_128f, ParameterSet::Sha2_192s]
        .map(|set| signed(set, signing_context(set)));
    for (index, set) in [ParameterSet::Sha2_128f, ParameterSet::Sha2_192s]
        .into_iter()
        .enumerate()
    {
        let (key, signature) = &signatures[index];
        let other = 1 - index;
        let mut body = push(key);
        body.push(0xac);
        let redeem = redeem_script(set, &Code(body.clone())).unwrap();
        assert_eq!(redeem.0[5], if index == 0 { 1 } else { 2 });
        let raw = spend(&redeem, signature);
        let sighash = |program: &Code, _: &zcash_script::signature::HashType| {
            assert_eq!(program.0, redeem.0);
            Some([42; 32])
        };
        let checker = CallbackTransactionSignatureChecker {
            sighash: &sighash,
            lock_time: 0,
            is_final: false,
        };
        assert_eq!(verify_spend(&raw, flags, &checker), Ok(true));
        let selected = classify_spend(&raw.sig.0, &raw.pub_key).unwrap();
        match selected {
            SpendMode::Pq(selected) => {
                assert_eq!(selected.parameters(), set);
                assert_eq!(selected.body(), body)
            }
            SpendMode::Legacy => panic!("committed PQ header selected legacy rules"),
        };
        assert_eq!(
            verify_spend(&spend(&redeem, &[]), flags, &checker),
            Ok(false)
        );
        assert!(verify_spend(&spend(&redeem, &signatures[other].1), flags, &checker).is_err());
        let (_, wrong_context) = signed(set, b"wrong-protocol-context");
        assert_eq!(
            verify_spend(&spend(&redeem, &wrong_context), flags, &checker),
            Ok(false)
        );
        let mut changed = redeem.clone();
        changed.0[5] = if index == 0 { 2 } else { 1 };
        let mut substitution = spend(&changed, signature);
        substitution.pub_key = raw.pub_key.clone();
        assert_eq!(
            verify_spend(&substitution, flags, &checker),
            Err(Error::CommitmentMismatch)
        );
        assert!(
            verify_spend(&spend(&changed, signature), flags, &checker).is_err(),
            "recommitting a version cannot reinterpret the original key/signature"
        );
        let mut other_key_body = push(&signatures[other].0);
        other_key_body.push(0xac);
        let other_key_redeem = redeem_script(set, &Code(other_key_body)).unwrap();
        assert!(verify_spend(&spend(&other_key_redeem, signature), flags, &checker).is_err());
        let mut extended = signature.clone();
        extended.push(0);
        assert!(verify_spend(&spend(&redeem, &extended), flags, &checker).is_err());
        let mut bad_selector = signature.clone();
        *bad_selector.last_mut().unwrap() = 0;
        assert!(verify_spend(&spend(&redeem, &bad_selector), flags, &checker).is_err());
    }
}
