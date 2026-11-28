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
fn schemes_bind_parameters_context_and_exact_encodings() {
    use super::*;
    use crate::pq::{ParameterSet, sha2_128f, sha2_192s};
    use zcash_protocol::consensus::NetworkType;

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
    /// The shortest encoding of this payload, which PQ inputs are required to use.
    fn push(value: &[u8]) -> Vec<u8> {
        let mut bytes = if value.len() < 0x4c {
            vec![value.len() as u8]
        } else if value.len() < 0x100 {
            vec![0x4c, value.len() as u8]
        } else {
            let mut prefix = vec![0x4d];
            prefix.extend(u16::try_from(value.len()).unwrap().to_le_bytes());
            prefix
        };
        bytes.extend(value);
        bytes
    }
    /// The canonical output of this scheme committing to this body.
    fn output_of(set: ParameterSet, body: &Code) -> Code {
        output_script(set, body).unwrap()
    }
    /// The serialized input spending that output with this signature.
    fn input_for(body: &Code, signature: &[u8]) -> Vec<u8> {
        let mut input = push(signature);
        input.extend(push(&body.0));
        input
    }
    /// Verifies a spend of this scheme's output for this body.
    fn verify(
        network: NetworkType,
        set: ParameterSet,
        body: &Code,
        signature: &[u8],
        checker: &CallbackTransactionSignatureChecker<'_>,
    ) -> Result<bool, Error> {
        parse_output(&output_of(set, body))
            .unwrap()
            .unwrap()
            .verify_spend(network, &input_for(body, signature), checker)
    }
    const NETWORK: NetworkType = NetworkType::Main;
    let signatures = [ParameterSet::Sha2_128f, ParameterSet::Sha2_192s]
        .map(|set| signed(set, signing_context(NETWORK, set)));
    for (index, set) in [ParameterSet::Sha2_128f, ParameterSet::Sha2_192s]
        .into_iter()
        .enumerate()
    {
        let (key, signature) = &signatures[index];
        let other = 1 - index;
        let mut key_body = push(key);
        key_body.push(0xac);
        let body = Code(key_body);
        let previous_output = output_of(set, &body);
        // The scheme is in the output and only there; the body is the committed script.
        assert_eq!(previous_output.0[1], set.scheme_opcode());
        assert_eq!(previous_output.0[HEADER_BYTES..], sha256::hash(&body.0));
        let sighash = |program: &Code, _: &zcash_script::signature::HashType| {
            assert_eq!(program.0, body.0);
            Some([42; 32])
        };
        let checker = CallbackTransactionSignatureChecker {
            sighash: &sighash,
            lock_time: 0,
            is_final: false,
        };
        let parsed = parse_output(&previous_output).unwrap().unwrap();
        let serialized = input_for(&body, signature);
        assert_eq!(
            parsed.verify_spend(NETWORK, &serialized, &checker),
            Ok(true)
        );
        let selected = parsed.authenticate_spend(&serialized).unwrap();
        assert_eq!(selected.parameters(), set);
        assert_eq!(selected.body(), body.0);
        assert_eq!(selected.sig_op_count(true), 1);
        assert_eq!(verify(NETWORK, set, &body, &[], &checker), Ok(false));
        assert!(verify(NETWORK, set, &body, &signatures[other].1, &checker).is_err());
        let (_, wrong_context) = signed(set, b"wrong-protocol-context");
        assert_eq!(
            verify(NETWORK, set, &body, &wrong_context, &checker),
            Ok(false)
        );
        // The context binds the network, which no transaction digest separates.
        for network in [NetworkType::Test, NetworkType::Regtest] {
            assert_ne!(signing_context(network, set), signing_context(NETWORK, set));
            assert_eq!(
                verify(network, set, &body, signature, &checker),
                Ok(false),
                "a signature for one network must not verify on another"
            );
        }
        // Nothing in the body says which scheme committed to it, so the output's scheme
        // is the only thing separating the parameter sets. Committing to this body under
        // the other scheme produces an output nothing here can spend, since this key is
        // the wrong length for it, and the context and digest bind the scheme besides.
        let other_set = [ParameterSet::Sha2_128f, ParameterSet::Sha2_192s][other];
        let crossed = output_of(other_set, &body);
        assert_eq!(crossed.0[HEADER_BYTES..], previous_output.0[HEADER_BYTES..]);
        assert_ne!(crossed.0[1], previous_output.0[1]);
        assert!(verify(NETWORK, other_set, &body, signature, &checker).is_err());
        // A different body is a different commitment, whatever its contents.
        let mut other_key_body = push(&signatures[other].0);
        other_key_body.push(0xac);
        let other_key_body = Code(other_key_body);
        assert_eq!(
            parsed.verify_spend(NETWORK, &input_for(&other_key_body, signature), &checker),
            Err(Error::CommitmentMismatch)
        );
        assert!(verify(NETWORK, set, &other_key_body, signature, &checker).is_err());
        let mut extended = signature.clone();
        extended.push(0);
        assert!(verify(NETWORK, set, &body, &extended, &checker).is_err());
        let mut bad_selector = signature.clone();
        *bad_selector.last_mut().unwrap() = 0;
        assert!(verify(NETWORK, set, &body, &bad_selector, &checker).is_err());
    }
}
