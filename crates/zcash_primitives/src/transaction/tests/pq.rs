// Library integration for supplied programs and for scripts authenticated against the
// PQ output that commits to them. These tests do not activate PQ validation or
// establish node acceptance.

use alloc::vec::Vec;

use crate::transaction::tests::{TestTransparentAuth, TestUnauthorized};
use self::crypto::SigningKey;
use crate::transaction::{
    TransactionData, TxVersion,
    sighash::{SignableInput, signature_hash},
    txid::TxIdDigester,
};
use transparent::{
    address::Script,
    bundle::{Bundle, OutPoint, TxIn, TxOut},
    pq::{self},
    sighash::{self, SighashType},
};
use zcash_protocol::{consensus::BranchId, value::Zatoshis};
use zcash_script::{
    interpreter::{CallbackTransactionSignatureChecker, Error as InterpreterError, Flags},
    pq as pq_script,
    script::{self, Code},
    signature::HashType,
};

// Deliberately a test context, not the future consensus context.
const CONTEXT: &[u8] = b"common/pq/script-test/v1";

fn program(key: &[u8]) -> Code {
    let mut bytes = vec![u8::try_from(key.len()).unwrap()];
    bytes.extend_from_slice(key);
    bytes.push(0xac); // CHECKSIG
    Code(bytes)
}

/// The shortest encoding of this payload. PQ inputs must use it, and a script body
/// means the same thing either way.
fn pushed(value: &[u8]) -> Vec<u8> {
    match value {
        [] => vec![0x00],                                       // OP_0
        [0x81] => vec![0x4f],                                   // OP_1NEGATE
        [byte] if (1..=16).contains(byte) => vec![0x50 + byte], // OP_1 ..= OP_16
        _ => {
            let mut input = if value.len() < 0x4c {
                vec![value.len() as u8]
            } else if value.len() < 0x100 {
                vec![0x4c, value.len() as u8]
            } else {
                let mut prefix = vec![0x4d];
                prefix.extend_from_slice(&u16::try_from(value.len()).unwrap().to_le_bytes());
                prefix
            };
            input.extend_from_slice(value);
            input
        }
    }
}

fn transaction(key: &[u8]) -> TransactionData<TestUnauthorized> {
    transaction_with_program(&program(key))
}

fn transaction_with_program(code: &Code) -> TransactionData<TestUnauthorized> {
    TransactionData::from_parts(
        TxVersion::V5,
        BranchId::Nu5,
        0,
        100u32.into(),
        Some(Bundle {
            vin: vec![TxIn::from_parts(
                OutPoint::new([7; 32], 0),
                Script::default(),
                0,
            )],
            vout: vec![TxOut::new(
                Zatoshis::const_from_u64(90),
                Script(Code(vec![0x51])),
            )],
            authorization: TestTransparentAuth {
                input_amounts: vec![Zatoshis::const_from_u64(100)],
                input_scriptpubkeys: vec![Script(code.clone())],
            },
        }),
        None,
        None,
        None,
    )
}

fn digest(tx: &TransactionData<TestUnauthorized>, selector: u8) -> Option<[u8; 32]> {
    let previous = &tx
        .transparent_bundle()
        .unwrap()
        .authorization
        .input_scriptpubkeys[0];
    digest_with_script(tx, selector, previous)
}

fn digest_with_script(
    tx: &TransactionData<TestUnauthorized>,
    selector: u8,
    script_code: &Script,
) -> Option<[u8; 32]> {
    let hash_type = SighashType::parse(selector)?;
    let bundle = tx.transparent_bundle().unwrap();
    // ZIP 244 rejects SINGLE without the corresponding transparent output.
    if selector & sighash::SIGHASH_MASK == sighash::SIGHASH_SINGLE && bundle.vout.is_empty() {
        return None;
    }
    let previous = &bundle.authorization.input_scriptpubkeys[0];
    let input = sighash::SignableInput::from_parts(
        bundle,
        hash_type,
        0,
        script_code,
        previous,
        bundle.authorization.input_amounts[0],
    )
    .unwrap();
    Some(
        *signature_hash(
            tx,
            &SignableInput::Transparent(input),
            &tx.digest(TxIdDigester),
        )
        .as_ref(),
    )
}

mod output_spends {
    use super::*;
    use transparent::{bundle::Authorized, pq::output};
    use zcash_protocol::consensus::NetworkType;

    const NETWORK: NetworkType = NetworkType::Main;

    fn context() -> &'static [u8] {
        output::signing_context(NETWORK, PARAMETERS)
    }

    fn transaction(body: &Code) -> TransactionData<TestUnauthorized> {
        let output = TxOut::new(
            Zatoshis::const_from_u64(100),
            Script(output::output_script(PARAMETERS, body).unwrap()),
        );
        let mut wire = Vec::new();
        output.write(&mut wire).unwrap();
        let decoded = TxOut::read(&mut &wire[..]).unwrap();
        assert_eq!(decoded, output);
        // The spent output carries the format and scheme on chain, and no address type
        // encodes them.
        assert_eq!(decoded.recipient_address(), None);
        transaction_with_program(&decoded.script_pubkey().0)
    }

    fn install_input(tx: &mut TransactionData<TestUnauthorized>, input: &[u8]) {
        let bundle = tx.transparent_bundle.as_mut().unwrap();
        let previous = &bundle.vin[0];
        let encoded = TxIn::<Authorized>::from_parts(
            previous.prevout().clone(),
            Script(Code(input.to_vec())),
            previous.sequence(),
        );
        let mut wire = Vec::new();
        encoded.write(&mut wire).unwrap();
        let decoded = TxIn::<Authorized>::read(&mut &wire[..]).unwrap();
        assert_eq!(decoded.script_sig().0.0, input);
        bundle.vin[0] = TxIn::from_parts(
            decoded.prevout().clone(),
            decoded.script_sig().clone(),
            decoded.sequence(),
        );
    }

    fn signed_input(
        key: &SigningKey,
        tx: &TransactionData<TestUnauthorized>,
        body: &Code,
        selector: u8,
        context: &[u8],
    ) -> Vec<u8> {
        let mut signature = key
            .sign(
                &digest_with_script(tx, selector, &Script(body.clone())).unwrap(),
                context,
            )
            .unwrap();
        signature.push(selector);
        let mut input = pushed(&signature);
        input.extend_from_slice(&pushed(&body.0));
        input
    }

    fn spend_null_fail() -> Result<bool, output::Error> {
        null_fail().map_err(output::Error::Pq)
    }

    fn check(
        tx: &TransactionData<TestUnauthorized>,
        body: &Code,
    ) -> Result<bool, output::Error> {
        let bundle = tx.transparent_bundle().unwrap();
        let sighash = |script_code: &Code, hash_type: &HashType| {
            // The digest is taken over the body script, which is all that executes.
            assert_eq!(script_code.0, body.0);
            digest_with_script(tx, hash_type.raw_bits() as u8, &Script(script_code.clone()))
        };
        output::parse_output(&bundle.authorization.input_scriptpubkeys[0].0)?
            .expect("these tests spend PQ outputs")
            .verify_spend(
                NETWORK,
                &bundle.vin[0].script_sig().0.0,
                &CallbackTransactionSignatureChecker {
                    sighash: &sighash,
                    lock_time: i64::from(tx.lock_time()),
                    is_final: bundle.vin[0].sequence() == u32::MAX,
                },
            )
    }

    #[test]
    fn serialized_threshold_authenticates_each_signer_in_its_own_slot() {
        let keys: Vec<_> = (3..=5)
            .map(|seed| SigningKey::from_seed(&[seed; crypto::SEED_BYTES]))
            .collect();
        let body = threshold_program(
            2,
            &keys.iter().map(SigningKey::public_key).collect::<Vec<_>>(),
            false,
        );
        let mut tx = transaction(&body);
        let signatures: Vec<_> = keys
            .iter()
            .map(|key| {
                let mut input =
                    signed_input(key, &tx, &body, sighash::SIGHASH_ALL, context());
                input.truncate(input.len() - pushed(&body.0).len());
                input
            })
            .collect();
        // The serialized signature pushes, unwrapped back into payloads for `slots`.
        let payloads: Vec<Vec<u8>> = signatures.iter().map(|push| push[3..].to_vec()).collect();
        for pair in [[0, 1], [0, 2], [1, 2]] {
            let chosen: Vec<_> = (0..3)
                .map(|index| pair.contains(&index).then(|| &payloads[index]))
                .collect();
            install_input(&mut tx, &[slots(&chosen), pushed(&body.0)].concat());
            assert_eq!(check(&tx, &body), Ok(true), "signers {pair:?}");
        }
        // A signature in another key's slot is a failed signature, not a skipped one.
        let crossed = [Some(&payloads[1]), Some(&payloads[0]), None];
        install_input(&mut tx, &[slots(&crossed), pushed(&body.0)].concat());
        assert_eq!(check(&tx, &body), spend_null_fail());
        let mut forged = payloads[0].clone();
        forged[0] ^= 1;
        let forged = [Some(&forged), None, Some(&payloads[2])];
        install_input(&mut tx, &[slots(&forged), pushed(&body.0)].concat());
        assert_eq!(check(&tx, &body), spend_null_fail());
    }

    #[test]
    fn serialized_spend_authenticates_the_committed_script_and_v5_transaction() {
        let key = SigningKey::from_seed(&[3; crypto::SEED_BYTES]);
        let body = program(&key.public_key());
        let mut tx = transaction(&body);
        let input = signed_input(&key, &tx, &body, sighash::SIGHASH_ALL, context());
        install_input(&mut tx, &input);
        assert_eq!(check(&tx, &body), Ok(true));

        for mutate in [
            |tx: &mut TransactionData<TestUnauthorized>| tx.lock_time += 1,
            |tx: &mut TransactionData<TestUnauthorized>| tx.expiry_height = 101u32.into(),
            |tx: &mut TransactionData<TestUnauthorized>| tx.consensus_branch_id = BranchId::Nu6,
            |tx: &mut TransactionData<TestUnauthorized>| {
                tx.transparent_bundle.as_mut().unwrap().vout[0] =
                    TxOut::new(Zatoshis::const_from_u64(89), Script(Code(vec![0x51])));
            },
            |tx: &mut TransactionData<TestUnauthorized>| {
                tx.transparent_bundle
                    .as_mut()
                    .unwrap()
                    .authorization
                    .input_amounts[0] = Zatoshis::const_from_u64(101);
            },
            |tx: &mut TransactionData<TestUnauthorized>| {
                tx.transparent_bundle.as_mut().unwrap().vin[0] =
                    TxIn::from_parts(OutPoint::new([8; 32], 0), Script::default(), 0);
            },
            |tx: &mut TransactionData<TestUnauthorized>| {
                tx.transparent_bundle.as_mut().unwrap().vin[0] =
                    TxIn::from_parts(OutPoint::new([7; 32], 0), Script::default(), 1);
            },
        ] {
            let mut changed = transaction(&body);
            mutate(&mut changed);
            install_input(&mut changed, &input);
            assert_eq!(check(&changed, &body), spend_null_fail());
        }

        let mut forged = input.clone();
        forged[3] ^= 1;
        install_input(&mut tx, &forged);
        assert_eq!(check(&tx, &body), spend_null_fail());

        // Equivalent execution with different bytes still needs a different output/signature.
        let mut changed_body = vec![0x61]; // NOP
        changed_body.extend_from_slice(&body.0);
        let changed_body = Code(changed_body);
        let mut substituted = input[..input.len() - pushed(&body.0).len()].to_vec();
        substituted.extend_from_slice(&pushed(&changed_body.0));
        install_input(&mut tx, &substituted);
        assert_eq!(
            check(&tx, &changed_body),
            Err(output::Error::CommitmentMismatch)
        );
        let mut changed_tx = transaction(&changed_body);
        install_input(&mut changed_tx, &substituted);
        assert_eq!(check(&changed_tx, &changed_body), spend_null_fail());

        let wrong_context = signed_input(&key, &tx, &body, sighash::SIGHASH_ALL, CONTEXT);
        install_input(&mut tx, &wrong_context);
        assert_eq!(check(&tx, &body), spend_null_fail());
    }

    #[test]
    fn the_output_scheme_is_bound_by_the_v5_digest() {
        let key = SigningKey::from_seed(&[3; crypto::SEED_BYTES]);
        let body = program(&key.public_key());
        let mut tx = transaction(&body);
        let input = signed_input(&key, &tx, &body, sighash::SIGHASH_ALL, context());
        install_input(&mut tx, &input);
        assert_eq!(check(&tx, &body), Ok(true));
        let signed_digest = digest(&tx, sighash::SIGHASH_ALL);

        // The scheme now sits in the previous output, which the v5 digest commits to
        // directly; under the P2SH form it reached the digest only through the hash.
        let other = match PARAMETERS {
            pq::ParameterSet::Sha2_128f => pq::ParameterSet::Sha2_192s,
            pq::ParameterSet::Sha2_192s => pq::ParameterSet::Sha2_128f,
        };
        let mut flipped = tx
            .transparent_bundle()
            .unwrap()
            .authorization
            .input_scriptpubkeys[0]
            .0
            .clone();
        flipped.0[1] = other.scheme_opcode();
        tx.transparent_bundle
            .as_mut()
            .unwrap()
            .authorization
            .input_scriptpubkeys[0] = Script(flipped);
        assert_ne!(digest(&tx, sighash::SIGHASH_ALL), signed_digest);
        // The same commitment still authenticates the same script, because the commitment
        // covers the body alone. The output's scheme is what selects the rules, so this
        // spend is now rejected: for a key of the wrong length for them, or, when the input
        // is smaller than one of the other scheme's signatures, for not paying for the
        // check at all, which is charged first.
        let input_bytes = tx.transparent_bundle().unwrap().vin[0].script_sig().0.0.len();
        let expected = if input_bytes < other.signature_bytes() {
            InterpreterError::PqCheckBudget
        } else {
            InterpreterError::PubKeyType
        };
        assert!(matches!(
            check(&tx, &body),
            Err(output::Error::Pq(pq_script::Error::Script(
                script::Error::Interpreter(_, error)
            ))) if error == expected
        ));
    }

    #[test]
    fn a_pq_output_is_claimable_under_legacy_rules_and_only_the_flag_refuses_it() {
        let key = SigningKey::from_seed(&[3; crypto::SEED_BYTES]);
        let body = program(&key.public_key());
        let mut tx = transaction(&body);
        let script_pubkey = tx
            .transparent_bundle()
            .unwrap()
            .authorization
            .input_scriptpubkeys[0]
            .0
            .clone();

        // No signature check runs in any of this; the output is three pushes.
        let sighash = |_: &Code, _: &HashType| None;
        let checker = CallbackTransactionSignatureChecker {
            sighash: &sighash,
            lock_time: 0,
            is_final: false,
        };

        // This is what the legacy evaluator does with a real PQ output: the truthy
        // commitment is left on top of the stack, so an *empty* scriptSig satisfies it and
        // anyone takes the coins. The output is claimable wherever the PQ rules are not
        // active, which is the cost of an `OP_0` marker over `OP_RESERVED`, and the flag is
        // the whole of what replaces that protection. Asserted rather than assumed, so it
        // cannot change without this failing.
        for sig in [Vec::new(), vec![0x51], pushed(&body.0)] {
            assert_eq!(
                script::Raw::from_raw_parts(sig.clone(), script_pubkey.0.clone())
                    .eval(Flags::P2SH, &checker),
                Ok(true)
            );
            assert_eq!(
                script::Raw::from_raw_parts(sig, script_pubkey.0.clone())
                    .eval(Flags::P2SH | Flags::PqOutputs, &checker),
                Err((script::ComponentType::PubKey, script::Error::PqNamespace))
            );
        }

        // Nothing about that legacy acceptance carries into the PQ rules: the same inputs
        // are rejected there, and only a real signature over the committed body spends it.
        for sig in [Vec::new(), vec![0x51]] {
            install_input(&mut tx, &sig);
            assert!(check(&tx, &body).is_err());
        }
        let input = signed_input(&key, &tx, &body, sighash::SIGHASH_ALL, context());
        install_input(&mut tx, &input);
        assert_eq!(check(&tx, &body), Ok(true));
    }

    #[test]
    fn output_spends_retain_six_signing_modes_and_absolute_locktime() {
        let key = SigningKey::from_seed(&[3; crypto::SEED_BYTES]);
        let mut body = vec![0x01, 100, 0xb1, 0x75]; // 100 CLTV DROP
        body.extend_from_slice(&program(&key.public_key()).0);
        let body = Code(body);
        for selector in [1, 2, 3, 0x81, 0x82, 0x83] {
            let mut tx = transaction(&body);
            tx.lock_time = 100;
            let input = signed_input(&key, &tx, &body, selector, context());
            install_input(&mut tx, &input);
            assert_eq!(check(&tx, &body), Ok(true));
            tx.transparent_bundle.as_mut().unwrap().vout[0] =
                TxOut::new(Zatoshis::const_from_u64(89), Script(Code(vec![0x51])));
            assert_eq!(
                check(&tx, &body),
                if selector & sighash::SIGHASH_MASK == sighash::SIGHASH_NONE { Ok(true) } else { spend_null_fail() }
            );
            if selector & sighash::SIGHASH_MASK == sighash::SIGHASH_SINGLE {
                tx.transparent_bundle.as_mut().unwrap().vout.clear();
                assert_eq!(check(&tx, &body), spend_null_fail());
            }
            tx.lock_time = 99;
            assert!(matches!(
                check(&tx, &body),
                Err(output::Error::Pq(pq_script::Error::Script(
                    script::Error::Interpreter(_, InterpreterError::UnsatisfiedLockTime)
                )))
            ));
            tx.lock_time = 100;
            tx.transparent_bundle.as_mut().unwrap().vin[0] =
                TxIn::from_parts(OutPoint::new([7; 32], 0), Script(Code(input)), u32::MAX);
            assert!(matches!(
                check(&tx, &body),
                Err(output::Error::Pq(pq_script::Error::Script(
                    script::Error::Interpreter(_, InterpreterError::UnsatisfiedLockTime)
                )))
            ));
        }
    }
}

fn check(
    tx: &TransactionData<TestUnauthorized>,
    input: &[u8],
    code: &Code,
    context: &[u8],
) -> Result<bool, pq_script::Error> {
    let sighash = |_: &Code, hash_type: &HashType| digest(tx, hash_type.raw_bits() as u8);
    let checker = CallbackTransactionSignatureChecker {
        sighash: &sighash,
        lock_time: i64::from(tx.lock_time()),
        is_final: tx.transparent_bundle().unwrap().vin[0].sequence() == u32::MAX,
    };
    // Budgeted as the serialized input would be: these arguments, then the pushed program.
    let input_bytes = input.len() + pushed(&code.0).len();
    pq::script::verify_script(PARAMETERS, input, code, context, &checker, input_bytes)
}

/// What a non-empty signature that fails to verify does to a single-key spend.
fn null_fail() -> Result<bool, pq_script::Error> {
    Err(pq_script::Error::Script(script::Error::Interpreter(
        Some(zcash_script::opcode::PossiblyBad::Good(zcash_script::op::CHECKSIG)),
        InterpreterError::PqNullFail,
    )))
}

fn signature(key: &SigningKey, tx: &TransactionData<TestUnauthorized>, selector: u8) -> Vec<u8> {
    let mut signature = key.sign(&digest(tx, selector).unwrap(), CONTEXT).unwrap();
    signature.push(selector);
    signature
}

/// `<K1> CHECKSIG <K2> CHECKSIGADD ... <Kn> CHECKSIGADD <required> NUMEQUAL[VERIFY]`.
fn threshold_program(
    required: u8,
    keys: &[[u8; crypto::PUBLIC_KEY_BYTES]],
    verify: bool,
) -> Code {
    let mut bytes = Vec::new();
    for (index, key) in keys.iter().enumerate() {
        bytes.extend(pushed(key));
        bytes.push(if index == 0 { 0xac } else { pq_script::OP_CHECKSIGADD });
    }
    bytes.extend(pushed(&zcash_script::num::serialize(i64::from(required))));
    bytes.push(if verify { 0x9d } else { 0x9c }); // NUMEQUALVERIFY or NUMEQUAL
    Code(bytes)
}

/// The arguments [`threshold_program`] takes: a signature or an empty item for each key,
/// the first key's on top of the stack.
fn slots(signatures: &[Option<&Vec<u8>>]) -> Vec<u8> {
    signatures
        .iter()
        .rev()
        .flat_map(|signature| signature.map_or_else(|| vec![0], |signature| pushed(signature)))
        .collect()
}

fn interpreter_error(result: Result<bool, pq_script::Error>) -> InterpreterError {
    match result {
        Err(pq_script::Error::Script(script::Error::Interpreter(_, error))) => error,
        other => panic!("expected script execution to abort, got {other:?}"),
    }
}

#[test]
fn pq_script_executes_serialized_signature_over_real_v5_digest() {
    let key = SigningKey::from_seed(&[3; crypto::SEED_BYTES]);
    let public_key = key.public_key();
    let mut tx = transaction(&public_key);
    let code = program(&public_key);
    let argument = signature(&key, &tx, sighash::SIGHASH_ALL);
    let input = pushed(&argument);
    assert_eq!(input.len(), crypto::SIGNATURE_BYTES + 4);

    // Pass through the same length-prefixed script field used in transaction inputs.
    let mut wire = Vec::new();
    Script(Code(input.clone())).write(&mut wire).unwrap();
    let decoded = Script::read(&wire[..]).unwrap();
    assert_eq!(decoded.0.0, input);
    tx.transparent_bundle.as_mut().unwrap().vin[0] =
        TxIn::from_parts(OutPoint::new([7; 32], 0), decoded.clone(), 0);
    assert_eq!(check(&tx, &decoded.0.0, &code, CONTEXT), Ok(true));

    let mut verify_program = code.clone();
    *verify_program.0.last_mut().unwrap() = 0xad; // CHECKSIGVERIFY
    verify_program.0.push(0x51);
    assert_eq!(check(&tx, &input, &verify_program, CONTEXT), Ok(true));

    // The same bytes are not accepted by the unchanged legacy parser/evaluator.
    let legacy = script::Raw::from_raw_parts(input.clone(), code.0.clone());
    let sighash = |_: &Code, _: &HashType| digest(&tx, sighash::SIGHASH_ALL);
    let checker = CallbackTransactionSignatureChecker {
        sighash: &sighash,
        lock_time: 0,
        is_final: false,
    };
    assert!(matches!(
        legacy.eval(Flags::empty(), &checker),
        Err((script::ComponentType::Sig, script::Error::ScriptSize(_)))
    ));
    let legacy = script::Raw::from_raw_parts(pushed(&[1; 521]), vec![0x51]);
    assert!(matches!(
        legacy.eval(Flags::empty(), &checker),
        Err((
            script::ComponentType::Sig,
            script::Error::Opcode(zcash_script::opcode::Error::PushSize(_))
        ))
    ));

    assert_eq!(check(&tx, &input, &code, b"different context"), null_fail());
    assert_eq!(
        check(&tx, &input, &code, &[0; 256]),
        Err(pq_script::Error::ContextSize)
    );
    let other_key = SigningKey::from_seed(&[4; crypto::SEED_BYTES]).public_key();
    assert_eq!(check(&tx, &input, &program(&other_key), CONTEXT), null_fail());

    for position in [0, 24, crypto::SIGNATURE_BYTES - 1] {
        let mut altered = argument.clone();
        altered[position] ^= 1;
        assert_eq!(check(&tx, &pushed(&altered), &code, CONTEXT), null_fail());
    }
    for mutate in [
        |tx: &mut TransactionData<TestUnauthorized>| tx.lock_time += 1,
        |tx: &mut TransactionData<TestUnauthorized>| tx.expiry_height = 101u32.into(),
        |tx: &mut TransactionData<TestUnauthorized>| tx.consensus_branch_id = BranchId::Nu6,
        |tx: &mut TransactionData<TestUnauthorized>| {
            tx.transparent_bundle.as_mut().unwrap().vout[0] =
                TxOut::new(Zatoshis::const_from_u64(89), Script(Code(vec![0x51])));
        },
        |tx: &mut TransactionData<TestUnauthorized>| {
            tx.transparent_bundle
                .as_mut()
                .unwrap()
                .authorization
                .input_amounts[0] = Zatoshis::const_from_u64(101);
        },
        |tx: &mut TransactionData<TestUnauthorized>| {
            tx.transparent_bundle.as_mut().unwrap().vin[0] =
                TxIn::from_parts(OutPoint::new([8; 32], 0), Script::default(), 0);
        },
        |tx: &mut TransactionData<TestUnauthorized>| {
            tx.transparent_bundle
                .as_mut()
                .unwrap()
                .authorization
                .input_scriptpubkeys[0] = Script(Code(vec![0x51]));
        },
    ] {
        let mut changed = transaction(&public_key);
        mutate(&mut changed);
        assert_eq!(check(&changed, &input, &code, CONTEXT), null_fail());
    }
}

#[test]
fn pq_script_preserves_false_and_abort() {
    let key = SigningKey::from_seed(&[3; crypto::SEED_BYTES]);
    let tx = transaction(&key.public_key());
    let code = program(&key.public_key());
    let argument = signature(&key, &tx, sighash::SIGHASH_ALL);
    assert_eq!(check(&tx, &[0], &code, CONTEXT), Ok(false));
    let mut negated = code.clone();
    negated.0.push(0x91); // NOT: a false signature result remains usable by Script.
    assert_eq!(check(&tx, &[0], &negated, CONTEXT), Ok(true));
    let mut verify_code = code.clone();
    *verify_code.0.last_mut().unwrap() = 0xad;
    assert!(matches!(
        check(&tx, &[0], &verify_code, CONTEXT),
        Err(pq_script::Error::Script(script::Error::Interpreter(
            _,
            InterpreterError::Verify
        )))
    ));
    for length in [crypto::PUBLIC_KEY_BYTES - 1, crypto::PUBLIC_KEY_BYTES + 1] {
        let mut bad_program = program(&vec![0; length]);
        bad_program.0.push(0x91);
        assert!(matches!(
            check(&tx, &[0], &bad_program, CONTEXT),
            Err(pq_script::Error::Script(script::Error::Interpreter(
                _,
                InterpreterError::PubKeyType
            )))
        ));
    }
    assert_eq!(
        interpreter_error(check(
            &tx,
            &pushed(&argument[..crypto::SIGNATURE_BYTES]),
            &code,
            CONTEXT
        )),
        InterpreterError::PqSignatureSize
    );
    // A check is charged before its signature is examined, so an input too small to pay
    // for one is refused for that first. Either way nothing is verified.
    assert_eq!(
        interpreter_error(check(&tx, &pushed(&argument[..1]), &code, CONTEXT)),
        InterpreterError::PqCheckBudget
    );
    let mut extended = argument.clone();
    extended.push(0);
    let result = check(&tx, &pushed(&extended), &code, CONTEXT);
    if PARAMETERS == pq::ParameterSet::Sha2_128f {
        assert_eq!(result, Err(pq_script::Error::PushSize));
    } else {
        assert_eq!(interpreter_error(result), InterpreterError::PqSignatureSize);
    }
    let mut bad_selector = argument.clone();
    *bad_selector.last_mut().unwrap() = 0x04;
    assert!(check(&tx, &pushed(&bad_selector), &code, CONTEXT).is_err());
    *bad_selector.last_mut().unwrap() = sighash::SIGHASH_NONE;
    assert_eq!(
        check(&tx, &pushed(&bad_selector), &code, CONTEXT),
        null_fail()
    );
}

fn threshold_error(result: Result<bool, pq_script::Error>, opcode: u8) -> InterpreterError {
    match result {
        Err(pq_script::Error::Script(script::Error::Interpreter(Some(op), error))) => {
            assert_eq!(Vec::<u8>::from(&op), vec![opcode]);
            error
        }
        other => panic!("expected an interpreter error, got {other:?}"),
    }
}

#[test]
fn pq_script_one_of_one_threshold_takes_a_signature_or_an_empty_item() {
    let key = SigningKey::from_seed(&[3; crypto::SEED_BYTES]);
    for verify in [false, true] {
        let mut code = threshold_program(1, &[key.public_key()], verify);
        if verify {
            code.0.push(0x51);
        }
        let tx = transaction_with_program(&code);
        let argument = signature(&key, &tx, sighash::SIGHASH_ALL);
        assert_eq!(
            check(&tx, &slots(&[Some(&argument)]), &code, CONTEXT),
            Ok(true)
        );
        // Declining is an empty item, which fails the threshold, not the signature.
        let declined = check(&tx, &slots(&[None]), &code, CONTEXT);
        if verify {
            assert_eq!(threshold_error(declined, 0x9d), InterpreterError::Verify);
        } else {
            assert_eq!(declined, Ok(false));
        }
        // No dummy argument any more: an extra item is left on the stack and refused.
        assert_eq!(
            check(&tx, &[vec![0], pushed(&argument)].concat(), &code, CONTEXT),
            Err(pq_script::Error::Script(script::Error::CleanStack))
        );
        let mut altered = argument;
        altered[0] ^= 1;
        assert_eq!(
            check(&tx, &slots(&[Some(&altered)]), &code, CONTEXT),
            null_fail()
        );
    }
}

#[test]
fn pq_script_one_of_two_checks_only_the_signer() {
    let alice = SigningKey::from_seed(&[3; crypto::SEED_BYTES]);
    let bob = SigningKey::from_seed(&[4; crypto::SEED_BYTES]);
    let code = threshold_program(1, &[alice.public_key(), bob.public_key()], false);
    let tx = transaction_with_program(&code);
    let alice_signature = signature(&alice, &tx, sighash::SIGHASH_ALL);
    let bob_signature = signature(&bob, &tx, sighash::SIGHASH_ALL);
    // Either key alone, with an empty item in the other's slot: one check, never a trial.
    for chosen in [[Some(&alice_signature), None], [None, Some(&bob_signature)]] {
        assert_eq!(check(&tx, &slots(&chosen), &code, CONTEXT), Ok(true));
    }
    // Both signing is a valid count of two, which a one-of-two does not accept.
    assert_eq!(
        check(
            &tx,
            &slots(&[Some(&alice_signature), Some(&bob_signature)]),
            &code,
            CONTEXT
        ),
        Ok(false)
    );
    // Bob's signature in Alice's slot fails, where CHECKMULTISIG would have moved on.
    let crossed = check(&tx, &slots(&[Some(&bob_signature), None]), &code, CONTEXT);
    assert_eq!(crossed, null_fail());
}

#[test]
fn pq_script_two_of_three_accepts_each_pair_and_rejects_misplaced_signatures() {
    let keys: Vec<_> = (3..=5)
        .map(|seed| SigningKey::from_seed(&[seed; crypto::SEED_BYTES]))
        .collect();
    for verify in [false, true] {
        let mut code = threshold_program(
            2,
            &keys.iter().map(SigningKey::public_key).collect::<Vec<_>>(),
            verify,
        );
        if verify {
            code.0.push(0x51);
        }
        let tx = transaction_with_program(&code);
        let arguments: Vec<_> = keys
            .iter()
            .map(|key| signature(key, &tx, sighash::SIGHASH_ALL))
            .collect();
        for pair in [[0, 1], [0, 2], [1, 2]] {
            let chosen: Vec<_> = (0..3)
                .map(|index| pair.contains(&index).then(|| &arguments[index]))
                .collect();
            assert_eq!(
                check(&tx, &slots(&chosen), &code, CONTEXT),
                Ok(true),
                "pair {pair:?}"
            );
        }
        // The first and third signatures in each other's slots.
        let swapped = [Some(&arguments[2]), None, Some(&arguments[0])];
        assert_eq!(check(&tx, &slots(&swapped), &code, CONTEXT), null_fail());
        let mut forged = vec![0; crypto::SIGNATURE_BYTES];
        forged.push(sighash::SIGHASH_ALL);
        let with_forgery = [None, Some(&forged), Some(&arguments[2])];
        assert_eq!(
            threshold_error(
                check(&tx, &slots(&with_forgery), &code, CONTEXT),
                pq_script::OP_CHECKSIGADD
            ),
            InterpreterError::PqNullFail
        );
        assert!(
            check(&tx, &[0, 0], &code, CONTEXT).is_err(),
            "insufficient stack arguments abort"
        );
    }
}

#[test]
fn pq_script_large_thresholds_and_multiple_checks_fit_bounded_resources() {
    let key = SigningKey::from_seed(&[3; crypto::SEED_BYTES]);
    // Past CHECKMULTISIG's twenty keys. Duplicate keys remain legal, as in legacy Script;
    // this fixture measures signature transport and verifications, not ownership.
    let keys = 25;
    let code = threshold_program(keys, &vec![key.public_key(); usize::from(keys)], false);
    let tx = transaction_with_program(&code);
    let argument = signature(&key, &tx, sighash::SIGHASH_ALL);
    let input = slots(&vec![Some(&argument); usize::from(keys)]);
    let start = std::time::Instant::now();
    assert_eq!(check(&tx, &input, &code, CONTEXT), Ok(true));
    std::eprintln!(
        "{keys}-of-{keys}: input={} bytes, verification={:?}",
        input.len(),
        start.elapsed()
    );

    // One signer among twenty keys: nineteen empty slots, one check.
    let mut wrong = key.public_key();
    wrong[0] ^= 1;
    let mut public_keys = vec![key.public_key()];
    public_keys.extend([wrong; 19]);
    let code = threshold_program(1, &public_keys, false);
    let tx = transaction_with_program(&code);
    let argument = signature(&key, &tx, sighash::SIGHASH_ALL);
    let mut chosen = vec![None; 20];
    chosen[0] = Some(&argument);
    let start = std::time::Instant::now();
    assert_eq!(check(&tx, &slots(&chosen), &code, CONTEXT), Ok(true));
    std::eprintln!("1-of-20 with nineteen declined slots: {:?}", start.elapsed());

    // Two checks of one signature need two copies of it in the input, each paying.
    let mut code = program(&key.public_key());
    *code.0.last_mut().unwrap() = 0xad; // CHECKSIGVERIFY
    code.0.extend(program(&key.public_key()).0);
    let tx = transaction_with_program(&code);
    let argument = signature(&key, &tx, sighash::SIGHASH_ALL);
    assert_eq!(
        check(
            &tx,
            &[pushed(&argument), pushed(&argument)].concat(),
            &code,
            CONTEXT
        ),
        Ok(true)
    );
    // And one copy checked twice is over budget.
    let mut copied = vec![0x76]; // DUP
    copied.extend(&code.0);
    let copied = Code(copied);
    let tx = transaction_with_program(&copied);
    let argument = signature(&key, &tx, sighash::SIGHASH_ALL);
    assert_eq!(
        threshold_error(check(&tx, &pushed(&argument), &copied, CONTEXT), 0xac),
        InterpreterError::PqCheckBudget
    );
}

#[test]
fn pq_script_absolute_locktime_checks_boundaries_types_and_sequence() {
    // These exercise the script condition, not block-height or mempool finality.
    for (required, lock_time, sequence, succeeds) in [
        (100, 99, 0, false),
        (100, 100, 0, true),
        (100, 101, 0, true),
        (100, 100, u32::MAX - 1, true),
        (100, 100, u32::MAX, false),
        (499_999_999, 500_000_000, 0, false),
        (500_000_000, 499_999_999, 0, false),
        (500_000_001, 500_000_000, 0, false),
        (500_000_000, 500_000_000, 0, true),
        (500_000_000, 500_000_001, 0, true),
        (500_000_000, 500_000_000, u32::MAX, false),
        (u32::MAX, u32::MAX, 0, true),
    ] {
        let mut bytes = pushed(&zcash_script::num::serialize(i64::from(required)));
        bytes.extend_from_slice(&[0xb1, 0x75, 0x51]); // CLTV DROP TRUE
        let code = Code(bytes);
        let mut tx = transaction_with_program(&code);
        tx.lock_time = lock_time;
        tx.transparent_bundle.as_mut().unwrap().vin[0] =
            TxIn::from_parts(OutPoint::new([7; 32], 0), Script::default(), sequence);
        let result = check(&tx, &[], &code, CONTEXT);
        let case = format!("deadline {required}, locktime {lock_time}, sequence {sequence}");
        if succeeds {
            assert_eq!(result, Ok(true), "{case}");
        } else {
            assert_eq!(
                interpreter_error(result),
                InterpreterError::UnsatisfiedLockTime,
                "{case}"
            );
        }
    }

    let code = Code(vec![0x4f, 0xb1, 0x75, 0x51]); // -1 CLTV DROP TRUE
    let tx = transaction_with_program(&code);
    assert_eq!(
        interpreter_error(check(&tx, &[], &code, CONTEXT)),
        InterpreterError::NegativeLockTime
    );
}

#[test]
fn pq_script_recovery_branch_requires_its_key_and_absolute_locktime() {
    let owner = SigningKey::from_seed(&[3; crypto::SEED_BYTES]);
    let recovery = SigningKey::from_seed(&[4; crypto::SEED_BYTES]);
    let cosigner = SigningKey::from_seed(&[5; crypto::SEED_BYTES]);
    let mut bytes = vec![0x63]; // IF: owner and cosigner may spend before recovery.
    bytes.extend_from_slice(
        &threshold_program(2, &[owner.public_key(), cosigner.public_key()], false).0,
    );
    bytes.push(0x67); // ELSE
    bytes.extend_from_slice(&pushed(&[100]));
    bytes.extend_from_slice(&[0xb1, 0x75]); // 100 CLTV DROP
    bytes.extend_from_slice(&program(&recovery.public_key()).0);
    bytes.push(0x68); // ENDIF
    let code = Code(bytes);

    for lock_time in [99, 100] {
        let mut tx = transaction_with_program(&code);
        tx.lock_time = lock_time;
        // Sign each transaction separately so the earlier failure is the timelock,
        // rather than a stale signature for a different transaction locktime.
        let owner_signature = signature(&owner, &tx, sighash::SIGHASH_ALL);
        let cosigner_signature = signature(&cosigner, &tx, sighash::SIGHASH_ALL);
        let recovery_signature = signature(&recovery, &tx, sighash::SIGHASH_ALL);

        let mut input = slots(&[Some(&owner_signature), Some(&cosigner_signature)]);
        input.push(0x51);
        assert_eq!(check(&tx, &input, &code, CONTEXT), Ok(true));

        // The recovery key's signature in the owner's slot is a failed signature.
        let mut input = slots(&[Some(&recovery_signature), Some(&cosigner_signature)]);
        input.push(0x51);
        assert_eq!(check(&tx, &input, &code, CONTEXT), null_fail());

        for (argument, succeeds) in [(&owner_signature, false), (&recovery_signature, true)] {
            let mut input = pushed(argument);
            input.push(0);
            let result = check(&tx, &input, &code, CONTEXT);
            if lock_time < 100 {
                assert_eq!(
                    interpreter_error(result),
                    InterpreterError::UnsatisfiedLockTime
                );
            } else if succeeds {
                assert_eq!(result, Ok(true));
            } else {
                assert_eq!(result, null_fail());
            }
        }
    }
}

#[test]
fn pq_script_uses_existing_branches_and_absolute_locktime() {
    let key = SigningKey::from_seed(&[3; crypto::SEED_BYTES]);
    let public_key = key.public_key();
    let single = program(&public_key);
    let mut bytes = vec![0x63, 0x51, 0xb1, 0x75]; // IF 1 CLTV DROP
    bytes.extend_from_slice(&single.0);
    bytes.push(0x67); // ELSE
    bytes.extend_from_slice(&single.0);
    bytes.push(0x68); // ENDIF
    let code = Code(bytes);
    let mut tx = transaction(&public_key);
    tx.lock_time = 1;
    tx.transparent_bundle
        .as_mut()
        .unwrap()
        .authorization
        .input_scriptpubkeys[0] = Script(code.clone());
    let argument = signature(&key, &tx, sighash::SIGHASH_ALL);
    let mut input = pushed(&argument);
    input.push(0x51);
    assert_eq!(check(&tx, &input, &code, CONTEXT), Ok(true));
    *input.last_mut().unwrap() = 0;
    assert_eq!(check(&tx, &input, &code, CONTEXT), Ok(true));
    *input.last_mut().unwrap() = 0x51;
    tx.lock_time = 0;
    assert!(matches!(
        check(&tx, &input, &code, CONTEXT),
        Err(pq_script::Error::Script(script::Error::Interpreter(
            _,
            InterpreterError::UnsatisfiedLockTime
        )))
    ));
}

#[test]
fn pq_script_accepts_existing_signing_modes_without_an_all_only_rule() {
    let key = SigningKey::from_seed(&[3; crypto::SEED_BYTES]);
    let public_key = key.public_key();
    let tx = transaction(&public_key);
    let code = program(&public_key);
    for selector in [1, 2, 3, 0x81, 0x82, 0x83] {
        let input = pushed(&signature(&key, &tx, selector));
        assert_eq!(check(&tx, &input, &code, CONTEXT), Ok(true));
        let mut changed = transaction(&public_key);
        changed.transparent_bundle.as_mut().unwrap().vout[0] =
            TxOut::new(Zatoshis::const_from_u64(89), Script(Code(vec![0x51])));
        assert_eq!(
            check(&changed, &input, &code, CONTEXT),
            if selector & 0x1f == 2 { Ok(true) } else { null_fail() }
        );
        if selector & 0x1f == 3 {
            changed.transparent_bundle.as_mut().unwrap().vout.clear();
            assert_eq!(check(&changed, &input, &code, CONTEXT), null_fail());
        }
    }
}
