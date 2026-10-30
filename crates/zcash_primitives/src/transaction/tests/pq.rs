// Library integration for supplied programs and authenticated P2SH redeem scripts.
// These tests do not activate PQ validation or establish node acceptance.

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

fn pushed(value: &[u8]) -> Vec<u8> {
    let mut input = vec![0x4d]; // PUSHDATA2 uses a fixed-width unsigned length.
    input.extend_from_slice(&u16::try_from(value.len()).unwrap().to_le_bytes());
    input.extend_from_slice(value);
    input
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

mod p2sh_spends {
    use super::*;
    use transparent::{address::TransparentAddress, bundle::Authorized, pq::p2sh, util::hash160};

    fn transaction(redeem: &Code) -> TransactionData<TestUnauthorized> {
        let output = TxOut::new(
            Zatoshis::const_from_u64(100),
            TransparentAddress::ScriptHash(hash160::hash(&redeem.0))
                .script()
                .into(),
        );
        let mut wire = Vec::new();
        output.write(&mut wire).unwrap();
        let decoded = TxOut::read(&mut &wire[..]).unwrap();
        assert_eq!(decoded, output);
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
        redeem: &Code,
        selector: u8,
        context: &[u8],
    ) -> Vec<u8> {
        let mut signature = key
            .sign(
                &digest_with_script(tx, selector, &Script(redeem.clone())).unwrap(),
                context,
            )
            .unwrap();
        signature.push(selector);
        let mut input = pushed(&signature);
        input.extend_from_slice(&pushed(&redeem.0));
        input
    }

    fn check(tx: &TransactionData<TestUnauthorized>, redeem: &Code) -> Result<bool, p2sh::Error> {
        let bundle = tx.transparent_bundle().unwrap();
        let spend = script::Raw::from_raw_parts(
            bundle.vin[0].script_sig().0.0.clone(),
            bundle.authorization.input_scriptpubkeys[0].0.0.clone(),
        );
        let sighash = |script_code: &Code, hash_type: &HashType| {
            // The execution header is authenticated even though only the body executes.
            assert_eq!(script_code.0, redeem.0);
            digest_with_script(tx, hash_type.raw_bits() as u8, &Script(script_code.clone()))
        };
        p2sh::verify_spend(
            &spend,
            Flags::P2SH | Flags::CHECKLOCKTIMEVERIFY,
            &CallbackTransactionSignatureChecker {
                sighash: &sighash,
                lock_time: i64::from(tx.lock_time()),
                is_final: bundle.vin[0].sequence() == u32::MAX,
            },
        )
    }

    #[test]
    fn serialized_p2sh_multisig_authenticates_distinct_signers_and_order() {
        let keys: Vec<_> = (3..=5)
            .map(|seed| SigningKey::from_seed(&[seed; crypto::SEED_BYTES]))
            .collect();
        let body = multisig_program(
            2,
            &keys.iter().map(SigningKey::public_key).collect::<Vec<_>>(),
            false,
        );
        let redeem = p2sh::redeem_script(PARAMETERS, &body).unwrap();
        let mut tx = transaction(&redeem);
        let arguments: Vec<_> = keys
            .iter()
            .map(|key| {
                let mut input = signed_input(
                    key,
                    &tx,
                    &redeem,
                    sighash::SIGHASH_ALL,
                    p2sh::signing_context(PARAMETERS),
                );
                input.truncate(input.len() - pushed(&redeem.0).len());
                input
            })
            .collect();
        for pair in [[0, 1], [0, 2], [1, 2], [2, 0]] {
            let input = [
                vec![0],
                arguments[pair[0]].clone(),
                arguments[pair[1]].clone(),
                pushed(&redeem.0),
            ]
            .concat();
            install_input(&mut tx, &input);
            assert_eq!(
                check(&tx, &redeem),
                Ok(pair != [2, 0]),
                "signer order {pair:?}"
            );
        }
        let mut forged = arguments[0].clone();
        forged[3] ^= 1; // Alter signature payload after its PUSHDATA2 prefix.
        let input = [vec![0], forged, arguments[2].clone(), pushed(&redeem.0)].concat();
        install_input(&mut tx, &input);
        assert_eq!(check(&tx, &redeem), Ok(false));
    }

    #[test]
    fn serialized_p2sh_spend_authenticates_script_and_v5_transaction() {
        let key = SigningKey::from_seed(&[3; crypto::SEED_BYTES]);
        let body = program(&key.public_key());
        let redeem = p2sh::redeem_script(PARAMETERS, &body).unwrap();
        let mut tx = transaction(&redeem);
        let input = signed_input(
            &key,
            &tx,
            &redeem,
            sighash::SIGHASH_ALL,
            p2sh::signing_context(PARAMETERS),
        );
        install_input(&mut tx, &input);
        assert_eq!(check(&tx, &redeem), Ok(true));

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
            let mut changed = transaction(&redeem);
            mutate(&mut changed);
            install_input(&mut changed, &input);
            assert_eq!(check(&changed, &redeem), Ok(false));
        }

        let mut forged = input.clone();
        forged[3] ^= 1;
        install_input(&mut tx, &forged);
        assert_eq!(check(&tx, &redeem), Ok(false));

        // Equivalent execution with different bytes still needs a different output/signature.
        let mut changed_body = vec![0x61]; // NOP
        changed_body.extend_from_slice(&body.0);
        let changed_redeem =
            p2sh::redeem_script(PARAMETERS, &Code(changed_body)).unwrap();
        let mut substituted = input[..input.len() - pushed(&redeem.0).len()].to_vec();
        substituted.extend_from_slice(&pushed(&changed_redeem.0));
        install_input(&mut tx, &substituted);
        assert_eq!(
            check(&tx, &changed_redeem),
            Err(p2sh::Error::CommitmentMismatch)
        );
        let mut changed_tx = transaction(&changed_redeem);
        install_input(&mut changed_tx, &substituted);
        assert_eq!(check(&changed_tx, &changed_redeem), Ok(false));

        let wrong_context = signed_input(&key, &tx, &redeem, sighash::SIGHASH_ALL, CONTEXT);
        install_input(&mut tx, &wrong_context);
        assert_eq!(check(&tx, &redeem), Ok(false));
    }

    #[test]
    fn p2sh_retains_six_signing_modes_and_absolute_locktime() {
        let key = SigningKey::from_seed(&[3; crypto::SEED_BYTES]);
        let mut body = vec![0x01, 100, 0xb1, 0x75]; // 100 CLTV DROP
        body.extend_from_slice(&program(&key.public_key()).0);
        let redeem = p2sh::redeem_script(PARAMETERS, &Code(body)).unwrap();
        for selector in [1, 2, 3, 0x81, 0x82, 0x83] {
            let mut tx = transaction(&redeem);
            tx.lock_time = 100;
            let input = signed_input(
                &key,
                &tx,
                &redeem,
                selector,
                p2sh::signing_context(PARAMETERS),
            );
            install_input(&mut tx, &input);
            assert_eq!(check(&tx, &redeem), Ok(true));
            tx.transparent_bundle.as_mut().unwrap().vout[0] =
                TxOut::new(Zatoshis::const_from_u64(89), Script(Code(vec![0x51])));
            assert_eq!(
                check(&tx, &redeem),
                Ok(selector & sighash::SIGHASH_MASK == sighash::SIGHASH_NONE)
            );
            if selector & sighash::SIGHASH_MASK == sighash::SIGHASH_SINGLE {
                tx.transparent_bundle.as_mut().unwrap().vout.clear();
                assert_eq!(check(&tx, &redeem), Ok(false));
            }
            tx.lock_time = 99;
            assert!(matches!(
                check(&tx, &redeem),
                Err(p2sh::Error::Pq(pq_script::Error::Script(
                    script::Error::Interpreter(_, InterpreterError::UnsatisfiedLockTime)
                )))
            ));
            tx.lock_time = 100;
            tx.transparent_bundle.as_mut().unwrap().vin[0] =
                TxIn::from_parts(OutPoint::new([7; 32], 0), Script(Code(input)), u32::MAX);
            assert!(matches!(
                check(&tx, &redeem),
                Err(p2sh::Error::Pq(pq_script::Error::Script(
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
    pq::script::verify_script(PARAMETERS, input, code, context, &checker)
}

fn signature(key: &SigningKey, tx: &TransactionData<TestUnauthorized>, selector: u8) -> Vec<u8> {
    let mut signature = key.sign(&digest(tx, selector).unwrap(), CONTEXT).unwrap();
    signature.push(selector);
    signature
}

fn multisig_program(
    required: u8,
    keys: &[[u8; crypto::PUBLIC_KEY_BYTES]],
    verify: bool,
) -> Code {
    assert!((1..=20).contains(&required));
    assert!((usize::from(required)..=20).contains(&keys.len()));
    let mut bytes = pushed(&zcash_script::num::serialize(i64::from(required)));
    for key in keys {
        bytes.push(u8::try_from(key.len()).unwrap());
        bytes.extend_from_slice(key);
    }
    bytes.extend(pushed(&zcash_script::num::serialize(
        i64::try_from(keys.len()).unwrap(),
    )));
    bytes.push(if verify { 0xaf } else { 0xae }); // CHECKMULTISIG[VERIFY]
    Code(bytes)
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

    assert_eq!(check(&tx, &input, &code, b"different context"), Ok(false));
    assert_eq!(
        check(&tx, &input, &code, &[0; 256]),
        Err(pq_script::Error::ContextSize)
    );
    let other_key = SigningKey::from_seed(&[4; crypto::SEED_BYTES]).public_key();
    assert_eq!(check(&tx, &input, &program(&other_key), CONTEXT), Ok(false));

    for position in [0, 24, crypto::SIGNATURE_BYTES - 1] {
        let mut altered = argument.clone();
        altered[position] ^= 1;
        assert_eq!(check(&tx, &pushed(&altered), &code, CONTEXT), Ok(false));
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
        assert_eq!(check(&changed, &input, &code, CONTEXT), Ok(false));
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
    for short in [&argument[..1], &argument[..crypto::SIGNATURE_BYTES]] {
        assert!(matches!(
            check(&tx, &pushed(short), &code, CONTEXT),
            Err(pq_script::Error::Script(script::Error::Interpreter(
                _,
                InterpreterError::PqSignatureSize
            )))
        ));
    }
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
        Ok(false)
    );
}

#[test]
fn pq_script_multisig_one_of_one_checks_signatures_and_consumes_dummy() {
    let key = SigningKey::from_seed(&[3; crypto::SEED_BYTES]);
    for verify in [false, true] {
        let mut code = multisig_program(1, &[key.public_key()], verify);
        if verify {
            // DEPTH 0 EQUAL: VERIFY must consume everything, including the dummy.
            code.0.extend_from_slice(&[0x74, 0x00, 0x87]);
        } else {
            // DEPTH 1 EQUALVERIFY: only the signature-check result may remain.
            code.0.extend_from_slice(&[0x74, 0x51, 0x88]);
        }
        let tx = transaction_with_program(&code);
        let argument = signature(&key, &tx, sighash::SIGHASH_ALL);
        let mut input = vec![0];
        input.extend_from_slice(&pushed(&argument));
        assert_eq!(check(&tx, &input, &code, CONTEXT), Ok(true));

        // No NULLDUMMY policy flag is enabled: a nonempty dummy is consumed too.
        input[0] = 0x51;
        assert_eq!(check(&tx, &input, &code, CONTEXT), Ok(true));
        assert!(matches!(
            interpreter_error(check(&tx, &pushed(&argument), &code, CONTEXT)),
            InterpreterError::InvalidStackOperation(_)
        ));

        let mut altered = argument;
        altered[0] ^= 1;
        let mut forged = vec![0];
        forged.extend_from_slice(&pushed(&altered));
        for invalid_input in [&forged[..], &[0, 0][..]] {
            let result = check(&tx, invalid_input, &code, CONTEXT);
            if verify {
                assert_eq!(interpreter_error(result), InterpreterError::Verify);
            } else {
                assert_eq!(result, Ok(false));
            }
        }
    }
}

#[test]
fn pq_script_multisig_one_of_two_searches_past_failed_matches() {
    let alice = SigningKey::from_seed(&[3; crypto::SEED_BYTES]);
    let bob = SigningKey::from_seed(&[4; crypto::SEED_BYTES]);
    let code = multisig_program(1, &[alice.public_key(), bob.public_key()], false);
    let tx = transaction_with_program(&code);

    // Keys are searched from the top of the stack, so Bob matches on the first attempt.
    let mut input = vec![0];
    input.extend_from_slice(&pushed(&signature(&bob, &tx, sighash::SIGHASH_ALL)));
    assert_eq!(check(&tx, &input, &code, CONTEXT), Ok(true));

    // Reaching Alice requires a failed match against Bob first.
    let mut input = vec![0];
    input.extend_from_slice(&pushed(&signature(&alice, &tx, sighash::SIGHASH_ALL)));
    assert_eq!(check(&tx, &input, &code, CONTEXT), Ok(true));
}

#[test]
fn pq_script_multisig_two_of_three_accepts_each_pair_and_rejects_wrong_order() {
    let keys: Vec<_> = (3..=5)
        .map(|seed| SigningKey::from_seed(&[seed; crypto::SEED_BYTES]))
        .collect();
    for verify in [false, true] {
        let mut code = multisig_program(
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
            let input = [
                vec![0],
                pushed(&arguments[pair[0]]),
                pushed(&arguments[pair[1]]),
            ]
            .concat();
            assert_eq!(
                check(&tx, &input, &code, CONTEXT),
                Ok(true),
                "pair {pair:?}"
            );
        }
        let reversed = [vec![0], pushed(&arguments[2]), pushed(&arguments[0])].concat();
        let forged = [
            vec![0],
            pushed(&vec![0; crypto::SIGNATURE_BYTES + 1]),
            pushed(&arguments[2]),
        ]
        .concat();
        // Use a valid selector for the cryptographically invalid signature.
        let mut forged = forged;
        forged[3 + crypto::SIGNATURE_BYTES + 1] = sighash::SIGHASH_ALL;
        for input in [reversed, forged] {
            let result = check(&tx, &input, &code, CONTEXT);
            if verify {
                assert_eq!(interpreter_error(result), InterpreterError::Verify);
            } else {
                assert_eq!(result, Ok(false));
            }
        }
        assert!(
            check(&tx, &[0, 0], &code, CONTEXT).is_err(),
            "insufficient stack arguments abort"
        );
    }
}

#[test]
fn pq_script_large_multisig_and_multiple_checks_fit_bounded_resources() {
    let key = SigningKey::from_seed(&[3; crypto::SEED_BYTES]);
    // Duplicate keys remain legal, as in legacy Script. This fixture measures
    // signature transport and twenty verifications, not distinct ownership.
    let code = multisig_program(20, &[key.public_key(); 20], false);
    let tx = transaction_with_program(&code);
    let argument = signature(&key, &tx, sighash::SIGHASH_ALL);
    let mut input = vec![0];
    for _ in 0..20 {
        input.extend(pushed(&argument));
    }
    let start = std::time::Instant::now();
    assert_eq!(check(&tx, &input, &code, CONTEXT), Ok(true));
    std::eprintln!(
        "20-of-20: input={} bytes, initial signature payload={} bytes, verification={:?}",
        input.len(),
        20 * argument.len(),
        start.elapsed()
    );

    // Nineteen failed matches before reaching the sole matching key.
    let mut wrong = key.public_key();
    wrong[0] ^= 1;
    let mut public_keys = vec![key.public_key()];
    public_keys.extend([wrong; 19]);
    let code = multisig_program(1, &public_keys, false);
    let tx = transaction_with_program(&code);
    let input = [vec![0], pushed(&signature(&key, &tx, sighash::SIGHASH_ALL))].concat();
    let start = std::time::Instant::now();
    assert_eq!(check(&tx, &input, &code, CONTEXT), Ok(true));
    std::eprintln!(
        "1-of-20 with nineteen missed matches: {:?}",
        start.elapsed()
    );

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
        &multisig_program(2, &[owner.public_key(), cosigner.public_key()], false).0,
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

        let mut input = [
            vec![0],
            pushed(&owner_signature),
            pushed(&cosigner_signature),
        ]
        .concat();
        input.push(0x51);
        assert_eq!(check(&tx, &input, &code, CONTEXT), Ok(true));

        let mut input = [
            vec![0],
            pushed(&recovery_signature),
            pushed(&cosigner_signature),
        ]
        .concat();
        input.push(0x51);
        assert_eq!(check(&tx, &input, &code, CONTEXT), Ok(false));

        for (argument, succeeds) in [(&owner_signature, false), (&recovery_signature, true)] {
            let mut input = pushed(argument);
            input.push(0);
            let result = check(&tx, &input, &code, CONTEXT);
            if lock_time < 100 {
                assert_eq!(
                    interpreter_error(result),
                    InterpreterError::UnsatisfiedLockTime
                );
            } else {
                assert_eq!(result, Ok(succeeds));
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
            Ok(selector & 0x1f == 2)
        );
        if selector & 0x1f == 3 {
            changed.transparent_bundle.as_mut().unwrap().vout.clear();
            assert_eq!(check(&changed, &input, &code, CONTEXT), Ok(false));
        }
    }
}
