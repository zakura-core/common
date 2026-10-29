//! Library integration only: the supplied program is authenticated by this fixture.
//! These are not activated PQ outputs or transactions accepted by a node.

use alloc::vec::Vec;

use super::{TestTransparentAuth, TestUnauthorized};
use crate::transaction::{
    TransactionData, TxVersion,
    sighash::{SignableInput, signature_hash},
    txid::TxIdDigester,
};
use transparent::{
    address::Script,
    bundle::{Bundle, OutPoint, TxIn, TxOut},
    pq::{self, SigningKey},
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
        previous,
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
    pq::script::verify_script(input, code, context, &checker)
}

fn signature(key: &SigningKey, tx: &TransactionData<TestUnauthorized>, selector: u8) -> Vec<u8> {
    let mut signature = key.sign(&digest(tx, selector).unwrap(), CONTEXT).unwrap();
    signature.push(selector);
    signature
}

fn multisig_program(required: u8, keys: &[[u8; pq::PUBLIC_KEY_BYTES]], verify: bool) -> Code {
    assert!((1..=16).contains(&required));
    assert!((usize::from(required)..=16).contains(&keys.len()));
    let mut bytes = vec![0x50 + required];
    for key in keys {
        bytes.push(u8::try_from(key.len()).unwrap());
        bytes.extend_from_slice(key);
    }
    bytes.push(0x50 + u8::try_from(keys.len()).unwrap());
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
    let key = SigningKey::from_seed(&[3; pq::SEED_BYTES]);
    let public_key = key.public_key();
    let mut tx = transaction(&public_key);
    let code = program(&public_key);
    let argument = signature(&key, &tx, sighash::SIGHASH_ALL);
    let input = pushed(&argument);
    assert_eq!(input.len(), 16_228);

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
    let other_key = SigningKey::from_seed(&[4; pq::SEED_BYTES]).public_key();
    assert_eq!(check(&tx, &input, &program(&other_key), CONTEXT), Ok(false));

    for position in [0, 24, pq::SIGNATURE_BYTES - 1] {
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
fn pq_script_preserves_false_and_abort_and_bounds_verification_attempts() {
    let key = SigningKey::from_seed(&[3; pq::SEED_BYTES]);
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
    for public_key in [&[0; 47][..], &[0; 49][..]] {
        let mut bad_program = program(public_key);
        bad_program.0.push(0x91);
        assert!(matches!(
            check(&tx, &[0], &bad_program, CONTEXT),
            Err(pq_script::Error::Script(script::Error::Interpreter(
                _,
                InterpreterError::PubKeyType
            )))
        ));
    }
    for short in [&argument[..1], &argument[..pq::SIGNATURE_BYTES]] {
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
    assert_eq!(
        check(&tx, &pushed(&extended), &code, CONTEXT),
        Err(pq_script::Error::PushSize)
    );
    let mut bad_selector = argument.clone();
    *bad_selector.last_mut().unwrap() = 0x04;
    assert!(check(&tx, &pushed(&bad_selector), &code, CONTEXT).is_err());
    *bad_selector.last_mut().unwrap() = sighash::SIGHASH_NONE;
    assert_eq!(
        check(&tx, &pushed(&bad_selector), &code, CONTEXT),
        Ok(false)
    );

    // A failed first check must consume the same budget as a successful check.
    let mut repeated = vec![0x76]; // DUP the signature
    repeated.extend_from_slice(&code.0);
    repeated.push(0x75); // DROP first result
    repeated.extend_from_slice(&code.0);
    for context in [CONTEXT, b"wrong context".as_slice()] {
        assert!(matches!(
            check(&tx, &pushed(&argument), &Code(repeated.clone()), context),
            Err(pq_script::Error::Script(script::Error::Interpreter(
                _,
                InterpreterError::PqSignatureBudget
            )))
        ));
    }

    // CHECKMULTISIG searches keys from the top of the stack. A failed first key
    // match must not allow another verification outside the same attempt budget.
    let mut multisig = vec![0x51];
    multisig.extend_from_slice(&code.0[..code.0.len() - 1]);
    let mut wrong_key = key.public_key();
    wrong_key[0] ^= 1;
    let wrong_key_push = program(&wrong_key);
    multisig.extend_from_slice(&wrong_key_push.0[..wrong_key_push.0.len() - 1]);
    multisig.extend_from_slice(&[0x52, 0xae]);
    let mut input = vec![0]; // CHECKMULTISIG's extra consumed stack item.
    input.extend_from_slice(&pushed(&argument));
    assert!(matches!(
        check(&tx, &input, &Code(multisig), CONTEXT),
        Err(pq_script::Error::Script(script::Error::Interpreter(
            _,
            InterpreterError::PqSignatureBudget
        )))
    ));
}

#[test]
fn pq_script_multisig_one_of_one_checks_signatures_and_consumes_dummy() {
    let key = SigningKey::from_seed(&[3; pq::SEED_BYTES]);
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
fn pq_script_multisig_one_of_two_obeys_key_order_and_attempt_limit() {
    let alice = SigningKey::from_seed(&[3; pq::SEED_BYTES]);
    let bob = SigningKey::from_seed(&[4; pq::SEED_BYTES]);
    let code = multisig_program(1, &[alice.public_key(), bob.public_key()], false);
    let tx = transaction_with_program(&code);

    // Keys are searched from the top of the stack, so Bob matches on the first attempt.
    let mut input = vec![0];
    input.extend_from_slice(&pushed(&signature(&bob, &tx, sighash::SIGHASH_ALL)));
    assert_eq!(check(&tx, &input, &code, CONTEXT), Ok(true));

    // Alice is a permitted signer, but reaching her key needs a second attempt.
    let mut input = vec![0];
    input.extend_from_slice(&pushed(&signature(&alice, &tx, sighash::SIGHASH_ALL)));
    assert_eq!(
        interpreter_error(check(&tx, &input, &code, CONTEXT)),
        InterpreterError::PqSignatureBudget
    );
}

#[test]
fn pq_script_multisig_two_of_three_exceeds_current_attempt_limit() {
    let alice = SigningKey::from_seed(&[3; pq::SEED_BYTES]);
    let bob = SigningKey::from_seed(&[4; pq::SEED_BYTES]);
    let carol = SigningKey::from_seed(&[5; pq::SEED_BYTES]);
    let code = multisig_program(
        2,
        &[alice.public_key(), bob.public_key(), carol.public_key()],
        false,
    );
    let tx = transaction_with_program(&code);
    let mut input = vec![0];
    // Both signatures are valid, in matching key order, and fit the input-size limit.
    for key in [&bob, &carol] {
        let argument = signature(key, &tx, sighash::SIGHASH_ALL);
        assert!(
            pq::verify(
                &key.public_key(),
                &digest(&tx, sighash::SIGHASH_ALL).unwrap(),
                CONTEXT,
                &argument[..pq::SIGNATURE_BYTES],
            )
            .is_ok()
        );
        input.extend_from_slice(&pushed(&argument));
    }
    assert!(input.len() <= pq_script::MAX_INPUT_BYTES);
    assert_eq!(
        interpreter_error(check(&tx, &input, &code, CONTEXT)),
        InterpreterError::PqSignatureBudget
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
    let owner = SigningKey::from_seed(&[3; pq::SEED_BYTES]);
    let recovery = SigningKey::from_seed(&[4; pq::SEED_BYTES]);
    let mut bytes = vec![0x63]; // IF: owner may spend without the recovery timelock.
    bytes.extend_from_slice(&program(&owner.public_key()).0);
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
        let recovery_signature = signature(&recovery, &tx, sighash::SIGHASH_ALL);

        let mut input = pushed(&owner_signature);
        input.push(0x51);
        assert_eq!(check(&tx, &input, &code, CONTEXT), Ok(true));

        let mut input = pushed(&recovery_signature);
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
    let key = SigningKey::from_seed(&[3; pq::SEED_BYTES]);
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
    let key = SigningKey::from_seed(&[3; pq::SEED_BYTES]);
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
