use crate::{address::Script, bundle::TxOut};
use core::cell::Cell;
use zcash_protocol::value::Zatoshis;
use zcash_script::{interpreter::Error as InterpreterError, script};

fn push(value: &[u8]) -> Vec<u8> {
    if value.is_empty() {
        return vec![0];
    }
    if let [value @ 1..=16] = value {
        return vec![0x50 + value];
    }
    if value == [0x81] {
        return vec![0x4f];
    }
    let mut bytes = if value.len() <= 75 {
        vec![u8::try_from(value.len()).unwrap()]
    } else {
        let mut p = vec![0x4d];
        p.extend(u16::try_from(value.len()).unwrap().to_le_bytes());
        p
    };
    bytes.extend(value);
    bytes
}
fn single(key: &[u8], opcode: u8) -> Code {
    let mut code = push(key);
    code.push(opcode);
    Code(code)
}
fn signature(key: &crypto::SigningKey) -> Vec<u8> {
    let mut sig = key.sign(&[42; 32], signing_context(PARAMETERS)).unwrap();
    sig.push(1);
    sig
}
fn run_with(
    output: &Code,
    arguments: &[u8],
    flags: Flags,
    lock_time: i64,
    is_final: bool,
) -> Result<bool, Error> {
    let callback = |script: &Code, _: &signature::HashType| {
        assert_eq!(script.0, output.0);
        Some([42; 32])
    };
    parse_output(output).unwrap().unwrap().verify_spend(
        arguments,
        flags,
        &CallbackTransactionSignatureChecker {
            sighash: &callback,
            lock_time,
            is_final,
        },
    )
}
fn run(output: &Code, arguments: &[u8]) -> Result<bool, Error> {
    run_with(
        output,
        arguments,
        Flags::MinimalData | Flags::NullDummy | Flags::CleanStack,
        0,
        false,
    )
}
fn interpreter_error(result: Result<bool, Error>) -> InterpreterError {
    match result {
        Err(Error::Execution(pq::Error::Script(script::Error::Interpreter(_, e)))) => e,
        other => panic!("expected interpreter rejection, received {other:?}"),
    }
}

#[test]
fn envelope_commits_one_version_and_preserves_complete_serialization() {
    let output = output_script(PARAMETERS, &Code(vec![0x51])).unwrap();
    assert_eq!(&output.0[..6], &[0x50, 3, b'S', b'L', b'H', 1]);
    assert_eq!(output.0[6], PARAMETERS.version());
    let parsed = parse_output(&output).unwrap().unwrap();
    assert_eq!(parsed.parameters(), PARAMETERS);
    assert_eq!(parsed.script_code().0, output.0);
    assert_eq!(run(&output, &[]), Ok(true));
    let previous = TxOut::new(Zatoshis::const_from_u64(100), Script(output.clone()));
    let mut bytes = Vec::new();
    previous.write(&mut bytes).unwrap();
    let decoded = TxOut::read(&mut bytes.as_slice()).unwrap();
    assert_eq!(previous.script_pubkey(), decoded.script_pubkey());
    assert!(previous.recipient_address().is_none());
    let checker = CallbackTransactionSignatureChecker {
        sighash: &|_, _| panic!("legacy execution requested a signature"),
        lock_time: 0,
        is_final: false,
    };
    assert!(matches!(
        script::Raw::from_raw_parts(vec![], output.0.clone()).eval(Flags::empty(), &checker),
        Err((
            _,
            script::Error::Interpreter(_, InterpreterError::BadOpcode)
        ))
    ));
    for version in [0, 3, 255] {
        let mut changed = output.clone();
        changed.0[6] = version;
        assert!(
            matches!(parse_output(&changed), Err(Error::UnsupportedVersion(v)) if v == version)
        );
    }
    for changed in [
        PREFIX.to_vec(),
        [PREFIX, &[1]].concat(),
        [PREFIX, &[0x4c, 1, 1, 0x51]].concat(),
    ] {
        assert!(matches!(parse_output(&Code(changed)), Err(Error::Envelope)));
    }
    assert!(parse_output(&Code(vec![0x51])).unwrap().is_none());
    assert!(
        output_script(
            PARAMETERS,
            &Code(vec![0; pq::MAX_SCRIPT_BYTES - HEADER_BYTES])
        )
        .is_ok()
    );
    assert!(
        output_script(
            PARAMETERS,
            &Code(vec![0; pq::MAX_SCRIPT_BYTES - HEADER_BYTES + 1])
        )
        .is_err()
    );
    let mut oversized = output;
    oversized.0.resize(pq::MAX_SCRIPT_BYTES + 1, 0);
    assert!(parse_output(&oversized).is_err());
}

#[test]
fn signature_checks_preserve_false_abort_verify_and_context_rules() {
    let key = crypto::SigningKey::from_seed(&[1; crypto::SEED_BYTES]);
    let output = output_script(PARAMETERS, &single(&key.public_key(), 0xba)).unwrap();
    let sig = signature(&key);
    assert_eq!(run(&output, &push(&sig)), Ok(true));
    assert_eq!(run(&output, &[0]), Ok(false));
    let mut incorrect = sig.clone();
    incorrect[0] ^= 1;
    assert_eq!(run(&output, &push(&incorrect)), Ok(false));
    let mut wrong_context = key.sign(&[42; 32], b"different protocol").unwrap();
    wrong_context.push(1);
    assert_eq!(run(&output, &push(&wrong_context)), Ok(false));
    for length in [
        0,
        crypto::PUBLIC_KEY_BYTES - 1,
        crypto::PUBLIC_KEY_BYTES + 1,
    ] {
        let bad = output_script(PARAMETERS, &single(&vec![0; length], 0xba)).unwrap();
        assert_eq!(
            interpreter_error(run(&bad, &[0])),
            InterpreterError::PubKeyType
        );
    }
    for short in [&sig[..1], &sig[..crypto::SIGNATURE_BYTES]] {
        assert_eq!(
            interpreter_error(run(&output, &push(short))),
            InterpreterError::PqSignatureSize
        );
    }
    let mut extended = sig.clone();
    extended.push(0);
    assert!(run(&output, &push(&extended)).is_err());
    let mut selector = sig;
    *selector.last_mut().unwrap() = 4;
    assert!(run(&output, &push(&selector)).is_err());
    let mut body = single(&key.public_key(), 0xbb);
    body.0.push(0x51);
    let verify = output_script(PARAMETERS, &body).unwrap();
    assert_eq!(run(&verify, &push(&signature(&key))), Ok(true));
    assert_eq!(
        interpreter_error(run(&verify, &[0])),
        InterpreterError::Verify
    );
    let mut body = single(&key.public_key(), 0xba);
    body.0.push(0x91);
    assert_eq!(
        run(&output_script(PARAMETERS, &body).unwrap(), &[0]),
        Ok(true)
    );
    let mut changed = output;
    changed.0[6] = if PARAMETERS.version() == 1 { 2 } else { 1 };
    assert_eq!(
        interpreter_error(run(&changed, &[0])),
        InterpreterError::PubKeyType
    );
}

#[test]
fn distinct_multisig_pairs_order_dummy_and_verify_share_matching() {
    let keys = [1, 2, 3].map(|seed| crypto::SigningKey::from_seed(&[seed; crypto::SEED_BYTES]));
    let mut body = vec![0x52];
    for key in &keys {
        body.extend(push(&key.public_key()));
    }
    body.extend([0x53, 0xbc]);
    let output = output_script(PARAMETERS, &Code(body.clone())).unwrap();
    let signatures = keys.each_ref().map(signature);
    let arguments = |a: usize, b: usize| {
        let mut input = vec![0];
        input.extend(push(&signatures[a]));
        input.extend(push(&signatures[b]));
        input
    };
    for (a, b) in [(0, 1), (0, 2), (1, 2)] {
        assert_eq!(run(&output, &arguments(a, b)), Ok(true));
    }
    assert_eq!(run(&output, &arguments(2, 0)), Ok(false));
    let mut corrupt = arguments(0, 2);
    corrupt[4] ^= 1;
    assert_eq!(run(&output, &corrupt), Ok(false));
    let mut nonzero = vec![0x51];
    nonzero.extend(&arguments(0, 2)[1..]);
    assert_eq!(
        interpreter_error(run(&output, &nonzero)),
        InterpreterError::SigNullDummy
    );
    assert_eq!(
        run_with(&output, &nonzero, Flags::empty(), 0, false),
        Ok(true)
    );
    *body.last_mut().unwrap() = 0xbd;
    body.push(0x51);
    let verified = output_script(PARAMETERS, &Code(body)).unwrap();
    assert_eq!(run(&verified, &arguments(0, 2)), Ok(true));
    assert_eq!(
        interpreter_error(run(&verified, &arguments(2, 0))),
        InterpreterError::Verify
    );
    assert_eq!(
        parse_output(&output).unwrap().unwrap().sig_op_count(true),
        3
    );
    assert_eq!(
        parse_output(&output).unwrap().unwrap().sig_op_count(false),
        20
    );
}

#[test]
fn absolute_timelocks_and_branches_preserve_spending_conditions() {
    let key = crypto::SigningKey::from_seed(&[4; crypto::SEED_BYTES]);
    let sig = signature(&key);
    for deadline in [100i64, 500_000_001] {
        let mut body = vec![0x63]; // IF: normal signature path.
        body.extend(single(&key.public_key(), 0xba).0);
        body.push(0x67); // ELSE: absolute-time recovery with the same fixture key.
        body.extend(push(&zcash_script::num::serialize(deadline)));
        body.extend([0xb1, 0x75]);
        body.extend(single(&key.public_key(), 0xba).0);
        body.push(0x68);
        let output = output_script(PARAMETERS, &Code(body)).unwrap();
        let mut normal = push(&sig);
        normal.push(0x51);
        assert_eq!(run(&output, &normal), Ok(true));
        let mut recovery = push(&sig);
        recovery.push(0);
        for lock_time in [deadline - 1, deadline, deadline + 1] {
            let result = run_with(&output, &recovery, Flags::MinimalData, lock_time, false);
            if lock_time < deadline {
                assert_eq!(
                    interpreter_error(result),
                    InterpreterError::UnsatisfiedLockTime
                );
            } else {
                assert_eq!(result, Ok(true));
            }
        }
        assert_eq!(
            interpreter_error(run_with(&output, &recovery, Flags::empty(), deadline, true)),
            InterpreterError::UnsatisfiedLockTime
        );
        let wrong_type = if deadline < 500_000_000 {
            500_000_001
        } else {
            100
        };
        assert_eq!(
            interpreter_error(run_with(
                &output,
                &recovery,
                Flags::empty(),
                wrong_type,
                false
            )),
            InterpreterError::UnsatisfiedLockTime
        );
    }
}

#[test]
fn twenty_signature_capacity_and_key_count_boundaries() {
    let key = crypto::SigningKey::from_seed(&[5; crypto::SEED_BYTES]);
    let sig = signature(&key);
    let mut body = vec![1, 20]; // Numeric twenty has no dedicated small-integer opcode.
    let mut input = vec![0];
    for _ in 0..20 {
        body.extend(push(&key.public_key()));
        input.extend(push(&sig));
    }
    body.extend([1, 20, 0xbc]);
    let output = output_script(PARAMETERS, &Code(body)).unwrap();
    assert_eq!(run(&output, &input), Ok(true));
    assert!(input.len() <= pq::MAX_INPUT_BYTES);
    let mut body = vec![0];
    for _ in 0..21 {
        body.extend(push(&key.public_key()));
    }
    body.extend([1, 21, 0xbc]);
    let output = output_script(PARAMETERS, &Code(body)).unwrap();
    let checker = CallbackTransactionSignatureChecker {
        sighash: &|_, _| panic!("too many keys reached digest"),
        lock_time: 0,
        is_final: false,
    };
    assert_eq!(
        interpreter_error(parse_output(&output).unwrap().unwrap().verify_spend(
            &[0],
            Flags::empty(),
            &checker
        )),
        InterpreterError::PubKeyCount(None)
    );
}

#[test]
fn failed_multisig_matches_are_charged_before_more_work() {
    for groups in [9, 10] {
        let mut body = Vec::new();
        let mut input = Vec::new();
        let mut sig = vec![0; crypto::SIGNATURE_BYTES];
        sig.push(1);
        for _ in 0..groups {
            input.push(0);
            input.extend(push(&sig));
            body.push(0x51);
            for _ in 0..20 {
                body.extend(push(&vec![0; crypto::PUBLIC_KEY_BYTES]));
            }
            body.extend([1, 20, 0xbc, 0x75]);
        }
        body.push(0x51);
        let output = output_script(PARAMETERS, &Code(body)).unwrap();
        let calls = Cell::new(0);
        let callback = |code: &Code, _: &signature::HashType| {
            assert_eq!(code.0, output.0);
            calls.set(calls.get() + 1);
            None
        };
        let checker = CallbackTransactionSignatureChecker {
            sighash: &callback,
            lock_time: 0,
            is_final: false,
        };
        let result =
            parse_output(&output)
                .unwrap()
                .unwrap()
                .verify_spend(&input, Flags::empty(), &checker);
        if groups == 9 {
            assert_eq!(result, Ok(true));
        } else {
            assert_eq!(interpreter_error(result), InterpreterError::OpCount);
        }
        assert_eq!(calls.get(), 180);
    }
}

#[test]
fn ordinary_ecdsa_and_pq_checks_keep_separate_signature_rules() {
    let legacy = secp256k1::SecretKey::from_secret_bytes([9; 32]).unwrap();
    let public = secp256k1::PublicKey::from_secret_key(&legacy).serialize();
    let mut legacy_signature =
        secp256k1::ecdsa::sign(secp256k1::Message::from_digest([42; 32]), &legacy)
            .serialize_der()
            .to_vec();
    legacy_signature.push(1);
    let key = crypto::SigningKey::from_seed(&[6; crypto::SEED_BYTES]);
    let pq_signature = signature(&key);
    let mut body = single(&public, 0xad).0;
    body.extend(single(&key.public_key(), 0xba).0);
    let output = output_script(PARAMETERS, &Code(body)).unwrap();
    let mut input = push(&pq_signature);
    input.extend(push(&legacy_signature));
    assert_eq!(run(&output, &input), Ok(true));
    assert_eq!(
        parse_output(&output).unwrap().unwrap().sig_op_count(true),
        2
    );
    let mut wrong = legacy_signature;
    wrong[10] ^= 1;
    let mut input = push(&pq_signature);
    input.extend(push(&wrong));
    assert!(run(&output, &input) != Ok(true));
    let legacy_only = output_script(PARAMETERS, &single(&key.public_key(), 0xac)).unwrap();
    assert!(run(&legacy_only, &push(&pq_signature)) != Ok(true));
}
