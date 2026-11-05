use crate::{
    address::{Script, TransparentAddress},
    bundle::TxOut,
};
use zcash_protocol::value::Zatoshis;
use zcash_script::interpreter::Error as InterpreterError;

fn flags() -> Flags {
    Flags::P2SH | Flags::CHECKLOCKTIMEVERIFY
}

fn push(value: &[u8]) -> Vec<u8> {
    let mut bytes = vec![0x4d];
    bytes.extend_from_slice(&u16::try_from(value.len()).unwrap().to_le_bytes());
    bytes.extend_from_slice(value);
    bytes
}

fn output(redeem: &[u8]) -> Script {
    TransparentAddress::ScriptHash(hash160::hash(redeem))
        .script()
        .into()
}

fn raw(arguments: &[u8], redeem: &[u8]) -> script::Raw {
    let mut input = arguments.to_vec();
    input.extend_from_slice(&push(redeem));
    script::Raw::from_raw_parts(input, output(redeem).0.0)
}

fn no_digest(_: &Code, _: &zcash_script::signature::HashType) -> Option<[u8; 32]> {
    panic!("this input must not request a signature digest")
}

fn checker() -> CallbackTransactionSignatureChecker<'static> {
    CallbackTransactionSignatureChecker {
        sighash: &no_digest,
        lock_time: 0,
        is_final: false,
    }
}

fn check(spend: &script::Raw) -> Result<bool, Error> {
    verify_spend(spend, flags(), &checker())
}

fn legacy(spend: &script::Raw, flags: Flags) -> Result<bool, Error> {
    spend
        .eval(flags, &checker())
        .map_err(|(part, error)| Error::Legacy(part, error))
}

#[test]
fn ordinary_p2sh_output_commits_header_and_exact_body() {
    let redeem = redeem_script(PARAMETERS, &Code(vec![0x51])).unwrap();
    assert_eq!(hex::encode(&redeem.0), if PARAMETERS == ParameterSet::Sha2_128f { "50025051010151" } else { "50025051010251" });
    let previous = TxOut::new(Zatoshis::const_from_u64(100), output(&redeem.0));
    // Independently computed using hashlib SHA-256 followed by RIPEMD-160.
    assert_eq!(
        hex::encode(&previous.script_pubkey().0.0),
        if PARAMETERS == ParameterSet::Sha2_128f { "a9144e1be64b56f51d13abfc0410c03e7da93c83364f87" } else { "a9149b5318c80392225ef98b1f4787307be84a9250a387" }
    );
    assert_eq!(previous.script_pubkey().0.0.len(), 23);
    assert_eq!(
        previous.recipient_address(),
        Some(TransparentAddress::ScriptHash(hash160::hash(&redeem.0)))
    );
    let mut wire = Vec::new();
    previous.write(&mut wire).unwrap();
    let decoded = TxOut::read(&mut &wire[..]).unwrap();
    assert_eq!(decoded.script_pubkey(), previous.script_pubkey());
    assert_eq!(check(&raw(&[], &redeem.0)), Ok(true));

    let equivalent = redeem_script(
        PARAMETERS,
        &Code(vec![0x01, 0x01]),
    )
    .unwrap();
    let mut substituted = raw(&[], &equivalent.0);
    substituted.pub_key = previous.script_pubkey().0.clone();
    assert_eq!(check(&substituted), Err(Error::CommitmentMismatch));
    // Changing the output as well authenticates the different byte representation.
    assert_eq!(check(&raw(&[], &equivalent.0)), Ok(true));
    let legacy_result = legacy(&raw(&[], &redeem.0), flags());
    assert!(matches!(
        legacy_result,
        Err(Error::Legacy(
            script::ComponentType::Redeem,
            script::Error::Interpreter(_, InterpreterError::BadOpcode)
        ))
    ));
    assert_eq!(
        signing_context(PARAMETERS),
        if PARAMETERS == ParameterSet::Sha2_128f { &b"ZCASH/PQ/P2SH\x01"[..] } else { &b"ZCASH/PQ/P2SH\x02"[..] }
    );
}

#[test]
fn identifier_is_authenticated_before_selection_and_unknown_modes_reject() {
    let redeem = redeem_script(PARAMETERS, &Code(vec![0x51])).unwrap();
    for id in [0, 3, 255] {
        let mut changed = redeem.0.clone();
        changed[5] = id;
        let mut substituted = raw(&[], &changed);
        substituted.pub_key = output(&redeem.0).0;
        assert_eq!(check(&substituted), Err(Error::CommitmentMismatch));
        assert_eq!(
            check(&raw(&[], &changed)),
            Err(Error::UnsupportedIdentifier(id))
        );
    }
    for malformed in [
        NAMESPACE.to_vec(),
        [&NAMESPACE[..], &[0x01]].concat(),
        [&NAMESPACE[..], &[0x4c, 1, 1, 0x51]].concat(),
    ] {
        assert_eq!(check(&raw(&[], &malformed)), Err(Error::IdentifierEncoding));
    }
    // A tag in an inactive branch does not select PQ rules.
    let mut nested = vec![0x00, 0x63];
    nested.extend_from_slice(&redeem.0);
    nested.extend_from_slice(&[0x68, 0x51]);
    let spend = raw(&[], &nested);
    assert_eq!(check(&spend), legacy(&spend, flags()));
    assert_eq!(check(&spend), Ok(true));
    assert_eq!(
        verify_spend(&raw(&[], &redeem.0), Flags::empty(), &checker()),
        Err(Error::P2shFlagRequired)
    );
}

#[test]
fn ordinary_legacy_scripts_keep_original_bytes_flags_and_limits() {
    for redeem in [
        vec![],
        vec![0],
        vec![0x51],
        vec![0x74, 0x51, 0x88],
        vec![0x75, 0x51],
    ] {
        for arguments in [
            vec![],
            vec![0],
            vec![0x51],
            push(&[1]),
            push(&vec![1; 520]),
            push(&vec![1; 521]),
            vec![0; 1000],
        ] {
            let spend = raw(&arguments, &redeem);
            for flags in [
                flags(),
                flags() | Flags::MinimalData,
                flags() | Flags::CleanStack,
            ] {
                assert_eq!(
                    verify_spend(&spend, flags, &checker()),
                    legacy(&spend, flags)
                );
            }
        }
    }
    let spend = raw(&push(&[1]), &[0x75, 0x51]);
    assert_eq!(check(&spend), Ok(true));
    assert!(matches!(
        verify_spend(&spend, flags() | Flags::MinimalData, &checker()),
        Err(Error::Legacy(_, _))
    ));
    let oversized = raw(&vec![0; 10_001], &[0x51]);
    assert_eq!(check(&oversized), legacy(&oversized, flags()));
    assert!(matches!(
        check(&oversized),
        Err(Error::Legacy(
            script::ComponentType::Sig,
            script::Error::ScriptSize(_)
        ))
    ));
    let large_redeem = raw(&[], &vec![0; 521]);
    assert_eq!(check(&large_redeem), legacy(&large_redeem, flags()));
    assert!(matches!(
        check(&large_redeem),
        Err(Error::Legacy(_, script::Error::Opcode(_)))
    ));
    // Other output types never enter preliminary PQ parsing.
    let ordinary = script::Raw::from_raw_parts(vec![0x51, 0x75], vec![0x51]);
    assert_eq!(check(&ordinary), legacy(&ordinary, flags()));
}

#[test]
fn pq_arguments_and_redeem_script_use_larger_bounds_after_authentication() {
    let redeem = redeem_script(
        PARAMETERS,
        &Code(vec![0x75, 0x51]),
    )
    .unwrap();
    let spend = raw(&push(&vec![1; pq::MAX_PUSH_BYTES]), &redeem.0);
    assert_eq!(check(&spend), Ok(true));
    assert!(matches!(
        legacy(&spend, flags()),
        Err(Error::Legacy(_, script::Error::ScriptSize(_)))
    ));
    let oversized = raw(&push(&vec![1; pq::MAX_PUSH_BYTES + 1]), &redeem.0);
    assert_eq!(check(&oversized), Err(Error::Pq(pq::Error::PushSize)));

    // This valid body exceeds legacy P2SH's 520-byte redeem-script push limit.
    let mut body = push(&[1; 500]);
    body.push(0x75);
    body.extend_from_slice(&push(&[1; 500]));
    body.extend_from_slice(&[0x75, 0x51]);
    let redeem = redeem_script(PARAMETERS, &Code(body)).unwrap();
    assert_eq!(check(&raw(&[], &redeem.0)), Ok(true));
    let mut too_large = redeem.0;
    too_large.resize(pq::MAX_SCRIPT_BYTES + 1, 0);
    assert!(matches!(
        check(&raw(&[], &too_large)),
        Err(Error::Pq(pq::Error::Script(script::Error::ScriptSize(_))))
    ));
    assert!(
        redeem_script(
            PARAMETERS,
            &Code(vec![0; pq::MAX_SCRIPT_BYTES - HEADER_BYTES])
        )
        .is_ok()
    );
    assert!(
        redeem_script(
            PARAMETERS,
            &Code(vec![0; pq::MAX_SCRIPT_BYTES - HEADER_BYTES + 1])
        )
        .is_err()
    );
}

#[test]
fn full_input_bounds_include_final_script_and_its_push() {
    let redeem = redeem_script(PARAMETERS, &Code(vec![0x51])).unwrap();
    let mut args = Vec::new();
    let target = pq::MAX_INPUT_BYTES - push(&redeem.0).len();
    while args.len() + pq::MAX_PUSH_BYTES + 3 < target {
        args.extend(push(&vec![1; pq::MAX_PUSH_BYTES]));
    }
    args.extend(push(&vec![1; target - args.len() - 3]));
    let mut spend = raw(&args, &redeem.0);
    assert_eq!(spend.sig.0.len(), pq::MAX_INPUT_BYTES);
    assert_eq!(check(&spend), Ok(true));
    spend.sig.0.insert(0, 0);
    assert_eq!(check(&spend), Err(Error::Pq(pq::Error::InputSize)));
    let empty = redeem_script(PARAMETERS, &Code(vec![])).unwrap();
    assert_eq!(check(&raw(&[0x51], &empty.0)), Ok(true));
    assert_eq!(check(&raw(&[], &empty.0)), Ok(false));
    assert_eq!(check(&raw(&vec![0; 999], &empty.0)), Ok(false));
    assert!(matches!(
        check(&raw(&vec![0; 1000], &empty.0)),
        Err(Error::Pq(pq::Error::Script(script::Error::Interpreter(
            _,
            InterpreterError::StackSize(_)
        ))))
    ));
}

#[test]
fn preliminary_scan_rejects_malformed_input_without_executing_it() {
    let redeem = redeem_script(PARAMETERS, &Code(vec![0x51])).unwrap();
    for (input, error) in [
        (vec![], pq::Error::MissingScript),
        (vec![0x4d], pq::Error::TruncatedPush),
        (vec![0x4d, 1], pq::Error::TruncatedPush),
        (vec![0x4d, 1, 0], pq::Error::TruncatedPush),
        (vec![0x4e, 255, 255, 255, 255], pq::Error::PushSize),
        (vec![0xac], pq::Error::NotPushOnly),
    ] {
        let spend = script::Raw::from_raw_parts(input, output(&redeem.0).0.0);
        assert_eq!(check(&spend), Err(Error::Pq(error)));
    }
    // Missing the final script cannot turn an ordinary argument into PQ authority.
    let spend = script::Raw::from_raw_parts(push(&[0x51]), output(&redeem.0).0.0);
    assert_eq!(check(&spend), Err(Error::CommitmentMismatch));
}

#[test]
fn callback_receives_complete_redeem_script_for_each_failed_check() {
    let mut body = vec![0x76, u8::try_from(crypto::PUBLIC_KEY_BYTES).unwrap()]; // DUP argument; push key
    body.extend_from_slice(&[0; crypto::PUBLIC_KEY_BYTES]);
    body.extend_from_slice(&[0xac, 0x75, u8::try_from(crypto::PUBLIC_KEY_BYTES).unwrap()]); // CHECKSIG DROP; push key
    body.extend_from_slice(&[0; crypto::PUBLIC_KEY_BYTES]);
    body.push(0xac);
    let redeem = redeem_script(PARAMETERS, &Code(body)).unwrap();
    let mut signature = vec![0; crypto::SIGNATURE_BYTES];
    signature.push(1);
    let spend = raw(&push(&signature), &redeem.0);
    let calls = core::cell::Cell::new(0);
    let sighash = |script: &Code, _: &zcash_script::signature::HashType| {
        assert_eq!(script.0, redeem.0);
        calls.set(calls.get() + 1);
        Some([42; 32])
    };
    let checker = CallbackTransactionSignatureChecker {
        sighash: &sighash,
        lock_time: 0,
        is_final: false,
    };
    assert_eq!(verify_spend(&spend, flags(), &checker), Ok(false));
    assert_eq!(calls.get(), 2);
    let mut changed = spend;
    changed.pub_key.0[2] ^= 1;
    assert_eq!(check(&changed), Err(Error::CommitmentMismatch));
}

#[test]
fn shared_operation_limit_charges_failed_multisig_matches_before_verifying() {
    // Every CHECKMULTISIG costs its own operation plus twenty keys; DROP costs
    // one more. Nine groups fit at 198 operations, the tenth must abort before
    // requesting any further digests, even though every signature check fails.
    for groups in [9, 10] {
        let mut body = Vec::new();
        let mut arguments = Vec::new();
        let mut signature = vec![0; crypto::SIGNATURE_BYTES];
        signature.push(1);
        for _ in 0..groups {
            arguments.push(0);
            arguments.extend(push(&signature));
            body.push(0x51); // one required signature
            for _ in 0..20 {
                body.push(u8::try_from(crypto::PUBLIC_KEY_BYTES).unwrap());
                body.extend(vec![0; crypto::PUBLIC_KEY_BYTES]);
            }
            body.extend([1, 20, 0xae, 0x75]); // twenty keys, CHECKMULTISIG DROP
        }
        body.push(0x51);
        let redeem = redeem_script(PARAMETERS, &Code(body)).unwrap();
        let calls = core::cell::Cell::new(0);
        let sighash = |_: &Code, _: &zcash_script::signature::HashType| {
            calls.set(calls.get() + 1);
            None // Failed checks still consume the multisig operation allowance.
        };
        let transaction = CallbackTransactionSignatureChecker {
            sighash: &sighash,
            lock_time: 0,
            is_final: false,
        };
        let result = verify_spend(&raw(&arguments, &redeem.0), flags(), &transaction);
        if groups == 9 {
            assert_eq!(result, Ok(true));
        } else {
            assert!(matches!(
                result,
                Err(Error::Pq(pq::Error::Script(script::Error::Interpreter(
                    _,
                    InterpreterError::OpCount
                ))))
            ));
        }
        assert_eq!(calls.get(), 180);
    }
}

#[test]
fn multisig_rejects_more_than_twenty_keys_before_requesting_a_digest() {
    let mut body = vec![0];
    for _ in 0..21 {
        body.push(u8::try_from(crypto::PUBLIC_KEY_BYTES).unwrap());
        body.extend(vec![0; crypto::PUBLIC_KEY_BYTES]);
    }
    body.extend([1, 21, 0xae]);
    let redeem = redeem_script(PARAMETERS, &Code(body)).unwrap();
    assert!(matches!(
        check(&raw(&[0], &redeem.0)),
        Err(Error::Pq(pq::Error::Script(script::Error::Interpreter(
            _,
            InterpreterError::PubKeyCount(_)
        ))))
    ));
}
