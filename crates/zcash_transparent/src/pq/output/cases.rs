// These cases are compiled once per parameter set: `output/tests.rs` includes this file in
// a module for each one, where `PARAMETERS` is that set and `crypto` its primitives.

use crate::{
    address::{Script, TransparentAddress},
    bundle::TxOut,
};
use zcash_protocol::{consensus::NetworkType, value::Zatoshis};
use zcash_script::interpreter::{Error as InterpreterError, Flags};

const NETWORK: NetworkType = NetworkType::Main;

/// Flags for the legacy evaluator, which no PQ rule consults.
fn flags() -> Flags {
    Flags::P2SH | Flags::CHECKLOCKTIMEVERIFY
}

/// The shortest encoding of this payload, which PQ inputs are required to use.
fn push(value: &[u8]) -> Vec<u8> {
    let mut bytes = match value.len() {
        length if length < 0x4c => vec![length as u8],
        length if length < 0x100 => vec![0x4c, length as u8],
        length if length < 0x10000 => {
            let mut prefix = vec![0x4d];
            prefix.extend_from_slice(&(length as u16).to_le_bytes());
            prefix
        }
        length => {
            let mut prefix = vec![0x4e];
            prefix.extend_from_slice(&(length as u32).to_le_bytes());
            prefix
        }
    };
    bytes.extend_from_slice(value);
    bytes
}

/// The PQ output committing to this body, taken apart byte by byte in the first test.
fn output(body: &[u8]) -> Script {
    let mut bytes = vec![
        MARKER,
        VERSION_PUSH,
        PARAMETERS.version(),
        COMMITMENT_BYTES as u8,
    ];
    bytes.extend_from_slice(&hash160::hash(body));
    Script(Code(bytes))
}

/// An ordinary P2SH output, for the comparisons against unchanged legacy evaluation.
fn p2sh_output(redeem: &[u8]) -> Script {
    TransparentAddress::ScriptHash(hash160::hash(redeem))
        .script()
        .into()
}

/// The serialized spending input: arguments, then the committed body.
fn input(arguments: &[u8], body: &[u8]) -> Vec<u8> {
    let mut bytes = arguments.to_vec();
    bytes.extend_from_slice(&push(body));
    bytes
}

fn p2sh_raw(arguments: &[u8], redeem: &[u8]) -> script::Raw {
    script::Raw::from_raw_parts(input(arguments, redeem), p2sh_output(redeem).0.0)
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

/// Parses a previous output, then verifies this input against it.
fn check_output(previous_output: &Code, input: &[u8]) -> Result<bool, Error> {
    match parse_output(previous_output)? {
        Some(parsed) => parsed.verify_spend(NETWORK, input, &checker()),
        None => panic!("this previous output does not claim the PQ namespace"),
    }
}

/// Verifies a spend of the canonical output for this body.
fn check(arguments: &[u8], body: &[u8]) -> Result<bool, Error> {
    check_output(&output(body).0, &input(arguments, body))
}

fn clean_stack() -> Error {
    Error::Pq(pq::Error::Script(script::Error::CleanStack))
}

#[test]
fn output_carries_the_version_and_commits_the_exact_body() {
    let body = Code(vec![0x51]);
    let script = output_script(PARAMETERS, &body).unwrap();
    // The output carries the version, then pushes the hash of the body alone.
    assert_eq!(script.0.len(), 24);
    assert_eq!(script.0[..2], [MARKER, VERSION_PUSH]);
    assert_eq!(script.0[2], PARAMETERS.version());
    assert_eq!(script.0[HEADER_BYTES], COMMITMENT_BYTES as u8);
    assert_eq!(script.0[HEADER_BYTES + 1..], hash160::hash(&body.0));
    // Independently computed using hashlib SHA-256 followed by RIPEMD-160.
    assert_eq!(
        hex::encode(&script.0),
        if PARAMETERS == ParameterSet::Sha2_128f {
            "50010114da1745e9b549bd0bfa1a569971c77eba30cd5a4b"
        } else {
            "50010214da1745e9b549bd0bfa1a569971c77eba30cd5a4b"
        }
    );
    // The commitment covers the body alone, so the other version's output for the same
    // body differs in exactly the version byte. Both are spendable only by a key of
    // their own version's length, which is what keeps them apart.
    let other = match PARAMETERS {
        ParameterSet::Sha2_128f => ParameterSet::Sha2_192s,
        ParameterSet::Sha2_192s => ParameterSet::Sha2_128f,
    };
    let other_script = output_script(other, &body).unwrap();
    assert_eq!(other_script.0[2], other.version());
    assert_eq!(other_script.0[HEADER_BYTES..], script.0[HEADER_BYTES..]);
    assert_ne!(other_script.0, script.0);

    // It survives the wire unchanged, and is not any address type this crate encodes.
    let previous = TxOut::new(Zatoshis::const_from_u64(100), Script(script.clone()));
    let mut wire = Vec::new();
    previous.write(&mut wire).unwrap();
    let decoded = TxOut::read(&mut &wire[..]).unwrap();
    assert_eq!(decoded.script_pubkey(), previous.script_pubkey());
    assert_eq!(previous.recipient_address(), None);

    let parsed = parse_output(&script).unwrap().unwrap();
    assert_eq!(parsed.parameters(), PARAMETERS);
    assert_eq!(parsed.commitment(), &hash160::hash(&body.0));
    assert_eq!(classify_created_output(&script), CreatedOutput::Pq(PARAMETERS));
    assert_eq!(check(&[], &body.0), Ok(true));

    // A different body is a different commitment, so the original output rejects it.
    let equivalent = Code(vec![0x01, 0x01]);
    assert_eq!(
        check_output(&script, &input(&[], &equivalent.0)),
        Err(Error::CommitmentMismatch)
    );
    // Committing to those bytes in the output authenticates them instead.
    assert_eq!(check(&[], &equivalent.0), Ok(true));

    // The output itself fails under the unchanged legacy evaluator, so it is never
    // claimable where these rules are not active.
    let under_legacy = script::Raw::from_raw_parts(input(&[], &body.0), script.0.clone())
        .eval(flags(), &checker());
    assert!(matches!(
        under_legacy,
        Err((
            script::ComponentType::PubKey,
            script::Error::Interpreter(_, InterpreterError::BadOpcode)
        ))
    ));
    assert_eq!(
        signing_context(NETWORK, PARAMETERS),
        if PARAMETERS == ParameterSet::Sha2_128f {
            &b"ZCASH/PQ/OUT/main\x01"[..]
        } else {
            &b"ZCASH/PQ/OUT/main\x02"[..]
        }
    );
}

#[test]
fn unknown_versions_and_non_canonical_outputs_are_rejected_at_creation() {
    let body = Code(vec![0x51]);
    let script = output_script(PARAMETERS, &body).unwrap();

    // An unknown version yields no output to spend, whatever an input pushes for it.
    for version in [0, 3, 255] {
        let mut changed = script.clone();
        changed.0[2] = version;
        assert_eq!(
            parse_output(&changed),
            Err(Error::UnsupportedVersion(version))
        );
        assert_eq!(
            classify_created_output(&changed),
            CreatedOutput::Malformed(Error::UnsupportedVersion(version))
        );
    }

    let mut trailing = script.0.clone();
    trailing.push(0);
    let mut wide_push = script.0.clone();
    wide_push[HEADER_BYTES] = 0x4c;
    // The version must be pushed by the one-byte push opcode, not OP_1 and not a wider one.
    let mut wide_version = script.0.clone();
    wide_version[1] = 0x02;
    let mut small_version = script.0.clone();
    small_version[1] = 0x50 + PARAMETERS.version();
    for malformed in [
        vec![MARKER],
        vec![MARKER, VERSION_PUSH],
        vec![MARKER, VERSION_PUSH, PARAMETERS.version()],
        script.0[..OUTPUT_BYTES - 1].to_vec(),
        trailing,
        wide_push,
        wide_version,
        small_version,
    ] {
        assert_eq!(parse_output(&Code(malformed.clone())), Err(Error::OutputEncoding));
        assert_eq!(
            classify_created_output(&Code(malformed)),
            CreatedOutput::Malformed(Error::OutputEncoding)
        );
    }

    // Every other output shape is legacy, and a creation rule may ban it by height.
    for legacy_output in [
        p2sh_output(&body.0).0,
        Script::from(TransparentAddress::PublicKeyHash([1; 20]).script()).0,
        Code(vec![0x6a, 0x02, 1, 2]), // OP_RETURN data
        Code(vec![]),
        Code(vec![0x51]),
    ] {
        assert_eq!(parse_output(&legacy_output), Ok(None));
        assert_eq!(
            classify_created_output(&legacy_output),
            CreatedOutput::Legacy
        );
    }

    // The same commitment in a P2SH output is a different output under different rules:
    // it is not a PQ output, and legacy rules spend it, here successfully.
    let p2sh = p2sh_raw(&[], &body.0);
    assert_eq!(parse_output(&p2sh.pub_key), Ok(None));
    assert_eq!(p2sh.eval(flags(), &checker()), Ok(true));
}

#[test]
fn pq_arguments_and_committed_body_use_larger_bounds_after_authentication() {
    let body = vec![0x75, 0x51];
    let large = push(&vec![1; pq::MAX_PUSH_BYTES]);
    assert_eq!(check(&large, &body), Ok(true));
    // The same argument exceeds every legacy push bound.
    assert!(matches!(
        p2sh_raw(&large, &body).eval(flags(), &checker()),
        Err((_, script::Error::ScriptSize(_)))
    ));
    let oversized = push(&vec![1; pq::MAX_PUSH_BYTES + 1]);
    assert_eq!(
        check(&oversized, &body),
        Err(Error::Pq(pq::Error::PushSize))
    );
    // A longer-than-necessary encoding of an accepted argument is rejected.
    let mut non_minimal = vec![0x4d, 0x20, 0x00];
    non_minimal.extend_from_slice(&[1; 0x20]);
    assert_eq!(
        check(&non_minimal, &body),
        Err(Error::Pq(pq::Error::PushEncoding))
    );

    // This valid body exceeds legacy P2SH's 520-byte redeem-script push limit.
    let mut body = push(&[1; 500]);
    body.push(0x75);
    body.extend_from_slice(&push(&[1; 500]));
    body.extend_from_slice(&[0x75, 0x51]);
    assert_eq!(check(&[], &body), Ok(true));
    let mut too_large = body;
    too_large.resize(pq::MAX_SCRIPT_BYTES + 1, 0);
    // The size bound is applied before the commitment is computed over those bytes.
    assert!(matches!(
        check(&[], &too_large),
        Err(Error::Pq(pq::Error::Script(script::Error::ScriptSize(_))))
    ));
    // An output cannot be built for a body no spend could execute either.
    assert!(output_script(PARAMETERS, &Code(vec![0; pq::MAX_SCRIPT_BYTES])).is_ok());
    assert!(output_script(PARAMETERS, &Code(vec![0; pq::MAX_SCRIPT_BYTES + 1])).is_err());
}

#[test]
fn full_input_bounds_include_the_committed_body_and_its_push() {
    // Arguments of the largest accepted size, with a body that consumes all of them.
    let large = push(&vec![1; pq::MAX_PUSH_BYTES]);
    let count = (pq::MAX_INPUT_BYTES - 64) / large.len();
    let mut arguments: Vec<u8> = (0..count).flat_map(|_| large.clone()).collect();
    let mut body = vec![0x75; count + 1];
    body.push(0x51);
    // One filler argument brings the complete serialized input to exactly the bound.
    let filler = pq::MAX_INPUT_BYTES - arguments.len() - push(&body).len() - 3;
    arguments.extend(push(&vec![1; filler]));
    let serialized = input(&arguments, &body);
    assert_eq!(serialized.len(), pq::MAX_INPUT_BYTES);
    let previous_output = output(&body).0;
    assert_eq!(check_output(&previous_output, &serialized), Ok(true));
    let mut over = serialized;
    over.insert(0, 0);
    assert_eq!(
        check_output(&previous_output, &over),
        Err(Error::Pq(pq::Error::InputSize))
    );

    // Neither an empty final stack nor a leftover argument satisfies a PQ output.
    assert_eq!(check(&[0x51], &[]), Ok(true));
    assert_eq!(check(&[], &[]), Err(clean_stack()));
    assert_eq!(check(&[0x51, 0x51], &[]), Err(clean_stack()));
    assert_eq!(check(&vec![0; 999], &[]), Err(clean_stack()));
    assert!(matches!(
        check(&vec![0; 1000], &[]),
        Err(Error::Pq(pq::Error::Script(script::Error::Interpreter(
            _,
            InterpreterError::StackSize(_)
        ))))
    ));
}

#[test]
fn preliminary_scan_rejects_malformed_input_without_executing_it() {
    let previous_output = output(&[0x51]).0;
    for (serialized, error) in [
        (vec![], pq::Error::MissingScript),
        (vec![0x4d], pq::Error::TruncatedPush),
        (vec![0x4d, 1], pq::Error::TruncatedPush),
        (vec![0x4d, 1, 0], pq::Error::TruncatedPush),
        (vec![0x4e, 255, 255, 255, 255], pq::Error::PushSize),
        (vec![0x4c, 1, 0x20], pq::Error::PushEncoding),
        (vec![0xac], pq::Error::NotPushOnly),
    ] {
        assert_eq!(
            check_output(&previous_output, &serialized),
            Err(Error::Pq(error))
        );
    }
    // Missing the final script cannot turn an ordinary argument into PQ authority.
    assert_eq!(
        check_output(&previous_output, &push(&[0x52])),
        Err(Error::CommitmentMismatch)
    );
}

#[test]
fn callback_receives_the_committed_body_for_each_failed_check() {
    let mut body = vec![0x76, u8::try_from(crypto::PUBLIC_KEY_BYTES).unwrap()]; // DUP argument; push key
    body.extend_from_slice(&[0; crypto::PUBLIC_KEY_BYTES]);
    body.extend_from_slice(&[0xac, 0x75, u8::try_from(crypto::PUBLIC_KEY_BYTES).unwrap()]); // CHECKSIG DROP; push key
    body.extend_from_slice(&[0; crypto::PUBLIC_KEY_BYTES]);
    body.push(0xac);
    let mut signature = vec![0; crypto::SIGNATURE_BYTES];
    signature.push(1);
    let serialized = input(&push(&signature), &body);
    let previous_output = output(&body).0;
    let calls = core::cell::Cell::new(0);
    let sighash = |script: &Code, _: &zcash_script::signature::HashType| {
        assert_eq!(script.0, body);
        calls.set(calls.get() + 1);
        Some([42; 32])
    };
    let checker = CallbackTransactionSignatureChecker {
        sighash: &sighash,
        lock_time: 0,
        is_final: false,
    };
    let parsed = parse_output(&previous_output).unwrap().unwrap();
    assert_eq!(parsed.verify_spend(NETWORK, &serialized, &checker), Ok(false));
    assert_eq!(calls.get(), 2);
    // Both signature operations in every branch are counted, before any of them runs.
    let selected = parsed.authenticate_spend(&serialized).unwrap();
    assert_eq!(selected.sig_op_count(true), 2);
    assert_eq!(selected.body(), body);
    // A changed commitment no longer authenticates the same script, a changed version
    // selects rules that do not exist, and a changed version push is not an encoding.
    let mut changed = previous_output.clone();
    changed.0[HEADER_BYTES + 2] ^= 1;
    assert_eq!(
        check_output(&changed, &serialized),
        Err(Error::CommitmentMismatch)
    );
    let mut reversioned = previous_output.clone();
    reversioned.0[2] ^= 1;
    assert!(matches!(
        parse_output(&reversioned),
        Err(Error::UnsupportedVersion(_))
    ));
    let mut reframed = previous_output;
    reframed.0[1] ^= 1;
    assert_eq!(parse_output(&reframed), Err(Error::OutputEncoding));
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
        let serialized = input(&arguments, &body);
        let parsed = parse_output(&output(&body).0).unwrap().unwrap();
        let result = parsed.verify_spend(NETWORK, &serialized, &transaction);
        if groups == 9 {
            assert_eq!(result, Ok(true));
            // Twenty keys are charged for each of the nine matches.
            let selected = parsed.authenticate_spend(&serialized).unwrap();
            assert_eq!(selected.sig_op_count(true), 180);
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
    assert!(matches!(
        check(&[0], &body),
        Err(Error::Pq(pq::Error::Script(script::Error::Interpreter(
            _,
            InterpreterError::PubKeyCount(_)
        ))))
    ));
}
