//! Attempts to make a PQ script run more signature checks than its input pays for.
//!
//! A stand-in signer keeps these exact and fast: a signature is valid when every byte equals
//! the first byte of its four-byte key, and every check with a non-empty signature is
//! counted, so each test can assert both the outcome and how much cryptography ran.

use alloc::{vec, vec::Vec};
use core::{cell::Cell, num::NonZeroUsize};

use super::{CheckBudget, Error, OP_CHECKSIGADD, eval_script, signature_check_count};
use crate::{
    interpreter::{self, Flags, SignatureChecker},
    script, signature,
};

/// The stand-in signature size: what each check costs.
const SIG: usize = 100;
const KEY: usize = 4;

const CHECKSIG: u8 = 0xac;
const CHECKSIGVERIFY: u8 = 0xad;
const CHECKMULTISIG: u8 = 0xae;
const CHECKMULTISIGVERIFY: u8 = 0xaf;
const NUMEQUAL: u8 = 0x9c;
const NOT: u8 = 0x91;
const DUP: u8 = 0x76;
const DROP: u8 = 0x75;
const SWAP: u8 = 0x7c;
const OVER: u8 = 0x78;
const NIP: u8 = 0x77;
const TWO_DUP: u8 = 0x6e;
const IF: u8 = 0x63;
const ENDIF: u8 = 0x68;

struct Signer {
    checks: Cell<usize>,
}

impl Signer {
    fn new() -> Self {
        Self {
            checks: Cell::new(0),
        }
    }
}

impl SignatureChecker for Signer {
    fn check_signature(
        &self,
        signature: &[u8],
        public_key: &[u8],
        _: Flags,
        _: &script::Code,
    ) -> Result<bool, interpreter::Error> {
        if public_key.len() != KEY {
            return Err(interpreter::Error::PubKeyType);
        }
        if signature.is_empty() {
            return Ok(false);
        }
        self.checks.set(self.checks.get() + 1);
        Ok(signature.len() == SIG && signature.iter().all(|byte| *byte == public_key[0]))
    }

    fn check_sig(&self, _: &signature::Decoded, _: &[u8], _: &script::Code) -> bool {
        unreachable!("PQ scripts never decode an ECDSA signature")
    }

    fn check_lock_time(&self, _: i64) -> bool {
        false
    }
}

fn key(id: u8) -> Vec<u8> {
    vec![id; KEY]
}

fn sig(id: u8) -> Vec<u8> {
    vec![id; SIG]
}

/// The shortest push of `data`, as both the input and a script body must use.
fn push(data: &[u8]) -> Vec<u8> {
    let mut bytes = match data {
        [] => return vec![0x00],
        [0x81] => return vec![0x4f],
        [n @ 1..=16] => return vec![0x50 + n],
        _ if data.len() < 0x4c => vec![data.len() as u8],
        _ if data.len() < 0x100 => vec![0x4c, data.len() as u8],
        _ => {
            let mut bytes = vec![0x4d];
            bytes.extend_from_slice(&(data.len() as u16).to_le_bytes());
            bytes
        }
    };
    bytes.extend_from_slice(data);
    bytes
}

fn number(n: u8) -> u8 {
    assert!((1..=16).contains(&n));
    0x50 + n
}

/// Runs `body` on `arguments` (bottom of the stack first), budgeted as a real input would
/// be: the serialized arguments and the pushed body together.
fn run(arguments: &[Vec<u8>], body: &[u8]) -> (Result<bool, Error>, usize) {
    let input: Vec<u8> = arguments.iter().flat_map(|item| push(item)).collect();
    let budget = budget(arguments, body);
    let signer = Signer::new();
    let result = eval_script(&input, &script::Code(body.to_vec()), &signer, budget);
    (result, signer.checks.get())
}

/// The budget of a real input carrying these arguments and this body.
fn budget(arguments: &[Vec<u8>], body: &[u8]) -> CheckBudget {
    let input_bytes =
        arguments.iter().map(|item| push(item).len()).sum::<usize>() + push(body).len();
    CheckBudget::new(input_bytes, NonZeroUsize::new(SIG).unwrap())
}

fn failed_with(result: &Result<bool, Error>, expected: interpreter::Error) -> bool {
    matches!(result, Err(Error::Script(script::Error::Interpreter(_, error))) if *error == expected)
}

/// `<K1> CHECKSIG <K2> CHECKSIGADD ... <Kn> CHECKSIGADD <k> NUMEQUAL`.
fn threshold(keys: &[Vec<u8>], required: u8) -> Vec<u8> {
    let mut body = Vec::new();
    for (index, key) in keys.iter().enumerate() {
        body.extend(push(key));
        body.push(if index == 0 { CHECKSIG } else { OP_CHECKSIGADD });
    }
    body.extend(push(&[required]));
    body.push(NUMEQUAL);
    body
}

/// The arguments for `threshold`, one per key, the first key's on top of the stack.
fn slots(signers: &[Option<u8>]) -> Vec<Vec<u8>> {
    signers
        .iter()
        .rev()
        .map(|signer| signer.map_or_else(Vec::new, sig))
        .collect()
}

#[test]
fn a_k_of_n_runs_exactly_k_checks_and_always_fits_its_budget() {
    // Well past the twenty keys CHECKMULTISIG allows.
    let n = 30u8;
    let keys: Vec<_> = (1..=n).map(key).collect();
    for required in 1..=n {
        let body = threshold(&keys, required);
        // Signers spread across the slots, not only the first ones.
        let signers: Vec<_> = (1..=n)
            .map(|id| {
                (u32::from(id) * u32::from(required) % u32::from(n) < u32::from(required))
                    .then_some(id)
            })
            .collect();
        let signed = signers.iter().flatten().count();
        let arguments = slots(&signers);
        let (result, checks) = run(&arguments, &body);
        assert_eq!(checks, signed, "{required}-of-{n}");
        assert_eq!(
            result,
            Ok(signed == usize::from(required)),
            "{required}-of-{n}"
        );
        assert_eq!(signature_check_count(&script::Code(body)), u32::from(n));
    }
}

#[test]
fn every_k_of_n_with_k_signers_passes() {
    let keys: Vec<_> = (1..=5).map(key).collect();
    let body = threshold(&keys, 2);
    for first in 1..=5u8 {
        for second in first + 1..=5 {
            let signers: Vec<_> = (1..=5)
                .map(|id| (id == first || id == second).then_some(id))
                .collect();
            assert_eq!(run(&slots(&signers), &body), (Ok(true), 2));
        }
    }
    // One signer short is false, not an error: the count simply does not match.
    assert_eq!(
        run(&slots(&[Some(1), None, None, None, None]), &body),
        (Ok(false), 1)
    );
    // A signature in the wrong key's slot is an invalid non-empty signature.
    let (result, checks) = run(&slots(&[Some(2), Some(1), None, None, None]), &body);
    assert!(failed_with(&result, interpreter::Error::PqNullFail));
    assert_eq!(checks, 1, "the spend stops at the first failed signature");
}

#[test]
fn checking_a_copied_signature_is_over_budget() {
    // DUP <A> CHECKSIGVERIFY <A> CHECKSIG: one signature, checked twice.
    let mut body = vec![DUP];
    body.extend(push(&key(1)));
    body.push(CHECKSIGVERIFY);
    body.extend(push(&key(1)));
    body.push(CHECKSIG);
    let (result, checks) = run(&[sig(1)], &body);
    assert!(failed_with(&result, interpreter::Error::PqCheckBudget));
    assert_eq!(checks, 1, "the copy is refused before its check runs");
    // The same body is fine when the copy is not a copy.
    let mut honest = vec![];
    honest.extend(push(&key(1)));
    honest.push(CHECKSIGVERIFY);
    honest.extend(push(&key(1)));
    honest.push(CHECKSIG);
    assert_eq!(run(&[sig(1), sig(1)], &honest), (Ok(true), 2));
}

#[test]
fn the_design_documents_copy_constructions_stop_at_the_budget() {
    // <A> then (2DUP CHECKSIGVERIFY) x 99 then CHECKSIG: 199 operations, 100 checks of one
    // signature. Before the budget all 100 ran.
    let mut verify_copies = push(&key(1));
    for _ in 0..99 {
        verify_copies.extend([TWO_DUP, CHECKSIGVERIFY]);
    }
    verify_copies.push(CHECKSIG);

    // The CHECKSIGADD form: 0, then (OVER SWAP <A> CHECKSIGADD) x 60, NIP, then count = 60.
    let mut add_copies = vec![0x00];
    for _ in 0..60 {
        add_copies.extend([OVER, SWAP]);
        add_copies.extend(push(&key(1)));
        add_copies.push(OP_CHECKSIGADD);
    }
    add_copies.push(NIP);
    add_copies.extend(push(&[60]));
    add_copies.push(NUMEQUAL);

    for (body, intended) in [(verify_copies, 100u32), (add_copies, 60)] {
        assert_eq!(signature_check_count(&script::Code(body.clone())), intended);
        // Every byte of the input pays, the revealed script's included, so the long script
        // buys a few checks of its own here; with real signature sizes a script (at most
        // 10,000 bytes) is worth less than one. What it cannot do is run more checks than
        // its bytes pay for.
        let affordable = budget(&[sig(1)], &body).max_checks();
        assert!(affordable < intended as usize);
        let (result, checks) = run(&[sig(1)], &body);
        assert!(failed_with(&result, interpreter::Error::PqCheckBudget));
        assert_eq!(
            checks, affordable,
            "the first check past the budget never runs"
        );
    }
}

/// `<junk> <sig>` under `SWAP DROP` then `copies` checks of the one signature.
fn padded(junk: usize, copies: usize) -> (Result<bool, Error>, usize) {
    let mut body = vec![SWAP, DROP];
    for _ in 1..copies {
        body.push(DUP);
        body.extend(push(&key(1)));
        body.push(CHECKSIGVERIFY);
    }
    body.extend(push(&key(1)));
    body.push(CHECKSIG);
    run(&[vec![0xee; junk], sig(1)], &body)
}

fn padded_input_bytes(junk: usize, copies: usize) -> usize {
    let mut body = vec![SWAP, DROP];
    for _ in 1..copies {
        body.push(DUP);
        body.extend(push(&key(1)));
        body.push(CHECKSIGVERIFY);
    }
    body.extend(push(&key(1)));
    body.push(CHECKSIG);
    push(&vec![0xee; junk]).len() + push(&sig(1)).len() + push(&body).len()
}

#[test]
fn padding_buys_checks_only_at_the_price_of_a_signature() {
    for copies in [2, 3, 5] {
        // The least junk that pays for every check, found by search, since push prefixes
        // grow with the junk.
        let junk = (0..copies * SIG)
            .find(|&junk| padded_input_bytes(junk, copies) >= copies * SIG)
            .unwrap();
        assert_eq!(padded(junk, copies), (Ok(true), copies), "{copies} checks");
        // A byte less, and the last check is refused before it runs.
        let (result, checks) = padded(junk - 1, copies);
        assert!(failed_with(&result, interpreter::Error::PqCheckBudget));
        assert_eq!(checks, copies - 1);
        // Never more checks than the input's bytes divided by the signature size.
        assert!(padded_input_bytes(junk, copies) / SIG >= copies);
        assert!(padded_input_bytes(junk - 1, copies) / SIG < copies);
    }
}

#[test]
fn empty_signatures_are_free_and_false() {
    // 99 declined checks and a true result: no budget is needed for any of them.
    let mut body = Vec::new();
    for _ in 0..99 {
        body.push(0x00);
        body.extend(push(&key(1)));
        body.extend([CHECKSIG, DROP]);
    }
    body.push(number(1));
    assert_eq!(run(&[], &body), (Ok(true), 0));
    // A declined CHECKSIG under NOT is the one way to prove a key did not sign.
    let mut not_signed = push(&key(1));
    not_signed.extend([CHECKSIG, NOT]);
    assert_eq!(run(&[vec![]], &not_signed), (Ok(true), 0));
    // Even declining, the key has to be well formed.
    let mut bad_key = push(&[1; KEY + 1]);
    bad_key.extend([CHECKSIG, NOT]);
    assert!(failed_with(
        &run(&[vec![]], &bad_key).0,
        interpreter::Error::PubKeyType
    ));
}

#[test]
fn a_failed_non_empty_signature_invalidates_the_spend() {
    let wrong = sig(2);
    for opcode in [CHECKSIG, CHECKSIGVERIFY] {
        let mut body = push(&key(1));
        body.push(opcode);
        if opcode == CHECKSIGVERIFY {
            body.push(number(1));
        }
        let (result, checks) = run(core::slice::from_ref(&wrong), &body);
        assert!(
            failed_with(&result, interpreter::Error::PqNullFail),
            "{opcode:#x}"
        );
        assert_eq!(checks, 1);
    }
    // NOT cannot turn a bad signature into a passing spend.
    let mut negated = push(&key(1));
    negated.extend([CHECKSIG, NOT]);
    assert!(failed_with(
        &run(core::slice::from_ref(&wrong), &negated).0,
        interpreter::Error::PqNullFail
    ));
    // Nor can CHECKSIGADD count it as a decline.
    let mut added = vec![0x00];
    added.extend(push(&key(1)));
    added.extend([OP_CHECKSIGADD, 0x00, NUMEQUAL]);
    assert!(failed_with(
        &run(&[wrong], &added).0,
        interpreter::Error::PqNullFail
    ));
}

#[test]
fn checksigadd_counts_signers_and_checks_its_operands() {
    // (sig n pubkey -- n'), with n taken from the script.
    let mut body = vec![number(5)];
    body.extend(push(&key(1)));
    body.extend([OP_CHECKSIGADD, number(6), NUMEQUAL]);
    assert_eq!(run(&[sig(1)], &body), (Ok(true), 1));
    let mut declined = vec![number(5)];
    declined.extend(push(&key(1)));
    declined.extend([OP_CHECKSIGADD, number(5), NUMEQUAL]);
    assert_eq!(run(&[vec![]], &declined), (Ok(true), 0));

    // Too few operands.
    let mut short = push(&key(1));
    short.push(OP_CHECKSIGADD);
    assert!(failed_with(
        &run(&[sig(1)], &short).0,
        interpreter::Error::InvalidStackOperation(Some((2, 2)))
    ));
    // n is a number of at most four bytes.
    let mut wide = push(&[1, 0, 0, 0, 0]);
    wide.extend(push(&key(1)));
    wide.push(OP_CHECKSIGADD);
    assert!(matches!(
        run(&[vec![]], &wide).0,
        Err(Error::Script(script::Error::Interpreter(
            _,
            interpreter::Error::Num(_)
        )))
    ));
    // n is minimally encoded, so a count taken from the input has one spelling.
    let mut from_input = push(&key(1));
    from_input.extend([OP_CHECKSIGADD, number(1), NUMEQUAL]);
    assert_eq!(run(&[sig(1), vec![]], &from_input), (Ok(true), 1));
    assert!(matches!(
        run(&[sig(1), vec![0x00]], &from_input).0,
        Err(Error::Script(script::Error::Interpreter(
            _,
            interpreter::Error::Num(_)
        )))
    ));
    // A malformed key aborts, as for CHECKSIG.
    let mut bad_key = vec![0x00];
    bad_key.extend(push(&[1; KEY - 1]));
    bad_key.push(OP_CHECKSIGADD);
    assert!(failed_with(
        &run(&[sig(1)], &bad_key).0,
        interpreter::Error::PubKeyType
    ));
}

#[test]
fn checksigadd_counts_against_the_operation_limit_even_when_skipped() {
    let skipped = |count: usize| {
        let mut body = vec![0x00, IF];
        body.extend(vec![OP_CHECKSIGADD; count]);
        body.extend([ENDIF, number(1)]);
        run(&[], &body).0
    };
    // IF and ENDIF are two operations of the 201.
    assert_eq!(skipped(199), Ok(true));
    assert!(failed_with(&skipped(200), interpreter::Error::OpCount));
}

#[test]
fn multisig_is_invalid_anywhere_in_a_pq_script() {
    let mut executed = vec![0x00, number(1)];
    executed.extend(push(&key(1)));
    executed.extend([number(1), CHECKMULTISIG]);
    let mut skipped = vec![0x00, IF, CHECKMULTISIGVERIFY, ENDIF, number(1)];
    for body in [&mut executed, &mut skipped] {
        let (result, checks) = run(&[sig(1)], body);
        assert!(
            failed_with(&result, interpreter::Error::PqMultisig),
            "{body:?}"
        );
        assert_eq!(checks, 0);
    }
    // Both opcodes, at the end of an otherwise passing script.
    for opcode in [CHECKMULTISIG, CHECKMULTISIGVERIFY] {
        let body = vec![number(1), 0x00, IF, opcode, ENDIF];
        assert!(failed_with(
            &run(&[], &body).0,
            interpreter::Error::PqMultisig
        ));
    }
}

#[test]
fn legacy_scripts_keep_their_meaning_for_both_opcodes() {
    let legacy = |pub_key: Vec<u8>| {
        script::Raw::from_raw_parts(vec![], pub_key)
            .eval(
                Flags::CHECKLOCKTIMEVERIFY,
                &interpreter::NullSignatureChecker(),
            )
            .map_err(|(_, error)| error)
    };
    // 0xba stays an unknown opcode: fatal when executed, harmless when skipped.
    assert!(matches!(
        legacy(vec![OP_CHECKSIGADD]),
        Err(script::Error::Interpreter(_, interpreter::Error::BadOpcode))
    ));
    assert_eq!(
        legacy(vec![0x00, IF, OP_CHECKSIGADD, ENDIF, number(1)]),
        Ok(true)
    );
    // And a legacy zero-of-zero multisig still runs.
    assert_eq!(legacy(vec![0x00, 0x00, 0x00, CHECKMULTISIG]), Ok(true));
}

#[test]
fn the_check_count_covers_every_branch_and_stops_where_parsing_does() {
    let mut body = push(&key(1));
    body.extend([CHECKSIG, IF, CHECKSIGVERIFY, 0x67, OP_CHECKSIGADD, ENDIF]);
    assert_eq!(signature_check_count(&script::Code(body.clone())), 3);
    // A disabled opcode adds nothing and counting continues past it.
    body.extend([0x7e, CHECKSIG]);
    assert_eq!(signature_check_count(&script::Code(body.clone())), 4);
    // A truncated push ends it.
    body.extend([0x4c, 0x05, CHECKSIG]);
    assert_eq!(signature_check_count(&script::Code(body)), 4);
}
