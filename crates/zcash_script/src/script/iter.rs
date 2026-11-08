//! Much of the code is common between the script components, so this provides operations on
//! iterators that can be shared.

use alloc::vec::Vec;

use crate::{
    interpreter, opcode,
    script::{self, Evaluable},
};

/// The one place the legacy evaluator decides to refuse a PQ-namespace script.
///
/// Pairing the flag with the predicate here means a later call site cannot pick up one
/// without the other, which would be fail-open.
fn refuse_pq_namespace(flags: interpreter::Flags, script: &[u8]) -> Result<(), script::Error> {
    if flags.contains(interpreter::Flags::PqOutputs) && script::is_pq_namespace(script) {
        return Err(script::Error::PqNamespace);
    }
    Ok(())
}

/// [`refuse_pq_namespace`] for a typed component, whose bytes have to be materialized.
///
/// The flag is tested first so that nothing allocates while the rule is inactive, and the
/// length before `to_bytes`, so that only a script which could be in the namespace pays for
/// it.
fn refuse_pq_namespace_component<T: script::Evaluable>(
    flags: interpreter::Flags,
    component: &T,
) -> Result<(), script::Error> {
    if flags.contains(interpreter::Flags::PqOutputs)
        && component.byte_len() == script::PQ_NAMESPACE_BYTES
    {
        return refuse_pq_namespace(flags, &component.to_bytes());
    }
    Ok(())
}

/// Evaluate an entire script.
pub fn eval_script<T: script::Evaluable, U: script::Evaluable>(
    sig: &T,
    pub_key: &U,
    flags: interpreter::Flags,
    checker: &dyn interpreter::SignatureChecker,
) -> Result<bool, (script::ComponentType, script::Error)> {
    // This comes before anything reads the scriptSig, because it must not depend on it: a
    // namespace script is satisfied by an empty scriptSig under these rules, so the refusal
    // has to come from the output alone. Deciding it first also stops a spender from
    // choosing which error a node reports by varying the sig.
    refuse_pq_namespace_component(flags, pub_key)
        .map_err(|e| (script::ComponentType::PubKey, e))?;
    if flags.contains(interpreter::Flags::SigPushOnly) && !sig.is_push_only() {
        Err((script::ComponentType::Sig, script::Error::SigPushOnly))
    } else {
        let data_stack = sig
            .eval(flags, checker, interpreter::Stack::new())
            .map_err(|e| (script::ComponentType::Sig, e))?;
        let pub_key_stack = pub_key
            .eval(flags, checker, data_stack.clone())
            .map_err(|e| (script::ComponentType::PubKey, e))?;
        if pub_key_stack
            .last()
            .is_ok_and(|v| interpreter::cast_to_bool(v))
        {
            if flags.contains(interpreter::Flags::P2SH) && pub_key.is_pay_to_script_hash() {
                // script_sig must be literals-only or validation fails
                if sig.is_push_only() {
                    data_stack
                        .split_last()
                        .map_err(|_| script::Error::MissingRedeemScript)
                        .and_then(|(pub_key_2, remaining_stack)| {
                            // The same refusal for a redeem script, so the rule is simply
                            // that the legacy evaluator never runs a namespace script. A
                            // P2SH wrapper hides it behind a hash until the first spend,
                            // but it is satisfied by no arguments at all, so a wallet
                            // treating a P2SH-wrapped PQ script as PQ-protected would be
                            // wrong.
                            refuse_pq_namespace(flags, pub_key_2)?;
                            script::Code(pub_key_2.clone()).eval(flags, checker, remaining_stack)
                        })
                        .map(|p2sh_stack| {
                            if p2sh_stack
                                .last()
                                .is_ok_and(|v| interpreter::cast_to_bool(v))
                            {
                                Some(p2sh_stack)
                            } else {
                                None
                            }
                        })
                        .map_err(|e| (script::ComponentType::Redeem, e))
                } else {
                    Err((script::ComponentType::Sig, script::Error::SigPushOnly))
                }
            } else {
                Ok(Some(pub_key_stack))
            }
            .and_then(|mresult_stack| {
                match mresult_stack {
                    None => Ok(false),
                    Some(result_stack) => {
                        // The CLEANSTACK check is only performed after potential P2SH evaluation, as the
                        // non-P2SH evaluation of a P2SH script will obviously not result in a clean stack
                        // (the P2SH inputs remain).
                        if flags.contains(interpreter::Flags::CleanStack) {
                            // Disallow CLEANSTACK without P2SH, because Bitcoin did.
                            assert!(flags.contains(interpreter::Flags::P2SH));
                            if result_stack.len() == 1 {
                                Ok(true)
                            } else {
                                Err((script::ComponentType::Redeem, script::Error::CleanStack))
                            }
                        } else {
                            Ok(true)
                        }
                    }
                }
            })
        } else {
            Ok(false)
        }
    }
}

/// Additional stack-payload accounting; opcode stack-depth limits always apply.
/// This bounds stack memory when large PQ signatures are duplicated or moved
/// between stacks. The abstraction is kept general for possible future uses
/// that need an additional stack-byte limit.
pub(crate) enum AdditionalStackByteLimit {
    None,
    #[cfg(feature = "pq")]
    Limited(usize),
}

impl AdditionalStackByteLimit {
    fn check(&self, _state: &interpreter::State) -> Result<(), interpreter::Error> {
        match self {
            Self::None => Ok(()),
            #[cfg(feature = "pq")]
            Self::Limited(limit) => _state.check_stack_bytes(*limit),
        }
    }
}

/// Executes parsed instructions with the caller's verifier and stack-byte rule.
/// Parsing limits and final spending conditions remain with the calling path.
pub fn eval<T: Into<opcode::PossiblyBad> + opcode::Evaluable + Clone>(
    mut iter: impl Iterator<Item = Result<T, script::Error>>,
    flags: interpreter::Flags,
    script_code: &script::Code,
    stack: interpreter::Stack<Vec<u8>>,
    checker: &dyn interpreter::SignatureChecker,
    additional_stack_byte_limit: AdditionalStackByteLimit,
) -> Result<interpreter::Stack<Vec<u8>>, script::Error> {
    let initial_state = interpreter::State::initial(stack);
    additional_stack_byte_limit
        .check(&initial_state)
        .map_err(|e| script::Error::Interpreter(None, e))?;
    iter.try_fold(initial_state, |state, elem| {
        elem.and_then(|op| {
            let state = op
                .eval(flags, script_code, checker, state)
                .map_err(|e| script::Error::Interpreter(Some(op.clone().into()), e))?;
            additional_stack_byte_limit
                .check(&state)
                .map_err(|e| script::Error::Interpreter(Some(op.into()), e))?;
            Ok(state)
        })
    })
    .and_then(|final_state| match final_state.vexec.len() {
        0 => Ok(final_state.stack),
        n => Err(script::Error::UnclosedConditional(n)),
    })
}

/// Pre-version-0.6, Bitcoin always counted CHECKMULTISIGs as 20 sigops. With pay-to-script-hash,
/// that changed: CHECKMULTISIGs serialized in script_sigs are counted more accurately, assuming
/// they are of the form ... OP_N CHECKMULTISIG ...
///
/// This mirrors zcashd's `CScript::GetSigOpCount`, which walks the script with `GetOp` and stops
/// only when `GetOp` fails (a push that runs past the end of the script). Bytes this crate
/// classifies as `Disabled` (OP_CAT, ..., and OP_CODESEPARATOR) are read by zcashd's `GetOp` like
/// any other opcode: they perform no signature operation, so they add 0 and counting continues.
/// They are rejected only when a script is *evaluated*, never while counting. Treating one as a
/// hard stop here would under-count sigops relative to zcashd and open a consensus split, so we
/// skip past it.
pub fn sig_op_count<T: Into<opcode::PossiblyBad> + opcode::Evaluable>(
    iter: impl Iterator<Item = Result<T, opcode::Error>>,
    accurate: bool,
) -> u32 {
    let mut n: u32 = 0;
    let mut last_opcode: Option<opcode::PossiblyBad> = None;
    for item in iter {
        match item {
            Ok(op) => {
                n += op.sig_op_count(last_opcode.take());
                last_opcode = accurate.then(|| op.into());
            }
            // A disabled opcode is a valid byte to zcashd's `GetOp`: 0 sigops, keep going, and
            // reset `last_opcode` so a following CHECKMULTISIG is charged the full 20 (zcashd sets
            // `lastOpcode` to the disabled opcode, which is never OP_1..=OP_16).
            Err(opcode::Error::Disabled(_)) => last_opcode = None,
            // `Read` is a truncated push (zcashd's `GetOp` returns false -> stop). `PushSize` is a
            // push declaring more than LargeValue::MAX_SIZE (520) bytes, which cannot occur inside
            // a spendable (<= 520-byte) redeem script, so a hard stop cannot diverge from zcashd on
            // any consensus-valid input.
            Err(opcode::Error::Read { .. } | opcode::Error::PushSize(_)) => break,
        }
    }
    n
}

#[cfg(test)]
mod sig_op_count_tests {
    use alloc::vec::Vec;

    use crate::script::Code;

    /// `sig_op_count` must match zcashd's `CScript::GetSigOpCount` even when the script contains
    /// opcodes this crate buckets under `Disabled` -- in particular OP_CODESEPARATOR (0xab), which
    /// is a normal, valid opcode in zcashd and must not stop the count.
    #[test]
    fn does_not_short_circuit_on_disabled_opcodes() {
        // OP_1 OP_CHECKMULTISIG: accurate counts the OP_N prefix (1); legacy counts 20.
        assert_eq!(Code(Vec::from([0x51u8, 0xae])).sig_op_count(true), 1);
        assert_eq!(Code(Vec::from([0x51u8, 0xae])).sig_op_count(false), 20);

        // OP_CODESEPARATOR (0xab) then OP_CHECKSIG: zcashd keeps counting -> 1.
        assert_eq!(Code(Vec::from([0xabu8, 0xac])).sig_op_count(true), 1);

        // OP_CAT (0x7e, truly disabled) then OP_CHECKSIG: zcashd still keeps counting -> 1.
        assert_eq!(Code(Vec::from([0x7eu8, 0xac])).sig_op_count(true), 1);

        // OP_CODESEPARATOR before 50 x OP_CHECKMULTISIG: each charged 20 (no OP_N prefix),
        // matching zcashd's GetSigOpCount(true) == 1000.
        let mut s = Vec::from([0xabu8]);
        s.extend([0xaeu8; 50]);
        assert_eq!(Code(s).sig_op_count(true), 1000);

        // A truncated push stops the count, like zcashd's GetOp returning false.
        assert_eq!(Code(Vec::from([0xacu8, 0x05, 0x01])).sig_op_count(true), 1);
    }
}

#[cfg(test)]
mod pq_namespace_tests {
    use alloc::vec::Vec;

    use ripemd::Ripemd160;
    use sha2::{Digest, Sha256};

    use crate::{
        interpreter::{Flags, NullSignatureChecker},
        script::{self, Code},
    };

    /// A commitment that is not all zeroes, so it is truthy on the stack.
    const COMMITMENT: [u8; 32] = [7; 32];

    /// The canonical namespace script for `version`: `OP_0 OP_<version> 0x20 <32 bytes>`.
    fn namespace_script(version: u8) -> Vec<u8> {
        let mut bytes = Vec::from([0x00, 0x50 + version, 0x20]);
        bytes.extend_from_slice(&COMMITMENT);
        bytes
    }

    fn eval(sig: Vec<u8>, pub_key: Vec<u8>, flags: Flags) -> Result<bool, script::Error> {
        script::Raw::from_raw_parts(sig, pub_key)
            .eval(flags, &NullSignatureChecker())
            .map_err(|(_, error)| error)
    }

    fn eval_full(
        sig: Vec<u8>,
        pub_key: Vec<u8>,
        flags: Flags,
    ) -> Result<bool, (script::ComponentType, script::Error)> {
        script::Raw::from_raw_parts(sig, pub_key).eval(flags, &NullSignatureChecker())
    }

    /// Without the flag a namespace script is anyone-can-spend. This is the exposure the
    /// flag exists to close, and it is asserted so that it cannot change unnoticed: if the
    /// format ever stops being claimable under legacy rules, this test says so.
    #[test]
    fn a_namespace_script_is_satisfied_by_an_empty_sig_without_the_flag() {
        assert_eq!(
            eval(Vec::new(), namespace_script(1), Flags::empty()),
            Ok(true)
        );
        assert_eq!(eval(Vec::new(), namespace_script(1), Flags::P2SH), Ok(true));
    }

    /// Every version in the namespace is refused, the undefined ones included, so no
    /// version can be swept through this evaluator while it waits to be defined.
    #[test]
    fn the_flag_refuses_every_version_in_the_namespace() {
        for version in 1..=16u8 {
            assert_eq!(
                eval_full(Vec::new(), namespace_script(version), Flags::PqOutputs),
                Err((script::ComponentType::PubKey, script::Error::PqNamespace)),
                "version {version} was not refused"
            );
        }
    }

    /// The refusal comes from the output alone. It must not depend on the scriptSig, or a
    /// spender could pick which error a node reports, and an unparsable sig must not mask
    /// it either.
    #[test]
    fn the_refusal_does_not_depend_on_the_script_sig() {
        let mut long_push = Vec::from([100u8]);
        long_push.extend_from_slice(&[9; 100]);
        let sigs = [
            Vec::new(),
            Vec::from([0x51]),
            long_push,
            Vec::from([0x6a]), // OP_RETURN, so the sig is not push-only
            Vec::from([0x4c]),
            Vec::from([0xff; 40]),
        ];
        for sig in sigs {
            for flags in [
                Flags::PqOutputs,
                Flags::PqOutputs | Flags::SigPushOnly,
                Flags::PqOutputs | Flags::P2SH | Flags::CleanStack,
                Flags::all(),
            ] {
                assert_eq!(
                    eval_full(sig.clone(), namespace_script(1), flags),
                    Err((script::ComponentType::PubKey, script::Error::PqNamespace)),
                    "sig {sig:?} with flags {flags:?} was not refused"
                );
            }
        }
    }

    /// A script that is not byte-exact is not in the namespace, so setting the flag changes
    /// nothing about it. The non-minimal push matters most: it encodes the same commitment
    /// in thirty-six bytes, and an output has to be byte-exact to be recognized.
    #[test]
    fn the_flag_changes_nothing_for_a_near_miss() {
        let canonical = namespace_script(1);
        let mut shorter = Vec::from([0x00, 0x20]);
        shorter.extend_from_slice(&COMMITMENT);
        let mut non_minimal = Vec::from([0x00, 0x51, 0x4c, 0x20]);
        non_minimal.extend_from_slice(&COMMITMENT);
        let mut trailing = canonical.clone();
        trailing.push(0x00);
        let mut wrong_marker = canonical.clone();
        wrong_marker[0] = 0x51;
        let mut version_is_op_0 = canonical.clone();
        version_is_op_0[1] = 0x00;
        let mut version_is_reserved = canonical.clone();
        version_is_reserved[1] = 0x50;
        let mut version_is_nop = canonical.clone();
        version_is_nop[1] = 0x61;
        let mut short_push = canonical.clone();
        short_push[2] = 0x1f;
        let mut long_push_opcode = canonical.clone();
        long_push_opcode[2] = 0x21;

        for near_miss in [
            shorter,
            non_minimal,
            trailing,
            wrong_marker,
            version_is_op_0,
            version_is_reserved,
            version_is_nop,
            short_push,
            long_push_opcode,
            Vec::new(),
            canonical[..canonical.len() - 1].to_vec(),
        ] {
            assert!(
                !script::is_pq_namespace(&near_miss),
                "unexpectedly in the namespace: {near_miss:?}"
            );
            assert_eq!(
                eval(Vec::new(), near_miss.clone(), Flags::P2SH),
                eval(
                    Vec::new(),
                    near_miss.clone(),
                    Flags::P2SH | Flags::PqOutputs
                ),
                "the flag changed the result for {near_miss:?}"
            );
        }
    }

    /// A namespace script wrapped in P2SH is refused too, so the rule is simply that this
    /// evaluator never runs one. Without the flag it is satisfied by no arguments at all,
    /// which is the trap of treating a P2SH-wrapped PQ script as PQ-protected.
    #[test]
    fn the_flag_refuses_a_namespace_redeem_script_under_p2sh() {
        let redeem = namespace_script(1);
        let hash = Ripemd160::digest(Sha256::digest(&redeem));
        let mut pub_key = Vec::from([0xa9u8, 0x14]); // OP_HASH160, push 20
        pub_key.extend_from_slice(&hash);
        pub_key.push(0x87); // OP_EQUAL

        let mut sig = Vec::from([redeem.len() as u8]);
        sig.extend_from_slice(&redeem);

        assert_eq!(eval(sig.clone(), pub_key.clone(), Flags::P2SH), Ok(true));
        assert_eq!(
            eval_full(sig, pub_key, Flags::P2SH | Flags::PqOutputs),
            Err((script::ComponentType::Redeem, script::Error::PqNamespace))
        );
    }

    /// Both two-component entry points funnel through the guard, so the typed one is
    /// refused as well as the raw one.
    #[test]
    fn the_typed_entry_point_is_guarded_too() {
        let pub_key = Code(namespace_script(1)).to_component().unwrap();
        let sig = Code(Vec::new()).to_component().unwrap();
        let script = crate::Script { sig, pub_key };
        assert_eq!(
            script.eval(Flags::PqOutputs, &NullSignatureChecker()),
            Err((script::ComponentType::PubKey, script::Error::PqNamespace))
        );
        assert_eq!(
            script.eval(Flags::empty(), &NullSignatureChecker()),
            Ok(true)
        );
    }

    /// The predicate itself, independent of any evaluation.
    #[test]
    fn is_pq_namespace_accepts_exactly_the_namespace() {
        assert_eq!(script::PQ_NAMESPACE_BYTES, 35);
        for version in 1..=16u8 {
            let script = namespace_script(version);
            assert_eq!(script.len(), script::PQ_NAMESPACE_BYTES);
            assert!(script::is_pq_namespace(&script));
            assert!(Code(script).is_pq_namespace());
        }
        assert!(!script::is_pq_namespace(&[]));
        // A thirty-five-byte script whose version byte is `OP_0` is the marker twice over,
        // not a version, so it is outside the namespace.
        let mut version_is_op_0 = namespace_script(1);
        version_is_op_0[1] = 0x00;
        assert!(!script::is_pq_namespace(&version_is_op_0));
        // One byte either side of the version range.
        for opcode in [0x50u8, 0x61] {
            let mut script = namespace_script(1);
            script[1] = opcode;
            assert!(!script::is_pq_namespace(&script));
        }
    }
}
