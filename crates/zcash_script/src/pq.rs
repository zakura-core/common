//! Explicit, library-only execution of a spending script with large PQ arguments.
//!
//! This is not output validation: the caller must authenticate the supplied spending
//! script and select its verifier. There is no output marker, script commitment,
//! P2SH expansion, address format, or network activation here. Legacy parsers and
//! evaluators keep their existing limits even when this feature is enabled.
//!
//! Only the push-only input has larger items. The spending program uses the existing
//! opcode parser and shared execution loop. These provisional harness limits are not proposed
//! consensus limits; transaction/block work and relay qualification remain separate.
//!
//! Unlike the legacy evaluator, this one requires a canonical input, because ZIP 244 leaves
//! the serialized input out of the transaction identifier and a third party could otherwise
//! edit someone else's spend and keep it valid:
//!
//! - every pushed item, in the input and the script, uses its shortest encoding;
//! - every item read as a number is minimally encoded, so `1` has one spelling;
//! - `IF` and `NOTIF` take only an empty item or `0x01`, so a true `OP_1` cannot become
//!   `OP_2`, nor a false `OP_0` a pushed `0x00` or `0x80` (Bitcoin's `MINIMALIF`);
//! - execution ends with exactly one item on the stack.
//!
//! An item a script reads only for its truth elsewhere, through `VERIFY`, `IFDUP` or as the
//! final result, is not constrained; a script that takes such an item from its input
//! accepts every value of the same truth.
//!
//! The signature checks a spend may run are bounded by its size. A legacy script can check
//! one signature many times, by copying it or through the key trials of `CHECKMULTISIG`,
//! so the number of checks a block demands is not bounded by how many signatures fit in it.
//! Here:
//!
//! - `CHECKMULTISIG` and `CHECKMULTISIGVERIFY` are invalid wherever they appear, and
//!   `CHECKSIGADD` (`0xba`, from Bitcoin's BIP 342) replaces them. A k-of-n gives every key
//!   its own slot, and each slot holds a signature or an empty item, so it runs exactly k
//!   checks for k signatures.
//! - A non-empty signature that fails makes the spend invalid; only an empty one is false.
//! - Every check run with a non-empty signature costs [`CheckBudget`]'s per-check bytes, one
//!   signature's worth, and a spend whose checks cost more than its input is invalid. An
//!   honest check is paid for by its own signature; a copy is a check with no bytes behind
//!   it. So a block can never demand more checks than its size divided by the signature
//!   size, however its scripts are written.

use alloc::vec::Vec;
use core::cell::Cell;

use crate::{
    Opcode,
    interpreter::{self, Flags, SignatureChecker, Stack},
    num,
    opcode::{self, Bad, Control, Evaluable as _, Operation, PossiblyBad, PushValue},
    script, signature,
};

/// `OP_CHECKSIGADD`, which only PQ scripts define. Legacy scripts decode it as an unknown
/// opcode, which fails when executed.
pub const OP_CHECKSIGADD: u8 = 0xba;

/// Provisional serialized authorization bound, including every push and the final
/// pushed script. Room for about thirty full signatures, so it also caps a threshold
/// spend at about thirty signers; it is a byte bound, not a final consensus parameter.
pub const MAX_INPUT_BYTES: usize = 512 * 1024;
/// One SLH-DSA-SHA2-128f signature and its one-byte signing-mode selector.
pub const MAX_PUSH_BYTES: usize = 17_089;
/// Combined primary and alternate stack payload bytes, checked after every opcode.
pub const MAX_STACK_BYTES: usize = 1024 * 1024;
/// Spending scripts retain the existing script-size bound.
pub const MAX_SCRIPT_BYTES: usize = script::Code::MAX_SIZE;

/// Failure before or during PQ script execution.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum Error {
    /// The serialized input exceeds the harness bound.
    #[error("PQ input exceeds {MAX_INPUT_BYTES} bytes")]
    InputSize,
    /// A declared pushed item exceeds the bound, before allocating its payload.
    #[error("PQ push exceeds {MAX_PUSH_BYTES} bytes")]
    PushSize,
    /// A pushed item is encoded with a longer push than its payload needs.
    #[error("PQ input push is not minimally encoded")]
    PushEncoding,
    /// A push length or payload runs past the end of the input.
    #[error("truncated PQ input push")]
    TruncatedPush,
    /// The input contains an instruction other than a push.
    #[error("PQ input must be push-only")]
    NotPushOnly,
    /// The input has no final pushed redeem script.
    #[error("input has no redeem script")]
    MissingScript,
    /// The SLH-DSA context exceeds its standardized maximum length.
    #[error("SLH-DSA context exceeds 255 bytes")]
    ContextSize,
    /// Existing script parsing or execution rules rejected the spending program.
    #[error("spending script failed: {0}")]
    Script(#[from] script::Error),
}

/// The signature checks a spend may run: its input's bytes, one signature's worth per check.
///
/// Only checks given a non-empty signature are charged; an empty one runs no cryptography.
/// The input is the whole serialized spending input, including the revealed script, so a
/// spend can raise its budget only by carrying bytes, at the same rate a real signature
/// would. That is what bounds a block's checks by its size, whatever its scripts do.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckBudget {
    max_checks: usize,
}

impl CheckBudget {
    /// The budget of an input of `input_bytes`, where each check costs `signature_bytes`.
    pub const fn new(input_bytes: usize, signature_bytes: core::num::NonZeroUsize) -> Self {
        Self {
            max_checks: input_bytes / signature_bytes.get(),
        }
    }

    /// The most checks with a non-empty signature a spend under this budget may run.
    pub const fn max_checks(&self) -> usize {
        self.max_checks
    }
}

/// Wraps the caller's checker with the PQ rules every checking opcode shares: a non-empty
/// signature is charged to the budget before any cryptography runs, and must then be valid.
struct Budgeted<'a> {
    inner: &'a dyn SignatureChecker,
    remaining: Cell<usize>,
}

impl SignatureChecker for Budgeted<'_> {
    fn check_signature(
        &self,
        signature: &[u8],
        public_key: &[u8],
        flags: Flags,
        script_code: &script::Code,
    ) -> Result<bool, interpreter::Error> {
        if signature.is_empty() {
            // Free, and false: an empty item is how a key declines to sign. The inner
            // checker still sees it, so a malformed key aborts whether or not it signed.
            return self
                .inner
                .check_signature(signature, public_key, flags, script_code)
                .map(|_| false);
        }
        // Charge first, so a check over budget never reaches the cryptography.
        let remaining = self
            .remaining
            .get()
            .checked_sub(1)
            .ok_or(interpreter::Error::PqCheckBudget)?;
        self.remaining.set(remaining);
        if self
            .inner
            .check_signature(signature, public_key, flags, script_code)?
        {
            Ok(true)
        } else {
            Err(interpreter::Error::PqNullFail)
        }
    }

    fn check_sig(
        &self,
        signature: &signature::Decoded,
        public_key: &[u8],
        script_code: &script::Code,
    ) -> bool {
        self.inner.check_sig(signature, public_key, script_code)
    }

    fn check_lock_time(&self, lock_time: i64) -> bool {
        self.inner.check_lock_time(lock_time)
    }
}

/// An instruction of a PQ script: a shared opcode, or one only PQ scripts define.
///
/// Mapping at parse time leaves the shared evaluation loop, opcode tables and legacy
/// decoding untouched: `0xba` stays an unknown opcode everywhere else.
#[derive(Clone)]
enum Instruction {
    Shared(PossiblyBad),
    CheckSigAdd,
}

impl From<Instruction> for PossiblyBad {
    fn from(instruction: Instruction) -> Self {
        match instruction {
            Instruction::Shared(op) => op,
            Instruction::CheckSigAdd => PossiblyBad::Bad(Bad::Unknown(OP_CHECKSIGADD)),
        }
    }
}

impl opcode::Evaluable for Instruction {
    fn byte_len(&self) -> usize {
        match self {
            Self::Shared(op) => op.byte_len(),
            Self::CheckSigAdd => 1,
        }
    }

    fn to_bytes(&self) -> Vec<u8> {
        match self {
            Self::Shared(op) => op.to_bytes(),
            Self::CheckSigAdd => alloc::vec![OP_CHECKSIGADD],
        }
    }

    /// Multisig is refused here, so wherever it appears, executed or not, as a disabled
    /// opcode is.
    fn restrict(op: PossiblyBad) -> Result<Self, script::Error> {
        match op {
            PossiblyBad::Bad(Bad::Unknown(OP_CHECKSIGADD)) => Ok(Self::CheckSigAdd),
            PossiblyBad::Good(Opcode::Operation(
                Operation::OP_CHECKMULTISIG | Operation::OP_CHECKMULTISIGVERIFY,
            )) => Err(script::Error::Interpreter(
                Some(op),
                interpreter::Error::PqMultisig,
            )),
            op => Ok(Self::Shared(op)),
        }
    }

    fn eval(
        &self,
        flags: Flags,
        script: &script::Code,
        checker: &dyn SignatureChecker,
        mut state: interpreter::State,
    ) -> Result<interpreter::State, interpreter::Error> {
        match self {
            Self::Shared(
                op @ PossiblyBad::Good(Opcode::Control(Control::OP_IF | Control::OP_NOTIF)),
            ) => {
                // Only an executed IF reads its argument; a missing one is the shared
                // evaluator's error to report.
                if interpreter::should_exec(&state.vexec)
                    && state
                        .stack
                        .rget(0)
                        .is_ok_and(|argument| !matches!(argument.as_slice(), [] | [1]))
                {
                    return Err(interpreter::Error::PqMinimalIf);
                }
                op.eval(flags, script, checker, state)
            }
            Self::Shared(op) => op.eval(flags, script, checker, state),
            Self::CheckSigAdd => {
                // An operation like any other, counted whether or not its branch executes.
                state.increment_op_count(1)?;
                if interpreter::should_exec(&state.vexec) {
                    check_sig_add(flags, script, checker, &mut state.stack)?;
                }
                Ok(state)
            }
        }
    }

    fn extract_push_value(&self) -> Result<&PushValue, script::Error> {
        match self {
            Self::Shared(op) => op.extract_push_value(),
            Self::CheckSigAdd => Err(script::Error::Interpreter(
                Some(self.clone().into()),
                interpreter::Error::BadOpcode,
            )),
        }
    }

    fn sig_op_count(&self, last_opcode: Option<PossiblyBad>) -> u32 {
        match self {
            Self::Shared(op) => op.sig_op_count(last_opcode),
            Self::CheckSigAdd => 1,
        }
    }
}

/// `(sig n pubkey -- n')`: checks `sig` against `pubkey` and adds one to `n` when it signed.
///
/// An empty `sig` leaves `n` unchanged and runs no cryptography. A non-empty one has to be
/// valid, as [`Budgeted`] enforces, so the count it returns is exactly the number of
/// signatures supplied. `n` is a number of at most four bytes, as for any arithmetic.
fn check_sig_add(
    flags: Flags,
    script: &script::Code,
    checker: &dyn SignatureChecker,
    stack: &mut Stack<Vec<u8>>,
) -> Result<(), interpreter::Error> {
    stack.check_len(3)?;
    let public_key = stack.pop()?;
    let count = num::parse(&stack.pop()?, flags.contains(Flags::MinimalData), None)?;
    let signature = stack.pop()?;
    let signed = checker.check_signature(&signature, &public_key, flags, script)?;
    stack.push(num::serialize(count + i64::from(signed)));
    Ok(())
}

/// Counts the signature checks a PQ script can run: every `CHECKSIG`, `CHECKSIGVERIFY` and
/// `CHECKSIGADD`, in every branch.
///
/// Scripts have no loops and these scripts have no multisig, so each of these opcodes runs at
/// most once and this is an upper bound, not an estimate. The legacy counter reads `0xba` as
/// an unknown opcode and counts nothing for it, so it must not be used for a PQ script.
/// Counting stops where parsing does; such a script cannot be spent.
pub fn signature_check_count(program: &script::Code) -> u32 {
    let mut count = 0;
    for instruction in program.parse() {
        match instruction {
            Ok(PossiblyBad::Good(Opcode::Operation(
                Operation::OP_CHECKSIG | Operation::OP_CHECKSIGVERIFY,
            )))
            | Ok(PossiblyBad::Bad(Bad::Unknown(OP_CHECKSIGADD))) => count += 1,
            Ok(_) | Err(opcode::Error::Disabled(_)) => {}
            Err(opcode::Error::Read { .. } | opcode::Error::PushSize(_)) => break,
        }
    }
    count
}

// Large pushes borrow their payload; small integer opcodes store one decoded byte.
// Preliminary scanning never allocates an argument stack or copies pushed payloads.
enum PushedValue<'a> {
    Bytes(&'a [u8]),
    Small(u8),
}

impl PushedValue<'_> {
    fn as_bytes(&self) -> &[u8] {
        match self {
            Self::Bytes(bytes) => bytes,
            Self::Small(value) => core::slice::from_ref(value),
        }
    }
}

fn read_push(mut bytes: &[u8], limit: usize) -> Result<(PushedValue<'_>, &[u8]), Error> {
    let (&opcode, rest) = bytes.split_first().ok_or(Error::TruncatedPush)?;
    bytes = rest;
    let value = match opcode {
        0x00 => PushedValue::Bytes(&[]),
        0x4f => PushedValue::Small(0x81),
        0x51..=0x60 => PushedValue::Small(opcode - 0x50),
        0x01..=0x4e => {
            let length = match opcode {
                0x01..=0x4b => usize::from(opcode),
                _ => {
                    let width = match opcode {
                        0x4c => 1,
                        0x4d => 2,
                        _ => 4,
                    };
                    let (prefix, rest) =
                        bytes.split_at_checked(width).ok_or(Error::TruncatedPush)?;
                    bytes = rest;
                    let mut encoded = [0; 4];
                    encoded[..width].copy_from_slice(prefix);
                    usize::try_from(u32::from_le_bytes(encoded)).map_err(|_| Error::PushSize)?
                }
            };
            if length > limit {
                return Err(Error::PushSize);
            }
            let (value, rest) = bytes.split_at_checked(length).ok_or(Error::TruncatedPush)?;
            bytes = rest;
            if !is_minimal_push(opcode, value) {
                return Err(Error::PushEncoding);
            }
            PushedValue::Bytes(value)
        }
        _ => return Err(Error::NotPushOnly),
    };
    Ok((value, bytes))
}

/// Whether this payload has no shorter encoding, mirroring `LargeValue::is_minimal_push`
/// and the legacy `MinimalData` rule: a wider length prefix than the payload needs, or a
/// one-byte payload that `OP_1NEGATE` or `OP_1`..`OP_16` would have pushed, is not minimal.
fn is_minimal_push(opcode: u8, value: &[u8]) -> bool {
    match opcode {
        0x4c => 0x4c <= value.len(),
        0x4d => 0x100 <= value.len(),
        0x4e => 0x10000 <= value.len(),
        // A direct push. Note that a single zero byte is minimal: `OP_0` pushes no bytes.
        _ => match value {
            [byte] => *byte != 0x81 && (*byte < 1 || 16 < *byte),
            _ => true,
        },
    }
}

fn arguments(mut bytes: &[u8]) -> Result<Stack<Vec<u8>>, Error> {
    if bytes.len() > MAX_INPUT_BYTES {
        return Err(Error::InputSize);
    }
    let mut stack = Stack::new();
    while !bytes.is_empty() {
        let (value, rest) = read_push(bytes, MAX_PUSH_BYTES)?;
        bytes = rest;
        if stack.len() == interpreter::MAX_STACK_DEPTH {
            return Err(
                script::Error::Interpreter(None, interpreter::Error::StackSize(None)).into(),
            );
        }
        stack.push(value.as_bytes().to_vec());
    }
    Ok(stack)
}

/// A nonexecuting, allocation-free scan of push-only input and its final item.
///
/// This is preliminary parsing, not authorization or legacy validation. The full
/// input is bounded by [`MAX_INPUT_BYTES`]; payload lengths must fit that input.
/// No PQ argument-size or stack-depth rules are selected until the caller has
/// matched the final item against the output's commitment.
pub struct SpendingInput<'a> {
    arguments: &'a [u8],
    redeem_script: PushedValue<'a>,
    pushes: usize,
    len: usize,
}

impl<'a> SpendingInput<'a> {
    /// Locates the final pushed value without executing any input instructions.
    pub fn scan(input: &'a [u8]) -> Result<Self, Error> {
        if input.len() > MAX_INPUT_BYTES {
            return Err(Error::InputSize);
        }
        let mut remaining = input;
        let mut last = None;
        let mut pushes = 0;
        while !remaining.is_empty() {
            let arguments = &input[..input.len() - remaining.len()];
            let (value, rest) = read_push(remaining, MAX_INPUT_BYTES)?;
            remaining = rest;
            last = Some((arguments, value));
            pushes += 1;
        }
        let (arguments, redeem_script) = last.ok_or(Error::MissingScript)?;
        Ok(Self {
            arguments,
            redeem_script,
            pushes,
            len: input.len(),
        })
    }

    /// The whole serialized input's length, revealed script included: what a
    /// [`CheckBudget`] for this spend is made from.
    pub fn input_bytes(&self) -> usize {
        self.len
    }

    /// Returns the final pushed item, the script the output commits to.
    pub fn redeem_script(&self) -> &[u8] {
        self.redeem_script.as_bytes()
    }

    /// Returns the original argument bytes after checking PQ envelope bounds.
    ///
    /// Call only after authenticating the redeem script and selecting PQ. The
    /// final script counts towards both input size and stack depth. The returned
    /// arguments still require the PQ evaluator's per-item and execution checks.
    pub fn pq_arguments(&self) -> Result<&'a [u8], Error> {
        if self.redeem_script().len() > MAX_SCRIPT_BYTES {
            return Err(script::Error::ScriptSize(Some(self.redeem_script().len())).into());
        }
        if self.pushes > interpreter::MAX_STACK_DEPTH {
            return Err(
                script::Error::Interpreter(None, interpreter::Error::StackSize(None)).into(),
            );
        }
        Ok(self.arguments)
    }
}

/// Parses bounded serialized arguments, then executes the authenticated program.
///
/// The caller selects the verifier; no script bytes can select or downgrade it.
/// This executes the supplied program directly, without an outer P2SH evaluation.
/// A false final stack item returns `Ok(false)`; parsing/encoding errors, failed VERIFY
/// operations, a failed non-empty signature and a check over `budget` abort. Unlike the
/// legacy evaluator, a final stack holding anything other than exactly one item aborts, so
/// leftover or prepended arguments are rejected rather than ignored. Non-minimal pushes in
/// the input abort before execution. Absolute locktimes use the caller's checker. No
/// relay-policy flags are added.
///
/// `budget` should come from the whole serialized input, which `input` here (the arguments
/// alone) is not; see [`SpendingInput::input_bytes`].
pub fn eval_script(
    input: &[u8],
    program: &script::Code,
    checker: &dyn SignatureChecker,
    budget: CheckBudget,
) -> Result<bool, Error> {
    // Bound both byte streams before allocating argument values or executing anything.
    if input.len() > MAX_INPUT_BYTES {
        return Err(Error::InputSize);
    }
    if program.0.len() > script::Code::MAX_SIZE {
        return Err(script::Error::ScriptSize(Some(program.0.len())).into());
    }
    let checker = Budgeted {
        inner: checker,
        remaining: Cell::new(budget.max_checks()),
    };
    let stack = script::iter::eval(
        program.parse().map(|instruction| {
            instruction
                .map_err(script::Error::Opcode)
                .and_then(Instruction::restrict)
        }),
        // Locktimes have to mean what they say, and numbers and the script's own pushes
        // have one encoding each. Every other legacy flag is either specific to ECDSA or
        // multisig, relay policy, or a rule this evaluator already applies unconditionally.
        Flags::CHECKLOCKTIMEVERIFY | Flags::MinimalData,
        program,
        arguments(input)?,
        &checker,
        script::iter::AdditionalStackByteLimit::Limited(MAX_STACK_BYTES),
    )?;
    // Exactly one item, so neither an extra argument nor an unconsumed result can be
    // ignored. The legacy evaluator applies this only as the optional `CleanStack` policy.
    if stack.len() != 1 {
        return Err(script::Error::CleanStack.into());
    }
    Ok(stack
        .last()
        .is_ok_and(|item| interpreter::cast_to_bool(item)))
}

#[cfg(test)]
mod check_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::NullSignatureChecker;

    /// No check with a non-empty signature may run.
    const NO_CHECKS: CheckBudget = CheckBudget::new(0, core::num::NonZeroUsize::MIN);

    /// The shortest encoding of a `length`-byte payload, as the PQ rules require.
    fn push(length: usize) -> Vec<u8> {
        let mut input = if length < 0x4c {
            vec![length as u8]
        } else if length < 0x100 {
            vec![0x4c, length as u8]
        } else if length < 0x10000 {
            let mut bytes = vec![0x4d];
            bytes.extend_from_slice(&(length as u16).to_le_bytes());
            bytes
        } else {
            let mut bytes = vec![0x4e];
            bytes.extend_from_slice(&(length as u32).to_le_bytes());
            bytes
        };
        let prefix = input.len();
        input.resize(prefix + length, 1);
        input
    }

    /// The number of items an ordinary legacy run of this program would leave behind.
    fn final_items(input: &[u8], program: &script::Code) -> Option<usize> {
        script::iter::eval(
            program
                .parse()
                .map(|instruction| instruction.map_err(script::Error::Opcode)),
            Flags::CHECKLOCKTIMEVERIFY,
            program,
            arguments(input).ok()?,
            &NullSignatureChecker(),
            script::iter::AdditionalStackByteLimit::None,
        )
        .ok()
        .map(|stack| stack.len())
    }

    #[test]
    fn preliminary_scan_borrows_payloads_and_decodes_small_pushes() {
        let mut input = push(MAX_PUSH_BYTES);
        let prefix = input.len();
        input.extend_from_slice(&[0x02, 0x51, 0x75]);
        let scanned = SpendingInput::scan(&input).unwrap();
        assert!(core::ptr::eq(
            scanned.redeem_script().as_ptr(),
            input[prefix + 1..].as_ptr()
        ));
        assert_eq!(scanned.pq_arguments().unwrap(), &input[..prefix]);
        for (opcode, expected) in [
            (0x00, &[][..]),
            (0x4f, &[0x81][..]),
            (0x51, &[1][..]),
            (0x60, &[16][..]),
        ] {
            let bytes = [opcode];
            assert_eq!(
                SpendingInput::scan(&bytes).unwrap().redeem_script(),
                expected
            );
        }
        let over_argument_limit = push(MAX_PUSH_BYTES + 1);
        assert!(SpendingInput::scan(&over_argument_limit).is_ok());
        assert!(matches!(
            SpendingInput::scan(&[0x4e, 255, 255, 255, 255]),
            Err(Error::PushSize)
        ));
    }

    #[test]
    fn serialized_push_bounds_and_truncation() {
        let drop_then_true = script::Code(vec![0x75, 0x51]);
        let check =
            |input: &[u8]| eval_script(input, &drop_then_true, &NullSignatureChecker(), NO_CHECKS);
        assert_eq!(check(&push(MAX_PUSH_BYTES)), Ok(true));
        assert_eq!(check(&push(MAX_PUSH_BYTES + 1)), Err(Error::PushSize));
        assert_eq!(check(&[0x4e, 255, 255, 255, 255]), Err(Error::PushSize));
        for input in [&[0x4d][..], &[0x4d, 1], &[0x4d, 1, 0]] {
            assert_eq!(check(input), Err(Error::TruncatedPush));
        }
        assert_eq!(check(&vec![0; MAX_INPUT_BYTES + 1]), Err(Error::InputSize));
        assert_eq!(check(&[0x76]), Err(Error::NotPushOnly));
    }

    #[test]
    fn longer_than_necessary_push_encodings_are_rejected() {
        let drop_then_true = script::Code(vec![0x75, 0x51]);
        let check =
            |input: &[u8]| eval_script(input, &drop_then_true, &NullSignatureChecker(), NO_CHECKS);
        // The same single payload byte, encoded four ways. Only the direct push is minimal.
        assert_eq!(check(&[0x01, 0x20]), Ok(true));
        for wider in [
            vec![0x4c, 1, 0x20],
            vec![0x4d, 1, 0, 0x20],
            vec![0x4e, 1, 0, 0, 0, 0x20],
        ] {
            assert_eq!(check(&wider), Err(Error::PushEncoding));
            assert_eq!(
                SpendingInput::scan(&wider).map(|_| ()),
                Err(Error::PushEncoding),
                "a non-minimal push must not even reach commitment authentication"
            );
        }
        // A one-byte payload that a small-integer opcode would have pushed.
        for value in [0x01, 0x10, 0x81] {
            assert_eq!(check(&[0x01, value]), Err(Error::PushEncoding));
        }
        // A single zero byte is minimal: OP_0 pushes an empty item, not a zero byte.
        assert_eq!(check(&[0x01, 0x00]), Ok(true));
        // Boundaries: each wider prefix becomes minimal exactly at its own length.
        assert_eq!(check(&push(0x4b)), Ok(true));
        assert_eq!(check(&push(0x4c)), Ok(true));
        assert_eq!(check(&push(0xff)), Ok(true));
        assert_eq!(check(&push(0x100)), Ok(true));
        let mut barely_short = vec![0x4c, 0x4b];
        barely_short.resize(2 + 0x4b, 1);
        assert_eq!(check(&barely_short), Err(Error::PushEncoding));
        let mut two_byte_prefix = vec![0x4d, 0xff, 0x00];
        two_byte_prefix.resize(3 + 0xff, 1);
        assert_eq!(check(&two_byte_prefix), Err(Error::PushEncoding));
    }

    #[test]
    fn extra_and_leftover_stack_items_are_rejected() {
        let true_script = script::Code(vec![0x51]);
        let check = |input: &[u8], program: &script::Code| {
            eval_script(input, program, &NullSignatureChecker(), NO_CHECKS)
        };
        let clean_stack = Err(Error::Script(script::Error::CleanStack));
        assert_eq!(check(&[], &true_script), Ok(true));
        // An argument the program never consumes, which the legacy evaluator would ignore.
        assert_eq!(check(&[0x51], &true_script), clean_stack);
        assert_eq!(check(&[0x00], &true_script), clean_stack);
        // Prepending a junk push to someone else's otherwise valid input.
        assert_eq!(check(&[0x51], &script::Code(vec![])), Ok(true));
        assert_eq!(check(&[0x51, 0x51], &script::Code(vec![])), clean_stack);
        // An empty final stack is rejected, where the legacy evaluator returns false.
        assert_eq!(check(&[], &script::Code(vec![])), clean_stack);
        assert_eq!(check(&[0x51], &script::Code(vec![0x75])), clean_stack);
        // A result left beside a consumed argument.
        assert_eq!(check(&[0x51, 0x51], &script::Code(vec![0x75])), Ok(true));
    }

    #[test]
    fn ordinary_programs_keep_legacy_results_and_errors() {
        let mut programs = vec![
            vec![],
            vec![0],
            vec![0x51],
            vec![0x75],    // DROP can underflow or expose a different final value.
            vec![0, 0x69], // A false VERIFY aborts.
            vec![0x51, 0x63, 0x51], // An unclosed conditional aborts.
            vec![0, 0x63, 0, 0x67, 0x51, 0x68], // ELSE selects the true branch.
            vec![0, 0x63, 0x7e, 0x68, 0x51], // Disabled opcodes abort even in inactive branches.
            vec![0x4d, 2, 0, 1], // Truncated program push.
            push(521),     // Larger PQ arguments do not relax pushes inside the program.
        ];
        for count in [201, 202] {
            let mut program = vec![0x61; count]; // NOP at either side of the operation limit.
            program.push(0x51);
            programs.push(program);
        }
        for program in programs {
            for input in [vec![], vec![0], vec![0x51], vec![0, 0x51], push(520)] {
                let legacy = script::Raw::from_raw_parts(input.clone(), program.clone())
                    .eval(Flags::CHECKLOCKTIMEVERIFY, &NullSignatureChecker())
                    .map_err(|(_, error)| Error::Script(error));
                // Identical results and errors, except that the PQ rules additionally
                // require a single final item where the legacy evaluator ignores the rest.
                let expected = match final_items(&input, &script::Code(program.clone())) {
                    Some(1) => legacy,
                    Some(_) => Err(Error::Script(script::Error::CleanStack)),
                    None => legacy,
                };
                assert_eq!(
                    eval_script(
                        &input,
                        &script::Code(program.clone()),
                        &NullSignatureChecker(),
                        NO_CHECKS,
                    ),
                    expected,
                    "input {input:?}, program {program:?}",
                );
            }
        }
    }

    #[test]
    fn shared_signature_operation_budget_stops_before_the_extra_check() {
        struct CountingChecker(core::cell::Cell<usize>);
        impl interpreter::SignatureChecker for CountingChecker {
            fn check_signature(
                &self,
                _: &[u8],
                _: &[u8],
                _: Flags,
                _: &script::Code,
            ) -> Result<bool, interpreter::Error> {
                self.0.set(self.0.get() + 1);
                Ok(true)
            }
            fn check_sig(&self, _: &crate::signature::Decoded, _: &[u8], _: &script::Code) -> bool {
                unreachable!()
            }
            fn check_lock_time(&self, _: i64) -> bool {
                unreachable!()
            }
        }
        for count in [201, 202] {
            let checker = CountingChecker(core::cell::Cell::new(0));
            let code = script::Code([0, 0, 0xac].repeat(count));
            let result = eval_script(&[], &code, &checker, NO_CHECKS);
            if count == 201 {
                // Each check leaves its own result behind, which the clean-stack rule
                // rejects only after the budget has allowed exactly 201 operations.
                assert_eq!(result, Err(Error::Script(script::Error::CleanStack)));
            } else {
                assert!(matches!(
                    result,
                    Err(Error::Script(script::Error::Interpreter(
                        _,
                        interpreter::Error::OpCount
                    )))
                ));
            }
            assert_eq!(checker.0.get(), 201);
        }
    }

    #[test]
    fn complete_serialized_input_fits_at_the_byte_boundary() {
        let mut input = Vec::new();
        // Reserve a final empty redeem-script push, independently of argument size.
        while input.len() + MAX_PUSH_BYTES + 10 < MAX_INPUT_BYTES {
            input.extend(push(MAX_PUSH_BYTES));
        }
        // One filler push, then the one-byte empty push that ends the input exactly.
        input.extend(push(MAX_INPUT_BYTES - input.len() - 1 - 3));
        input.extend(push(0));
        assert_eq!(input.len(), MAX_INPUT_BYTES);
        let scanned = SpendingInput::scan(&input).unwrap();
        assert!(scanned.pq_arguments().is_ok());
        // Drop down to a single item, since every pushed argument stays on the stack.
        let program = script::Code(vec![0x75; scanned.pushes - 1]);
        assert_eq!(
            eval_script(&input, &program, &NullSignatureChecker(), NO_CHECKS),
            Ok(true)
        );
        input.push(0);
        assert!(matches!(SpendingInput::scan(&input), Err(Error::InputSize)));
        assert_eq!(
            eval_script(&input, &program, &NullSignatureChecker(), NO_CHECKS),
            Err(Error::InputSize)
        );
    }

    #[test]
    fn additional_stack_byte_limit_counts_main_and_alternate_payloads() {
        let input = push(MAX_PUSH_BYTES);
        let copies = MAX_STACK_BYTES / MAX_PUSH_BYTES;
        let duplicates = vec![0x76; copies - 1]; // DUP up to the byte bound.
        let mut program = duplicates.clone();
        program.extend(vec![0x75; copies - 1]); // DROP back down to a single item.
        assert_eq!(
            eval_script(
                &input,
                &script::Code(program),
                &NullSignatureChecker(),
                NO_CHECKS
            ),
            Ok(true)
        );
        let mut program = duplicates;
        program.push(0x6b); // TOALTSTACK must not free the payload budget.
        program.extend_from_slice(&[0x76, 0x6a]); // DUP crosses the bound before RETURN.
        assert!(matches!(
            eval_script(
                &input,
                &script::Code(program),
                &NullSignatureChecker(),
                NO_CHECKS
            ),
            Err(Error::Script(script::Error::Interpreter(
                Some(_),
                interpreter::Error::StackBytes
            )))
        ));
        assert!(
            eval_script(
                &vec![0; 1001],
                &script::Code(vec![0x51]),
                &NullSignatureChecker(),
                NO_CHECKS,
            )
            .is_err()
        );
    }

    #[test]
    fn a_third_party_cannot_respell_an_if_argument_or_a_number() {
        let error = |input: &[u8], program: &[u8]| match eval_script(
            input,
            &script::Code(program.to_vec()),
            &NullSignatureChecker(),
            NO_CHECKS,
        ) {
            Err(Error::Script(script::Error::Interpreter(_, error))) => Some(error),
            _ => None,
        };
        // IF 1 ELSE 1 ENDIF: both branches pass, so under legacy rules any argument does,
        // and a third party could respell the spender's choice without invalidating it.
        for opcode in [0x63, 0x64] {
            let program = [opcode, 0x51, 0x67, 0x51, 0x68];
            for canonical in [&[0x00][..], &[0x51]] {
                let run = eval_script(
                    canonical,
                    &script::Code(program.to_vec()),
                    &NullSignatureChecker(),
                    NO_CHECKS,
                );
                assert_eq!(run, Ok(true));
            }
            for respelled in [
                &[0x52][..],
                &[0x60],
                &[0x4f],
                &[0x01, 0x00],
                &[0x01, 0x80],
                &[0x02, 0x01, 0x00],
            ] {
                assert_eq!(
                    error(respelled, &program),
                    Some(interpreter::Error::PqMinimalIf),
                    "{opcode:#x} with {respelled:?}"
                );
            }
        }
        // An IF that does not execute reads nothing, so its would-be argument is not judged.
        assert_eq!(
            eval_script(
                &[],
                &script::Code(vec![0x00, 0x63, 0x52, 0x63, 0x68, 0x68, 0x51]),
                &NullSignatureChecker(),
                NO_CHECKS
            ),
            Ok(true)
        );
        // A number from the input has one spelling: 1 is OP_1, not 0x01 0x00.
        let one_equals = [0x51, 0x9c];
        assert_eq!(
            eval_script(
                &[0x51],
                &script::Code(one_equals.to_vec()),
                &NullSignatureChecker(),
                NO_CHECKS
            ),
            Ok(true)
        );
        assert!(matches!(
            error(&[0x02, 0x01, 0x00], &one_equals),
            Some(interpreter::Error::Num(_))
        ));
        // And the committed script spells its own pushes the shortest way.
        assert_eq!(
            error(&[], &[0x4c, 0x01, 0x20, 0x75, 0x51]),
            Some(interpreter::Error::MinimalData)
        );
    }
}
