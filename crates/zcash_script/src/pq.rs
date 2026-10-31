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

use alloc::vec::Vec;

use crate::{
    interpreter::{self, Flags, SignatureChecker, Stack},
    script,
};

/// Provisional serialized authorization bound, including pushes and the P2SH redeem
/// script. Accommodates 20 full signatures and multiple checking instructions; it
/// is a byte bound, not a signature-count limit or a final consensus parameter.
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
            PushedValue::Bytes(value)
        }
        _ => return Err(Error::NotPushOnly),
    };
    Ok((value, bytes))
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
/// authenticated the redeem script and recognized its execution identifier.
pub struct SpendingInput<'a> {
    arguments: &'a [u8],
    redeem_script: PushedValue<'a>,
    pushes: usize,
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
        })
    }

    /// Returns the complete redeem script, including any execution identifier.
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
/// A false final stack item returns `Ok(false)`; parsing/encoding errors and failed
/// VERIFY operations abort. Empty final stacks return false, like the legacy evaluator.
/// Absolute locktime checks use the caller's checker. No relay-policy flags are added.
pub fn eval_script(
    input: &[u8],
    program: &script::Code,
    checker: &dyn SignatureChecker,
) -> Result<bool, Error> {
    // Bound both byte streams before allocating argument values or executing anything.
    if input.len() > MAX_INPUT_BYTES {
        return Err(Error::InputSize);
    }
    if program.0.len() > script::Code::MAX_SIZE {
        return Err(script::Error::ScriptSize(Some(program.0.len())).into());
    }
    let stack = script::iter::eval(
        program
            .parse()
            .map(|instruction| instruction.map_err(script::Error::Opcode)),
        Flags::CHECKLOCKTIMEVERIFY,
        program,
        arguments(input)?,
        checker,
        script::iter::AdditionalStackByteLimit::Limited(MAX_STACK_BYTES),
    )?;
    Ok(stack
        .last()
        .is_ok_and(|item| interpreter::cast_to_bool(item)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::NullSignatureChecker;

    fn push(length: usize) -> Vec<u8> {
        let mut input = vec![0x4e];
        input.extend_from_slice(&(length as u32).to_le_bytes());
        input.resize(5 + length, 1);
        input
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
        let check = |input: &[u8]| eval_script(input, &drop_then_true, &NullSignatureChecker());
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
                assert_eq!(
                    eval_script(
                        &input,
                        &script::Code(program.clone()),
                        &NullSignatureChecker()
                    ),
                    legacy,
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
            let result = eval_script(&[], &code, &checker);
            if count == 201 {
                assert_eq!(result, Ok(true));
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
        input.extend(push(MAX_INPUT_BYTES - input.len() - 10));
        input.extend(push(0));
        assert_eq!(input.len(), MAX_INPUT_BYTES);
        assert!(SpendingInput::scan(&input).unwrap().pq_arguments().is_ok());
        assert_eq!(
            eval_script(&input, &script::Code(vec![0x51]), &NullSignatureChecker()),
            Ok(true)
        );
        input.push(0);
        assert!(matches!(SpendingInput::scan(&input), Err(Error::InputSize)));
        assert_eq!(
            eval_script(&input, &script::Code(vec![0x51]), &NullSignatureChecker()),
            Err(Error::InputSize)
        );
    }

    #[test]
    fn additional_stack_byte_limit_counts_main_and_alternate_payloads() {
        let input = push(MAX_PUSH_BYTES);
        let copies = MAX_STACK_BYTES / MAX_PUSH_BYTES;
        let mut program = vec![0x76; copies - 1]; // DUP up to the byte bound.
        assert_eq!(
            eval_script(
                &input,
                &script::Code(program.clone()),
                &NullSignatureChecker()
            ),
            Ok(true)
        );
        program.push(0x6b); // TOALTSTACK must not free the payload budget.
        program.extend_from_slice(&[0x76, 0x6a]); // DUP crosses the bound before RETURN.
        assert!(matches!(
            eval_script(&input, &script::Code(program), &NullSignatureChecker()),
            Err(Error::Script(script::Error::Interpreter(
                Some(_),
                interpreter::Error::StackBytes
            )))
        ));
        assert!(
            eval_script(
                &vec![0; 1001],
                &script::Code(vec![0x51]),
                &NullSignatureChecker()
            )
            .is_err()
        );
    }
}
