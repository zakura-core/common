//! Explicit, library-only execution of a spending script with large PQ arguments.
//!
//! This is not output validation: the caller must authenticate the supplied spending
//! script and select its verifier. There is no output marker, script commitment,
//! P2SH expansion, address format, or network activation here. Legacy parsers and
//! evaluators keep their existing limits even when this feature is enabled.
//!
//! Only the push-only input has larger items. The spending program uses the existing
//! opcode parser and interpreter. These provisional harness limits are not proposed
//! consensus limits; multisigner/resource qualification is a later increment.

use alloc::vec::Vec;

use crate::{
    interpreter::{self, Flags, SignatureChecker, Stack, State},
    opcode::Evaluable,
    script,
};

/// Enough for two signature arguments and small auxiliary arguments in the harness.
pub const MAX_INPUT_BYTES: usize = 32 * 1024;
/// One SLH-DSA-SHA2-192s signature and its one-byte signing-mode selector.
pub const MAX_PUSH_BYTES: usize = 16_225;
/// Combined primary and alternate stack payload bytes, checked after every opcode.
pub const MAX_STACK_BYTES: usize = 64 * 1024;

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
    /// The SLH-DSA context exceeds its standardized maximum length.
    #[error("SLH-DSA context exceeds 255 bytes")]
    ContextSize,
    /// Existing script parsing or execution rules rejected the spending program.
    #[error("spending script failed: {0}")]
    Script(#[from] script::Error),
}

fn arguments(mut bytes: &[u8]) -> Result<Stack<Vec<u8>>, Error> {
    if bytes.len() > MAX_INPUT_BYTES {
        return Err(Error::InputSize);
    }
    let mut stack = Stack::new();
    while let Some((&opcode, rest)) = bytes.split_first() {
        bytes = rest;
        let value = match opcode {
            0x00 => Vec::new(),
            0x4f => vec![0x81],
            0x51..=0x60 => vec![opcode - 0x50],
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
                if length > MAX_PUSH_BYTES {
                    return Err(Error::PushSize);
                }
                let (value, rest) = bytes.split_at_checked(length).ok_or(Error::TruncatedPush)?;
                bytes = rest;
                value.to_vec()
            }
            _ => return Err(Error::NotPushOnly),
        };
        if stack.len() == interpreter::MAX_STACK_DEPTH {
            return Err(
                script::Error::Interpreter(None, interpreter::Error::StackSize(None)).into(),
            );
        }
        stack.push(value);
    }
    Ok(stack)
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
    let mut state = State::initial(arguments(input)?);
    state
        .check_stack_bytes(MAX_STACK_BYTES)
        .map_err(|e| script::Error::Interpreter(None, e))?;
    for instruction in program.parse() {
        let instruction = instruction.map_err(script::Error::Opcode)?;
        state = instruction
            .eval(Flags::CHECKLOCKTIMEVERIFY, program, checker, state)
            .map_err(|e| script::Error::Interpreter(Some(instruction.clone()), e))?;
        state
            .check_stack_bytes(MAX_STACK_BYTES)
            .map_err(|e| script::Error::Interpreter(Some(instruction), e))?;
    }
    if state.vexec.len() != 0 {
        return Err(script::Error::UnclosedConditional(state.vexec.len()).into());
    }
    Ok(state
        .stack
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
    fn stack_bound_includes_duplicates_and_alternate_stack() {
        let input = push(MAX_PUSH_BYTES);
        // Four copies fit. Moving one to the alternate stack must not free its budget.
        let program = script::Code(vec![0x76, 0x76, 0x76, 0x6b, 0x76]);
        assert!(matches!(
            eval_script(&input, &program, &NullSignatureChecker()),
            Err(Error::Script(script::Error::Interpreter(
                _,
                interpreter::Error::StackBytes
            )))
        ));
        let program = script::Code(vec![0x76, 0x76, 0x76]);
        assert_eq!(
            eval_script(&input, &program, &NullSignatureChecker()),
            Ok(true)
        );
        assert!(eval_script(&vec![0; 1001], &program, &NullSignatureChecker()).is_err());
    }
}
