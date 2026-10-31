//! Bounded argument transport and execution for native PQ scripts.
//!
//! This module has no cryptographic dependency. Its caller authenticates the previous
//! output, supplies its complete signing script, and selects a signature checker.

use alloc::vec::Vec;
use thiserror::Error;

use crate::{
    interpreter::{self, Flags, SignatureChecker, Stack},
    opcode, script,
};

/// Maximum serialized argument bytes. This accommodates twenty full PQ signatures.
pub const MAX_INPUT_BYTES: usize = 512 * 1024;
/// Maximum argument payload: one SHA2-128f signature and its signing-mode byte.
pub const MAX_PUSH_BYTES: usize = 17_089;
/// Maximum combined main and alternate stack payload.
pub const MAX_STACK_BYTES: usize = 1024 * 1024;
/// Complete output size, including the native envelope.
pub const MAX_SCRIPT_BYTES: usize = script::Code::MAX_SIZE;

/// Invalid native argument transport or script execution.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum Error {
    /// The complete serialized input exceeds its bound.
    #[error("native input size exceeded")]
    InputSize,
    /// An argument exceeds its payload bound.
    #[error("native push size exceeded")]
    PushSize,
    /// A push is missing its length prefix or payload.
    #[error("truncated native argument push")]
    TruncatedPush,
    /// Input arguments contain an executable operation.
    #[error("native arguments must be push-only")]
    NotPushOnly,
    /// The shared interpreter rejected the script.
    #[error(transparent)]
    Script(#[from] script::Error),
}

fn arguments(mut bytes: &[u8], flags: Flags) -> Result<Stack<Vec<u8>>, Error> {
    if bytes.len() > MAX_INPUT_BYTES {
        return Err(Error::InputSize);
    }
    let mut stack = Stack::new();
    while let Some((&op, remaining)) = bytes.split_first() {
        bytes = remaining;
        let value = match op {
            0 => Vec::new(),
            0x4f => vec![0x81],
            0x51..=0x60 => vec![op - 0x50],
            1..=0x4e => {
                let length = if op <= 0x4b {
                    usize::from(op)
                } else {
                    let width = match op {
                        0x4c => 1,
                        0x4d => 2,
                        _ => 4,
                    };
                    let (prefix, remaining) =
                        bytes.split_at_checked(width).ok_or(Error::TruncatedPush)?;
                    bytes = remaining;
                    let mut length = [0; 4];
                    length[..width].copy_from_slice(prefix);
                    usize::try_from(u32::from_le_bytes(length)).map_err(|_| Error::PushSize)?
                };
                if length > MAX_PUSH_BYTES {
                    return Err(Error::PushSize);
                }
                let (value, remaining) =
                    bytes.split_at_checked(length).ok_or(Error::TruncatedPush)?;
                bytes = remaining;
                value.to_vec()
            }
            _ => return Err(Error::NotPushOnly),
        };
        if flags.contains(Flags::MinimalData) {
            let minimal = match value.as_slice() {
                [] => 0,
                [1..=16] => 0x50 + value[0],
                [0x81] => 0x4f,
                v if v.len() <= 75 => u8::try_from(v.len()).expect("at most 75 bytes"),
                v if v.len() <= 255 => 0x4c,
                _ => 0x4d,
            };
            if op != minimal {
                return Err(
                    script::Error::Interpreter(None, interpreter::Error::MinimalData).into(),
                );
            }
        }
        if stack.len() == interpreter::MAX_STACK_DEPTH {
            return Err(
                script::Error::Interpreter(None, interpreter::Error::StackSize(None)).into(),
            );
        }
        stack.push(value);
    }
    Ok(stack)
}

pub(crate) fn check_stack_bytes(state: &interpreter::State) -> Result<(), script::Error> {
    let bytes: usize = state
        .stack
        .iter()
        .chain(state.altstack().iter())
        .map(Vec::len)
        .sum();
    if bytes > MAX_STACK_BYTES {
        Err(script::Error::Interpreter(
            None,
            interpreter::Error::PqStackBytes,
        ))
    } else {
        Ok(())
    }
}

/// Executes a native body with bounded push-only arguments through the shared interpreter.
///
/// `script_code` is the complete trusted output used for signing; `body` excludes its
/// envelope. Native signature operations and absolute locktimes are always enabled.
/// Other applicable flags, including clean-stack, minimal-data and null-dummy, are honored.
pub fn eval(
    input: &[u8],
    body: &script::Code,
    script_code: &script::Code,
    flags: Flags,
    checker: &dyn SignatureChecker,
) -> Result<bool, Error> {
    if script_code.0.len() > script::Code::MAX_SIZE || body.0.len() > script::Code::MAX_SIZE {
        return Err(script::Error::ScriptSize(None).into());
    }
    let flags = flags | Flags::NativePq | Flags::CHECKLOCKTIMEVERIFY;
    let stack = script::iter::eval(
        body.parse().map(|op| op.map_err(script::Error::Opcode)),
        flags,
        script_code,
        arguments(input, flags)?,
        checker,
    )?;
    let success = stack.last().is_ok_and(|v| interpreter::cast_to_bool(v));
    if success && flags.contains(Flags::CleanStack) && stack.len() != 1 {
        return Err(script::Error::CleanStack.into());
    }
    Ok(success)
}

/// Counts both ECDSA and PQ signature operations, including inactive branches.
/// Legacy counters deliberately retain their previous treatment of unknown bytes.
pub fn sig_op_count(program: &script::Code, accurate: bool) -> u32 {
    use opcode::Evaluable;
    let mut count = 0;
    let mut previous = None;
    for op in program.parse() {
        match op {
            Ok(op) => {
                count += match &op {
                    opcode::PossiblyBad::Good(crate::Opcode::Operation(operation)) => {
                        operation.pq_sig_op_count(previous.take())
                    }
                    _ => op.sig_op_count(previous.take()),
                };
                previous = accurate.then_some(op);
            }
            Err(opcode::Error::Disabled(_)) => previous = None,
            Err(_) => break,
        }
    }
    count
}

#[cfg(test)]
mod tests;
