//! Experimental post-quantum transparent accounts for regtest.
//!
//! An account has one fixed P2SH address, while the WOTS+ key allowed to spend from it
//! changes on every spend. The current key is named by the account's control output;
//! each spend consumes that output, is signed by a key it names, and creates the next one.
//! Other payments to the address are spent alongside it without signatures of their own.
//!
//! Each step commits to [`SPARES`] keys so an unconfirmed spend can be replaced without
//! signing twice with one key. Callers must never sign twice with the same spare: the
//! derived keys can always be recomputed, so this module cannot prevent it.

mod authorization;
mod derive;
mod input;
mod keyset;
mod rules;
mod templates;

pub use authorization::Authorization;
pub use derive::{master_from_seed, signing_key};
pub use input::{FormError, WotsInput, classify};
pub use keyset::{KeySet, leaf_commit, root_from_path};
pub use rules::{AccountCheck, AccountError, check_accounts};
pub use templates::{AccountScript, ControlOutput};
pub use wots_plus::{MessageDigest, SigningKey, VerifyingKey};

/// The only account and control-output version defined for the prototype.
pub const VERSION: u8 = 0x01;
/// Marks an account redeem script. The script interpreter treats it as an invalid opcode.
pub const OP_CHECKWOTSACCOUNT: u8 = 0xba;
/// Marks a control output. The script interpreter treats it as an invalid opcode.
pub const OP_WOTSCONTROL: u8 = 0xbb;
/// Number of keys committed for each step.
pub const SPARES: usize = 4;
/// Experimental verification charge per authorization; not a production cost model.
pub const WOTS_SIGOP_COST: u32 = 100;

/// Script signature of a control input: the authorization pushes only.
pub const CONTROL_SCRIPT_SIG_SIZE: usize = authorization::ENCODED_SIZE;
/// Script signature of a deposit input that carries the first spend's authorization.
pub const SIGNING_DEPOSIT_SCRIPT_SIG_SIZE: usize =
    authorization::ENCODED_SIZE + 1 + AccountScript::SIZE;
/// Script signature of a deposit input covered by another input's authorization.
pub const COVERED_DEPOSIT_SCRIPT_SIG_SIZE: usize = 1 + AccountScript::SIZE;

/// Serialized size of a transparent input with a script signature of `script_sig` bytes.
pub const fn input_size(script_sig: usize) -> usize {
    let compact_size = if script_sig < 253 { 1 } else { 3 };
    36 + compact_size + script_sig + 4
}

/// Serialized size of a control output, including its value and script length.
pub const CONTROL_OUTPUT_SIZE: usize = 8 + 1 + ControlOutput::SIZE;

/// Appends one data push in the only encoding accounts accept.
pub(crate) fn push(bytes: &mut alloc::vec::Vec<u8>, value: &[u8]) {
    // Script push lengths are unsigned little-endian, not signed script numbers.
    match value.len() {
        0..=75 => bytes.push(u8::try_from(value.len()).expect("direct pushes fit one byte")),
        76..=255 => {
            bytes.push(0x4c);
            bytes.push(u8::try_from(value.len()).expect("PUSHDATA1 lengths fit one byte"));
        }
        256..=520 => {
            bytes.push(0x4d);
            bytes.extend(
                u16::try_from(value.len())
                    .expect("bounded pushes fit two bytes")
                    .to_le_bytes(),
            );
        }
        _ => unreachable!("account elements are at most 520 bytes"),
    }
    bytes.extend_from_slice(value);
}

/// Splits a script into its data pushes, or returns `None` if it contains anything else
/// or any push not in the encoding [`push`] produces.
pub(crate) fn pushes(script: &[u8]) -> Option<alloc::vec::Vec<&[u8]>> {
    let mut values = alloc::vec::Vec::new();
    let mut rest = script;
    while let Some((&opcode, tail)) = rest.split_first() {
        let (len, tail) = match opcode {
            0..=75 => (usize::from(opcode), tail),
            0x4c => {
                let (&len, tail) = tail.split_first()?;
                (usize::from(len), tail)
            }
            0x4d => {
                let (len, tail) = tail.split_at_checked(2)?;
                (usize::from(u16::from_le_bytes([len[0], len[1]])), tail)
            }
            _ => return None,
        };
        if len > 520 {
            return None;
        }
        let (value, tail) = tail.split_at_checked(len)?;
        values.push(value);
        rest = tail;
    }
    let mut canonical = alloc::vec::Vec::with_capacity(script.len());
    for value in &values {
        push(&mut canonical, value);
    }
    (canonical == script).then_some(values)
}

#[cfg(test)]
mod tests;
