//! Constant values represented as opcodes.

#![allow(non_camel_case_types)]

use alloc::{
    string::{String, ToString},
    vec::Vec,
};

use bounded_vec::{BoundedVec, EmptyBoundedVec};

use crate::{num, opcode, script::Asm, signature};

/// Data values that aren’t represented within their opcode byte.
///
/// TODO: These should have lower bounds that can prevent non-minimal encodings, but that requires
///       at least `const_generic_exprs`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum LargeValue {
    /// NB: The lower bound here is 1 because `PushdataBytelength([;0])` has the same encoding as
    ///     [`OP_0`].
    PushdataBytelength(BoundedVec<u8, 1, 0x4b>),
    /// A value whose byte length can fit into a single byte.
    OP_PUSHDATA1(EmptyBoundedVec<u8, 0xff>),
    /// A value whose byte length can fit into two bytes.
    OP_PUSHDATA2(EmptyBoundedVec<u8, { Self::MAX_SIZE }>),
    /// NB: This constructor is only possible when [`crate::interpreter::Flags::MinimalData`] isn't set.
    OP_PUSHDATA4(EmptyBoundedVec<u8, { Self::MAX_SIZE }>),
}

use LargeValue::*;

impl LargeValue {
    const PUSHDATA1_BYTE: u8 = 0x4c;
    const PUSHDATA2_BYTE: u8 = 0x4d;
    const PUSHDATA4_BYTE: u8 = 0x4e;

    /// The maximum number of bytes able to be stored in a single [`super::PushValue`].
    pub(crate) const MAX_SIZE: usize = 520; // bytes

    /// The number of bytes this requires in a script.
    pub(crate) fn byte_len(&self) -> usize {
        1 + match self {
            PushdataBytelength(data) => data.as_slice().len(),
            OP_PUSHDATA1(data) => 1 + data.as_slice().len(),
            OP_PUSHDATA2(data) => 2 + data.as_slice().len(),
            OP_PUSHDATA4(data) => 4 + data.as_slice().len(),
        }
    }

    /// Returns a [`LargeValue`] as minimally-encoded as possible. That is, values that
    /// should be minimally-encoded as [`SmallValue`]s will be [`LargeValue`].
    pub(crate) fn from_slice(v: &[u8]) -> Option<LargeValue> {
        if v.len() > Self::MAX_SIZE {
            return None;
        }
        if let Ok(bv) = BoundedVec::try_from(v.to_vec()) {
            Some(PushdataBytelength(bv))
        } else if let Ok(bv) = BoundedVec::try_from(v.to_vec()) {
            Some(OP_PUSHDATA1(bv))
        } else if let Ok(bv) = BoundedVec::try_from(v.to_vec()) {
            Some(OP_PUSHDATA2(bv))
        } else if let Ok(bv) = BoundedVec::try_from(v.to_vec()) {
            Some(OP_PUSHDATA4(bv))
        } else {
            None
        }
    }

    fn split_value(script: &[u8], needed_bytes: usize) -> (Result<&[u8], opcode::Error>, &[u8]) {
        match script.split_at_checked(needed_bytes) {
            None => (
                Err(opcode::Error::Read {
                    expected_bytes: needed_bytes,
                    available_bytes: script.len(),
                }),
                &[],
            ),
            Some((value, remainder)) => (
                // NB: This check would ideally be done before the `split_at_checked` call, but the
                //     C++ impl reads the bytes before checking if the size is too large.
                if needed_bytes <= Self::MAX_SIZE {
                    Ok(value)
                } else {
                    Err(opcode::Error::PushSize(Some(needed_bytes)))
                },
                remainder,
            ),
        }
    }

    /// First splits `size_size` bytes to determine the size of the value to read, then splits the
    /// value.
    fn split_tagged_value(
        script: &[u8],
        size_size: usize,
    ) -> (Result<&[u8], opcode::Error>, &[u8]) {
        let (res, rem) = Self::split_value(script, size_size);
        match res {
            Err(_) => (res, rem),
            Ok(bytes) => {
                let mut size = 0;
                for byte in bytes.iter().rev() {
                    size <<= 8;
                    size |= usize::from(*byte);
                }
                Self::split_value(rem, size)
            }
        }
    }

    /// Parse a single [`LargeValue`] from a script. Returns `None` if the first byte doesn’t
    /// correspond to a [`LargeValue`].
    pub(crate) fn parse(script: &[u8]) -> Option<(Result<LargeValue, opcode::Error>, &[u8])> {
        match script.split_first() {
            None => Some((
                Err(opcode::Error::Read {
                    expected_bytes: 1,
                    available_bytes: 0,
                }),
                &[],
            )),
            Some((leading_byte, script)) => match leading_byte {
                0x01..LargeValue::PUSHDATA1_BYTE => {
                    let (res, rem) = Self::split_value(script, (*leading_byte).into());
                    Some((
                        res.map(|v| {
                            PushdataBytelength(v.to_vec().try_into().expect("fits into BoundedVec"))
                        }),
                        rem,
                    ))
                }
                &LargeValue::PUSHDATA1_BYTE => {
                    let (res, rem) = Self::split_tagged_value(script, 1);
                    Some((
                        res.map(|v| {
                            OP_PUSHDATA1(v.to_vec().try_into().expect("fits into BoundedVec"))
                        }),
                        rem,
                    ))
                }
                &LargeValue::PUSHDATA2_BYTE => {
                    let (res, rem) = Self::split_tagged_value(script, 2);
                    Some((
                        res.map(|v| {
                            OP_PUSHDATA2(v.to_vec().try_into().expect("fits into BoundedVec"))
                        }),
                        rem,
                    ))
                }
                &LargeValue::PUSHDATA4_BYTE => {
                    let (res, rem) = Self::split_tagged_value(script, 4);
                    Some((
                        res.map(|v| {
                            OP_PUSHDATA4(v.to_vec().try_into().expect("fits into BoundedVec"))
                        }),
                        rem,
                    ))
                }
                _ => None,
            },
        }
    }

    /// Get the [`crate::interpreter::Stack`] element represented by this [`LargeValue`].
    pub(crate) fn value(&self) -> &[u8] {
        match self {
            PushdataBytelength(v) => v.as_slice(),
            OP_PUSHDATA1(v) => v.as_slice(),
            OP_PUSHDATA2(v) => v.as_slice(),
            OP_PUSHDATA4(v) => v.as_slice(),
        }
    }

    /// Returns false if there is a smaller possible encoding of the provided value.
    pub(crate) fn is_minimal_push(&self) -> bool {
        match self {
            PushdataBytelength(data) => match data.as_slice() {
                [b] => *b != 0x81 && (*b < 1 || 16 < *b),
                _ => true,
            },
            OP_PUSHDATA1(data) => usize::from(Self::PUSHDATA1_BYTE) <= data.as_slice().len(),
            OP_PUSHDATA2(data) => 0x100 <= data.as_slice().len(),
            OP_PUSHDATA4(data) => 0x10000 <= data.as_slice().len(),
        }
    }

    /// Returns the numeric value represented by the opcode, if one exists.
    pub(crate) fn to_num(&self) -> Result<i64, num::Error> {
        num::parse(
            self.value(),
            false,
            // To ensure that any encoding supported by `num` is supported here.
            Some(usize::MAX),
        )
    }
}

impl From<&LargeValue> for Vec<u8> {
    /// Encodes the value the way [`LargeValue::parse`] reads it: the `OP_PUSHDATA*` opcode,
    /// the length as an unsigned little-endian field of the width that opcode selects, then
    /// the data. For `PushdataBytelength`, the single length byte is itself the opcode.
    fn from(value: &LargeValue) -> Self {
        let (prefix, len_width, contents): (&[u8], usize, &[u8]) = match value {
            PushdataBytelength(bv) => (&[], 1, bv.as_slice()),
            OP_PUSHDATA1(bv) => (&[LargeValue::PUSHDATA1_BYTE], 1, bv.as_slice()),
            OP_PUSHDATA2(bv) => (&[LargeValue::PUSHDATA2_BYTE], 2, bv.as_slice()),
            OP_PUSHDATA4(bv) => (&[LargeValue::PUSHDATA4_BYTE], 4, bv.as_slice()),
        };
        let len = u32::try_from(contents.len())
            .expect("contents are at most `LargeValue::MAX_SIZE` bytes")
            .to_le_bytes();

        prefix
            .iter()
            .chain(&len[..len_width])
            .chain(contents)
            .copied()
            .collect()
    }
}

impl Asm for LargeValue {
    fn to_asm(&self, attempt_sighash_decode: bool) -> String {
        // The logic below follows the zcashd implementation in its
        // `ScriptToAsmStr()`
        // https://github.com/zcash/zcash/blob/2352fbc1ed650ac4369006bea11f7f20ee046b84/src/core_write.cpp#L73-L115
        let mut value = self.value().to_vec();
        let mut hash_type = String::new();
        #[cfg(feature = "signature-validation")]
        if attempt_sighash_decode && value.len() > 4 {
            if let signature::Validity::Valid(signature) =
                signature::Decoded::from_bytes(&value, false, true)
            {
                value = signature.sig().serialize_der().to_vec();
                hash_type = format!("[{}]", signature.sighash_type().to_asm(false));
            }
        }
        if value.len() <= 4 {
            // zcashd ultimately uses `CScriptNum()`-> `set_vch()`, which was
            // replaced with `num::parse()` in this crate
            let n = num::parse(&value, false, Some(8)).unwrap_or(0);
            return n.to_string();
        }
        // hex::encode(), but avoids the `hex` dependency
        value
            .iter()
            .map(|b| format!("{:02x}", b))
            .collect::<Vec<_>>()
            .join("")
            + &hash_type
    }
}

/// Data values represented entirely by their opcode byte.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
#[allow(missing_docs)]
#[repr(u8)]
pub enum SmallValue {
    // push value
    OP_0 = 0x00,
    OP_1NEGATE = 0x4f,
    OP_1 = 0x51,
    OP_2 = 0x52,
    OP_3 = 0x53,
    OP_4 = 0x54,
    OP_5 = 0x55,
    OP_6 = 0x56,
    OP_7 = 0x57,
    OP_8 = 0x58,
    OP_9 = 0x59,
    OP_10 = 0x5a,
    OP_11 = 0x5b,
    OP_12 = 0x5c,
    OP_13 = 0x5d,
    OP_14 = 0x5e,
    OP_15 = 0x5f,
    OP_16 = 0x60,
}

use SmallValue::*;

impl SmallValue {
    /// Decodes this opcode from its byte encoding.
    pub(super) fn decode(b: u8) -> Option<Self> {
        match b {
            0x00 => Some(Self::OP_0),
            0x4f => Some(Self::OP_1NEGATE),
            0x51 => Some(Self::OP_1),
            0x52 => Some(Self::OP_2),
            0x53 => Some(Self::OP_3),
            0x54 => Some(Self::OP_4),
            0x55 => Some(Self::OP_5),
            0x56 => Some(Self::OP_6),
            0x57 => Some(Self::OP_7),
            0x58 => Some(Self::OP_8),
            0x59 => Some(Self::OP_9),
            0x5a => Some(Self::OP_10),
            0x5b => Some(Self::OP_11),
            0x5c => Some(Self::OP_12),
            0x5d => Some(Self::OP_13),
            0x5e => Some(Self::OP_14),
            0x5f => Some(Self::OP_15),
            0x60 => Some(Self::OP_16),
            _ => None,
        }
    }

    /// Returns the byte encoding of this opcode.
    pub(crate) fn encode(self) -> u8 {
        // This is how you get the discriminant, but using `as` everywhere is too much code smell
        self as u8
    }

    /// Get the [`crate::interpreter::Stack`] element represented by this [`SmallValue`].
    pub(crate) fn value(&self) -> Vec<u8> {
        match self {
            OP_0 => vec![],
            OP_1NEGATE => vec![0x81],
            _ => vec![self.encode() - (OP_1.encode() - 1)],
        }
    }

    /// Returns the numeric value of the opcode. It will always be in the range -1..=16.
    pub(crate) fn to_num(self) -> i8 {
        match self {
            OP_0 => 0,
            OP_1NEGATE => -1,
            OP_1 => 1,
            OP_2 => 2,
            OP_3 => 3,
            OP_4 => 4,
            OP_5 => 5,
            OP_6 => 6,
            OP_7 => 7,
            OP_8 => 8,
            OP_9 => 9,
            OP_10 => 10,
            OP_11 => 11,
            OP_12 => 12,
            OP_13 => 13,
            OP_14 => 14,
            OP_15 => 15,
            OP_16 => 16,
        }
    }
}

impl Asm for SmallValue {
    /// zcashd prints small values script elements as numbers (e.g. OP_1 → "1").
    /// https://github.com/zcash/zcash/blob/v6.11.0/src/script/script.cpp#L19-L40
    fn to_asm(&self, _attempt_sighash_decode: bool) -> String {
        match self {
            OP_0 => "0",
            OP_1NEGATE => "-1",
            OP_1 => "1",
            OP_2 => "2",
            OP_3 => "3",
            OP_4 => "4",
            OP_5 => "5",
            OP_6 => "6",
            OP_7 => "7",
            OP_8 => "8",
            OP_9 => "9",
            OP_10 => "10",
            OP_11 => "11",
            OP_12 => "12",
            OP_13 => "13",
            OP_14 => "14",
            OP_15 => "15",
            OP_16 => "16",
        }
        .to_string()
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use super::LargeValue;
    use crate::num;

    /// Data whose bytes all differ from their neighbours, so a misplaced length field
    /// shows up as different data rather than an identical shifted copy.
    fn data(len: usize) -> Vec<u8> {
        (0..len).map(|i| (i % 251) as u8).collect()
    }

    /// The encoding the parser accepts: the opcode, a `len_width`-byte unsigned
    /// little-endian length (absent for direct pushes, whose opcode is the length), then
    /// the data.
    fn wire_encoding(opcode: Option<u8>, len_width: usize, contents: &[u8]) -> Vec<u8> {
        let len = u32::try_from(contents.len()).unwrap().to_le_bytes();
        match opcode {
            None => [&len[..1], contents].concat(),
            Some(op) => [&[op][..], &len[..len_width], contents].concat(),
        }
    }

    /// The upstream `zcash_script` 0.6.0 encoder, which wrote lengths as script numbers.
    fn legacy_encoding(value: &LargeValue) -> Vec<u8> {
        let (prefix, contents) = match value {
            LargeValue::PushdataBytelength(bv) => (None, bv.as_slice()),
            LargeValue::OP_PUSHDATA1(bv) => (Some(LargeValue::PUSHDATA1_BYTE), bv.as_slice()),
            LargeValue::OP_PUSHDATA2(bv) => (Some(LargeValue::PUSHDATA2_BYTE), bv.as_slice()),
            LargeValue::OP_PUSHDATA4(bv) => (Some(LargeValue::PUSHDATA4_BYTE), bv.as_slice()),
        };
        prefix
            .into_iter()
            .chain(num::serialize(contents.len().try_into().unwrap()))
            .chain(contents.iter().copied())
            .collect()
    }

    /// Every push encoding a script can contain, including non-minimal ones (which
    /// consensus accepts), parses and re-encodes to the same bytes.
    #[test]
    fn every_push_encoding_round_trips() {
        let forms = [
            (None, 1, 1..=0x4b),
            (Some(LargeValue::PUSHDATA1_BYTE), 1, 0..=0xff),
            (
                Some(LargeValue::PUSHDATA2_BYTE),
                2,
                0..=LargeValue::MAX_SIZE,
            ),
            (
                Some(LargeValue::PUSHDATA4_BYTE),
                4,
                0..=LargeValue::MAX_SIZE,
            ),
        ];
        for (opcode, len_width, lens) in forms {
            for len in lens {
                let bytes = wire_encoding(opcode, len_width, &data(len));
                let (parsed, rest) = LargeValue::parse(&bytes).expect("a push opcode");
                let parsed = parsed.expect("a valid push");
                assert!(rest.is_empty(), "{opcode:?} {len}: trailing bytes");
                assert_eq!(parsed.value(), data(len), "{opcode:?} {len}: value");
                assert_eq!(parsed.byte_len(), bytes.len(), "{opcode:?} {len}: byte_len");
                assert_eq!(Vec::from(&parsed), bytes, "{opcode:?} {len}: re-encoding");
            }
        }
    }

    /// Values built by `push_value` encode the way the parser reads them, and differ from
    /// the upstream encoder only for 128–255-byte pushes, where upstream added a sign
    /// byte.
    #[test]
    fn minimal_pushes_change_only_for_128_to_255_bytes() {
        for len in 1..=LargeValue::MAX_SIZE {
            let value = LargeValue::from_slice(&data(len)).expect("at most 520 bytes");
            let bytes = Vec::from(&value);
            assert_eq!(
                LargeValue::parse(&bytes).map(|(v, rest)| (v, rest.len())),
                Some((Ok(value.clone()), 0)),
                "{len}: does not round-trip"
            );
            assert_eq!(
                bytes == legacy_encoding(&value),
                !(128..=255).contains(&len),
                "{len}: unexpected difference from the upstream encoding"
            );
        }
    }

    #[test]
    fn from_slice_rejects_values_over_520_bytes() {
        assert!(LargeValue::from_slice(&data(LargeValue::MAX_SIZE)).is_some());
        assert_eq!(
            LargeValue::from_slice(&data(LargeValue::MAX_SIZE + 1)),
            None
        );
    }
}
