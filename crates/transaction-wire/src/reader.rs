//! A bounds-checked cursor over borrowed bytes.

use alloc::vec::Vec;

use zcash_protocol::encoding::MAX_COMPACT_SIZE;

use crate::DecodeError;

pub(crate) struct Reader<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    pub(crate) fn new(data: &'a [u8]) -> Self {
        Reader { data, pos: 0 }
    }

    pub(crate) fn position(&self) -> usize {
        self.pos
    }

    pub(crate) fn remaining(&self) -> usize {
        self.data.len() - self.pos
    }

    pub(crate) fn take(&mut self, n: usize, field: &'static str) -> Result<&'a [u8], DecodeError> {
        let remaining = self.remaining();
        if n > remaining {
            return Err(DecodeError::Truncated {
                field,
                needed: n - remaining,
            });
        }
        let out = &self.data[self.pos..self.pos + n];
        self.pos += n;
        Ok(out)
    }

    pub(crate) fn array<const N: usize>(
        &mut self,
        field: &'static str,
    ) -> Result<&'a [u8; N], DecodeError> {
        let bytes = self.take(N, field)?;
        Ok(bytes.try_into().expect("take returned exactly N bytes"))
    }

    pub(crate) fn u8(&mut self, field: &'static str) -> Result<u8, DecodeError> {
        Ok(self.array::<1>(field)?[0])
    }

    pub(crate) fn u32_le(&mut self, field: &'static str) -> Result<u32, DecodeError> {
        Ok(u32::from_le_bytes(*self.array(field)?))
    }

    pub(crate) fn le_bytes8(&mut self, field: &'static str) -> Result<[u8; 8], DecodeError> {
        Ok(*self.array(field)?)
    }

    /// Reads a canonical CompactSize no larger than `MAX_COMPACT_SIZE`, matching
    /// `zcash_protocol::encoding::CompactSize::read`.
    pub(crate) fn compact_size(&mut self, field: &'static str) -> Result<usize, DecodeError> {
        let flag = self.u8(field)?;
        let value = match flag {
            0..=252 => u64::from(flag),
            253 => {
                let n = u16::from_le_bytes(*self.array(field)?);
                if n < 253 {
                    return Err(DecodeError::NonCanonicalCompactSize { field });
                }
                u64::from(n)
            }
            254 => {
                let n = u32::from_le_bytes(*self.array(field)?);
                if n < 0x1_0000 {
                    return Err(DecodeError::NonCanonicalCompactSize { field });
                }
                u64::from(n)
            }
            255 => {
                let n = u64::from_le_bytes(*self.array(field)?);
                if n < 0x1_0000_0000 {
                    return Err(DecodeError::NonCanonicalCompactSize { field });
                }
                n
            }
        };
        if value > u64::from(MAX_COMPACT_SIZE) {
            return Err(DecodeError::CompactSizeTooLarge { field, value });
        }
        // MAX_COMPACT_SIZE fits in u32, and every supported target has at least 32-bit usize.
        Ok(usize::try_from(value).expect("bounded by MAX_COMPACT_SIZE"))
    }

    /// Reads a CompactSize element count and rejects it unless `count` elements of at
    /// least `min_element_size` bytes each fit in the remaining input. Callers may then
    /// allocate `count` elements: the allocation is bounded by the input length.
    pub(crate) fn count(
        &mut self,
        field: &'static str,
        min_element_size: usize,
    ) -> Result<usize, DecodeError> {
        let count = self.compact_size(field)?;
        self.check_count(field, count, min_element_size)?;
        Ok(count)
    }

    pub(crate) fn check_count(
        &self,
        field: &'static str,
        count: usize,
        element_size: usize,
    ) -> Result<(), DecodeError> {
        match count.checked_mul(element_size) {
            Some(total) if total <= self.remaining() => Ok(()),
            _ => Err(DecodeError::CountExceedsInput { field, count }),
        }
    }

    /// Reads a CompactSize-prefixed byte string.
    pub(crate) fn var_bytes(&mut self, field: &'static str) -> Result<&'a [u8], DecodeError> {
        let len = self.compact_size(field)?;
        self.take(len, field)
    }

    /// Reads `count` elements with `f` after a bounds-checked allocation.
    pub(crate) fn elements<T>(
        &mut self,
        count: usize,
        mut f: impl FnMut(&mut Self) -> Result<T, DecodeError>,
    ) -> Result<Vec<T>, DecodeError> {
        let mut out = Vec::with_capacity(count);
        for _ in 0..count {
            out.push(f(self)?);
        }
        Ok(out)
    }
}
