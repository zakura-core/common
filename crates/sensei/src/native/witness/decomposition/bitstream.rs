//! Streaming canonical words and generic running-sum assignment.
//!
//! The test-only vector decompositions keep independent implementations as
//! references for the streamed production helpers.

#[cfg(test)]
use super::super::SINSEMILLA_WORD_BITS;
use super::super::writer::{AdviceValue, RowMap, WitnessWriter};
use crate::Error;
use crate::native::field::{CanonicalUint, Fp};
#[cfg(test)]
use alloc::vec::Vec;

/// Reference word decomposition. Production Sinsemilla writing streams
/// words and running sums from one window position (`WordStream`); this
/// single-view path is retained as the oracle the fused pass is pinned
/// against.
#[cfg(test)]
pub(in crate::native::witness) fn decompose_words(
    value: &Fp,
    count: usize,
) -> Result<Vec<usize>, Error> {
    if count == 0
        || count
            .checked_mul(SINSEMILLA_WORD_BITS)
            .is_none_or(|bits| bits > 255)
    {
        return Err(Error::InternalInvariant);
    }
    let integer = value.to_canonical_uint();
    (0..count)
        .map(|word| {
            usize::try_from(
                integer
                    .window(word * SINSEMILLA_WORD_BITS, SINSEMILLA_WORD_BITS)
                    .ok_or(Error::InternalInvariant)?,
            )
            .map_err(|_| Error::InternalInvariant)
        })
        .collect()
}

#[cfg(test)]
pub(in crate::native::witness) fn running_sum(
    value: &Fp,
    word_bits: usize,
    num_words: usize,
) -> Result<Vec<Fp>, Error> {
    if word_bits == 0
        || word_bits > 10
        || num_words == 0
        || word_bits
            .checked_mul(num_words)
            .is_none_or(|bits| bits > 255)
    {
        return Err(Error::InternalInvariant);
    }
    let integer = value.to_canonical_uint();
    (0..=num_words)
        .map(|index| {
            <Fp>::from_canonical_uint(integer.shr(index * word_bits))
                .ok_or(Error::InternalInvariant)
        })
        .collect()
}

/// Decomposes `value` once into its `count` low-to-high `word_bits`-wide words
/// together with the running sums `z_i = value >> (i * word_bits)` as field
/// elements (`count + 1` entries, `z_0 = value`), walking the canonical
/// integer a single time where the gadget writers need both views of the same
/// scalar (`running_sum` plus `scalar_windows`/`decompose_words` walked it
/// once per view).
/// The `word_bits`-wide words of a value, least significant first, each
/// paired with the running sum the writer assigns beside it — the value
/// shifted past the preceding words — streamed from one integer window
/// position instead of materialized as a word vector and a sum vector.
/// [`Self::final_sum`] is the sum past every word (the strictness term).
pub(in crate::native::witness) struct WordStream {
    pub(in crate::native::witness) shifted: CanonicalUint,
    pub(in crate::native::witness) word_bits: usize,
    pub(in crate::native::witness) remaining: usize,
}

impl WordStream {
    pub(in crate::native::witness) fn new(
        value: &Fp,
        word_bits: usize,
        count: usize,
    ) -> Result<Self, Error> {
        if word_bits == 0
            || word_bits > 10
            || count == 0
            || word_bits.checked_mul(count).is_none_or(|bits| bits > 255)
        {
            return Err(Error::InternalInvariant);
        }
        Ok(Self {
            shifted: value.to_canonical_uint(),
            word_bits,
            remaining: count,
        })
    }

    /// The running sum past every remaining word: the value shifted past all
    /// of them.
    pub(in crate::native::witness) fn final_sum(&self) -> Result<Fp, Error> {
        <Fp>::from_canonical_uint(self.shifted.shr(self.remaining * self.word_bits))
            .ok_or(Error::InternalInvariant)
    }
}

impl Iterator for WordStream {
    type Item = Result<(usize, Fp), Error>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;
        Some((|| {
            let sum = <Fp>::from_canonical_uint(self.shifted).ok_or(Error::InternalInvariant)?;
            let word = usize::try_from(
                self.shifted
                    .window(0, self.word_bits)
                    .ok_or(Error::InternalInvariant)?,
            )
            .map_err(|_| Error::InternalInvariant)?;
            self.shifted = self.shifted.shr(self.word_bits);
            Ok((word, sum))
        })())
    }
}

/// Fills `digits` with the `word_bits`-wide words of `value`, least
/// significant first, and `sums` with the running sums — `sums[i]` is the
/// value shifted past the first `i` words, so `sums` holds one entry more
/// than `digits` — from one [`WordStream`]: the fixed-base paths' arrays,
/// with no vector in between.
pub(in crate::native::witness) fn fill_words_and_running_sums(
    value: &Fp,
    word_bits: usize,
    digits: &mut [usize],
    sums: &mut [Fp],
) -> Result<(), Error> {
    if sums.len() != digits.len() + 1 {
        return Err(Error::InternalInvariant);
    }
    let stream = WordStream::new(value, word_bits, digits.len())?;
    let final_sum = stream.final_sum()?;
    for ((digit, sum), item) in digits.iter_mut().zip(sums.iter_mut()).zip(stream) {
        let (word, running) = item?;
        *digit = word;
        *sum = running;
    }
    sums[digits.len()] = final_sum;
    Ok(())
}

/// Reference word-and-sum decomposition as vectors: the tests' oracle for
/// [`WordStream`] and [`fill_words_and_running_sums`].
#[cfg(test)]
pub(in crate::native::witness) fn words_with_running_sums(
    value: &Fp,
    word_bits: usize,
    count: usize,
) -> Result<(Vec<usize>, Vec<Fp>), Error> {
    if word_bits == 0
        || word_bits > 10
        || count == 0
        || word_bits.checked_mul(count).is_none_or(|bits| bits > 255)
    {
        return Err(Error::InternalInvariant);
    }
    let mut shifted = value.to_canonical_uint();
    let mut words = Vec::with_capacity(count);
    let mut sums = Vec::with_capacity(count + 1);
    sums.push(*value);
    for _ in 0..count {
        let word = usize::try_from(
            shifted
                .window(0, word_bits)
                .ok_or(Error::InternalInvariant)?,
        )
        .map_err(|_| Error::InternalInvariant)?;
        words.push(word);
        shifted = shifted.shr(word_bits);
        sums.push(<Fp>::from_canonical_uint(shifted).ok_or(Error::InternalInvariant)?);
    }
    Ok((words, sums))
}

/// Writes the successive high parts after removing each low word, including
/// the final remainder. A strict stream requires that remainder to be zero.
#[allow(clippy::too_many_arguments)] // fixed-layout coordinates are passed individually
pub(in crate::native::witness) fn write_running_sum(
    writer: &mut WitnessWriter,
    row_map: &RowMap,
    column: usize,
    region: usize,
    value: &Fp,
    word_bits: usize,
    num_words: usize,
    strict: bool,
) -> Result<(), Error> {
    // The terms stream from one window position; a caller that needs one of
    // them afterwards reads it through `running_sum_at`.
    let stream = WordStream::new(value, word_bits, num_words)?;
    let last = stream.final_sum()?;
    if strict && !last.is_zero() {
        return Err(Error::UnsatisfiedWitness);
    }
    let start = row_map.absolute_row(region, 0)?;
    for (local_row, term) in stream.enumerate() {
        let (_, term) = term?;
        writer.write_advice(column, start + local_row, AdviceValue::Direct(term))?;
    }
    writer.write_advice(column, start + num_words, AdviceValue::Direct(last))
}
