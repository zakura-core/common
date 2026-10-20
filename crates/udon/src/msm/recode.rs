//! Opaque recoding geometry shared by sizing, cached preparation, and kernels.
//!
//! Joint digits retain their actual length. Cached Booth digits use chunked rows
//! of up to 256 terms; widths through eight use one byte and wider widths use
//! two. Writing a cache overwrites its entire required prefix, including partial
//! final chunks. [`window_rows`] can instead extract a window from GLV components
//! without storing digits; its signed midpoint convention differs from the cache.

use super::storage::Storage;

use super::{Algorithm, ArithmeticOptions, CurveError, PastaCurve, ScalarStorage, checked_count};
use crate::curve::pasta::{digits::centered_digit, eisenstein, parameters::GlvParameters};
use crate::exec::{Executor, TaskBudget, for_each_chunk_mut};

pub(super) const CHUNK: usize = 256;
pub(super) const JOINT_STRIDE: usize = eisenstein::MAX_DIGITS + 1;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Geometry {
    Short(u8),
    Joint,
    Booth(u8),
    Alpha(u8),
}

const fn alpha_description(width: u8) -> super::AlphaDescription {
    match super::AlphaDescription::new(width) {
        Ok(description) => description,
        Err(_) => panic!("invalid internal alpha width"),
    }
}

impl Geometry {
    const fn for_len(n: usize, options: ArithmeticOptions) -> Self {
        match options.algorithm {
            Algorithm::Joint => return Self::Joint,
            Algorithm::Booth {
                width: Some(width), ..
            }
            | Algorithm::StreamingBooth { width: Some(width) } => return Self::Booth(width as u8),
            Algorithm::StreamingBooth { width: None } => return Self::Booth(8),
            _ => {}
        }
        if matches!(options.algorithm, Algorithm::Auto) && n < super::BOOTH_MIN {
            Self::Joint
        } else {
            // Larger windows reduce recoding work but enlarge each bucket
            // workspace. The shared selector can widen buckets when independent
            // workers amortize them.
            Self::Booth(if n < 192 {
                6
            } else if n < 512 {
                7
            } else if n < 4096 {
                8
            } else if n < 32768 {
                10
            } else {
                11
            })
        }
    }

    pub(super) const fn select(
        n: usize,
        shape: Shape,
        options: ArithmeticOptions,
        budget: crate::exec::TaskBudget,
    ) -> Self {
        let geometry = Self::for_shape(n, shape, options);
        if n >= 4096
            && budget.get() > 1
            && matches!(geometry, Self::Booth(_))
            && matches!(
                options.algorithm,
                Algorithm::Auto | Algorithm::Booth { width: None, .. }
            )
        {
            Self::Booth(11)
        } else {
            geometry
        }
    }

    pub(super) const fn for_shape(n: usize, shape: Shape, options: ArithmeticOptions) -> Self {
        let Shape { bits, weight } = shape;
        if !matches!(options.algorithm, Algorithm::Auto) || bits == 255 {
            return Self::for_len(n, options);
        }
        // Dense bounded rows eventually favor Booth buckets too. Keep sparse
        // rows on the short kernel; their high bit alone does not imply work.
        // Dense 128-bit rows share the full-width crossover at 8--32 terms.
        if (n >= 512 && bits >= 32 && weight > 8 * n)
            || (n >= 8 && n <= 32 && bits > 120 && weight > 32 * n)
        {
            Self::for_len(n, options)
        } else {
            Self::Short(bits)
        }
    }

    pub(super) const fn windows(self) -> usize {
        match self {
            Self::Booth(width) => 128_usize.div_ceil(width as usize),
            Self::Alpha(width) => alpha_description(width).main_windows() + 1,
            _ => 1,
        }
    }
    pub(super) const fn width(self) -> usize {
        match self {
            Self::Booth(w) | Self::Alpha(w) => w as usize,
            _ => 0,
        }
    }
    pub(super) const fn buckets(self) -> usize {
        match self {
            Self::Alpha(width) => alpha_description(width).layers(),
            _ => 1 << (self.width() - 1),
        }
    }
    pub(super) const fn stride(self) -> usize {
        match self {
            Self::Short(_) => 0,
            Self::Joint => JOINT_STRIDE,
            Self::Alpha(_) => 4 * self.windows(),
            Self::Booth(w) => 2 * self.windows() * if w > 8 { 2 } else { 1 },
        }
    }
    pub(super) const fn storage_len(self, terms: usize) -> Result<usize, CurveError> {
        checked_count::<u8>(terms, self.stride())
    }
}

#[derive(Clone, Copy, Debug)]
pub(super) struct Shape {
    // Maximum magnitude width, or 255 if any record needs full-width arithmetic.
    pub(super) bits: u8,
    // Sum of magnitude population counts, meaningful only when bits != 255.
    // Retained chunks inherit the whole row's weight as a conservative bound.
    pub(super) weight: usize,
}
impl Shape {
    pub(super) fn of<C: PastaCurve>(records: &[ScalarStorage<C>]) -> Self {
        let mut shape = Self { bits: 0, weight: 0 };
        for record in records {
            shape.bits = shape.bits.max(record.bits);
            if shape.bits == 255 {
                break;
            }
            shape.weight += record.magnitude.count_ones() as usize;
        }
        shape
    }
}

#[derive(Clone, Copy, Debug)]
pub(super) struct Cache<'a> {
    pub(super) geometry: Geometry,
    pub(super) digits: &'a [u8],
}

/// Visits both signed GLV digits for each term in `range` at one Booth window.
///
/// Requires a Booth width in `4..=12`, `window < geometry.windows()`, and a range
/// within `records`. Components must satisfy [`GlvParameters::BOUNDS`] so no
/// extra carry window is needed. With `DIRECT`, ignore `digits` and extract
/// overlapping Booth digits. Otherwise `digits` must contain the matching
/// [`write`] output for all records, even when visiting only a subrange.
#[inline(always)]
#[cfg(test)]
pub(super) fn window_rows<C: PastaCurve, const DIRECT: bool>(
    records: &[ScalarStorage<C>],
    digits: &[u8],
    range: core::ops::Range<usize>,
    geometry: Geometry,
    window: usize,
    visit: impl FnMut(usize, i16, i16),
) {
    window_views::<C, DIRECT>(records, digits, range, geometry, window, visit)
}

pub(super) fn window_views<C: PastaCurve, const DIRECT: bool>(
    records: impl Storage<ScalarStorage<C>>,
    digits: impl Storage<u8>,
    range: core::ops::Range<usize>,
    geometry: Geometry,
    window: usize,
    mut visit: impl FnMut(usize, i16, i16),
) {
    if !DIRECT {
        return rows_view(digits, records.len(), range, geometry, window, visit);
    }
    let width = geometry.width();
    let shift = window * width;
    let radix = 1_i16 << width;
    for term in range {
        let digits = records.get(term).halves.map(|component| {
            let magnitude = component.unsigned_abs();
            let value = ((magnitude >> shift) as i16) & (radix - 1);
            let overlap = if shift == 0 {
                0
            } else {
                ((magnitude >> (shift - 1)) & 1) as i16
            };
            // Subtracting radix contributes -1 to the next window; that window's
            // overlapping bit restores it. Applying the component sign can give
            // +128 at width eight. Keep i16 digits here: the carry-propagating
            // cache uses a different midpoint convention to fit signed bytes.
            let digit = value + overlap - if value >= radix / 2 { radix } else { 0 };
            if component < 0 { -digit } else { digit }
        });
        visit(term, digits[0], digits[1]);
    }
}

/// Writes the same digit layout as [`write`] using the caller's task budget.
///
/// `digits` must be exactly `geometry.storage_len(records.len())` bytes, so the
/// final chunk corresponds to the remaining records. Records must contain valid
/// GLV components. The executor completes all writes before this returns.
pub(super) fn write_parallel<C: PastaCurve, X: Executor>(
    records: &[ScalarStorage<C>],
    geometry: Geometry,
    digits: &mut [u8],
    book: Option<super::AlphaCodebook<'_>>,
    budget: TaskBudget,
    executor: &X,
) {
    let write = |records: &[ScalarStorage<C>], geometry: Geometry, digits: &mut [u8]| {
        if let Some(book) = book {
            for (record, row) in records
                .iter()
                .zip(digits.chunks_exact_mut(geometry.stride()))
            {
                book.write(record.halves, row);
            }
        } else {
            write(records, geometry, digits);
        }
    };
    // Small rows avoid another round of executor joins. Short geometry stores no
    // digits, so it must also bypass for_each_chunk_mut's nonzero chunk length.
    if records.len() < 1024 || budget == TaskBudget::SERIAL || geometry.stride() == 0 {
        return write(records, geometry, digits);
    }
    // Split only at packed-chunk boundaries; splitting inside a Booth chunk
    // would change the row offsets consumed by rows(). Each callback is serial
    // and needs no further share of the executor budget.
    for_each_chunk_mut(
        digits,
        CHUNK * geometry.stride(),
        budget,
        executor,
        |chunk, digits, _| {
            let start = chunk * CHUNK;
            write(
                &records[start..records.len().min(start + CHUNK)],
                geometry,
                digits,
            );
        },
    );
}

pub(super) fn write<C: PastaCurve>(
    records: &[ScalarStorage<C>],
    geometry: Geometry,
    digits: &mut [u8],
) {
    let stride = geometry.stride();
    match geometry {
        Geometry::Alpha(_) => unreachable!("α recoding needs its codebook"),
        Geometry::Short(_) => (),
        Geometry::Joint => {
            for (record, row) in records.iter().zip(digits.chunks_exact_mut(stride)) {
                let (codes, len) = eisenstein::recode(record.halves[0], record.halves[1]);
                row[..eisenstein::MAX_DIGITS].copy_from_slice(&codes);
                row[eisenstein::MAX_DIGITS] = len as u8;
            }
        }
        Geometry::Booth(width) => {
            // Both curve bounds leave room for an incoming carry in the last
            // window for every supported width. Width eight has 16 data rows.
            const {
                assert!(GlvParameters::<C>::BOOTH_WINDOWS == 16);
            }
            let shift = (geometry.windows() - 1) * usize::from(width);
            for bound in GlvParameters::<C>::BOUNDS {
                assert!((bound >> shift) + 1 < 1 << (width - 1));
            }
            let bytes = if width > 8 { 2 } else { 1 };
            for (chunk, rows) in records.chunks(CHUNK).zip(digits.chunks_mut(CHUNK * stride)) {
                for (i, record) in chunk.iter().enumerate() {
                    for (half, value) in record.halves.into_iter().enumerate() {
                        let mut magnitude = value.unsigned_abs();
                        let mut carry = 0;
                        for window in 0..geometry.windows() {
                            let digit = centered_digit(
                                (magnitude & ((1 << width) - 1)) as u16,
                                value < 0,
                                &mut carry,
                                u32::from(width),
                            );
                            let offset = ((window * 2 + half) * chunk.len() + i) * bytes;
                            rows[offset] = digit as u8;
                            if bytes == 2 {
                                rows[offset + 1] = (digit >> 8) as u8;
                            }
                            magnitude >>= width;
                        }
                        debug_assert_eq!(magnitude, 0);
                        debug_assert_eq!(carry, 0);
                    }
                }
            }
        }
    }
}

/// Visits contiguous rows once per intersecting chunk, amortizing row lookup.
#[cfg(test)]
pub(super) fn rows(
    digits: &[u8],
    terms: usize,
    range: core::ops::Range<usize>,
    geometry: Geometry,
    window: usize,
    visit: impl FnMut(usize, i16, i16),
) {
    rows_view(digits, terms, range, geometry, window, visit)
}

pub(super) fn rows_view(
    digits: impl Storage<u8>,
    terms: usize,
    range: core::ops::Range<usize>,
    geometry: Geometry,
    window: usize,
    mut visit: impl FnMut(usize, i16, i16),
) {
    let bytes = if geometry.width() > 8 { 2 } else { 1 };
    let stride = geometry.stride();
    let mut first = range.start;
    while first < range.end {
        let start = first / CHUNK * CHUNK;
        let len = (terms - start).min(CHUNK);
        let end = range.end.min(start + len);
        let offset = start * stride + 2 * window * len * bytes;
        let a = digits.slice(offset..offset + len * bytes);
        let b = digits.slice(offset + len * bytes..offset + 2 * len * bytes);
        let ca = a.contiguous();
        let cb = b.contiguous();
        if bytes == 1
            && let (Some(a), Some(b)) = (ca, cb)
        {
            for term in first..end {
                let i = term - start;
                visit(term, i16::from(a[i] as i8), i16::from(b[i] as i8));
            }
        } else {
            for term in first..end {
                let i = (term - start) * bytes;
                let read = |row: _, contiguous: Option<&[u8]>| {
                    let byte = |j| contiguous.map_or_else(|| Storage::get(row, j), |s| s[j]);
                    if bytes == 1 {
                        i16::from(byte(i) as i8)
                    } else {
                        i16::from_le_bytes([byte(i), byte(i + 1)])
                    }
                };
                visit(term, read(a, ca), read(b, cb));
            }
        }
        first = end;
    }
}

/// Writes table-dependent digits without changing the generic cache format.
pub(super) fn write_bases<C: PastaCurve>(
    records: &[ScalarStorage<C>],
    geometry: Geometry,
    digits: &mut [u8],
    bases: super::Bases<'_, C>,
) {
    if let Geometry::Alpha(width) = geometry {
        let codebook = bases.alpha().expect("α plan requires α bases");
        assert_eq!(codebook.description().window_bits(), width);
        for (record, row) in records
            .iter()
            .zip(digits.chunks_exact_mut(geometry.stride()))
        {
            codebook.write(record.halves, row);
        }
    } else {
        write(records, geometry, digits);
    }
}
