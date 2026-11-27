//! Canonical compressed encodings, independent of stored Montgomery layout.

use super::{AffinePoint, PastaCurve, Point, curve_rhs};
use crate::checks::assert_length;
use crate::field::PastaField;

/// Encodings decoded together by [`Point::batch_from_bytes`]: four
/// interleaved scalar chains, or two AVX2 vectors of four where the field
/// backend has them.
#[cfg(not(all(udon_avx2, not(miri))))]
const DECODE_LANES: usize = 4;
#[cfg(all(udon_avx2, not(miri)))]
const DECODE_LANES: usize = 8;

impl<C: PastaCurve> AffinePoint<C> {
    /// Encodes this point in 32 canonical compressed bytes.
    ///
    /// The low 255 bits hold canonical little-endian `x`; the high bit of the
    /// last byte is the parity of canonical `y` (set for odd). This encoding is
    /// independent of the Montgomery layout used by [`bento::Pod`].
    pub fn to_bytes(&self) -> [u8; 32] {
        let mut bytes = self.x.to_bytes();
        bytes[31] |= u8::from(self.y.is_odd()) << 7;
        bytes
    }

    /// Decodes a canonical compressed nonidentity point.
    ///
    /// Uses the format from [`Self::to_bytes`]. Returns `None` for the all-zero
    /// identity encoding or any encoding rejected by [`Point::from_bytes`].
    pub fn from_bytes(bytes: [u8; 32]) -> Option<Self> {
        Point::<C>::from_bytes(bytes)?.0
    }
}

impl<C: PastaCurve> Point<C> {
    /// Encodes identity as 32 zero bytes or a nonidentity point in compressed form.
    ///
    /// Nonidentity points use [`AffinePoint::to_bytes`].
    pub fn to_bytes(&self) -> [u8; 32] {
        self.as_affine().map_or([0; 32], AffinePoint::to_bytes)
    }

    /// Decodes identity or a canonical compressed point.
    ///
    /// Uses the format from [`Self::to_bytes`], accepting all-zero bytes as
    /// identity. For other inputs, returns `None` if `x` is at least the
    /// base-field modulus, `x³ + 5` has no square root, or neither root has the
    /// encoded parity. There is no affine point at `x = 0` on either Pasta
    /// curve, so identity's encoding is unambiguous; setting its sign bit is
    /// rejected.
    ///
    /// Both Pasta groups have prime order, so curve membership also establishes
    /// subgroup membership. No additional subgroup check is needed.
    pub fn from_bytes(mut bytes: [u8; 32]) -> Option<Self> {
        if bytes == [0; 32] {
            return Some(Self::IDENTITY);
        }
        let odd = bytes[31] >> 7 != 0;
        bytes[31] &= 0x7f;
        let x = PastaField::from_bytes(bytes)?;
        let mut y = curve_rhs::<C>(&x).reduce().sqrt()?;
        // Zero is the only root whose negation does not change parity.
        if y.is_zero() && odd {
            return None;
        }
        if y.is_odd() != odd {
            y = y.neg().reduce();
        }
        // Canonical decoding and the square root already establish reduced,
        // on-curve coordinates.
        debug_assert_eq!(y.square().reduce(), curve_rhs::<C>(&x).reduce());
        Some(
            AffinePoint {
                x,
                y,
                marker: core::marker::PhantomData,
            }
            .to_point(),
        )
    }

    /// Decodes a batch of encodings together, interleaving square-root chains.
    ///
    /// `output` must have exactly `encodings.len()` elements; a mismatch panics
    /// before either buffer changes. Accepts and rejects exactly the encodings
    /// [`Self::from_bytes`] does, writing the same points in order. Returns
    /// `None` when any encoding is rejected, leaving `output` unspecified.
    ///
    /// Full lane groups of ordinary encodings run their square-root
    /// exponentiations together: as interleaved scalar chains, or four per
    /// AVX2 register where the field backend has those kernels. Groups holding
    /// an identity encoding or a zero radicand decode one encoding at a time
    /// through [`Self::from_bytes`], as does a remainder shorter than a group
    /// unless padding it to whole vectors is cheaper.
    ///
    /// ```
    /// use zakura_udon::curve::{PallasPoint, PallasProjective};
    ///
    /// let g = PallasProjective::GENERATOR.to_point();
    /// let encodings = [g.to_bytes(), g.neg().to_bytes(), [0; 32]];
    /// let mut output = [PallasPoint::IDENTITY; 3];
    /// PallasPoint::batch_from_bytes(&encodings, &mut output).unwrap();
    /// assert_eq!(output, [g, g.neg(), PallasPoint::IDENTITY]);
    /// assert_eq!(PallasPoint::batch_from_bytes(&[[0xff; 32]], &mut [g]), None);
    /// ```
    pub fn batch_from_bytes(encodings: &[[u8; 32]], output: &mut [Self]) -> Option<()> {
        assert_length("output", encodings.len(), output.len());
        let mut chunks = encodings.chunks_exact(DECODE_LANES);
        let mut decoded = output.chunks_exact_mut(DECODE_LANES);
        for (chunk, decoded) in (&mut chunks).zip(&mut decoded) {
            let chunk = chunk.try_into().expect("chunks are lane sized");
            let decoded = decoded.try_into().expect("chunks are lane sized");
            decode_lanes::<C, DECODE_LANES>(chunk, decoded)?;
        }
        decode_remainder::<C>(chunks.remainder(), decoded.into_remainder())
    }
}

// Fewer encodings than a lane group. Scalar lanes gain nothing from padding,
// so each encoding decodes on its own.
#[cfg(not(all(udon_avx2, not(miri))))]
fn decode_remainder<C: PastaCurve>(encodings: &[[u8; 32]], output: &mut [Point<C>]) -> Option<()> {
    for (encoding, decoded) in encodings.iter().zip(output) {
        *decoded = Point::from_bytes(*encoding)?;
    }
    Some(())
}

// Fewer encodings than a lane group. An AVX2 vector of four lanes costs about
// as much as two scalar decodes however many of its lanes are used, so a
// remainder is padded up to whole vectors wherever that is the cheaper cover:
// three or four encodings take one vector, five take a vector and a scalar
// decode, and six or seven take two vectors.
#[cfg(all(udon_avx2, not(miri)))]
fn decode_remainder<C: PastaCurve>(encodings: &[[u8; 32]], output: &mut [Point<C>]) -> Option<()> {
    const VECTOR: usize = DECODE_LANES / 2;
    match encodings.len() {
        0 => Some(()),
        1 | 2 => decode_slice(encodings, output),
        count if count <= VECTOR => decode_padded::<C, VECTOR>(encodings, output),
        count if count == VECTOR + 1 => {
            let (encodings, last) = encodings.split_at(VECTOR);
            let (output, decoded) = output.split_at_mut(VECTOR);
            decode_padded::<C, VECTOR>(encodings, output)?;
            decode_slice(last, decoded)
        }
        _ => decode_padded::<C, DECODE_LANES>(encodings, output),
    }
}

#[cfg(all(udon_avx2, not(miri)))]
fn decode_slice<C: PastaCurve>(encodings: &[[u8; 32]], output: &mut [Point<C>]) -> Option<()> {
    for (encoding, decoded) in encodings.iter().zip(output) {
        *decoded = Point::from_bytes(*encoding)?;
    }
    Some(())
}

// Decodes up to `N` encodings as one lane group whose unused lanes repeat the
// first encoding, which changes neither the outcome nor any used lane.
#[cfg(all(udon_avx2, not(miri)))]
fn decode_padded<C: PastaCurve, const N: usize>(
    encodings: &[[u8; 32]],
    output: &mut [Point<C>],
) -> Option<()> {
    let mut group = [encodings[0]; N];
    group[..encodings.len()].copy_from_slice(encodings);
    let mut decoded = [Point::IDENTITY; N];
    decode_lanes::<C, N>(&group, &mut decoded)?;
    output.copy_from_slice(&decoded[..encodings.len()]);
    Some(())
}

// One full lane group. Any identity encoding or zero radicand routes the group
// through the scalar decoder: sqrt's zero short-circuit never enters the lane
// exponentiation, and such encodings are rare in honest batches.
fn decode_lanes<C: PastaCurve, const N: usize>(
    encodings: &[[u8; 32]; N],
    output: &mut [Point<C>; N],
) -> Option<()> {
    let mut xs = [PastaField::ZERO; N];
    let mut radicands = [PastaField::ZERO; N];
    let mut odd = [false; N];
    for lane in 0..N {
        let mut bytes = encodings[lane];
        if bytes == [0; 32] {
            return decode_each(encodings, output);
        }
        odd[lane] = bytes[31] >> 7 != 0;
        bytes[31] &= 0x7f;
        xs[lane] = PastaField::from_bytes(bytes)?;
        radicands[lane] = curve_rhs::<C>(&xs[lane]).reduce();
        if radicands[lane].is_zero() {
            return decode_each(encodings, output);
        }
    }
    let roots = PastaField::sqrt_lanes(&radicands);
    for lane in 0..N {
        let mut y = roots[lane]?;
        // Nonzero radicands have nonzero roots, so the zero-parity rejection in
        // from_bytes cannot trigger; correcting the parity suffices.
        if y.is_odd() != odd[lane] {
            y = y.neg().reduce();
        }
        debug_assert_eq!(y.square().reduce(), radicands[lane]);
        output[lane] = AffinePoint {
            x: xs[lane],
            y,
            marker: core::marker::PhantomData,
        }
        .to_point();
    }
    Some(())
}

fn decode_each<C: PastaCurve, const N: usize>(
    encodings: &[[u8; 32]; N],
    output: &mut [Point<C>; N],
) -> Option<()> {
    for (encoding, output) in encodings.iter().zip(output.iter_mut()) {
        *output = Point::from_bytes(*encoding)?;
    }
    Some(())
}
