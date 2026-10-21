//! Shared construction of window bases, candidate points, and stored entries.
//!
//! Construction proceeds in three steps: powers of the multiplication base,
//! eight candidate digits per window, then the `(x, y, u)` records. Preserve
//! both region/window/digit order and the final-window offset convention;
//! generators and witness construction address these tables identically.

use alloc::vec::Vec;
use udon::{
    curve::{PallasAffine, PallasPoint, PallasProjective, batch_normalize},
    field::Fp,
};

use super::{
    FIXED_BASE_REGIONS, FIXED_BASE_TOTAL_WINDOWS, FIXED_BASE_WINDOW_BITS, FIXED_BASE_WINDOW_SIZE,
    FixedBase, fixed_base_window_offset, root_signs::ROOT_SIGNS,
};
use crate::records::WindowTableEntry;

/// The per-window bases `2^{3w}·G` of one fixed-base multiplication, affine
/// and in window order, together with the projective offset
/// `sum of 2·2^{3w}·G` over all but the final window. Used to derive the
/// circuit's candidate points and window tables.
///
/// The returned vector has `window_count` entries. With no windows it is
/// empty and the offset is the identity. [`PallasPoint`] represents identity
/// entries as well as affine points; candidate construction checks that its
/// window bases have affine coordinates.
pub fn fixed_window_bases(
    generator: &PallasAffine,
    window_count: usize,
) -> (Vec<PallasPoint>, PallasProjective) {
    let mut window_base = PallasProjective::from_affine(generator);
    let mut window_bases = Vec::with_capacity(window_count);
    for index in 0..window_count {
        window_bases.push(window_base);
        if index + 1 != window_count {
            for _ in 0..FIXED_BASE_WINDOW_BITS {
                window_base = window_base.double();
            }
        }
    }
    let offset = window_bases
        .iter()
        .take(window_bases.len().saturating_sub(1))
        .fold(PallasProjective::IDENTITY, |sum, base| sum.add(base))
        .double();
    (
        {
            let mut output = alloc::vec![udon::curve::Point::IDENTITY; window_bases.len()];
            let mut scratch = alloc::vec![udon::field::PastaField::ZERO; window_bases.len()];
            batch_normalize(&window_bases, &mut output, &mut scratch);
            output
        },
        offset,
    )
}

/// Every normalized candidate window point of one fixed-base multiplication,
/// flat in `[window][digit]` order: digit scalars `2..10` per non-final
/// window, and the offset-adjusted `0..8` of the final one — exactly the
/// points selected by the witness writer. Each region's candidates are
/// normalized together before the table's entries are constructed.
///
/// Returns `None` if a window base is the identity. Candidate points themselves
/// may be the identity; the stored-table builder requires affine coordinates
/// for every candidate. `window_count` is used as supplied and is not checked
/// against the base's pinned `z`-column length here.
pub fn fixed_base_window_candidates(
    base: FixedBase,
    window_count: usize,
) -> Option<Vec<PallasPoint>> {
    // Window bases 2^{3w}·G and the circuit's final-window offset.
    let (affine_bases, offset) = fixed_window_bases(&base.generator(), window_count);
    let neg_offset = offset.neg();
    let mut candidates = Vec::with_capacity(window_count * FIXED_BASE_WINDOW_SIZE as usize);
    for (index, window_base) in affine_bases.iter().enumerate() {
        let base_affine = window_base.as_affine()?;
        let is_final = index + 1 == window_count;
        let mut point = if is_final {
            neg_offset
        } else {
            base_affine.to_projective().double()
        };
        for digit in 0..FIXED_BASE_WINDOW_SIZE {
            candidates.push(point);
            if digit + 1 != FIXED_BASE_WINDOW_SIZE {
                point = point.add_mixed(base_affine);
            }
        }
    }
    Some({
        let mut output = alloc::vec![udon::curve::Point::IDENTITY; candidates.len()];
        let mut scratch = alloc::vec![udon::field::PastaField::ZERO; candidates.len()];
        batch_normalize(&candidates, &mut output, &mut scratch);
        output
    })
}

/// Builds the joint `(x, y, u)` window entries of every fixed-base region,
/// flat in [`FIXED_BASE_REGIONS`] order with each slot's windows starting at
/// [`super::fixed_base_window_offset`], indexed `[window][digit]`, each window's
/// pinned interpolation parameter `z` supplying `u = sqrt(y + z)`.
///
/// All values are witness-independent: the host-side generator bakes them
/// into the window-table artifact, and the prover runs this same code at load
/// when that artifact is not embedded, so the two views agree by
/// construction.
///
/// Returns `None` if a window base or candidate is the identity, a window
/// lacks a pinned `z` value, or `y + z` has no square root. The selected root
/// uses the pinned historical canonical parity, independent of [`Fp::sqrt`].
pub fn build_fixed_base_window_tables()
-> Option<Vec<[WindowTableEntry; FIXED_BASE_WINDOW_SIZE as usize]>> {
    let window_size = FIXED_BASE_WINDOW_SIZE as usize;
    let mut table = Vec::with_capacity(FIXED_BASE_TOTAL_WINDOWS);
    for (slot, (_, base, window_count)) in FIXED_BASE_REGIONS.into_iter().enumerate() {
        if let Some(previous_slot) =
            FIXED_BASE_REGIONS[..slot]
                .iter()
                .position(|(_, previous_base, previous_count)| {
                    *previous_base == base && *previous_count == window_count
                })
        {
            let source = fixed_base_window_offset(previous_slot);
            let destination = table.len();
            // The two note-commitment regions share their candidates and z
            // values. Reuse their roots too when the pinned choices match.
            if ROOT_SIGNS[source..source + window_count]
                == ROOT_SIGNS[destination..destination + window_count]
            {
                table.extend_from_within(source..source + window_count);
                continue;
            }
        }
        let candidates = fixed_base_window_candidates(base, window_count)?;
        let z_column = base.z_column();

        // Pair each candidate with its interpolation value u = sqrt(y + z).
        for window in 0..window_count {
            let z = <Fp>::from_u64(*z_column.get(window)?);
            let mut entries = [WindowTableEntry {
                x: <Fp>::ZERO,
                y: <Fp>::ZERO,
                u: <Fp>::ZERO,
            }; FIXED_BASE_WINDOW_SIZE as usize];
            for (digit, entry) in entries.iter_mut().enumerate() {
                let (x, y) = candidates[window * window_size + digit].coordinates()?;
                let u = y.add(&z).reduce().sqrt()?.into_loose();
                let odd = (ROOT_SIGNS[table.len()] >> digit) & 1;
                let u = if u.to_bytes()[0] & 1 == odd {
                    u
                } else {
                    u.neg()
                };
                *entry = WindowTableEntry {
                    x: x.into_loose(),
                    y: y.into_loose(),
                    u,
                };
            }
            table.push(entries);
        }
    }
    Some(table)
}

#[cfg(test)]
mod tests {
    use super::*;
    use udon::field::Fq;

    #[test]
    fn candidate_chains_match_independent_scalar_multiplication() {
        let base = FixedBase::NoteCommitR;
        let generator = base.generator();
        for count in [
            0,
            1,
            2,
            super::super::SHORT_SCALAR_WINDOWS,
            super::super::FULL_SCALAR_WINDOWS,
        ] {
            let candidates = fixed_base_window_candidates(base, count).unwrap();
            assert_eq!(candidates.len(), count * FIXED_BASE_WINDOW_SIZE as usize);
            // Derive the offset in the scalar field, independently of the
            // projective window-base accumulation.
            let mut power = <Fq>::ONE;
            let mut offset = <Fq>::ZERO;
            for _ in 0..count.saturating_sub(1) {
                offset = offset.add(&power.double());
                power = power.mul(&<Fq>::from_u64(FIXED_BASE_WINDOW_SIZE));
            }
            power = <Fq>::ONE;
            for (window, points) in candidates
                .chunks_exact(FIXED_BASE_WINDOW_SIZE as usize)
                .enumerate()
            {
                for (digit, point) in points.iter().enumerate() {
                    let scalar = if window + 1 == count {
                        power.mul(&<Fq>::from_u64(digit as u64)).sub(&offset)
                    } else {
                        power.mul(&<Fq>::from_u64(digit as u64 + 2))
                    };
                    assert_eq!(
                        *point,
                        generator.mul_projective(&scalar).to_point(),
                        "count {count}, window {window}, digit {digit}"
                    );
                }
                power = power.mul(&<Fq>::from_u64(FIXED_BASE_WINDOW_SIZE));
            }
        }
    }
}
