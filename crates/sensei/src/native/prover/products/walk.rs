//! Shared exclusive product walk and the test-only grouped-inversion adapter.

use crate::Error;
use crate::native::field::Fp;
#[cfg(test)]
use alloc::vec::Vec;

/// Exclusive grand-product walk `z_k = Π_{j<k} n_j / Π_{j<k} d_j` over `len`
/// rows in two independent interleaved lanes (rows `0..len/2` and
/// `len/2..len`): each lane runs its own numerator and denominator prefix
/// chains forward, the two denominator totals are inverted with one inversion
/// (the lane inverses cost two more multiplications), the second lane's
/// backward inverse chain is seeded with the first lane's ratio `z_{len/2}`
/// so its states come out as global exclusive products, and both backward
/// chains recover their exclusive inverse prefixes independently. Per row the
/// multiplication count is that of the single-lane walk (two forward, two
/// backward); the walk adds four multiplications in total. The sequential
/// dependency chain is halved, which is the whole point: the chains are
/// latency-bound. Field arithmetic is exact, so every `z_k` equals the
/// single-lane walk's value.
///
/// `row_factors(k)` yields `(n_k, d_k)`; `states[k]` receives `z_k` for
/// `k < len` and `denominators` every `d_k` in row order. Returns the final
/// product `z_len`, or `None` — with `denominators` filled and `states`
/// unspecified — when the denominator product is zero, for the caller's
/// zero-preserving reference fallback.
pub(in crate::native::prover) fn two_lane_exclusive_walk(
    len: usize,
    mut row_factors: impl FnMut(usize) -> Result<(Fp, Fp), Error>,
    states: &mut [Fp],
    denominators: &mut [Fp],
) -> Result<Option<Fp>, Error> {
    if states.len() < len || denominators.len() < len {
        return Err(Error::InternalInvariant);
    }
    let split = len / 2;
    let lanes = [(0, split), (split, len)];
    let mut numerator_prefixes = [<Fp>::ONE; 2];
    let mut denominator_prefixes = [<Fp>::ONE; 2];
    // Forward: the lanes advance together; the second may hold one more row.
    for step in 0..len - split {
        for (lane, &(start, end)) in lanes.iter().enumerate() {
            let index = start + step;
            if index >= end {
                continue;
            }
            let (numerator, denominator) = row_factors(index)?;
            states[index] = numerator_prefixes[lane];
            denominators[index] = denominator;
            numerator_prefixes[lane] = numerator_prefixes[lane].mul(&numerator);
            denominator_prefixes[lane] = denominator_prefixes[lane].mul(&denominator);
        }
    }
    let Some(inverse) = denominator_prefixes[0]
        .mul(&denominator_prefixes[1])
        .invert()
    else {
        return Ok(None);
    };
    // `(D_0·D_1)⁻¹·D_1 = D_0⁻¹` and `(D_0·D_1)⁻¹·D_0 = D_1⁻¹`; the second
    // lane's chain carries `z_{split} = N_0·D_0⁻¹` so its exclusive products
    // include the first lane's totals.
    let inverse_0 = inverse.mul(&denominator_prefixes[1]);
    let inverse_1 = inverse.mul(&denominator_prefixes[0]);
    let carry = numerator_prefixes[0].mul(&inverse_0);
    let mut inverses = [inverse_0, inverse_1.mul(&carry)];
    let final_product = numerator_prefixes[1].mul(&inverses[1]);
    // Backward: each chain multiplies its lane's denominators back in, so
    // `inverses[lane]` holds the exclusive inverse prefix at the current row.
    for step in (0..len - split).rev() {
        for (lane, &(start, end)) in lanes.iter().enumerate() {
            let index = start + step;
            if index >= end {
                continue;
            }
            inverses[lane] = inverses[lane].mul(&denominators[index]);
            states[index] = states[index].mul(&inverses[lane]);
        }
    }
    Ok(Some(final_product))
}

/// Reuses the caller's prefix allocation for Udon's zero-preserving batch inverse.
#[cfg(test)]
pub(in crate::native::prover) fn batch_invert_groups(
    groups: &mut [Vec<Fp>],
    prefixes: &mut Vec<Fp>,
) {
    prefixes.resize(groups.iter().map(Vec::len).sum(), <Fp>::ZERO);
    crate::native::field::batch_invert_groups(groups, prefixes);
}
