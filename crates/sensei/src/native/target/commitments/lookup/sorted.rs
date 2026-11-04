//! Abel summation for an ascending ten-bit usable prefix.

use super::*;

/// Full-domain suffixes `H[i] = sum_{j >= i} G[j]`, each stored as H, 2H, 4H.
/// Affine storage permits mixed additions and occupies 3 * N * 64 bytes.
pub(crate) struct SuffixGenerators {
    multiples: Vec<VestaAffine>,
}

impl SuffixGenerators {
    pub(crate) fn new(bases: &[PreparedAffinePoint<Vesta>]) -> Result<Self, TargetError> {
        if bases.len() != N {
            return Err(TargetError::Dimension);
        }
        let mut points = alloc::vec![VestaProjective::IDENTITY; 3 * N];
        let mut suffix = VestaProjective::IDENTITY;
        for row in (0..N).rev() {
            suffix = suffix.add_mixed(&bases[row].to_affine());
            points[3 * row] = suffix;
            points[3 * row + 1] = suffix.double();
            points[3 * row + 2] = points[3 * row + 1].double();
        }
        let multiples = normalized(&points)
            .iter()
            .map(|point| point.as_affine().copied())
            .collect::<Option<Vec<_>>>()
            .ok_or(TargetError::Malformed)?;
        Ok(Self { multiples })
    }

    pub(super) fn commit(&self, prefix: &SortedPrefix) -> VestaProjective {
        // Alternating chains let independent field operations overlap. The
        // outer commitment scheduler supplies lookup/Action parallelism.
        let mut chains = [VestaProjective::IDENTITY; 2];
        let mut lane = 0;
        for &(row, delta) in &prefix.deltas {
            let multiples = &self.multiples[3 * row as usize..][..3];
            for _ in 0..delta / 4 {
                chains[lane] = chains[lane].add_mixed(&multiples[2]);
                lane ^= 1;
            }
            if delta & 2 != 0 {
                chains[lane] = chains[lane].add_mixed(&multiples[1]);
                lane ^= 1;
            }
            if delta & 1 != 0 {
                chains[lane] = chains[lane].add_mixed(&multiples[0]);
                lane ^= 1;
            }
        }
        chains[0].add(&chains[1])
    }
}

pub(super) struct SortedPrefix {
    deltas: Vec<(u32, u16)>,
    #[cfg(test)]
    pub(super) last: Fp,
    #[cfg(test)]
    pub(super) interval_cost: usize,
}

impl SortedPrefix {
    #[cfg(test)]
    pub(super) fn from_runs(runs: &[(u32, Fp)]) -> Option<Self> {
        SortedAnalysis::new(runs).map(|analysis| analysis.materialize(runs))
    }
}

#[derive(Clone, Copy)]
pub(super) struct SortedAnalysis {
    pub(super) last: Fp,
    pub(super) additions: usize,
    /// Signed-window cost of the equivalent usable-prefix interval MSM.
    pub(super) interval_cost: usize,
    nonzero_deltas: usize,
}

impl SortedAnalysis {
    /// Eligibility depends on compressed values, including theta collisions.
    /// Inspect the runs without allocating a candidate representation.
    pub(super) fn new(runs: &[(u32, Fp)]) -> Option<Self> {
        let mut previous = 0;
        let mut previous_row = 0;
        let mut additions = 0;
        let mut interval_cost = 0;
        let mut nonzero_deltas = 0;
        for (index, &(row, value)) in runs.iter().enumerate() {
            let limbs = value.to_canonical_uint().limbs();
            if limbs[1] | limbs[2] | limbs[3] != 0 || limbs[0] > 1023 {
                return None;
            }
            let value = limbs[0] as u16;
            if row as usize >= USABLE_ROWS_END
                || (index == 0 && row != 0)
                || (index != 0 && (row <= previous_row || value <= previous))
            {
                return None;
            }
            let delta = value - previous;
            if index != 0 {
                interval_cost += 1 + (u16::BITS - delta.leading_zeros()).div_ceil(4) as usize;
            }
            nonzero_deltas += usize::from(delta != 0);
            additions += usize::from(delta / 4) + (delta % 4).count_ones() as usize;
            previous = value;
            previous_row = row;
        }
        if runs.is_empty() {
            return None;
        }
        Some(Self {
            last: Fp::from_u64(u64::from(previous)),
            additions,
            interval_cost: interval_cost
                + if previous == 0 {
                    0
                } else {
                    1 + (u16::BITS - previous.leading_zeros()).div_ceil(4) as usize
                },
            nonzero_deltas,
        })
    }

    pub(super) fn materialize(self, runs: &[(u32, Fp)]) -> SortedPrefix {
        let mut deltas = Vec::with_capacity(self.nonzero_deltas);
        let mut previous = 0;
        for &(row, value) in runs {
            let value = value.to_canonical_uint().limbs()[0] as u16;
            if value != previous {
                deltas.push((row, value - previous));
            }
            previous = value;
        }
        SortedPrefix {
            deltas,
            #[cfg(test)]
            last: self.last,
            #[cfg(test)]
            interval_cost: self.interval_cost,
        }
    }
}
