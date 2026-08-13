use core::{cmp, fmt, ops::Range};

use ff::PrimeField;
use group::{Curve, Group};

use crate::arithmetic::CurveAffine;

use super::{
    PROVER_FIXED_MSM_TABLE_BASES, PROVER_FIXED_MSM_TABLE_BLOCKS,
    PROVER_FIXED_MSM_TABLE_BLOCK_BASES, PROVER_FIXED_MSM_TABLE_POINTS,
};

#[derive(Debug)]
struct Block {
    base_start: usize,
    base_len: usize,
    table_start: usize,
}

/// A proving-only subset table for the fixed `g || w` bases.
///
/// The table omits each block's identity entry. Scalar-dependent indexing is
/// acceptable here because Halo 2 proving already uses variable-time MSMs.
pub(super) struct FixedBaseMsmTable<C: CurveAffine> {
    blocks: Vec<Block>,
    points: Vec<C>,
}

impl<C: CurveAffine> fmt::Debug for FixedBaseMsmTable<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FixedBaseMsmTable")
            .field("blocks", &self.blocks.len())
            .field("points", &self.points.len())
            .finish()
    }
}

impl<C: CurveAffine> FixedBaseMsmTable<C> {
    pub(super) fn new(g: &[C], w: C) -> Self {
        assert_eq!(g.len() + 1, PROVER_FIXED_MSM_TABLE_BASES);

        let mut blocks = Vec::with_capacity(PROVER_FIXED_MSM_TABLE_BLOCKS);
        let mut projective = Vec::with_capacity(PROVER_FIXED_MSM_TABLE_POINTS);

        for base_start in
            (0..PROVER_FIXED_MSM_TABLE_BASES).step_by(PROVER_FIXED_MSM_TABLE_BLOCK_BASES)
        {
            let base_len = cmp::min(
                PROVER_FIXED_MSM_TABLE_BLOCK_BASES,
                PROVER_FIXED_MSM_TABLE_BASES - base_start,
            );
            let table_start = projective.len();
            let table_len = 1usize << base_len;

            for mask in 1..table_len {
                let bit = mask.trailing_zeros() as usize;
                let previous = mask & (mask - 1);
                let base_index = base_start + bit;
                let base = if base_index < g.len() {
                    g[base_index]
                } else {
                    debug_assert_eq!(base_index, g.len());
                    w
                };
                let point = if previous == 0 {
                    base.to_curve()
                } else {
                    let mut point = projective[table_start + previous - 1];
                    point += base;
                    point
                };
                projective.push(point);
            }

            blocks.push(Block {
                base_start,
                base_len,
                table_start,
            });
        }

        assert_eq!(blocks.len(), PROVER_FIXED_MSM_TABLE_BLOCKS);
        assert_eq!(projective.len(), PROVER_FIXED_MSM_TABLE_POINTS);

        let mut points = vec![C::identity(); PROVER_FIXED_MSM_TABLE_POINTS];
        C::Curve::batch_normalize(&projective, &mut points);

        Self { blocks, points }
    }

    pub(super) fn multiply(&self, scalars: &[C::Scalar]) -> C::Curve {
        assert_eq!(scalars.len(), PROVER_FIXED_MSM_TABLE_BASES);
        self.multiply_range(0, scalars)
    }

    pub(super) fn multiply_range(&self, base_start: usize, scalars: &[C::Scalar]) -> C::Curve {
        let base_end = base_start
            .checked_add(scalars.len())
            .expect("fixed-base MSM range length overflowed");
        assert!(base_end <= PROVER_FIXED_MSM_TABLE_BASES);

        let scalar_reprs = scalars.iter().map(PrimeField::to_repr).collect::<Vec<_>>();
        let mut accumulator = C::Curve::identity();

        for bit in (0..C::Scalar::NUM_BITS as usize).rev() {
            if bit + 1 != C::Scalar::NUM_BITS as usize {
                accumulator = accumulator.double();
            }

            for block in &self.blocks {
                let block_end = block.base_start + block.base_len;
                let overlap = cmp::max(base_start, block.base_start)..cmp::min(base_end, block_end);
                if overlap.is_empty() {
                    continue;
                }

                let mask = self.range_mask(&scalar_reprs, base_start, block, overlap, bit);
                if mask != 0 {
                    accumulator += self.points[block.table_start + mask - 1];
                }
            }
        }

        accumulator
    }

    fn range_mask(
        &self,
        scalar_reprs: &[<C::Scalar as PrimeField>::Repr],
        range_start: usize,
        block: &Block,
        overlap: Range<usize>,
        bit: usize,
    ) -> usize {
        overlap.fold(0, |mask, base_index| {
            let repr = scalar_reprs[base_index - range_start].as_ref();
            let scalar_bit = (repr[bit / 8] >> (bit % 8)) & 1;
            mask | (usize::from(scalar_bit) << (base_index - block.base_start))
        })
    }
}

#[cfg(test)]
mod tests {
    use core::fmt::Debug;

    use ff::{Field, PrimeField};
    use group::{Curve, Group};
    use pasta_curves::{pallas, vesta};

    use crate::arithmetic::{best_multiexp, CurveAffine};

    use super::{
        FixedBaseMsmTable, PROVER_FIXED_MSM_TABLE_BASES, PROVER_FIXED_MSM_TABLE_BLOCKS,
        PROVER_FIXED_MSM_TABLE_POINTS,
    };

    fn power_of_two<F: Field>(bit: usize) -> F {
        (0..bit).fold(F::ONE, |value, _| value.double())
    }

    fn check_table<C>()
    where
        C: CurveAffine + Debug,
        C::Curve: Debug,
    {
        let bases = (0..PROVER_FIXED_MSM_TABLE_BASES)
            .map(|index| (C::Curve::generator() * C::Scalar::from(index as u64 + 1)).to_affine())
            .collect::<Vec<C>>();
        let (g, w) = bases.split_at(PROVER_FIXED_MSM_TABLE_BASES - 1);
        let table = FixedBaseMsmTable::new(g, w[0]);

        assert_eq!(table.blocks.len(), PROVER_FIXED_MSM_TABLE_BLOCKS);
        assert_eq!(table.points.len(), PROVER_FIXED_MSM_TABLE_POINTS);
        assert_eq!(table.points.capacity(), PROVER_FIXED_MSM_TABLE_POINTS);

        let ranges = [
            0..PROVER_FIXED_MSM_TABLE_BASES,
            1020..1021,
            1020..1024,
            1024..1025,
            1020..1030,
            1024..1030,
            1029..1030,
            2040..2041,
            2040..2047,
            2047..2048,
            2040..2048,
            2040..PROVER_FIXED_MSM_TABLE_BASES,
            2047..PROVER_FIXED_MSM_TABLE_BASES,
            2048..PROVER_FIXED_MSM_TABLE_BASES,
        ];

        for range in ranges {
            let mut scalars = (range.clone())
                .map(|index| C::Scalar::from((index as u64 + 3) * 0x1_0001))
                .collect::<Vec<_>>();
            if !scalars.is_empty() {
                let middle = scalars.len() / 2;
                let last = scalars.len() - 1;
                scalars[0] = -C::Scalar::ONE;
                scalars[middle] = power_of_two(128);
                scalars[last] = power_of_two(C::Scalar::NUM_BITS as usize - 1);
            }

            assert_eq!(
                table.multiply_range(range.start, &scalars),
                best_multiexp(&scalars, &bases[range]),
            );
        }

        let full_scalars = (0..PROVER_FIXED_MSM_TABLE_BASES)
            .map(|index| C::Scalar::from(index as u64 + 1))
            .collect::<Vec<_>>();
        assert_eq!(
            table.multiply(&full_scalars),
            best_multiexp(&full_scalars, &bases),
        );
    }

    #[test]
    fn pallas_full_and_range_msm_match() {
        check_table::<pallas::Affine>();
    }

    #[test]
    fn vesta_full_and_range_msm_match() {
        check_table::<vesta::Affine>();
    }
}
