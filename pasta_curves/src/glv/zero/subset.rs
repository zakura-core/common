//! Fixed-base subset-table baseline: the classical time/memory tradeoff the
//! prepared codebook must beat at comparable memory.
//!
//! The bases are partitioned into blocks of `block_bits` points and every
//! block's $2^t$ subset sums are precomputed (affine, one shared
//! normalization per block). A zero-check then walks the scalar bits from
//! the top: per bit column, double the accumulator once and add one
//! precomputed subset sum per block, selected by the block's bit mask. No
//! GLV, no endomorphisms — the point of this baseline is to price the
//! fixed-base assumption alone.
//!
//! At $n = 2048$ and $t = 12$ this stores about 700k affine points
//! (~45 MiB) and performs ~43k dependent mixed additions per check.

use alloc::vec::Vec;

use ff::PrimeField;
use group::CurveAffine as _;

use super::super::{scalar_limbs, GlvParams};

/// A prepared subset-sum table over a fixed base list.
#[derive(Debug)]
pub(crate) struct SubsetTable<C: GlvParams> {
    /// Flat table: `block * 2^block_bits + mask`, mask 0 = identity.
    sums: Vec<C::AffineExt>,
    block_bits: usize,
    terms: usize,
}

impl<C: GlvParams> SubsetTable<C> {
    /// Precomputes all block subset sums. `block_bits` in `1..=16`.
    pub(crate) fn prepare(bases: &[C::AffineExt], block_bits: usize) -> Self {
        assert!((1..=16).contains(&block_bits));
        let stride = 1usize << block_bits;
        let blocks = bases.len().div_ceil(block_bits.max(1));
        let mut sums = alloc::vec![C::AffineExt::identity(); blocks * stride];
        let mut projective = alloc::vec![C::identity(); stride];
        for (block, chunk) in bases.chunks(block_bits).enumerate() {
            let masks = 1usize << chunk.len();
            for mask in 1..masks {
                let low = mask.trailing_zeros() as usize;
                projective[mask] = projective[mask & (mask - 1)] + chunk[low];
            }
            C::batch_normalize(
                &projective[..masks],
                &mut sums[block * stride..block * stride + masks],
            );
        }
        SubsetTable {
            sums,
            block_bits,
            terms: bases.len(),
        }
    }

    /// The prepared memory footprint in bytes.
    pub(crate) fn bytes(&self) -> usize {
        self.sums.len() * core::mem::size_of::<C::AffineExt>()
    }

    /// Whether $\sum_i \[k_i\] P_i$ is the identity.
    pub(crate) fn is_zero_vartime(&self, scalars: &[C::ScalarExt]) -> bool {
        assert_eq!(scalars.len(), self.terms);
        let limbs: Vec<[u64; 4]> = scalars.iter().map(scalar_limbs).collect();
        let stride = 1usize << self.block_bits;
        let bits = C::ScalarExt::NUM_BITS as usize;
        let mut acc = C::identity();
        for bit in (0..bits).rev() {
            acc = acc.double();
            let (limb, shift) = (bit / 64, bit % 64);
            for (block, chunk) in limbs.chunks(self.block_bits).enumerate() {
                let mut mask = 0usize;
                for (position, scalar) in chunk.iter().enumerate() {
                    mask |= (((scalar[limb] >> shift) & 1) as usize) << position;
                }
                if mask != 0 {
                    acc += self.sums[block * stride + mask];
                }
            }
        }
        bool::from(acc.is_identity())
    }
}

#[cfg(test)]
mod tests {
    use super::super::testutil::zero_relation;
    use super::*;
    use crate::{pallas, vesta};
    use ff::Field;

    fn subset_zero_checks<C: GlvParams>() {
        let (scalars, bases) = zero_relation::<C>(70, 9);
        for block_bits in [3, 5, 8] {
            let table = SubsetTable::<C>::prepare(&bases, block_bits);
            assert!(table.is_zero_vartime(&scalars));
            let mut perturbed = scalars.clone();
            // Index 0 is an identity base in the corpus; perturb a live one.
            perturbed[10] += C::ScalarExt::ONE;
            assert!(!table.is_zero_vartime(&perturbed));
            let zeros = alloc::vec![C::ScalarExt::ZERO; bases.len()];
            assert!(table.is_zero_vartime(&zeros));
        }
    }

    macro_rules! subset_tests {
        ($mod_name:ident, $curve:ty) => {
            mod $mod_name {
                use super::*;

                #[test]
                fn zero_checks() {
                    subset_zero_checks::<$curve>();
                }
            }
        };
    }

    subset_tests!(pallas_subset, pallas::Point);
    subset_tests!(vesta_subset, vesta::Point);
}
