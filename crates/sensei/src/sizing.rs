//! Checked storage and index dimensions for a proving request.
//!
//! These bounds prevent arithmetic overflow and unrepresentable slices. They
//! do not reserve memory or enforce a caller's resource policy.
use crate::{Action, Error};
use sensei_shared::{ADVICE_COLUMNS, N};

/// Maximum Actions expanded in one quotient window.
///
/// Bounds transient cosets, not total proof memory: coefficients retained for
/// openings and stage records still scale with the request's Action count.
pub(crate) const ACTION_WINDOW: usize = 16;

#[derive(Clone, Copy, Debug)]
pub(crate) struct RequestShape {
    pub(crate) actions: usize,
    pub(crate) proof_bytes: usize,
    pub(crate) random_words: usize,
}

fn count<T>(items: usize, per_item: usize) -> Option<usize> {
    items
        .checked_mul(per_item)
        .filter(|n| *n <= isize::MAX as usize / size_of::<T>().max(1))
}

impl RequestShape {
    pub(crate) fn new(actions: usize) -> Result<Self, Error> {
        Self::checked(actions).ok_or(Error::InvalidInput)
    }
    fn checked(actions: usize) -> Option<Self> {
        if actions == 0 {
            return None;
        }
        count::<Action>(actions, 1)?;
        let proof_bytes = crate::native::protocol::transcript_encoding::proof_capacity(actions)?;
        count::<u8>(proof_bytes, 1)?;
        let samples = actions.checked_mul(148)?.checked_add(46)?;
        let random_words = count::<u64>(samples, 8)?;
        // Advice, permuted lookups, and products survive until openings.
        let polynomials = count::<usize>(actions, ADVICE_COLUMNS + 6 + 6)?;
        count::<udon::field::Fp>(polynomials, N)?;
        count::<udon::field::Fp>(actions, crate::native::prover::fold_order::TERMS_PER_ACTION)?;
        count::<udon::field::Fp>(actions.checked_mul(49)?.checked_add(45)?, 1)?;
        // Also bound scalar records, work/frontier indices, and their rounding.
        count::<udon::msm::ScalarStorage<udon::curve::Vesta>>(polynomials, N)?;
        count::<usize>(polynomials, 32)?;
        Some(Self {
            actions,
            proof_bytes,
            random_words,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn accepts_dynamic_counts_and_rejects_size_overflow() {
        let mut counts = vec![1, 2, 16, 17, 63, 64, 65, 128];
        if usize::BITS >= 64 {
            counts.extend([1024, 1_000_000]);
        }
        for actions in counts {
            let shape = RequestShape::new(actions).unwrap();
            assert_eq!(shape.proof_bytes, 2720 + 2272 * actions);
            assert_eq!(shape.random_words, (148 * actions + 46) * 8);
        }
        for actions in [0, usize::MAX, usize::MAX / 148, isize::MAX as usize / N] {
            assert!(matches!(
                RequestShape::new(actions),
                Err(Error::InvalidInput)
            ));
        }
    }
}
