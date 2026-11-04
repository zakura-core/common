//! Orchard Merkle hashing, with complete and weighted batch paths.
//!
//! The standard domain and weighted domain's tables follow the primitive
//! [cache ownership](crate::primitives#lazy-data-and-ownership) policy. With
//! pointer atomics, racing first uses may build multiple weighted domains before
//! one is retained; without them, each access rebuilds and owns its domain.
//! [`BatchWorkspace`] retains caller-owned scratch independently of those caches.
use super::cache::{Cache as OnceBox, Cached};
use super::{
    Fp, leos2bsp, pallas,
    sinsemilla::{
        HashDomain, K,
        weighted::{BatchHashWorkspace, UncheckedFixedLengthHashDomain},
    },
};
use alloc::{boxed::Box, vec::Vec};

const BASE_BITS: usize = Fp::NUM_BITS as usize;
const DOMAIN: &str = "z.cash:Orchard-MerkleCRH";
/// A Merkle parent hash consumes a left and a right child.
const MERKLE_CRH_CHILDREN: usize = 2;
/// The level word is followed by one field encoding for each child.
const MERKLE_CRH_BITS: usize = K + MERKLE_CRH_CHILDREN * BASE_BITS;
/// Orchard Merkle CRH inputs always pad to this many Sinsemilla words.
const MERKLE_CRH_WORDS: usize = MERKLE_CRH_BITS / K;
const _: () = assert!(MERKLE_CRH_BITS.is_multiple_of(K));
/// Complete Sinsemilla words in one 255-bit child encoding.
const MERKLE_CRH_FULL_CHILD_WORDS: usize = BASE_BITS / K;
/// Bits left after decoding a child's complete Sinsemilla words.
const MERKLE_CRH_CHILD_REMAINDER_BITS: usize = BASE_BITS % K;
/// Index of the word spanning the left and right child encodings.
const MERKLE_CRH_CROSS_CHILD_WORD: usize = 1 + MERKLE_CRH_FULL_CHILD_WORDS;
const SINSEMILLA_WORD_MASK: u16 = (1 << K) - 1;
const CHILD_REMAINDER_MASK: u8 = (1 << MERKLE_CRH_CHILD_REMAINDER_BITS) - 1;
const BYTE_BITS: usize = u8::BITS as usize;

static STANDARD: OnceBox<HashDomain> = OnceBox::new();
static WEIGHTED: OnceBox<UncheckedFixedLengthHashDomain<MERKLE_CRH_WORDS>> = OnceBox::new();
fn standard() -> Cached<HashDomain> {
    STANDARD.get_or_init(|| Box::new(HashDomain::new(DOMAIN)))
}
fn weighted() -> Cached<UncheckedFixedLengthHashDomain<MERKLE_CRH_WORDS>> {
    WEIGHTED.get_or_init(|| {
        Box::new(UncheckedFixedLengthHashDomain::new(
            core::ops::Deref::deref(&standard()),
        ))
    })
}
fn message(level: u8, left: Fp, right: Fp) -> impl Iterator<Item = bool> {
    (0..K)
        .map(move |bit| (u16::from(level) >> bit) & 1 != 0)
        .chain(leos2bsp(left.to_bytes()).take(BASE_BITS))
        .chain(leos2bsp(right.to_bytes()).take(BASE_BITS))
}
/// Computes a Merkle parent with Sinsemilla failure mapped to zero.
pub fn hash(level: u8, left: Fp, right: Fp) -> Fp {
    standard()
        .hash(message(level, left, right))
        .unwrap_or(Fp::ZERO)
}
/// Computes parents with one shared normalization of all successful hashes.
pub fn hash_batch(level: u8, pairs: impl IntoIterator<Item = (Fp, Fp)>) -> Vec<Fp> {
    let points: Vec<_> = pairs
        .into_iter()
        .map(|(left, right)| standard().hash_to_point(message(level, left, right)))
        .collect();
    let normalized = pallas::normalize_batch(
        points
            .iter()
            .map(|point| point.unwrap_or(pallas::Point::identity())),
    );
    normalized
        .into_iter()
        .zip(points)
        .map(|(point, valid)| {
            if bool::from(valid.is_some()) {
                point.raw_coordinates().0
            } else {
                Fp::ZERO
            }
        })
        .collect()
}
/// Reusable allocations for the fixed-length weighted hash path.
///
/// Owns the message, result, and scratch buffers used by [`weighted_hash_batch`].
/// Their capacities are retained across calls, including empty or smaller
/// batches, until this workspace is dropped.
#[derive(Debug, Default)]
pub struct BatchWorkspace {
    messages: Vec<[u16; MERKLE_CRH_WORDS]>,
    hash: BatchHashWorkspace,
}
/// Computes a parent with the opt-in weighted Sinsemilla algorithm.
/// This has the same exceptional-input assumptions as
/// [`UncheckedFixedLengthHashDomain`].
pub fn weighted_hash(level: u8, left: Fp, right: Fp) -> Fp {
    weighted().hash_words(&words(level, left, right))
}
/// Computes weighted parents, retaining allocations and sharing affine inversions.
///
/// This has the same exceptional-input assumptions as
/// [`UncheckedFixedLengthHashDomain`]; use [`hash_batch`] for Sinsemilla's
/// specified failure handling.
///
/// Returns one hash per pair in iteration order, or an empty slice for no pairs.
/// The returned slice borrows `workspace`, preventing another mutable borrow
/// while the slice is in use. The next call replaces the results while retaining
/// the workspace's buffer capacities for reuse.
pub fn weighted_hash_batch(
    level: u8,
    pairs: impl IntoIterator<Item = (Fp, Fp)>,
    workspace: &mut BatchWorkspace,
) -> &[Fp] {
    workspace.messages.clear();
    workspace.messages.extend(
        pairs
            .into_iter()
            .map(|(left, right)| words(level, left, right)),
    );
    weighted().hash_words_batch_with_workspace(&workspace.messages, &mut workspace.hash)
}

fn words(level: u8, left: Fp, right: Fp) -> [u16; MERKLE_CRH_WORDS] {
    fn word_at(bytes: &[u8; 32], bit_offset: usize) -> u16 {
        let byte_offset = bit_offset / BYTE_BITS;
        let shift = bit_offset % BYTE_BITS;
        let window =
            u16::from(bytes[byte_offset]) | (u16::from(bytes[byte_offset + 1]) << BYTE_BITS);
        let word = window >> shift;

        if shift + K > u16::BITS as usize {
            (word | (u16::from(bytes[byte_offset + 2]) << (u16::BITS as usize - shift)))
                & SINSEMILLA_WORD_MASK
        } else {
            word & SINSEMILLA_WORD_MASK
        }
    }

    let left = left.to_bytes();
    let right = right.to_bytes();
    let mut words = [0; MERKLE_CRH_WORDS];

    words[0] = u16::try_from(usize::from(level)).expect("an Orchard tree level fits into u16");
    for (index, word) in words[1..MERKLE_CRH_CROSS_CHILD_WORD].iter_mut().enumerate() {
        *word = word_at(&left, index * K);
    }
    let left_tail_offset = MERKLE_CRH_FULL_CHILD_WORDS * K;
    words[MERKLE_CRH_CROSS_CHILD_WORD] = u16::from(
        (left[left_tail_offset / BYTE_BITS] >> (left_tail_offset % BYTE_BITS))
            & CHILD_REMAINDER_MASK,
    ) | (u16::from(right[0] & CHILD_REMAINDER_MASK)
        << MERKLE_CRH_CHILD_REMAINDER_BITS);
    for (index, word) in words[MERKLE_CRH_CROSS_CHILD_WORD + 1..]
        .iter_mut()
        .enumerate()
    {
        *word = word_at(&right, MERKLE_CRH_CHILD_REMAINDER_BITS + index * K);
    }

    words
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::format;
    use proptest::prelude::*;
    /// Deterministic edge vectors for the direct word decoder, pinning the
    /// mask and shift boundaries independently of proptest's sampling: the
    /// all-zero and all-one bit patterns, both ends of the canonical range,
    /// dense low limbs, and alternating bits (reduced from an over-wide raw
    /// encoding), at the bottom and top tree levels.
    #[test]
    fn weighted_words_edge_vectors() {
        let edges = [
            Fp::zero(),
            Fp::one(),
            -Fp::one(),
            Fp::from(u64::MAX),
            Fp::from_raw([u64::MAX; 4]),
            Fp::from_raw([0x5555_5555_5555_5555; 4]),
            Fp::from_raw([0xAAAA_AAAA_AAAA_AAAA; 4]),
        ];

        for level in [0, (sensei_shared::MERKLE_DEPTH - 1) as u8] {
            for left in edges {
                for right in edges {
                    let expected: Vec<_> = message(level, left, right).collect();
                    let actual: Vec<_> = words(level, left, right)
                        .into_iter()
                        .flat_map(|word| (0..K).map(move |bit| ((word >> bit) & 1) == 1))
                        .collect();
                    assert_eq!(actual, expected);
                }
            }
        }
    }

    proptest! {
            #[test]
        fn weighted_words_match_merkle_message(
            level in 0_u8..sensei_shared::MERKLE_DEPTH as u8,
            left in any::<[u8; 64]>().prop_map(|bytes| Fp::from_uniform_bytes(&bytes)),
            right in any::<[u8; 64]>().prop_map(|bytes| Fp::from_uniform_bytes(&bytes)),
        ) {
            let expected: Vec<_> = message(level, left, right).collect();
            let actual: Vec<_> = words(level, left, right)
                .into_iter()
                .flat_map(|word| (0..K).map(move |bit| ((word >> bit) & 1) == 1))
                .collect();

            prop_assert_eq!(actual, expected);
        }

    }
}
