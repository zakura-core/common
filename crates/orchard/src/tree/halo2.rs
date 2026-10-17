use super::*;
#[allow(unused_imports)]
use crate::backend::prelude::*;
use crate::backend::sinsemilla::HashDomain;
#[cfg(feature = "weighted-merkle")]
use crate::backend::sinsemilla::weighted::UncheckedFixedLengthHashDomain;
#[cfg(feature = "weighted-merkle")]
use crate::constants::sinsemilla::K;
use crate::constants::sinsemilla::MERKLE_CRH_PERSONALIZATION;
#[cfg(not(feature = "weighted-merkle"))]
use crate::spec::extract_p_bottom_batch;
// The uncommitted leaf is defined as pallas::Base(2).
// <https://zips.z.cash/protocol/protocol.pdf#thmuncommittedorchard>
/// A Merkle parent hash consumes a left and a right child.
#[cfg(feature = "weighted-merkle")]
const MERKLE_CRH_CHILDREN: usize = 2;
/// The level word is followed by one field encoding for each child.
#[cfg(feature = "weighted-merkle")]
const MERKLE_CRH_BITS: usize = K + MERKLE_CRH_CHILDREN * L_ORCHARD_MERKLE;
/// Orchard Merkle CRH inputs always pad to this many Sinsemilla words.
#[cfg(feature = "weighted-merkle")]
pub(super) const MERKLE_CRH_WORDS: usize = MERKLE_CRH_BITS / K;
#[cfg(feature = "weighted-merkle")]
const _: () = assert!(MERKLE_CRH_BITS.is_multiple_of(K));
/// Complete Sinsemilla words in one 255-bit child encoding.
#[cfg(feature = "weighted-merkle")]
const MERKLE_CRH_FULL_CHILD_WORDS: usize = L_ORCHARD_MERKLE / K;
/// Bits left after decoding a child's complete Sinsemilla words.
#[cfg(feature = "weighted-merkle")]
const MERKLE_CRH_CHILD_REMAINDER_BITS: usize = L_ORCHARD_MERKLE % K;
/// Index of the word spanning the left and right child encodings.
#[cfg(feature = "weighted-merkle")]
const MERKLE_CRH_CROSS_CHILD_WORD: usize = 1 + MERKLE_CRH_FULL_CHILD_WORDS;
#[cfg(feature = "weighted-merkle")]
const SINSEMILLA_WORD_MASK: u16 = (1 << K) - 1;
#[cfg(feature = "weighted-merkle")]
const CHILD_REMAINDER_MASK: u8 = (1 << MERKLE_CRH_CHILD_REMAINDER_BITS) - 1;
#[cfg(feature = "weighted-merkle")]
const BYTE_BITS: usize = u8::BITS as usize;

#[cfg(feature = "weighted-merkle")]
static MERKLE_CRH_DOMAIN: OnceTable<UncheckedFixedLengthHashDomain<MERKLE_CRH_WORDS>> =
    OnceTable::new();

#[cfg(feature = "weighted-merkle")]
fn merkle_crh_domain() -> &'static UncheckedFixedLengthHashDomain<MERKLE_CRH_WORDS> {
    MERKLE_CRH_DOMAIN.get_or_init(|| {
        UncheckedFixedLengthHashDomain::new(&HashDomain::new(MERKLE_CRH_PERSONALIZATION))
    })
}

#[cfg(not(feature = "weighted-merkle"))]
static MERKLE_CRH_DOMAIN: OnceTable<HashDomain> = OnceTable::new();

#[cfg(not(feature = "weighted-merkle"))]
fn merkle_crh_domain() -> &'static HashDomain {
    MERKLE_CRH_DOMAIN.get_or_init(|| HashDomain::new(MERKLE_CRH_PERSONALIZATION))
}

#[cfg(feature = "weighted-merkle")]
pub(super) fn merkle_crh(
    level: Level,
    left: &MerkleHashOrchard,
    right: &MerkleHashOrchard,
) -> pallas::Base {
    merkle_crh_domain().hash_words(&merkle_crh_words(level, left, right))
}

#[cfg(not(feature = "weighted-merkle"))]
pub(super) fn merkle_crh(
    level: Level,
    left: &MerkleHashOrchard,
    right: &MerkleHashOrchard,
) -> pallas::Base {
    merkle_crh_domain()
        .hash(merkle_crh_message(level, left, right))
        .unwrap_or(pallas::Base::zero())
}

#[cfg(not(feature = "weighted-merkle"))]
fn merkle_crh_to_point(
    level: Level,
    left: &MerkleHashOrchard,
    right: &MerkleHashOrchard,
) -> CtOption<pallas::Point> {
    merkle_crh_domain().hash_to_point(merkle_crh_message(level, left, right))
}

#[cfg(feature = "weighted-merkle")]
fn merkle_crh_words(
    level: Level,
    left: &MerkleHashOrchard,
    right: &MerkleHashOrchard,
) -> [u16; MERKLE_CRH_WORDS] {
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

    let left = left.0.to_repr();
    let right = right.0.to_repr();
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
impl MerkleHashOrchard {
    /// Combines same-level node pairs in order, sharing normalization across the batch.
    pub fn combine_batch<'a>(
        level: Level,
        pairs: impl IntoIterator<Item = (&'a Self, &'a Self)>,
    ) -> Vec<Self> {
        #[cfg(feature = "weighted-merkle")]
        {
            let mut workspace = MerkleHashBatchWorkspace::default();
            let mut output = Vec::new();
            Self::combine_batch_with_workspace(level, pairs, &mut workspace, &mut output);
            output
        }

        #[cfg(not(feature = "weighted-merkle"))]
        {
            extract_p_bottom_batch(
                pairs
                    .into_iter()
                    .map(|(left, right)| merkle_crh_to_point(level, left, right)),
            )
            .map(|hash| MerkleHashOrchard(hash.unwrap_or(pallas::Base::zero())))
            .collect()
        }
    }
    #[cfg(feature = "weighted-merkle")]
    /// Combines node pairs while reusing temporary allocations and the output buffer.
    pub fn combine_batch_with_workspace<'a>(
        level: Level,
        pairs: impl IntoIterator<Item = (&'a Self, &'a Self)>,
        workspace: &mut MerkleHashBatchWorkspace,
        output: &mut Vec<Self>,
    ) {
        workspace.messages.clear();
        workspace.messages.extend(
            pairs
                .into_iter()
                .map(|(left, right)| merkle_crh_words(level, left, right)),
        );
        let hashes = merkle_crh_domain()
            .hash_words_batch_with_workspace(&workspace.messages, &mut workspace.hash);
        output.clear();
        output.reserve(hashes.len());
        output.extend(hashes.iter().copied().map(MerkleHashOrchard));
    }
}

// Keep the legacy decoder's independent bit-layout checks with its implementation.
#[cfg(all(test, feature = "weighted-merkle"))]
mod tests {
    use super::*;
    use crate::tree::testing::arb_merkle_hash;
    use proptest::prelude::*;

    /// Deterministic edge vectors for the direct word decoder, pinning the
    /// mask and shift boundaries independently of proptest's sampling: the
    /// all-zero and all-one bit patterns, both ends of the canonical range,
    /// dense low limbs, and alternating bits (reduced from an over-wide raw
    /// encoding), at the bottom and top tree levels.
    #[test]
    fn weighted_words_edge_vectors() {
        let edges = [
            pallas::Base::zero(),
            pallas::Base::one(),
            -pallas::Base::one(),
            pallas::Base::from(u64::MAX),
            pallas::Base::from_raw([u64::MAX; 4]),
            pallas::Base::from_raw([0x5555_5555_5555_5555; 4]),
            pallas::Base::from_raw([0xAAAA_AAAA_AAAA_AAAA; 4]),
        ];

        for level in [0, u8::try_from(MERKLE_DEPTH_ORCHARD - 1).unwrap()] {
            let level = Level::from(level);
            for left in edges.map(MerkleHashOrchard) {
                for right in edges.map(MerkleHashOrchard) {
                    let expected: Vec<_> = merkle_crh_message(level, &left, &right).collect();
                    let actual: Vec<_> = merkle_crh_words(level, &left, &right)
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
            level in 0_u8..u8::try_from(MERKLE_DEPTH_ORCHARD).unwrap(),
            left in arb_merkle_hash(),
            right in arb_merkle_hash(),
        ) {
            let level = Level::from(level);
            let expected: Vec<_> = merkle_crh_message(level, &left, &right).collect();
            let actual: Vec<_> = merkle_crh_words(level, &left, &right)
                .into_iter()
                .flat_map(|word| (0..K).map(move |bit| ((word >> bit) & 1) == 1))
                .collect();

            prop_assert_eq!(actual, expected);
        }

    }
}
