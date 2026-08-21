//! Types related to Orchard note commitment trees and anchors.

use alloc::vec::Vec;
use core::iter;

#[cfg(feature = "weighted-merkle")]
use crate::constants::sinsemilla::K;
use crate::{
    constants::{
        sinsemilla::{i2lebsp_k, L_ORCHARD_MERKLE, MERKLE_CRH_PERSONALIZATION},
        MERKLE_DEPTH_ORCHARD,
    },
    note::commitment::ExtractedNoteCommitment,
};

#[cfg(not(feature = "weighted-merkle"))]
use crate::spec::extract_p_bottom_batch;

use incrementalmerkletree::{Hashable, Level};
use pasta_curves::pallas;
#[cfg(feature = "weighted-merkle")]
use sinsemilla::weighted::UncheckedFixedLengthHashDomain;
use sinsemilla::HashDomain;

use ff::{Field, PrimeField, PrimeFieldBits};
use lazy_static::lazy_static;
use rand::Rng;
use serde::de::{Deserializer, Error};
use serde::ser::Serializer;
use serde::{Deserialize, Serialize};
use subtle::{Choice, ConditionallySelectable, CtOption};

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
const MERKLE_CRH_WORDS: usize = MERKLE_CRH_BITS / K;
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
lazy_static! {
    static ref MERKLE_CRH_DOMAIN: UncheckedFixedLengthHashDomain<MERKLE_CRH_WORDS> =
        UncheckedFixedLengthHashDomain::new(&HashDomain::new(MERKLE_CRH_PERSONALIZATION));
}

#[cfg(not(feature = "weighted-merkle"))]
lazy_static! {
    static ref MERKLE_CRH_DOMAIN: HashDomain = HashDomain::new(MERKLE_CRH_PERSONALIZATION);
}

#[cfg(feature = "weighted-merkle")]
fn merkle_crh(level: Level, left: &MerkleHashOrchard, right: &MerkleHashOrchard) -> pallas::Base {
    MERKLE_CRH_DOMAIN.hash_words(&merkle_crh_words(level, left, right))
}

#[cfg(not(feature = "weighted-merkle"))]
fn merkle_crh(level: Level, left: &MerkleHashOrchard, right: &MerkleHashOrchard) -> pallas::Base {
    MERKLE_CRH_DOMAIN
        .hash(merkle_crh_message(level, left, right))
        .unwrap_or(pallas::Base::zero())
}

#[cfg(not(feature = "weighted-merkle"))]
fn merkle_crh_to_point(
    level: Level,
    left: &MerkleHashOrchard,
    right: &MerkleHashOrchard,
) -> CtOption<pallas::Point> {
    MERKLE_CRH_DOMAIN.hash_to_point(merkle_crh_message(level, left, right))
}

lazy_static! {
    static ref UNCOMMITTED_ORCHARD: pallas::Base = pallas::Base::from(2);
    pub(crate) static ref EMPTY_ROOTS: Vec<MerkleHashOrchard> = {
        iter::empty()
            .chain(Some(MerkleHashOrchard::empty_leaf()))
            .chain(
                (0..MERKLE_DEPTH_ORCHARD).scan(MerkleHashOrchard::empty_leaf(), |state, l| {
                    let l = l as u8;
                    *state = MerkleHashOrchard::combine(l.into(), state, state);
                    Some(*state)
                }),
            )
            .collect()
    };
}

/// The root of an Orchard commitment tree. This must be a value
/// in the range {0..=q_ℙ-1}
#[derive(Eq, PartialEq, Clone, Copy, Debug)]
pub struct Anchor(pallas::Base);

impl From<pallas::Base> for Anchor {
    fn from(anchor_field: pallas::Base) -> Anchor {
        Anchor(anchor_field)
    }
}

impl From<MerkleHashOrchard> for Anchor {
    fn from(anchor: MerkleHashOrchard) -> Anchor {
        Anchor(anchor.0)
    }
}

impl Anchor {
    /// The anchor of the empty Orchard note commitment tree.
    ///
    /// This anchor does not correspond to any valid anchor for a spend, so it
    /// may only be used for bundles without real spends — e.g. coinbase bundles,
    /// where the pool's consensus rules permit them — or in circumstances where
    /// Orchard functionality is not active.
    pub fn empty_tree() -> Anchor {
        Anchor(MerkleHashOrchard::empty_root(Level::from(MERKLE_DEPTH_ORCHARD as u8)).0)
    }

    pub(crate) fn inner(&self) -> pallas::Base {
        self.0
    }

    /// Parses an Orchard anchor from a byte encoding.
    pub fn from_bytes(bytes: [u8; 32]) -> CtOption<Anchor> {
        pallas::Base::from_repr(bytes).map(Anchor)
    }

    /// Returns the byte encoding of this anchor.
    pub fn to_bytes(self) -> [u8; 32] {
        self.0.to_repr()
    }
}

/// The Merkle path from a leaf of the note commitment tree
/// to its anchor.
#[derive(Clone, Debug)]
pub struct MerklePath {
    position: u32,
    auth_path: [MerkleHashOrchard; MERKLE_DEPTH_ORCHARD],
}

#[cfg(any(test, feature = "test-dependencies"))]
#[cfg_attr(docsrs, doc(cfg(feature = "test-dependencies")))]
impl From<(incrementalmerkletree::Position, Vec<MerkleHashOrchard>)> for MerklePath {
    fn from(path: (incrementalmerkletree::Position, Vec<MerkleHashOrchard>)) -> Self {
        let position: u64 = path.0.into();
        Self {
            position: position as u32,
            auth_path: path.1.try_into().unwrap(),
        }
    }
}

impl From<incrementalmerkletree::MerklePath<MerkleHashOrchard, 32>> for MerklePath {
    fn from(path: incrementalmerkletree::MerklePath<MerkleHashOrchard, 32>) -> Self {
        let position: u64 = path.position().into();
        Self {
            position: position as u32,
            auth_path: path.path_elems().try_into().unwrap(),
        }
    }
}

impl MerklePath {
    /// Generates a dummy Merkle path for use in dummy spent notes.
    #[cfg_attr(feature = "unstable-voting-circuits", visibility::make(pub))]
    pub(crate) fn dummy(mut rng: &mut impl Rng) -> Self {
        MerklePath {
            position: rng.next_u32(),
            auth_path: [(); MERKLE_DEPTH_ORCHARD]
                .map(|_| MerkleHashOrchard(pallas::Base::random(&mut rng))),
        }
    }

    /// Instantiates a new Merkle path given a leaf position and authentication path.
    pub(crate) fn new(position: u32, auth_path: [pallas::Base; MERKLE_DEPTH_ORCHARD]) -> Self {
        Self::from_parts(position, auth_path.map(MerkleHashOrchard))
    }

    /// Instantiates a new Merkle path given a leaf position and authentication path.
    pub fn from_parts(position: u32, auth_path: [MerkleHashOrchard; MERKLE_DEPTH_ORCHARD]) -> Self {
        Self {
            position,
            auth_path,
        }
    }

    /// <https://zips.z.cash/protocol/protocol.pdf#orchardmerklecrh>
    /// The layer with 2^n nodes is called "layer n":
    ///      - leaves are at layer MERKLE_DEPTH_ORCHARD = 32;
    ///      - the root is at layer 0.
    /// `l` is MERKLE_DEPTH_ORCHARD - layer - 1.
    ///      - when hashing two leaves, we produce a node on the layer above the leaves, i.e.
    ///        layer = 31, l = 0
    ///      - when hashing to the final root, we produce the anchor with layer = 0, l = 31.
    pub fn root(&self, cmx: ExtractedNoteCommitment) -> Anchor {
        self.auth_path
            .iter()
            .enumerate()
            .fold(MerkleHashOrchard::from_cmx(&cmx), |node, (l, sibling)| {
                let l = l as u8;
                if self.position & (1 << l) == 0 {
                    MerkleHashOrchard::combine(l.into(), &node, sibling)
                } else {
                    MerkleHashOrchard::combine(l.into(), sibling, &node)
                }
            })
            .into()
    }

    /// Returns the position of the leaf using this Merkle path.
    pub fn position(&self) -> u32 {
        self.position
    }

    /// Returns the authentication path.
    pub fn auth_path(&self) -> [MerkleHashOrchard; MERKLE_DEPTH_ORCHARD] {
        self.auth_path
    }
}

/// A newtype wrapper for leaves and internal nodes in the Orchard
/// incremental note commitment tree.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MerkleHashOrchard(pallas::Base);

impl MerkleHashOrchard {
    /// Creates an incremental tree leaf digest from the specified
    /// Orchard extracted note commitment.
    pub fn from_cmx(value: &ExtractedNoteCommitment) -> Self {
        MerkleHashOrchard(value.inner())
    }

    /// Only used in the circuit.
    #[cfg_attr(feature = "unstable-voting-circuits", visibility::make(pub))]
    pub(crate) fn inner(&self) -> pallas::Base {
        self.0
    }

    /// Convert this digest to its canonical byte representation.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.to_repr()
    }

    /// Parses a incremental tree leaf digest from the bytes of
    /// a note commitment.
    ///
    /// Returns the empty `CtOption` if the provided bytes represent
    /// a non-canonical encoding.
    pub fn from_bytes(bytes: &[u8; 32]) -> CtOption<Self> {
        pallas::Base::from_repr(*bytes).map(MerkleHashOrchard)
    }

    /// Combines same-level node pairs using `MerkleCRH^Orchard`.
    ///
    /// This is equivalent to calling [`Hashable::combine`] for each pair in
    /// input order, but normalizes all resulting projective Pallas points
    /// together to amortize the field inversion across the batch.
    ///
    /// Every pair is evaluated at `level`. As with [`Hashable::combine`], the
    /// caller is responsible for supplying children that belong at that level.
    ///
    /// The input iterator is consumed once and only borrows its nodes. This
    /// method allocates and returns one digest per input pair, preserving input
    /// order. An empty iterator returns an empty [`Vec`].
    pub fn combine_batch<'a>(
        level: Level,
        pairs: impl IntoIterator<Item = (&'a Self, &'a Self)>,
    ) -> Vec<Self> {
        #[cfg(feature = "weighted-merkle")]
        {
            let messages: Vec<_> = pairs
                .into_iter()
                .map(|(left, right)| merkle_crh_words(level, left, right))
                .collect();
            MERKLE_CRH_DOMAIN
                .hash_words_batch(&messages)
                .into_iter()
                .map(MerkleHashOrchard)
                .collect()
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

fn merkle_crh_message(
    level: Level,
    left: &MerkleHashOrchard,
    right: &MerkleHashOrchard,
) -> impl Iterator<Item = bool> {
    i2lebsp_k(usize::from(level))
        .into_iter()
        .chain(left.0.to_le_bits().into_iter().take(L_ORCHARD_MERKLE))
        .chain(right.0.to_le_bits().into_iter().take(L_ORCHARD_MERKLE))
}

impl ConditionallySelectable for MerkleHashOrchard {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        MerkleHashOrchard(pallas::Base::conditional_select(&a.0, &b.0, choice))
    }
}

impl Hashable for MerkleHashOrchard {
    fn empty_leaf() -> Self {
        MerkleHashOrchard(*UNCOMMITTED_ORCHARD)
    }

    /// Implements `MerkleCRH^Orchard` as defined in
    /// <https://zips.z.cash/protocol/protocol.pdf#orchardmerklecrh>
    ///
    /// The layer with 2^n nodes is called "layer n":
    ///      - leaves are at layer MERKLE_DEPTH_ORCHARD = 32;
    ///      - the root is at layer 0.
    /// `l` is MERKLE_DEPTH_ORCHARD - layer - 1.
    ///      - when hashing two leaves, we produce a node on the layer above the leaves, i.e.
    ///        layer = 31, l = 0
    ///      - when hashing to the final root, we produce the anchor with layer = 0, l = 31.
    fn combine(level: Level, left: &Self, right: &Self) -> Self {
        MerkleHashOrchard(merkle_crh(level, left, right))
    }

    fn empty_root(level: Level) -> Self {
        EMPTY_ROOTS[<usize>::from(level)]
    }
}

impl Serialize for MerkleHashOrchard {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.to_bytes().serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for MerkleHashOrchard {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let parsed = <[u8; 32]>::deserialize(deserializer)?;
        <Option<_>>::from(Self::from_bytes(&parsed)).ok_or_else(|| {
            Error::custom(
            "Attempted to deserialize a non-canonical representation of a Pallas base field element.",
        )
        })
    }
}

/// Test utilities available under the `test-dependencies` feature flag.
#[cfg(any(test, feature = "test-dependencies"))]
pub mod testing {
    use ff::{Field, FromUniformBytes};
    use proptest::{arbitrary::any, strategy::Strategy};
    use rand::{
        distr::{Distribution, StandardUniform},
        Rng,
    };

    use super::MerkleHashOrchard;

    /// Width required by the field's uniform-byte reduction.
    const UNIFORM_BYTES: usize = 64;

    impl MerkleHashOrchard {
        /// Return a random fake `MerkleHashOrchard`.
        pub fn random(rng: &mut impl Rng) -> Self {
            StandardUniform.sample(rng)
        }
    }

    /// Generate an arbitrary Orchard note-commitment tree node.
    pub fn arb_merkle_hash() -> impl Strategy<Value = MerkleHashOrchard> {
        any::<[u8; UNIFORM_BYTES]>().prop_map(|bytes| {
            MerkleHashOrchard(pasta_curves::pallas::Base::from_uniform_bytes(&bytes))
        })
    }

    impl Distribution<MerkleHashOrchard> for StandardUniform {
        fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> MerkleHashOrchard {
            MerkleHashOrchard(pasta_curves::Fp::random(rng))
        }
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "weighted-merkle")]
    use crate::{constants::sinsemilla::K, tree::merkle_crh_words};

    use {
        crate::{
            constants::{sinsemilla::MERKLE_CRH_PERSONALIZATION, MERKLE_DEPTH_ORCHARD},
            tree::{merkle_crh_message, testing::arb_merkle_hash, MerkleHashOrchard, EMPTY_ROOTS},
        },
        alloc::vec::Vec,
        group::ff::{Field, PrimeField},
        incrementalmerkletree::{
            frontier::Frontier, Hashable, Level, Marking, MerklePath, Retention,
        },
        pasta_curves::pallas,
        proptest::prelude::*,
        rand::SeedableRng,
        rand_chacha::ChaCha20Rng,
        shardtree::{store::memory::MemoryShardStore, ShardTree},
        sinsemilla::HashDomain,
    };

    /// Batch sizes exercise empty, singleton, odd, and tree-level workloads.
    const BATCH_WIDTHS: [usize; 12] = [0, 1, 2, 3, 4, 8, 16, 32, 64, 128, 256, 512];
    /// Fixed seed makes the scalar-equivalence test deterministic.
    const BATCH_TEST_SEED: [u8; 32] = [0x42; 32];

    /// These commitment values are derived from the bundle data that was generated for
    /// testing commitment tree construction inside of zcashd here.
    /// <https://github.com/zcash/zcash/blob/ecec1f9769a5e37eb3f7fd89a4fcfb35bc28eed7/src/test/data/merkle_roots_orchard.h>
    const ZCASHD_COMMITMENTS: [[u8; 32]; 5] = [
        [
            0x68, 0x13, 0x5c, 0xf4, 0x99, 0x33, 0x22, 0x90, 0x99, 0xa4, 0x4e, 0xc9, 0x9a, 0x75,
            0xe1, 0xe1, 0xcb, 0x46, 0x40, 0xf9, 0xb5, 0xbd, 0xec, 0x6b, 0x32, 0x23, 0x85, 0x6f,
            0xea, 0x16, 0x39, 0x0a,
        ],
        [
            0x78, 0x31, 0x50, 0x08, 0xfb, 0x29, 0x98, 0xb4, 0x30, 0xa5, 0x73, 0x1d, 0x67, 0x26,
            0x20, 0x7d, 0xc0, 0xf0, 0xec, 0x81, 0xea, 0x64, 0xaf, 0x5c, 0xf6, 0x12, 0x95, 0x69,
            0x01, 0xe7, 0x2f, 0x0e,
        ],
        [
            0xee, 0x94, 0x88, 0x05, 0x3a, 0x30, 0xc5, 0x96, 0xb4, 0x30, 0x14, 0x10, 0x5d, 0x34,
            0x77, 0xe6, 0xf5, 0x78, 0xc8, 0x92, 0x40, 0xd1, 0xd1, 0xee, 0x17, 0x43, 0xb7, 0x7b,
            0xb6, 0xad, 0xc4, 0x0a,
        ],
        [
            0x9d, 0xdc, 0xe7, 0xf0, 0x65, 0x01, 0xf3, 0x63, 0x76, 0x8c, 0x5b, 0xca, 0x3f, 0x26,
            0x46, 0x60, 0x83, 0x4d, 0x4d, 0xf4, 0x46, 0xd1, 0x3e, 0xfc, 0xd7, 0xc6, 0xf1, 0x7b,
            0x16, 0x7a, 0xac, 0x1a,
        ],
        [
            0xbd, 0x86, 0x16, 0x81, 0x1c, 0x6f, 0x5f, 0x76, 0x9e, 0xa4, 0x53, 0x9b, 0xba, 0xff,
            0x0f, 0x19, 0x8a, 0x6c, 0xdf, 0x3b, 0x28, 0x0d, 0xd4, 0x99, 0x26, 0x16, 0x3b, 0xd5,
            0x3f, 0x53, 0xa1, 0x21,
        ],
    ];

    /// This value was produced by the Python test vector generation code implemented here:
    /// <https://github.com/zcash-hackworks/zcash-test-vectors/blob/f4d756410c8f2456f5d84cedf6dac6eb8c068eed/orchard_merkle_tree.py>
    const ZCASHD_ANCHOR: [u8; 32] = [
        0xc8, 0x75, 0xbe, 0x2d, 0x60, 0x87, 0x3f, 0x8b, 0xcd, 0xeb, 0x91, 0x28, 0x2e, 0x64, 0x2e,
        0x0c, 0xc6, 0x5f, 0xf7, 0xd0, 0x64, 0x2d, 0x13, 0x7b, 0x28, 0xcf, 0x28, 0xcc, 0x9c, 0x52,
        0x7f, 0x0e,
    ];

    /// Width required by the field's uniform-byte reduction.
    const UNIFORM_BYTES: usize = 64;

    /// Height of the deterministic fixture tree built from [`fixture_leaves`]:
    /// 2^11 leaves fold through levels of 1024, 512, ..., 2, 1 parents, so one
    /// tree exercises `combine_batch` at every power-of-two width from 1024
    /// down to 1 (and, at level 1, the 1024-leaf-tree first level).
    const FIXTURE_TREE_HEIGHT: usize = 11;
    /// Number of leaves in the fixture tree (2^11 = 2048).
    const FIXTURE_LEAVES: usize = 1 << FIXTURE_TREE_HEIGHT;
    /// The leading run of edge-case leaves placed contiguously, so that
    /// edge cases are paired with each other (and their parents with each
    /// other, up the tree); the remaining edge cases are spread through the
    /// BLAKE2b fill so they are paired with ordinary values.
    const FIXTURE_CONTIGUOUS_EDGES: usize = 256;
    /// BLAKE2b personalization for the fill values (exactly 16 bytes).
    const FIXTURE_FILL_PERSONALIZATION: &[u8; 16] = b"ZakuraMerkleFx01";

    /// Edge-case tree nodes, in a fixed order, with duplicates removed.
    ///
    /// Intended to stress the Merkle CRH and its batched evaluation on
    /// inputs that random sampling never produces: the protocol's special
    /// values (zero, one, the uncommitted leaf `2`, `p - 1`, `p - 2`,
    /// `(p - 1) / 2`), every canonical power of two and its negation
    /// (single set bit and single clear bit at every position), a single
    /// all-ones Sinsemilla word at each of the 26 word offsets (including
    /// the word straddling the child boundary), alternating word and bit
    /// patterns, the largest canonical values above `2^254`, and the empty
    /// root of every tree level.
    fn edge_case_leaves() -> alloc::vec::Vec<MerkleHashOrchard> {
        use alloc::collections::BTreeSet;
        use alloc::vec::Vec;
        use ff::PrimeField;
        use incrementalmerkletree::{Hashable, Level};
        use pasta_curves::pallas;

        use crate::constants::{sinsemilla::K, MERKLE_DEPTH_ORCHARD};

        /// `2^bit` as raw limbs (for `bit < 256`).
        fn bit_limbs(bit: usize) -> [u64; 4] {
            let mut limbs = [0u64; 4];
            limbs[bit / 64] = 1u64 << (bit % 64);
            limbs
        }
        /// `value` if its 255-bit raw encoding is a canonical field element.
        fn canonical(limbs: [u64; 4]) -> Option<pallas::Base> {
            let mut bytes = [0u8; 32];
            for (chunk, limb) in bytes.as_chunks_mut::<8>().0.iter_mut().zip(limbs) {
                *chunk = limb.to_le_bytes();
            }
            pallas::Base::from_repr(bytes).into()
        }
        /// Raw limbs with bits `[lo, lo + width)` set (clipped to 256 bits).
        fn bit_run(lo: usize, width: usize) -> [u64; 4] {
            let mut limbs = [0u64; 4];
            for bit in lo..(lo + width).min(256) {
                limbs[bit / 64] |= 1u64 << (bit % 64);
            }
            limbs
        }

        let one = pallas::Base::ONE;
        let mut candidates: Vec<pallas::Base> = alloc::vec![
            pallas::Base::ZERO,
            one,
            one + one, // the uncommitted leaf
            -one,
            -(one + one),
            pallas::Base::TWO_INV - one, // (p - 1) / 2
        ];
        // Single set bit, and single clear bit (`p - 2^i`), at every position.
        for bit in 0..256 {
            if let Some(v) = canonical(bit_limbs(bit)) {
                candidates.push(v);
                candidates.push(-v);
            }
        }
        // One all-ones Sinsemilla word at each word offset of the 255-bit
        // child encoding; the top word is clipped to the canonical range.
        let words = crate::constants::sinsemilla::L_ORCHARD_MERKLE.div_ceil(K);
        for word in 0..words {
            let lo = word * K;
            let mut width = K;
            while width > 0 {
                if let Some(v) = canonical(bit_run(lo, width)) {
                    candidates.push(v);
                    break;
                }
                width -= 1;
            }
        }
        // Alternating words (every other 10-bit word all ones) and bits.
        for phase in 0..2 {
            let mut limbs = [0u64; 4];
            for word in (phase..words).step_by(2) {
                for (i, l) in bit_run(word * K, K).iter().enumerate() {
                    limbs[i] |= l;
                }
            }
            // Clear the top bits until canonical.
            for bit in (0..256).rev() {
                if let Some(v) = canonical(limbs) {
                    candidates.push(v);
                    break;
                }
                limbs[bit / 64] &= !(1u64 << (bit % 64));
            }
        }
        for pattern in [
            0x5555_5555_5555_5555u64,
            0xAAAA_AAAA_AAAA_AAAA,
            0x0F0F_0F0F_0F0F_0F0F,
            0xF0F0_F0F0_F0F0_F0F0,
        ] {
            candidates.push(pallas::Base::from_raw([pattern; 4]));
        }
        // Largest canonical values: p - 1 - 2^i just below the modulus, and
        // 2^254 + (2^i - 1) just above the top power of two.
        for bit in [1usize, 8, 64, 120, 124] {
            candidates.push(-one - pallas::Base::from_raw(bit_limbs(bit)));
            candidates.push(
                pallas::Base::from_raw(bit_limbs(254)) + pallas::Base::from_raw(bit_run(0, bit)),
            );
        }
        // The empty root at every level (and the leaf level).
        for level in 0..=MERKLE_DEPTH_ORCHARD {
            candidates.push(MerkleHashOrchard::empty_root(Level::from(level as u8)).0);
        }

        let mut seen = BTreeSet::new();
        candidates
            .into_iter()
            .filter(|v| seen.insert(v.to_repr()))
            .map(MerkleHashOrchard)
            .collect()
    }

    /// Deterministic fixture of [`FIXTURE_LEAVES`] distinct leaves: the
    /// [`edge_case_leaves`] (the first [`FIXTURE_CONTIGUOUS_EDGES`] of them
    /// contiguous, the rest spread at a fixed stride) interleaved with
    /// BLAKE2b-derived fill values. RNG-free and fully determined by this
    /// function, so the vectors pinned in `test_vectors/merkle_fixture.rs`
    /// are reproducible; [`print_merkle_fixture_vectors`] regenerates them.
    fn fixture_leaves() -> alloc::vec::Vec<MerkleHashOrchard> {
        use alloc::collections::BTreeSet;
        use ff::{FromUniformBytes, PrimeField};

        let edges = edge_case_leaves();
        assert!(edges.len() > FIXTURE_CONTIGUOUS_EDGES);
        assert!(edges.len() < FIXTURE_LEAVES / 2);
        let spread = edges.len() - FIXTURE_CONTIGUOUS_EDGES;
        let stride = (FIXTURE_LEAVES - FIXTURE_CONTIGUOUS_EDGES) / spread;

        let mut leaves: alloc::vec::Vec<Option<MerkleHashOrchard>> =
            alloc::vec![None; FIXTURE_LEAVES];
        let mut seen = BTreeSet::new();
        for (i, edge) in edges.iter().enumerate() {
            let position = if i < FIXTURE_CONTIGUOUS_EDGES {
                i
            } else {
                FIXTURE_CONTIGUOUS_EDGES + (i - FIXTURE_CONTIGUOUS_EDGES) * stride
            };
            leaves[position] = Some(*edge);
            seen.insert(edge.to_bytes());
        }

        let mut counter = 0u64;
        for slot in leaves.iter_mut() {
            if slot.is_some() {
                continue;
            }
            loop {
                let hash = blake2b_simd::Params::new()
                    .hash_length(UNIFORM_BYTES)
                    .personal(FIXTURE_FILL_PERSONALIZATION)
                    .hash(&counter.to_le_bytes());
                counter += 1;
                let mut uniform = [0u8; UNIFORM_BYTES];
                uniform.copy_from_slice(hash.as_bytes());
                let value = pasta_curves::pallas::Base::from_uniform_bytes(&uniform);
                if seen.insert(value.to_repr()) {
                    *slot = Some(MerkleHashOrchard(value));
                    break;
                }
            }
        }
        leaves
            .into_iter()
            .map(|leaf| leaf.expect("every slot filled"))
            .collect()
    }

    fn combine_with_fresh_domain(
        level: Level,
        left: &MerkleHashOrchard,
        right: &MerkleHashOrchard,
    ) -> MerkleHashOrchard {
        let domain = HashDomain::new(MERKLE_CRH_PERSONALIZATION);
        MerkleHashOrchard(
            domain
                .hash(merkle_crh_message(level, left, right))
                .unwrap_or(pallas::Base::zero()),
        )
    }

    #[test]
    fn combine_batch_matches_scalar_at_every_level_and_width() {
        let mut rng = ChaCha20Rng::from_seed(BATCH_TEST_SEED);
        let pairs: Vec<_> = (0..*BATCH_WIDTHS.last().expect("batch widths are nonempty"))
            .map(|_| {
                (
                    MerkleHashOrchard(pallas::Base::random(&mut rng)),
                    MerkleHashOrchard(pallas::Base::random(&mut rng)),
                )
            })
            .collect();
        let tree_depth = u8::try_from(MERKLE_DEPTH_ORCHARD).expect("Orchard tree depth fits in u8");

        for level in 0..tree_depth {
            let level = Level::from(level);
            for width in BATCH_WIDTHS {
                let expected: Vec<_> = pairs[..width]
                    .iter()
                    .map(|(left, right)| MerkleHashOrchard::combine(level, left, right))
                    .collect();
                let actual = MerkleHashOrchard::combine_batch(
                    level,
                    pairs[..width].iter().map(|(left, right)| (left, right)),
                );

                assert_eq!(actual, expected, "level {level:?}, width {width}");
            }
        }
    }

    #[test]
    fn cached_merkle_crh_domain_matches_fresh_domains() {
        // Domain construction depends only on its personalization. Cover every
        // level here; the official vectors below cover varied canonical nodes.
        let tree_depth = u8::try_from(MERKLE_DEPTH_ORCHARD).expect("Orchard tree depth fits in u8");
        let left = MerkleHashOrchard::empty_leaf();
        let right = MerkleHashOrchard::empty_root(Level::from(tree_depth));

        for level in 0..tree_depth {
            let level = Level::from(level);
            assert_eq!(
                MerkleHashOrchard::combine(level, &left, &right),
                combine_with_fresh_domain(level, &left, &right),
            );
        }
    }

    fn generic_combine(
        domain: &HashDomain,
        level: Level,
        left: &MerkleHashOrchard,
        right: &MerkleHashOrchard,
    ) -> MerkleHashOrchard {
        MerkleHashOrchard(
            domain
                .hash(merkle_crh_message(level, left, right))
                .unwrap_or(pallas::Base::zero()),
        )
    }

    /// Deterministic edge vectors for the direct word decoder, pinning the
    /// mask and shift boundaries independently of proptest's sampling: the
    /// all-zero and all-one bit patterns, both ends of the canonical range,
    /// dense low limbs, and alternating bits (reduced from an over-wide raw
    /// encoding), at the bottom and top tree levels.
    #[cfg(feature = "weighted-merkle")]
    #[test]
    fn weighted_words_edge_vectors() {
        use crate::tree::{merkle_crh_message, merkle_crh_words};

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
        #[cfg(feature = "weighted-merkle")]
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

        #[test]
        fn production_merkle_combine_matches_generic(
            level in 0_u8..u8::try_from(MERKLE_DEPTH_ORCHARD).unwrap(),
            left in arb_merkle_hash(),
            right in arb_merkle_hash(),
        ) {
            let domain = HashDomain::new(MERKLE_CRH_PERSONALIZATION);
            let level = Level::from(level);
            prop_assert_eq!(
                MerkleHashOrchard::combine(level, &left, &right),
                generic_combine(&domain, level, &left, &right),
            );
        }
    }

    // ----------------------------------------------------------------------
    // Fixed-vector tests for `MerkleHashOrchard::combine_batch`.
    //
    // `combine_batch_matches_scalar_at_every_level_and_width` above checks the
    // batched combine against the scalar one on random nodes. The four tests
    // below instead pin it to fixed bytes, so a regression shared by both
    // implementations (or in the Sinsemilla evaluator underneath) is caught
    // too. They differ in where the bytes come from and in what shape of
    // input the batch sees:
    //
    // | test                                      | vectors from              | children            | batch widths        |
    // |-------------------------------------------|---------------------------|---------------------|---------------------|
    // | `combine_batch_matches_empty_root_vectors`| zcash-test-vectors        | identical (empty    | 512 (= the first    |
    // |                                           | `orchard_empty_roots.py`  | root, every level)  | level of a 1024-    |
    // |                                           |                           |                     | leaf tree)          |
    // | `combine_batch_matches_merkle_path_vectors`| zcash-test-vectors       | distinct, external  | 8/4/2/1 per tree;   |
    // |                                           | `orchard_merkle_tree.py`  | (16 snapshots of a  | 128/64/32/16 with   |
    // |                                           |                           | 16-leaf tree)       | all trees batched   |
    // | `combine_batch_matches_zcashd_anchor_vector`| zcashd                  | live node left,     | 1..3, all 32 levels |
    // |                                           | `merkle_roots_orchard.h`  | empty root right    |                     |
    // | `fixture_tree_matches_vectors`            | this crate's scalar path, | 2048 distinct, 586  | 1024/512/.../1      |
    // |                                           | recorded in               | edge cases          |                     |
    // |                                           | `merkle_fixture.rs`       |                     |                     |
    //
    // The first three use vectors produced outside this crate; only the last
    // is self-generated, which is why it additionally checks every node
    // against the scalar `combine` and a fresh generic Sinsemilla domain.
    // Widths of 32 and above reach the batch-affine evaluator under
    // `weighted-merkle`.
    // ----------------------------------------------------------------------

    /// Pins the batched combine directly to the protocol's fixed empty-root
    /// vectors (`orchard_empty_roots.py`): at each of the 32 levels, 512
    /// copies of the pair (empty root, empty root) must all hash to the
    /// next level's empty root. The width is the first level of a
    /// 1024-leaf tree; the children are identical, so this pins the
    /// per-level domain separation but not left/right asymmetry (see the
    /// tests that follow for that).
    #[test]
    fn combine_batch_matches_empty_root_vectors() {
        let empty_roots = crate::test_vectors::commitment_tree::test_vectors().empty_roots;
        let width = *BATCH_WIDTHS.last().expect("batch widths are nonempty");
        for level in 0..MERKLE_DEPTH_ORCHARD {
            let child = MerkleHashOrchard::from_bytes(&empty_roots[level]).unwrap();
            let pairs = vec![(&child, &child); width];
            let parents =
                MerkleHashOrchard::combine_batch(Level::from(u8::try_from(level).unwrap()), pairs);

            assert_eq!(parents.len(), width);
            for parent in parents {
                assert_eq!(parent.to_bytes(), empty_roots[level + 1], "level {level}");
            }
        }
    }

    /// Folds `leaves` up to a single depth-`DEPTH` root using one
    /// [`MerkleHashOrchard::combine_batch`] call per level, i.e. the way a
    /// tree builder would use the batch API. Levels with an odd number of
    /// nodes are right-padded with the protocol's fixed empty-root vector
    /// for that level (taken from the test vectors, not from the crate's own
    /// `empty_root`), so every input the batch sees is pinned to external
    /// bytes. Returns the nodes of every level, from the leaves (index 0) to
    /// the root (index `DEPTH`), so callers can check internal nodes too.
    fn batched_levels<const DEPTH: usize>(
        leaves: &[MerkleHashOrchard],
    ) -> Vec<Vec<MerkleHashOrchard>> {
        let empty_roots = crate::test_vectors::commitment_tree::test_vectors().empty_roots;
        let mut levels = vec![leaves.to_vec()];
        for level in 0..DEPTH {
            let mut nodes = levels[level].clone();
            if nodes.len() % 2 == 1 {
                nodes.push(MerkleHashOrchard::from_bytes(&empty_roots[level]).unwrap());
            }
            let pairs = nodes
                .as_chunks::<2>()
                .0
                .iter()
                .map(|pair| (&pair[0], &pair[1]));
            let parents =
                MerkleHashOrchard::combine_batch(Level::from(u8::try_from(level).unwrap()), pairs);
            assert_eq!(parents.len(), nodes.len() / 2);
            levels.push(parents);
        }
        assert_eq!(levels[DEPTH].len(), 1);
        levels
    }

    /// Pins the batched combine to the zcash-test-vectors Merkle path set
    /// (`orchard_merkle_tree.py`, vendored in `test_vectors/merkle_path.rs`).
    ///
    /// That set is one 16-leaf (depth-4) tree, snapshotted after each of its
    /// 16 appends: each snapshot records all 16 leaf slots (appended leaves,
    /// then the uncommitted value `2` for the rest), the authentication path
    /// of every leaf, and the root. These are the only externally produced
    /// Orchard Merkle vectors with *distinct* left and right children, and
    /// because every internal node is the path sibling of some leaf, every
    /// node of every snapshot has recorded bytes — so every output of every
    /// batch below is checked, not just the root.
    ///
    /// Two passes: each snapshot folded on its own (widths 8, 4, 2, 1), then
    /// all 16 snapshots' pairs at a level in one call (widths 128, 64, 32,
    /// 16), which is how a few small external vectors still reach the
    /// large-batch evaluator.
    #[test]
    fn combine_batch_matches_merkle_path_vectors() {
        const DEPTH: usize = 4;
        const LEAVES: usize = 1 << DEPTH;
        let vectors = crate::test_vectors::merkle_path::test_vectors();
        assert_eq!(vectors.len(), LEAVES);

        // Expected node at (level, index), from the authentication paths: the
        // sibling of leaf `j` at level `l` is the node at index `(j >> l) ^ 1`,
        // so index `k` is the level-`l` path entry of leaf `(k ^ 1) << l`.
        let expected = |tv: &crate::test_vectors::merkle_path::TestVector,
                        level: usize,
                        index: usize|
         -> [u8; 32] {
            if level == DEPTH {
                tv.root
            } else {
                tv.paths[(index ^ 1) << level][level]
            }
        };

        // Per-tree folds: each tree's pairs batched on their own (widths 8,
        // 4, 2, 1), with every node and the root checked.
        let mut per_level_nodes: Vec<Vec<Vec<MerkleHashOrchard>>> = Vec::new();
        for tv in &vectors {
            let leaves: Vec<_> = tv
                .leaves
                .iter()
                .map(|leaf| MerkleHashOrchard::from_bytes(leaf).unwrap())
                .collect();
            let levels = batched_levels::<DEPTH>(&leaves);
            for (level, nodes) in levels.iter().enumerate() {
                for (index, node) in nodes.iter().enumerate() {
                    assert_eq!(
                        node.to_bytes(),
                        expected(tv, level, index),
                        "level {level}, index {index}"
                    );
                }
            }
            per_level_nodes.push(levels);
        }

        // Cross-tree batches: all sixteen trees' pairs at one level in a
        // single call, checked pair by pair against the same fixed bytes.
        for level in 0..DEPTH {
            let pairs: Vec<(&MerkleHashOrchard, &MerkleHashOrchard)> = per_level_nodes
                .iter()
                .flat_map(|levels| {
                    levels[level]
                        .as_chunks::<2>()
                        .0
                        .iter()
                        .map(|pair| (&pair[0], &pair[1]))
                })
                .collect();
            assert_eq!(pairs.len(), LEAVES * (LEAVES >> (level + 1)));
            let parents =
                MerkleHashOrchard::combine_batch(Level::from(u8::try_from(level).unwrap()), pairs);
            let per_tree = LEAVES >> (level + 1);
            for (position, parent) in parents.iter().enumerate() {
                let (tree, index) = (position / per_tree, position % per_tree);
                assert_eq!(
                    parent.to_bytes(),
                    expected(&vectors[tree], level + 1, index),
                    "level {level}, tree {tree}, index {index}"
                );
            }
        }
    }

    /// Pins the batched combine, level by level through the full 32-level
    /// tree, to the anchor zcashd derived for five commitments
    /// (`merkle_roots_orchard.h`; see [`ZCASHD_COMMITMENTS`]). With five
    /// leaves, most levels hold a single live node that is paired with the
    /// fixed empty root on its right, so this is the asymmetric (live,
    /// empty) shape that the empty-root test cannot see, at every level up
    /// to the top. Every prefix of the commitments is also folded and
    /// compared with the incremental frontier.
    #[test]
    fn combine_batch_matches_zcashd_anchor_vector() {
        let leaves: Vec<_> = ZCASHD_COMMITMENTS
            .iter()
            .map(|cmx| MerkleHashOrchard::from_bytes(cmx).unwrap())
            .collect();
        let levels = batched_levels::<MERKLE_DEPTH_ORCHARD>(&leaves);
        assert_eq!(levels[MERKLE_DEPTH_ORCHARD][0].to_bytes(), ZCASHD_ANCHOR);

        // Every prefix of the commitments must also match the incremental
        // frontier, which the fixed anchor pins at the full length.
        for prefix in 1..=leaves.len() {
            let mut frontier: Frontier<MerkleHashOrchard, 32> = Frontier::empty();
            for leaf in &leaves[..prefix] {
                frontier.append(*leaf);
            }
            let levels = batched_levels::<MERKLE_DEPTH_ORCHARD>(&leaves[..prefix]);
            assert_eq!(
                levels[MERKLE_DEPTH_ORCHARD][0],
                frontier.root(),
                "prefix {prefix}"
            );
        }
    }

    /// The 2^11-leaf fixture tree (see [`fixture_leaves`]): 2048 distinct
    /// leaves, 586 of them edge cases, folded with one `combine_batch` call
    /// per level at widths 1024, 512, ..., 1. Two kinds of check:
    ///
    /// - every batched parent at every level must equal the scalar
    ///   `combine` and a fresh generic Sinsemilla domain (the full tree,
    ///   node by node);
    /// - the root, the first and last node of every level, and every node
    ///   of the top three levels must equal the bytes recorded in
    ///   `test_vectors/merkle_fixture.rs`, which were generated by the
    ///   scalar path and are what makes this a regression vector rather
    ///   than only an equivalence test.
    ///
    /// The vectors are self-generated (no external implementation has hashed
    /// this tree), which is why the first check exists. Regenerate them with
    /// [`print_merkle_fixture_vectors`] if the leaf set is deliberately
    /// changed; any other change to these bytes is a bug.
    #[test]
    fn fixture_tree_matches_vectors() {
        let leaves = fixture_leaves();
        assert_eq!(leaves.len(), FIXTURE_LEAVES);
        let distinct: alloc::collections::BTreeSet<_> =
            leaves.iter().map(MerkleHashOrchard::to_bytes).collect();
        assert_eq!(
            distinct.len(),
            FIXTURE_LEAVES,
            "fixture leaves must be distinct"
        );

        let levels = batched_levels::<FIXTURE_TREE_HEIGHT>(&leaves);
        let domain = HashDomain::new(MERKLE_CRH_PERSONALIZATION);
        for level in 0..FIXTURE_TREE_HEIGHT {
            let merkle_level = Level::from(u8::try_from(level).unwrap());
            for (index, pair) in levels[level].as_chunks::<2>().0.iter().enumerate() {
                let batched = levels[level + 1][index];
                assert_eq!(
                    batched,
                    MerkleHashOrchard::combine(merkle_level, &pair[0], &pair[1]),
                    "scalar mismatch at level {level}, index {index}"
                );
                assert_eq!(
                    batched,
                    generic_combine(&domain, merkle_level, &pair[0], &pair[1]),
                    "generic mismatch at level {level}, index {index}"
                );
            }
        }

        let tv = crate::test_vectors::merkle_fixture::test_vectors();
        assert_eq!(levels[FIXTURE_TREE_HEIGHT][0].to_bytes(), tv.root);
        for (level, [first, last]) in tv.level_bounds.iter().enumerate() {
            let nodes = &levels[level + 1];
            assert_eq!(
                nodes[0].to_bytes(),
                *first,
                "first node of level {}",
                level + 1
            );
            assert_eq!(
                nodes[nodes.len() - 1].to_bytes(),
                *last,
                "last node of level {}",
                level + 1
            );
        }
        let top: Vec<[u8; 32]> = levels[FIXTURE_TREE_HEIGHT - 2..]
            .iter()
            .flat_map(|nodes| nodes.iter().map(MerkleHashOrchard::to_bytes))
            .collect();
        assert_eq!(top, tv.top_levels);
    }

    /// Prints the `test_vectors/merkle_fixture.rs` module for the current
    /// fixture leaves, using the scalar `combine` (not the batch). Run with
    ///
    /// ```text
    /// cargo test -p zakura-orchard --lib \
    ///     tree::tests::print_merkle_fixture_vectors -- --ignored --nocapture
    /// ```
    ///
    /// without `weighted-merkle`, so the upstream scalar path produces the
    /// bytes, then paste the output over the module. Only needed after a
    /// deliberate change to [`edge_case_leaves`] or [`fixture_leaves`].
    #[test]
    #[ignore]
    fn print_merkle_fixture_vectors() {
        use alloc::{format, string::String};

        fn fmt(bytes: [u8; 32], indent: &str) -> String {
            let mut out = format!("{indent}[\n");
            for row in bytes.chunks(14) {
                out.push_str(indent);
                out.push_str("    ");
                out.push_str(
                    &row.iter()
                        .map(|b| format!("0x{b:02x},"))
                        .collect::<Vec<_>>()
                        .join(" "),
                );
                out.push('\n');
            }
            out.push_str(&format!("{indent}],\n"));
            out
        }

        let leaves = fixture_leaves();
        let mut nodes = leaves.clone();
        let mut level_bounds = Vec::new();
        let mut top_levels = Vec::new();
        for level in 0..FIXTURE_TREE_HEIGHT {
            let merkle_level = Level::from(u8::try_from(level).unwrap());
            nodes = nodes
                .as_chunks::<2>()
                .0
                .iter()
                .map(|pair| MerkleHashOrchard::combine(merkle_level, &pair[0], &pair[1]))
                .collect();
            level_bounds.push([nodes[0].to_bytes(), nodes[nodes.len() - 1].to_bytes()]);
            if level + 1 >= FIXTURE_TREE_HEIGHT - 2 {
                top_levels.extend(nodes.iter().map(MerkleHashOrchard::to_bytes));
            }
        }
        let mut out = String::new();
        let edges = edge_case_leaves().len();
        out.push_str(&format!(
            "\
// Fixed vectors for the Orchard Merkle fixture tree.
//
// GENERATED by `tree::tests::print_merkle_fixture_vectors`; do not edit by
// hand. Regenerate (without `weighted-merkle`) only after a deliberate
// change to `tree::tests::edge_case_leaves` or `tree::tests::fixture_leaves`:
//
//     cargo test -p zakura-orchard --lib \\
//         tree::tests::print_merkle_fixture_vectors -- --ignored --nocapture
//
// The tree: {leaves} leaves (2^{height}), of which {edges} are edge cases
// (the protocol's special values, a single set or clear bit at every
// position, a single all-ones Sinsemilla word at every word offset,
// alternating patterns, the largest canonical values, and every empty
// root) and the rest BLAKE2b-derived fill; all leaves are distinct. The
// first 256 edge cases are contiguous so they pair with each other, the
// remainder are spread so they pair with fill values. Folding it yields
// levels of 1024, 512, ..., 2, 1 parents, so `combine_batch` is
// exercised at every power-of-two width from 1024 down to 1.
//
// What is recorded (the full tree would be 4095 nodes; the test checks
// all of them against the scalar implementation, and these bytes pin a
// representative subset as a regression vector):
// - `root`: the level-{height} root;
// - `level_bounds[l]`: the first and last parent of level `l + 1`, for
//   `l` in `0..{height}` (level 1 holds 1024 parents, level {height} holds 1);
// - `top_levels`: every node of levels {h2}, {h1}, and {height} (4 + 2 + 1, root last).
//
// Produced by the scalar `MerkleHashOrchard::combine` on this crate's
// default (non-weighted) Sinsemilla path; `tree::tests::fixture_tree_matches_vectors`
// checks the batched combine, on both paths, against them.

",
            leaves = leaves.len(),
            height = FIXTURE_TREE_HEIGHT,
            edges = edges,
            h2 = FIXTURE_TREE_HEIGHT - 2,
            h1 = FIXTURE_TREE_HEIGHT - 1,
        ));
        out.push_str("pub(crate) struct TestVector {\n");
        out.push_str(
            "    /// Root of the fixture tree (level 11).\n    pub(crate) root: [u8; 32],\n",
        );
        out.push_str("    /// `[first, last]` parent of level `l + 1`, for `l` in `0..11`.\n");
        out.push_str(&format!(
            "    pub(crate) level_bounds: [[[u8; 32]; 2]; {FIXTURE_TREE_HEIGHT}],\n"
        ));
        out.push_str("    /// Every node of levels 9, 10, and 11 (4 + 2 + 1, root last).\n");
        out.push_str("    pub(crate) top_levels: [[u8; 32]; 7],\n}\n\n");
        out.push_str("pub(crate) fn test_vectors() -> TestVector {\n    TestVector {\n");
        out.push_str("        root: ");
        out.push_str(fmt(nodes[0].to_bytes(), "        ").trim_start());
        out.push_str("        level_bounds: [\n");
        for [first, last] in level_bounds {
            out.push_str("            [\n");
            out.push_str(&fmt(first, "                "));
            out.push_str(&fmt(last, "                "));
            out.push_str("            ],\n");
        }
        out.push_str("        ],\n        top_levels: [\n");
        for node in top_levels {
            out.push_str(&fmt(node, "            "));
        }
        out.push_str("        ],\n    }\n}\n");
        std::println!("{out}");
    }

    #[test]
    fn test_vectors() {
        let tv_empty_roots = crate::test_vectors::commitment_tree::test_vectors().empty_roots;

        for (height, root) in EMPTY_ROOTS.iter().enumerate() {
            assert_eq!(tv_empty_roots[height], root.to_bytes());
        }

        let mut tree: ShardTree<MemoryShardStore<MerkleHashOrchard, u32>, 4, 3> =
            ShardTree::new(MemoryShardStore::empty(), 100);
        for (i, tv) in crate::test_vectors::merkle_path::test_vectors()
            .into_iter()
            .enumerate()
        {
            let checkpoint_id = u32::try_from(i).unwrap();
            let cmx = MerkleHashOrchard::from_bytes(&tv.leaves[i]).unwrap();
            tree.append(
                cmx,
                Retention::Checkpoint {
                    id: checkpoint_id,
                    marking: Marking::Marked,
                },
            )
            .unwrap();

            let root = tree.root_at_checkpoint_id(&checkpoint_id).unwrap().unwrap();
            assert_eq!(root.0, pallas::Base::from_repr(tv.root).unwrap());

            // Check paths for all leaves up to this point. The test vectors include paths
            // for not-yet-appended leaves (using UNCOMMITTED_ORCHARD as the leaf value),
            // but BridgeTree doesn't encode these.
            for j in 0..=i {
                let position = j.try_into().unwrap();
                assert_eq!(
                    tree.witness_at_checkpoint_id(position, &checkpoint_id)
                        .unwrap(),
                    MerklePath::from_parts(
                        tv.paths[j]
                            .iter()
                            .map(|v| MerkleHashOrchard::from_bytes(v).unwrap())
                            .collect(),
                        position
                    )
                    .ok()
                );
            }
        }
    }

    #[test]
    fn empty_roots_incremental() {
        use incrementalmerkletree::Hashable;

        let tv_empty_roots = crate::test_vectors::commitment_tree::test_vectors().empty_roots;

        for (level, tv_root) in tv_empty_roots.iter().enumerate() {
            assert_eq!(
                MerkleHashOrchard::empty_root(Level::from(level as u8))
                    .0
                    .to_repr(),
                *tv_root,
                "Empty root mismatch at level {}",
                level
            );
        }
    }

    #[test]
    fn anchor_incremental() {
        let mut frontier: Frontier<MerkleHashOrchard, 32> = Frontier::empty();
        for commitment in ZCASHD_COMMITMENTS.iter() {
            let cmx = MerkleHashOrchard(pallas::Base::from_repr(*commitment).unwrap());
            frontier.append(cmx);
        }
        assert_eq!(
            frontier.root().0,
            pallas::Base::from_repr(ZCASHD_ANCHOR).unwrap()
        );
    }
}
