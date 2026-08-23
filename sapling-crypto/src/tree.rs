use bitvec::{order::Lsb0, view::AsBits};
use group::{ff::PrimeField, Curve};
use incrementalmerkletree::{Hashable, Level};
use lazy_static::lazy_static;
use subtle::CtOption;

use alloc::vec::Vec;
use core::fmt;

use super::{
    note::ExtractedNoteCommitment,
    pedersen_hash::{pedersen_hash, Personalization},
};

pub const NOTE_COMMITMENT_TREE_DEPTH: u8 = 32;
pub type CommitmentTree =
    incrementalmerkletree::frontier::CommitmentTree<Node, NOTE_COMMITMENT_TREE_DEPTH>;
pub type IncrementalWitness =
    incrementalmerkletree::witness::IncrementalWitness<Node, NOTE_COMMITMENT_TREE_DEPTH>;
pub type MerklePath = incrementalmerkletree::MerklePath<Node, NOTE_COMMITMENT_TREE_DEPTH>;

lazy_static! {
    static ref UNCOMMITTED_SAPLING: bls12_381::Scalar = bls12_381::Scalar::one();
    static ref EMPTY_ROOTS: Vec<Node> = empty_roots();
}

fn empty_roots() -> Vec<Node> {
    let mut v = vec![Node::empty_leaf()];
    for d in 0..NOTE_COMMITMENT_TREE_DEPTH {
        let next = Node::combine(d.into(), &v[usize::from(d)], &v[usize::from(d)]);
        v.push(next);
    }
    v
}

/// Compute a parent node in the Sapling commitment tree given its two children.
pub fn merkle_hash(depth: usize, lhs: &[u8; 32], rhs: &[u8; 32]) -> [u8; 32] {
    merkle_hash_field(depth, lhs, rhs).to_repr()
}

fn merkle_hash_field(depth: usize, lhs: &[u8; 32], rhs: &[u8; 32]) -> jubjub::Base {
    let lhs = {
        let mut tmp = [false; 256];
        for (a, b) in tmp.iter_mut().zip(lhs.as_bits::<Lsb0>()) {
            *a = *b;
        }
        tmp
    };

    let rhs = {
        let mut tmp = [false; 256];
        for (a, b) in tmp.iter_mut().zip(rhs.as_bits::<Lsb0>()) {
            *a = *b;
        }
        tmp
    };

    pedersen_hash(
        Personalization::MerkleTree(depth),
        lhs.iter()
            .copied()
            .take(bls12_381::Scalar::NUM_BITS as usize)
            .chain(
                rhs.iter()
                    .copied()
                    .take(bls12_381::Scalar::NUM_BITS as usize),
            ),
    )
    .to_affine()
    .get_u()
}

/// The root of a Sapling commitment tree.
#[derive(Eq, PartialEq, Clone, Copy, Debug)]
pub struct Anchor(jubjub::Base);

impl From<jubjub::Base> for Anchor {
    fn from(anchor_field: jubjub::Base) -> Anchor {
        Anchor(anchor_field)
    }
}

impl From<Node> for Anchor {
    fn from(anchor: Node) -> Anchor {
        Anchor(anchor.0)
    }
}

impl Anchor {
    /// The anchor of the empty Sapling note commitment tree.
    ///
    /// This anchor does not correspond to any valid anchor for a spend, so it
    /// may only be used for coinbase bundles or in circumstances where Sapling
    /// functionality is not active.
    pub fn empty_tree() -> Anchor {
        Anchor(Node::empty_root(NOTE_COMMITMENT_TREE_DEPTH.into()).0)
    }

    pub(crate) fn inner(&self) -> jubjub::Base {
        self.0
    }

    /// Parses a Sapling anchor from a byte encoding.
    pub fn from_bytes(bytes: [u8; 32]) -> CtOption<Anchor> {
        jubjub::Base::from_repr(bytes).map(Self)
    }

    /// Returns the byte encoding of this anchor.
    pub fn to_bytes(self) -> [u8; 32] {
        self.0.to_repr()
    }
}

/// A node within the Sapling commitment tree.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Node(jubjub::Base);

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Node")
            .field("repr", &hex::encode(self.0.to_bytes()))
            .finish()
    }
}

impl Node {
    /// Creates a tree leaf from the given Sapling note commitment.
    pub fn from_cmu(value: &ExtractedNoteCommitment) -> Self {
        Node(value.inner())
    }

    /// Constructs a new note commitment tree node from a [`bls12_381::Scalar`]
    pub fn from_scalar(cmu: bls12_381::Scalar) -> Self {
        Self(cmu)
    }

    /// Parses a tree leaf from the bytes of a Sapling note commitment.
    ///
    /// Returns `None` if the provided bytes represent a non-canonical encoding.
    pub fn from_bytes(bytes: [u8; 32]) -> CtOption<Self> {
        jubjub::Base::from_repr(bytes).map(Self)
    }

    /// Returns the canonical byte representation of this node.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.to_repr()
    }

    /// Returns the wrapped value
    #[cfg(feature = "circuit")]
    pub(crate) fn inner(&self) -> &jubjub::Base {
        &self.0
    }
}

impl Hashable for Node {
    fn empty_leaf() -> Self {
        Node(*UNCOMMITTED_SAPLING)
    }

    fn combine(level: Level, lhs: &Self, rhs: &Self) -> Self {
        Node(merkle_hash_field(
            level.into(),
            &lhs.0.to_bytes(),
            &rhs.0.to_bytes(),
        ))
    }

    fn empty_root(level: Level) -> Self {
        EMPTY_ROOTS[<usize>::from(level)]
    }
}

impl From<Node> for bls12_381::Scalar {
    fn from(node: Node) -> Self {
        node.0
    }
}

#[cfg(any(test, feature = "test-dependencies"))]
pub(super) mod testing {
    use ff::Field;
    use proptest::prelude::*;
    use rand::{
        distr::{Distribution, StandardUniform},
        Rng as RandRng,
    };

    use super::Node;
    use crate::note::testing::arb_cmu;

    prop_compose! {
        pub fn arb_node()(cmu in arb_cmu()) -> Node {
            Node::from_cmu(&cmu)
        }
    }

    impl Node {
        /// Return a random fake `MerkleHashOrchard`.
        pub fn random(rng: &mut impl RandRng) -> Self {
            StandardUniform.sample(rng)
        }
    }

    impl Distribution<Node> for StandardUniform {
        fn sample<R: RandRng + ?Sized>(&self, rng: &mut R) -> Node {
            Node::from_scalar(bls12_381::Scalar::random(rng))
        }
    }
}

#[cfg(test)]
mod tests {
    use incrementalmerkletree::Hashable;

    use super::Node;

    /// Canonical encodings of `Node::empty_root` at levels 0..=32, matching
    /// `zcash_primitives` (`HEX_EMPTY_ROOTS`) so fused and windowed evaluators
    /// stay pinned to the protocol empty tree.
    const HEX_EMPTY_ROOTS: [&str; 33] = [
        "0100000000000000000000000000000000000000000000000000000000000000",
        "817de36ab2d57feb077634bca77819c8e0bd298c04f6fed0e6a83cc1356ca155",
        "ffe9fc03f18b176c998806439ff0bb8ad193afdb27b2ccbc88856916dd804e34",
        "d8283386ef2ef07ebdbb4383c12a739a953a4d6e0d6fb1139a4036d693bfbb6c",
        "e110de65c907b9dea4ae0bd83a4b0a51bea175646a64c12b4c9f931b2cb31b49",
        "912d82b2c2bca231f71efcf61737fbf0a08befa0416215aeef53e8bb6d23390a",
        "8ac9cf9c391e3fd42891d27238a81a8a5c1d3a72b1bcbea8cf44a58ce7389613",
        "d6c639ac24b46bd19341c91b13fdcab31581ddaf7f1411336a271f3d0aa52813",
        "7b99abdc3730991cc9274727d7d82d28cb794edbc7034b4f0053ff7c4b680444",
        "43ff5457f13b926b61df552d4e402ee6dc1463f99a535f9a713439264d5b616b",
        "ba49b659fbd0b7334211ea6a9d9df185c757e70aa81da562fb912b84f49bce72",
        "4777c8776a3b1e69b73a62fa701fa4f7a6282d9aee2c7a6b82e7937d7081c23c",
        "ec677114c27206f5debc1c1ed66f95e2b1885da5b7be3d736b1de98579473048",
        "1b77dac4d24fb7258c3c528704c59430b630718bec486421837021cf75dab651",
        "bd74b25aacb92378a871bf27d225cfc26baca344a1ea35fdd94510f3d157082c",
        "d6acdedf95f608e09fa53fb43dcd0990475726c5131210c9e5caeab97f0e642f",
        "1ea6675f9551eeb9dfaaa9247bc9858270d3d3a4c5afa7177a984d5ed1be2451",
        "6edb16d01907b759977d7650dad7e3ec049af1a3d875380b697c862c9ec5d51c",
        "cd1c8dbf6e3acc7a80439bc4962cf25b9dce7c896f3a5bd70803fc5a0e33cf00",
        "6aca8448d8263e547d5ff2950e2ed3839e998d31cbc6ac9fd57bc6002b159216",
        "8d5fa43e5a10d11605ac7430ba1f5d81fb1b68d29a640405767749e841527673",
        "08eeab0c13abd6069e6310197bf80f9c1ea6de78fd19cbae24d4a520e6cf3023",
        "0769557bc682b1bf308646fd0b22e648e8b9e98f57e29f5af40f6edb833e2c49",
        "4c6937d78f42685f84b43ad3b7b00f81285662f85c6a68ef11d62ad1a3ee0850",
        "fee0e52802cb0c46b1eb4d376c62697f4759f6c8917fa352571202fd778fd712",
        "16d6252968971a83da8521d65382e61f0176646d771c91528e3276ee45383e4a",
        "d2e1642c9a462229289e5b0e3b7f9008e0301cbb93385ee0e21da2545073cb58",
        "a5122c08ff9c161d9ca6fc462073396c7d7d38e8ee48cdb3bea7e2230134ed6a",
        "28e7b841dcbc47cceb69d7cb8d94245fb7cb2ba3a7a6bc18f13f945f7dbd6e2a",
        "e1f34b034d4a3cd28557e2907ebf990c918f64ecb50a94f01d6fda5ca5c7ef72",
        "12935f14b676509b81eb49ef25f39269ed72309238b4c145803544b646dca62d",
        "b2eed031d4d6a4f02a097f80b54cc1541d4163c6b6f5971f88b6e41d35c53814",
        "fbc2f4300c01f0b7820d00e3347c8da4ee614674376cbc45359daa54f9b5493e",
    ];

    #[test]
    fn empty_roots_match_protocol_vectors() {
        for (level, expected) in HEX_EMPTY_ROOTS.iter().enumerate() {
            assert_eq!(
                hex::encode(Node::empty_root((level as u8).into()).to_bytes()),
                *expected,
                "empty root mismatch at level {level}",
            );
        }
    }
}
