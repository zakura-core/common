//! Verification functions for the [Equihash] proof-of-work algorithm.
//!
//! [Equihash]: https://zips.z.cash/protocol/protocol.pdf#equihash

#[cfg(any(feature = "solver", test))]
use alloc::vec::Vec;
#[cfg(test)]
use blake2b_simd::Hash as Blake2bHash;
#[cfg(any(feature = "solver", test))]
use blake2b_simd::{Params as Blake2bParams, State as Blake2bState};
use core::fmt;
#[cfg(any(feature = "solver", test))]
use corez::io::Write;

#[cfg(test)]
use crate::minimal::expand_array;
use crate::{
    leaf_hash::{Digest, HEADER_BYTES, LeafHasher, NONCE_BYTES},
    minimal::{expand_array_into, indices_from_minimal},
    params::Params,
};

// `Node` and the functions that build it are the original node-based
// validators, kept as test oracles for the single-pass validator below.
#[cfg(test)]
#[derive(Clone)]
struct Node {
    hash: Vec<u8>,
    indices: Vec<u32>,
}

#[cfg(test)]
impl Node {
    fn new(p: &Params, state: &Blake2bState, i: u32) -> Self {
        let hash = generate_hash(state, i / p.indices_per_hash_output());
        let start = ((i % p.indices_per_hash_output()) * p.n / 8) as usize;
        let end = start + (p.n as usize) / 8;
        Node {
            hash: expand_array(&hash.as_bytes()[start..end], p.collision_bit_length(), 0),
            indices: vec![i],
        }
    }

    // Clippy incorrectly interprets the first argument as `self`.
    #[allow(clippy::wrong_self_convention)]
    fn from_children(a: Node, b: Node, trim: usize) -> Self {
        let hash: Vec<_> = a
            .hash
            .iter()
            .zip(b.hash.iter())
            .skip(trim)
            .map(|(a, b)| a ^ b)
            .collect();
        let indices = if a.indices_before(&b) {
            let mut indices = a.indices;
            indices.extend(b.indices.iter());
            indices
        } else {
            let mut indices = b.indices;
            indices.extend(a.indices.iter());
            indices
        };
        Node { hash, indices }
    }

    #[cfg(test)]
    fn from_children_ref(a: &Node, b: &Node, trim: usize) -> Self {
        let hash: Vec<_> = a
            .hash
            .iter()
            .zip(b.hash.iter())
            .skip(trim)
            .map(|(a, b)| a ^ b)
            .collect();
        let mut indices = Vec::with_capacity(a.indices.len() + b.indices.len());
        if a.indices_before(b) {
            indices.extend(a.indices.iter());
            indices.extend(b.indices.iter());
        } else {
            indices.extend(b.indices.iter());
            indices.extend(a.indices.iter());
        }
        Node { hash, indices }
    }

    fn indices_before(&self, other: &Node) -> bool {
        // Indices are serialized in big-endian so that integer
        // comparison is equivalent to array comparison
        self.indices[0] < other.indices[0]
    }

    fn is_zero(&self, len: usize) -> bool {
        self.hash.iter().take(len).all(|v| *v == 0)
    }
}

/// An Equihash solution failed to verify.
#[derive(Debug)]
pub struct Error(Kind);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Invalid solution: {}", self.0)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}

#[derive(Debug, PartialEq)]
pub(super) enum Kind {
    InvalidParams,
    Collision,
    OutOfOrder,
    DuplicateIdxs,
    NonZeroRootHash,
    UnsupportedInputLength,
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Kind::InvalidParams => f.write_str("invalid parameters"),
            Kind::Collision => f.write_str("invalid collision length between StepRows"),
            Kind::OutOfOrder => f.write_str("Index tree incorrectly ordered"),
            Kind::DuplicateIdxs => f.write_str("duplicate indices"),
            Kind::NonZeroRootHash => f.write_str("root hash of tree is non-zero"),
            Kind::UnsupportedInputLength => {
                f.write_str("input and nonce are not a Zcash block header and nonce")
            }
        }
    }
}

#[cfg(any(feature = "solver", test))]
pub(super) fn initialise_state(n: u32, k: u32, digest_len: u8) -> Blake2bState {
    let mut personalization: Vec<u8> = Vec::from(crate::BLAKE2B_PERSONALIZATION_PREFIX.as_slice());
    personalization.write_all(&n.to_le_bytes()).unwrap();
    personalization.write_all(&k.to_le_bytes()).unwrap();

    Blake2bParams::new()
        .hash_length(digest_len as usize)
        .personal(&personalization)
        .to_state()
}

#[cfg(test)]
fn generate_hash(base_state: &Blake2bState, i: u32) -> Blake2bHash {
    let mut lei = [0u8; 4];
    (&mut lei[..]).write_all(&i.to_le_bytes()).unwrap();

    let mut state = base_state.clone();
    state.update(&lei);
    state.finalize()
}

#[cfg(test)]
fn has_collision(a: &Node, b: &Node, len: usize) -> bool {
    a.hash
        .iter()
        .zip(b.hash.iter())
        .take(len)
        .all(|(a, b)| a == b)
}

#[cfg(test)]
fn distinct_indices(a: &Node, b: &Node) -> bool {
    for i in &(a.indices) {
        for j in &(b.indices) {
            if i == j {
                return false;
            }
        }
    }
    true
}

#[cfg(test)]
fn validate_subtrees(p: &Params, a: &Node, b: &Node) -> Result<(), Kind> {
    if !has_collision(a, b, p.collision_byte_length()) {
        Err(Kind::Collision)
    } else if b.indices_before(a) {
        Err(Kind::OutOfOrder)
    } else if !distinct_indices(a, b) {
        Err(Kind::DuplicateIdxs)
    } else {
        Ok(())
    }
}

#[cfg(test)]
fn is_valid_solution_iterative(
    p: Params,
    input: &[u8],
    nonce: &[u8],
    indices: &[u32],
) -> Result<(), Error> {
    let mut state = initialise_state(p.n, p.k, p.hash_output());
    state.update(input);
    state.update(nonce);

    let mut rows = Vec::new();
    for i in indices {
        rows.push(Node::new(&p, &state, *i));
    }

    let mut hash_len = p.hash_length();
    while rows.len() > 1 {
        let mut cur_rows = Vec::new();
        for pair in rows.chunks(2) {
            let a = &pair[0];
            let b = &pair[1];
            validate_subtrees(&p, a, b).map_err(Error)?;
            cur_rows.push(Node::from_children_ref(a, b, p.collision_byte_length()));
        }
        rows = cur_rows;
        hash_len -= p.collision_byte_length();
    }

    assert!(rows.len() == 1);

    if rows[0].is_zero(hash_len) {
        Ok(())
    } else {
        Err(Error(Kind::NonZeroRootHash))
    }
}

#[cfg(test)]
fn tree_validator(p: &Params, state: &Blake2bState, indices: &[u32]) -> Result<Node, Error> {
    if indices.len() > 1 {
        let end = indices.len();
        let mid = end / 2;
        let a = tree_validator(p, state, &indices[0..mid])?;
        let b = tree_validator(p, state, &indices[mid..end])?;
        validate_subtrees(p, &a, &b).map_err(Error)?;
        Ok(Node::from_children(a, b, p.collision_byte_length()))
    } else {
        Ok(Node::new(p, state, indices[0]))
    }
}

#[cfg(test)]
fn is_valid_solution_recursive(
    p: Params,
    input: &[u8],
    nonce: &[u8],
    indices: &[u32],
) -> Result<(), Error> {
    let mut state = initialise_state(p.n, p.k, p.hash_output());
    state.update(input);
    state.update(nonce);

    let root = tree_validator(&p, &state, indices)?;

    // Hashes were trimmed, so only need to check remaining length
    if root.is_zero(p.collision_byte_length()) {
        Ok(())
    } else {
        Err(Error(Kind::NonZeroRootHash))
    }
}

/// Checks whether `soln` is a valid solution for `(input, nonce)` with the
/// parameters `(n, k)`.
///
/// `input || nonce` must have the length of a Zcash block header and nonce
/// (108 and 32 bytes); other lengths are rejected.
pub fn is_valid_solution(
    n: u32,
    k: u32,
    input: &[u8],
    nonce: &[u8],
    soln: &[u8],
) -> Result<(), Error> {
    let p = Params::new(n, k).ok_or(Error(Kind::InvalidParams))?;
    let indices = indices_from_minimal(p, soln).ok_or(Error(Kind::InvalidParams))?;
    let hasher = LeafHasher::new(&p, input, nonce).ok_or(Error(Kind::UnsupportedInputLength))?;
    validate_tree(&p, &indices, |blocks, digests| hasher.hash(blocks, digests)).map_err(Error)
}

// The Zcash prefix length the leaf hasher accepts.
const _: () = assert!(HEADER_BYTES + NONCE_BYTES == 140);

/// Leaves hashed per call to `validate_tree`'s `hash`; a multiple of every
/// kernel's lane count.
const HASH_BATCH: usize = 64;

/// Validates the solution tree for `indices`, where `hash` writes the digest
/// of each block index in a batch.
///
/// Subtrees are merged in the same post-order, with the same checks in the
/// same order, as the recursive validator, so both report the same error.
fn validate_tree(
    p: &Params,
    indices: &[u32],
    mut hash: impl FnMut(&[u32], &mut [Digest]),
) -> Result<(), Kind> {
    // Anything else would leave the tree, or its root, partly unvisited.
    let leaves = indices.len();
    if p.solution_indices() != Some(leaves) {
        return Err(Kind::InvalidParams);
    }
    let per_hash = p.indices_per_hash_output();
    let leaf_bytes = p.n as usize / 8;
    let collision_bytes = p.collision_byte_length();
    let row_len = p.hash_length();

    // With every index distinct, each subtree pair's duplicate check passes.
    let mut sorted = indices.to_vec();
    sorted.sort_unstable();
    let all_distinct = sorted.windows(2).all(|w| w[0] != w[1]);
    drop(sorted);

    // `pending[h]` holds the unmerged left subtree of height `h`, which has
    // `row_len - h * collision_bytes` hash bytes after trimming.
    let mut pending = vec![0u8; (p.k as usize + 1) * row_len];
    let mut row = vec![0u8; row_len];
    // Hash leaves in small batches as the walk reaches them, so memory does
    // not grow with `2^k` and an invalid solution stops within one batch of
    // its first failing check.
    let mut blocks = [0u32; HASH_BATCH];
    let mut digests = [[0u8; 64]; HASH_BATCH];
    for (batch, chunk) in indices.chunks(HASH_BATCH).enumerate() {
        let blocks = &mut blocks[..chunk.len()];
        let digests = &mut digests[..chunk.len()];
        for (block, index) in blocks.iter_mut().zip(chunk) {
            *block = index / per_hash;
        }
        hash(blocks, digests);
        for (offset, (index, digest)) in chunk.iter().zip(digests.iter()).enumerate() {
            let leaf = batch * HASH_BATCH + offset;
            let start = (index % per_hash) as usize * leaf_bytes;
            expand_array_into(
                &digest[start..start + leaf_bytes],
                p.collision_bit_length(),
                0,
                &mut row,
            );

            // Each set low bit of `leaf` marks a pending left sibling.
            let mut height = 0;
            while leaf >> height & 1 == 1 {
                let len = row_len - height * collision_bytes;
                let left = &pending[height * row_len..][..len];
                let right_start = leaf + 1 - (1 << height);
                let left_start = right_start - (1 << height);
                let left_indices = &indices[left_start..right_start];
                let right_indices = &indices[right_start..=leaf];

                if left[..collision_bytes] != row[..collision_bytes] {
                    return Err(Kind::Collision);
                }
                if right_indices[0] < left_indices[0] {
                    return Err(Kind::OutOfOrder);
                }
                if !all_distinct && left_indices.iter().any(|i| right_indices.contains(i)) {
                    return Err(Kind::DuplicateIdxs);
                }

                // On success the merged subtree's indices are `left || right`,
                // which is their order in `indices`.
                for (i, left) in left[collision_bytes..].iter().enumerate() {
                    row[i] = left ^ row[collision_bytes + i];
                }
                height += 1;
            }
            let len = row_len - height * collision_bytes;
            pending[height * row_len..][..len].copy_from_slice(&row[..len]);
        }
    }

    // Hashes were trimmed, so the root holds one collision's worth of bytes.
    let root = &pending[p.k as usize * row_len..][..collision_bytes];
    if root.iter().all(|b| *b == 0) {
        Ok(())
    } else {
        Err(Kind::NonZeroRootHash)
    }
}

/// Runs the single-pass validator with `blake2b_simd` leaf hashes, which
/// accept any input length, such as the upstream test vectors'.
#[cfg(test)]
fn validate_with_reference(
    p: Params,
    input: &[u8],
    nonce: &[u8],
    indices: &[u32],
) -> Result<(), Kind> {
    validate_tree(&p, indices, |blocks, digests: &mut [Digest]| {
        let mut state = initialise_state(p.n, p.k, p.hash_output());
        state.update(input);
        state.update(nonce);
        for (block, digest) in blocks.iter().zip(digests) {
            let hash = generate_hash(&state, *block);
            digest[..hash.as_bytes().len()].copy_from_slice(hash.as_bytes());
        }
    })
}

/// [`is_valid_solution`] without the Zcash header length requirement, for
/// tests whose inputs predate it.
#[cfg(all(test, feature = "solver"))]
pub(crate) fn is_valid_solution_any_input(
    n: u32,
    k: u32,
    input: &[u8],
    nonce: &[u8],
    soln: &[u8],
) -> Result<(), Error> {
    let p = Params::new(n, k).ok_or(Error(Kind::InvalidParams))?;
    let indices = indices_from_minimal(p, soln).ok_or(Error(Kind::InvalidParams))?;
    validate_with_reference(p, input, nonce, &indices).map_err(Error)
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use super::{
        Kind, is_valid_solution, is_valid_solution_iterative, is_valid_solution_recursive,
        validate_tree, validate_with_reference,
    };
    use crate::leaf_hash::{Kernel, LeafHasher};
    use crate::minimal::indices_from_minimal;
    use crate::params::Params;
    use crate::test_vectors::{
        INVALID_TEST_VECTORS, MAINNET_415000_HEADER, MAINNET_415000_NONCE, MAINNET_415000_SOLUTION,
        REGTEST_GENESIS_HEADER, REGTEST_GENESIS_NONCE, REGTEST_GENESIS_SOLUTION,
        VALID_TEST_VECTORS,
    };

    fn mainnet_415000() -> (Vec<u8>, Vec<u8>, Vec<u8>) {
        (
            hex::decode(MAINNET_415000_HEADER).unwrap(),
            hex::decode(MAINNET_415000_NONCE).unwrap(),
            hex::decode(MAINNET_415000_SOLUTION).unwrap(),
        )
    }

    #[test]
    fn valid_test_vectors() {
        for tv in VALID_TEST_VECTORS {
            for soln in tv.solutions {
                is_valid_solution_iterative(tv.params, tv.input, &tv.nonce, soln).unwrap();
                is_valid_solution_recursive(tv.params, tv.input, &tv.nonce, soln).unwrap();
                validate_with_reference(tv.params, tv.input, &tv.nonce, soln).unwrap();
            }
        }
    }

    #[test]
    fn invalid_test_vectors() {
        for tv in INVALID_TEST_VECTORS {
            assert_eq!(
                is_valid_solution_iterative(tv.params, tv.input, &tv.nonce, tv.solution)
                    .unwrap_err()
                    .0,
                tv.error
            );
            assert_eq!(
                is_valid_solution_recursive(tv.params, tv.input, &tv.nonce, tv.solution)
                    .unwrap_err()
                    .0,
                tv.error
            );
            assert_eq!(
                validate_with_reference(tv.params, tv.input, &tv.nonce, tv.solution).unwrap_err(),
                tv.error
            );
        }
    }

    #[test]
    fn mainnet_block_415000() {
        let (header, nonce, soln) = mainnet_415000();
        is_valid_solution(200, 9, &header, &nonce, &soln).unwrap();

        let p = Params::new(200, 9).unwrap();
        let indices = indices_from_minimal(p, &soln).unwrap();
        is_valid_solution_recursive(p, &header, &nonce, &indices).unwrap();
        for kernel in Kernel::supported() {
            let hasher = LeafHasher::with_kernel(&p, &header, &nonce, kernel).unwrap();
            validate_tree(&p, &indices, |blocks, digests| hasher.hash(blocks, digests))
                .unwrap_or_else(|e| panic!("{kernel:?}: {e}"));
        }

        // The layout is fixed only in total length.
        let prefix = [&header[..], &nonce[..]].concat();
        is_valid_solution(200, 9, &prefix, &[], &soln).unwrap();

        let mut nonce = nonce;
        nonce[31] ^= 1;
        is_valid_solution(200, 9, &header, &nonce, &soln).unwrap_err();
    }

    #[test]
    fn regtest_genesis() {
        let header = hex::decode(REGTEST_GENESIS_HEADER).unwrap();
        let nonce = hex::decode(REGTEST_GENESIS_NONCE).unwrap();
        let soln = hex::decode(REGTEST_GENESIS_SOLUTION).unwrap();
        is_valid_solution(48, 5, &header, &nonce, &soln).unwrap();

        let p = Params::new(48, 5).unwrap();
        let indices = indices_from_minimal(p, &soln).unwrap();
        is_valid_solution_recursive(p, &header, &nonce, &indices).unwrap();
        for kernel in Kernel::supported() {
            let hasher = LeafHasher::with_kernel(&p, &header, &nonce, kernel).unwrap();
            validate_tree(&p, &indices, |blocks, digests| hasher.hash(blocks, digests))
                .unwrap_or_else(|e| panic!("{kernel:?}: {e}"));
        }

        // Every bit of the solution and nonce matters.
        for i in 0..soln.len() * 8 {
            let mut mutated = soln.clone();
            mutated[i / 8] ^= 1 << (i % 8);
            is_valid_solution(48, 5, &header, &nonce, &mutated).unwrap_err();
        }
        for i in 0..nonce.len() * 8 {
            let mut mutated = nonce.clone();
            mutated[i / 8] ^= 1 << (i % 8);
            is_valid_solution(48, 5, &header, &mutated, &soln).unwrap_err();
        }
        // Mainnet parameters reject the Regtest solution.
        is_valid_solution(200, 9, &header, &nonce, &soln).unwrap_err();
    }

    #[test]
    fn rejects_unsupported_parameters() {
        let (header, nonce, _) = mainnet_415000();
        // With a wrapping `1 << 64`, (520, 64) expected a one-byte solution
        // that decoded to no indices, leaving an unvisited all-zero root.
        for byte in 0..=u8::MAX {
            assert_eq!(
                is_valid_solution(520, 64, &header, &nonce, &[byte])
                    .unwrap_err()
                    .0,
                Kind::InvalidParams
            );
        }
        // Too wide for one BLAKE2b output, and collision lengths outside
        // 8..=24 bits. (448, 63) wrapped its solution length to zero on
        // 64-bit targets, and (134_217_736, 16_777_216) derived a 256 TiB
        // buffer from `k`.
        for (n, k) in [
            (520, 64),
            (1024, 3),
            (48, 7),
            (200, 7),
            (104, 3),
            (448, 63),
            (134_217_736, 16_777_216),
        ] {
            assert!(Params::new(n, k).is_none(), "({n}, {k})");
        }
        for (n, k) in [(200, 9), (48, 5), (96, 5), (144, 5), (96, 3), (512, 63)] {
            assert!(Params::new(n, k).is_some(), "({n}, {k})");
        }
        for (n, k) in [(448, 63), (134_217_736, 16_777_216)] {
            for soln in [&[][..], &[0]] {
                assert_eq!(
                    is_valid_solution(n, k, &header, &nonce, soln)
                        .unwrap_err()
                        .0,
                    Kind::InvalidParams
                );
            }
        }
        // `2^32` leaves overflow `usize` on 32-bit targets, where (264, 32)
        // wrapped to a one-byte solution with no indices.
        let p = Params::new(264, 32).unwrap();
        assert_eq!(
            p.solution_indices(),
            1usize.checked_shl(32),
            "the leaf count is checked, never wrapped",
        );
        assert_eq!(
            is_valid_solution(264, 32, &header, &nonce, &[0])
                .unwrap_err()
                .0,
            Kind::InvalidParams
        );
        // (512, 63) is accepted, but no solution length fits in `usize`
        // arithmetic on 64-bit targets without overflow.
        let p = Params::new(512, 63).unwrap();
        assert_eq!(p.solution_bytes(), None);
        assert_eq!(
            is_valid_solution(512, 63, &header, &nonce, &[0; 9])
                .unwrap_err()
                .0,
            Kind::InvalidParams
        );
    }

    #[test]
    fn validate_tree_rejects_wrong_leaf_counts() {
        let p = Params::new(200, 9).unwrap();
        for leaves in [0, 1, 511, 513] {
            let indices: Vec<u32> = (0..leaves).collect();
            assert_eq!(
                validate_tree(&p, &indices, |_, digests| digests.fill([0; 64])),
                Err(Kind::InvalidParams),
                "{leaves} leaves",
            );
        }
    }

    #[test]
    fn invalid_solutions_stop_within_one_hash_batch() {
        // An all-zero (168, 20) solution decodes to 2^20 zero indices, so its
        // first merge fails as a duplicate. Only the first batch is hashed.
        let p = Params::new(168, 20).unwrap();
        let soln = vec![0; p.solution_bytes().unwrap()];
        let indices = indices_from_minimal(p, &soln).unwrap();
        assert_eq!(indices.len(), 1 << 20);
        let mut hashed = 0;
        let result = validate_tree(&p, &indices, |blocks, digests| {
            hashed += blocks.len();
            digests.fill([0; 64]);
        });
        assert_eq!(result, Err(Kind::DuplicateIdxs));
        assert_eq!(hashed, super::HASH_BATCH);
    }

    #[test]
    fn rejects_other_input_lengths() {
        let (header, nonce, soln) = mainnet_415000();
        for (input, nonce) in [
            (&header[..107], &nonce[..]),
            (&header[..], &nonce[..31]),
            (&[header.clone(), vec![0]].concat()[..], &nonce[..]),
            (&[][..], &[][..]),
        ] {
            assert_eq!(
                is_valid_solution(200, 9, input, nonce, &soln)
                    .unwrap_err()
                    .0,
                Kind::UnsupportedInputLength
            );
        }
        // Parameter and encoding errors are reported first, as before.
        assert_eq!(
            is_valid_solution(200, 8, &[], &[], &soln).unwrap_err().0,
            Kind::InvalidParams
        );
        assert_eq!(
            is_valid_solution(200, 9, &[], &[], &soln[1..])
                .unwrap_err()
                .0,
            Kind::InvalidParams
        );
    }

    /// Returns a mutated copy of `indices` and a label for failures.
    fn mutate(indices: &[u32], rng: &mut u64, max_index: u32) -> (Vec<u32>, &'static str) {
        let mut next = |bound: usize| {
            // xorshift64*
            *rng ^= *rng >> 12;
            *rng ^= *rng << 25;
            *rng ^= *rng >> 27;
            (rng.wrapping_mul(0x2545_f491_4f6c_dd1d) >> 32) as usize % bound
        };
        let mut out = indices.to_vec();
        let len = out.len();
        let height = next(len.trailing_zeros() as usize);
        let width = 1 << height;
        let pair = next(len / (2 * width)) * 2 * width;
        let label = match next(6) {
            0 => {
                let (a, b) = (next(len), next(len));
                out.swap(a, b);
                "swap two indices"
            }
            1 => {
                let (left, right) = out[pair..pair + 2 * width].split_at_mut(width);
                left.swap_with_slice(right);
                "swap sibling subtrees"
            }
            2 => {
                let (a, b) = (next(len), next(len));
                out[b] = out[a];
                "copy one index"
            }
            3 => {
                out[next(len)] = next(max_index as usize + 1) as u32;
                "replace one index"
            }
            4 => {
                out.copy_within(pair..pair + width, pair + width);
                "duplicate a subtree over its sibling"
            }
            _ => "unchanged",
        };
        (out, label)
    }

    #[test]
    fn matches_recursive_validator_on_mutations() {
        let (header, nonce, soln) = mainnet_415000();
        let mainnet = Params::new(200, 9).unwrap();
        // Parameters, input, nonce, and indices of each valid solution.
        type Case<'a> = (Params, &'a [u8], &'a [u8], Vec<u32>);
        let mut cases: Vec<Case<'_>> = vec![(
            mainnet,
            &header,
            &nonce,
            indices_from_minimal(mainnet, &soln).unwrap(),
        )];
        for tv in VALID_TEST_VECTORS {
            for soln in tv.solutions {
                cases.push((tv.params, tv.input, &tv.nonce, soln.to_vec()));
            }
        }

        let mut rng = 0x5eed_u64;
        let mut seen = Vec::new();
        for (p, input, nonce, indices) in &cases {
            let max_index = (1u32 << (p.collision_bit_length() + 1)) - 1;
            let rounds = if p.k == 9 { 128 } else { 64 };
            for _ in 0..rounds {
                let (mutated, label) = mutate(indices, &mut rng, max_index);
                let expected =
                    is_valid_solution_recursive(*p, input, nonce, &mutated).map_err(|e| e.0);
                let actual = validate_with_reference(*p, input, nonce, &mutated);
                assert_eq!(actual, expected, "({}, {}) {label}", p.n, p.k);
                if input.len() + nonce.len() == 140 {
                    for kernel in Kernel::supported() {
                        let hasher = LeafHasher::with_kernel(p, input, nonce, kernel).unwrap();
                        let actual = validate_tree(p, &mutated, |blocks, digests| {
                            hasher.hash(blocks, digests)
                        });
                        assert_eq!(actual, expected, "{kernel:?} {label}");
                    }
                }
                if !seen.contains(&expected) {
                    seen.push(expected);
                }
            }
        }
        // A non-zero root needs crafted hashes; see `non_zero_root_hash`.
        for kind in [Kind::Collision, Kind::OutOfOrder, Kind::DuplicateIdxs] {
            let message = format!("no mutation produced {kind:?}");
            assert!(seen.contains(&Err(kind)), "{message}");
        }
        assert!(seen.contains(&Ok(())));
    }

    #[test]
    fn non_zero_root_hash() {
        // For (96, 5), expansion copies each 12-byte leaf slice unchanged and
        // every collision is two bytes. Hashes that are zero except the last
        // byte of leaf 0 pass every collision check and leave that byte in
        // the root.
        let p = Params::new(96, 5).unwrap();
        let indices: Vec<u32> = (0..32).collect();
        let result = validate_tree(&p, &indices, |blocks, digests| {
            for (block, digest) in blocks.iter().zip(digests) {
                *digest = [0; 64];
                if *block == 0 {
                    digest[11] = 1;
                }
            }
        });
        assert_eq!(result, Err(Kind::NonZeroRootHash));
    }

    #[test]
    fn all_bits_matter() {
        // Initialize the state according to one of the valid test vectors.
        let p = Params::new(96, 5).unwrap();
        let input = b"Equihash is an asymmetric PoW based on the Generalised Birthday problem.";
        let nonce = [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ];
        let soln = &[
            0x04, 0x6a, 0x8e, 0xd4, 0x51, 0xa2, 0x19, 0x73, 0x32, 0xe7, 0x1f, 0x39, 0xdb, 0x9c,
            0x79, 0xfb, 0xf9, 0x3f, 0xc1, 0x44, 0x3d, 0xa5, 0x8f, 0xb3, 0x8d, 0x05, 0x99, 0x17,
            0x21, 0x16, 0xd5, 0x55, 0xb1, 0xb2, 0x1f, 0x32, 0x70, 0x5c, 0xe9, 0x98, 0xf6, 0x0d,
            0xa8, 0x52, 0xf7, 0x7f, 0x0e, 0x7f, 0x4d, 0x63, 0xfc, 0x2d, 0xd2, 0x30, 0xa3, 0xd9,
            0x99, 0x53, 0xa0, 0x78, 0x7d, 0xfe, 0xfc, 0xab, 0x34, 0x1b, 0xde, 0xc8,
        ];

        // Prove that the solution is valid.
        let indices = indices_from_minimal(p, soln).unwrap();
        validate_with_reference(p, input, &nonce, &indices).unwrap();

        // Changing any single bit of the encoded solution should make it
        // invalid.
        for i in 0..soln.len() * 8 {
            let mut mutated = soln.to_vec();
            mutated[i / 8] ^= 1 << (i % 8);
            let indices = indices_from_minimal(p, &mutated).unwrap();
            validate_with_reference(p, input, &nonce, &indices).unwrap_err();
        }
    }

    #[test]
    fn mainnet_solution_bits_matter() {
        let (header, nonce, soln) = mainnet_415000();

        // Flip one bit of every byte, rotating through the bit positions, on
        // the public path. Every bit is covered by `all_bits_matter` above.
        for byte in 0..soln.len() {
            let mut mutated = soln.clone();
            mutated[byte] ^= 1 << (byte % 8);
            is_valid_solution(200, 9, &header, &nonce, &mutated).unwrap_err();
        }
    }
}
