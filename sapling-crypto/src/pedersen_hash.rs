//! Implementation of the Pedersen hash function used in Sapling.

#[cfg(test)]
pub(crate) mod test_vectors;

use alloc::vec::Vec;

use super::constants::{PEDERSEN_HASH_CHUNKS_PER_BLOCK, PEDERSEN_HASH_CHUNKS_PER_GENERATOR};

#[derive(Copy, Clone)]
pub enum Personalization {
    NoteCommitment,
    MerkleTree(usize),
}

impl Personalization {
    pub fn get_bits(&self) -> Vec<bool> {
        match *self {
            Personalization::NoteCommitment => vec![true, true, true, true, true, true],
            Personalization::MerkleTree(num) => {
                assert!(num < 63);

                (0..6).map(|i| (num >> i) & 1 == 1).collect()
            }
        }
    }
}

pub fn pedersen_hash<I>(personalization: Personalization, bits: I) -> jubjub::ExtendedPoint
where
    I: IntoIterator<Item = bool>,
{
    // Buffer the bit stream so we know the exact chunk count up front, but stop after the fixed
    // generator capacity. This keeps oversized or infinite public-API inputs from causing
    // unbounded allocation. The trailing bits of the final chunk are zero-padded (matching
    // Sapling's definition), but chunks beyond the message must never be added.
    let max_bits =
        crate::constants::PEDERSEN_HASH_GENERATORS.len() * PEDERSEN_HASH_CHUNKS_PER_GENERATOR * 3;
    let bits: Vec<bool> = personalization
        .get_bits()
        .into_iter()
        .chain(bits)
        .take(max_bits + 1)
        .collect();
    assert!(
        bits.len() <= max_bits,
        "we don't have enough Pedersen hash generators"
    );
    let bit = |i: usize| -> usize { usize::from(bits.get(i).copied().unwrap_or(false)) };

    // Number of 3-bit chunks, rounding up (the final chunk is zero-padded).
    let total_chunks = bits.len().div_ceil(3);

    let block_tables = &*crate::constants::PEDERSEN_HASH_BLOCK_TABLE;
    let single_tables = &*crate::constants::PEDERSEN_HASH_SINGLE_TABLE;

    // The table entries are precomputed-addition (Niels) points; accumulate into an extended
    // point via fast mixed additions.
    let mut result = jubjub::ExtendedPoint::identity();

    // Walk the chunks segment by segment (one generator per segment of
    // `PEDERSEN_HASH_CHUNKS_PER_GENERATOR` chunks), accumulating each chunk's precomputed
    // contribution `enc(chunk) * 2^{4j} * G`.
    let mut chunk = 0;
    let mut generator = 0;
    while chunk < total_chunks {
        let block_table = block_tables
            .get(generator)
            .expect("we don't have enough generators");
        let single_table = &single_tables[generator];

        let segment_end = core::cmp::min(chunk + PEDERSEN_HASH_CHUNKS_PER_GENERATOR, total_chunks);

        // `position` is the chunk's index within this segment, used to weight by 2^{4*position}.
        let mut position = 0;

        // Fold whole blocks of `PEDERSEN_HASH_CHUNKS_PER_BLOCK` chunks with a single lookup.
        while segment_end - chunk >= PEDERSEN_HASH_CHUNKS_PER_BLOCK {
            let mut raw = 0;
            for k in 0..PEDERSEN_HASH_CHUNKS_PER_BLOCK {
                let base = 3 * (chunk + k);
                raw |= (bit(base) | (bit(base + 1) << 1) | (bit(base + 2) << 2)) << (3 * k);
            }
            result += block_table[position / PEDERSEN_HASH_CHUNKS_PER_BLOCK][raw];

            chunk += PEDERSEN_HASH_CHUNKS_PER_BLOCK;
            position += PEDERSEN_HASH_CHUNKS_PER_BLOCK;
        }

        // Any chunks that do not fill a block (the tail of the final segment) are added singly.
        while chunk < segment_end {
            let base = 3 * chunk;
            let raw = bit(base) | (bit(base + 1) << 1) | (bit(base + 2) << 2);
            result += single_table[position][raw];

            chunk += 1;
            position += 1;
        }

        generator += 1;
    }

    result
}

#[cfg(test)]
pub mod test {
    use alloc::string::ToString;
    use group::Curve;

    use super::*;

    pub struct TestVector<'a> {
        pub personalization: Personalization,
        pub input_bits: Vec<u8>,
        pub hash_u: &'a str,
        pub hash_v: &'a str,
    }

    #[test]
    fn test_pedersen_hash_points() {
        let test_vectors = test_vectors::get_vectors();

        assert!(!test_vectors.is_empty());

        for v in test_vectors.iter() {
            let input_bools: Vec<bool> = v.input_bits.iter().map(|&i| i == 1).collect();

            // The 6 bits prefix is handled separately
            assert_eq!(v.personalization.get_bits(), &input_bools[..6]);

            let p = pedersen_hash(v.personalization, input_bools.into_iter().skip(6)).to_affine();

            assert_eq!(p.get_u().to_string(), v.hash_u);
            assert_eq!(p.get_v().to_string(), v.hash_v);
        }
    }

    /// Straightforward reference implementation: accumulate each segment's scalar and multiply
    /// the segment generator directly. The optimized [`pedersen_hash`] must match this exactly.
    fn reference_pedersen_hash(
        personalization: Personalization,
        input: &[bool],
    ) -> jubjub::ExtendedPoint {
        use core::ops::AddAssign;
        use ff::Field;

        let mut bits = personalization
            .get_bits()
            .into_iter()
            .chain(input.iter().copied());
        let mut result = jubjub::ExtendedPoint::identity();
        let mut generators = crate::constants::PEDERSEN_HASH_GENERATORS.iter();

        loop {
            let mut acc = jubjub::Fr::ZERO;
            let mut cur = jubjub::Fr::ONE;
            let mut chunks_remaining = PEDERSEN_HASH_CHUNKS_PER_GENERATOR;
            let mut encountered_bits = false;

            while let Some(a) = bits.next() {
                encountered_bits = true;
                let b = bits.next().unwrap_or(false);
                let c = bits.next().unwrap_or(false);

                let mut tmp = cur;
                if a {
                    tmp.add_assign(&cur);
                }
                cur = cur.double();
                if b {
                    tmp.add_assign(&cur);
                }
                if c {
                    tmp = -tmp;
                }
                acc.add_assign(&tmp);

                chunks_remaining -= 1;
                if chunks_remaining == 0 {
                    break;
                } else {
                    cur = cur.double().double().double();
                }
            }

            if !encountered_bits {
                break;
            }

            let g = generators.next().expect("we don't have enough generators");
            result += g * acc;
        }

        result
    }

    #[test]
    fn matches_reference_across_boundaries() {
        // Deterministic xorshift PRNG so the test needs no rng dependency.
        let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut next_bit = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state & 1 == 1
        };

        // Cover empty input, sub-chunk lengths, exact chunk/generator boundaries (a generator is
        // 63 chunks = 189 bits; the 6 prepended personalization bits shift the boundaries), the
        // merkle-hash size (510 input bits), and multi-generator inputs up to capacity (six
        // generators hold 1134 bits total, so at most 1128 input bits after personalization).
        let lengths = [
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 180, 181, 182, 183, 184, 185, 186, 369, 370, 371, 372,
            373, 374, 510, 516, 564, 1125, 1126, 1127, 1128,
        ];

        for personalization in [
            Personalization::NoteCommitment,
            Personalization::MerkleTree(31),
        ] {
            for &len in &lengths {
                let input: Vec<bool> = (0..len).map(|_| next_bit()).collect();
                assert_eq!(
                    pedersen_hash(personalization, input.iter().copied()),
                    reference_pedersen_hash(personalization, &input),
                    "mismatch at input length {len}",
                );
            }
        }
    }

    #[test]
    #[should_panic(expected = "we don't have enough Pedersen hash generators")]
    fn rejects_one_bit_over_generator_capacity() {
        let max_input_bits = crate::constants::PEDERSEN_HASH_GENERATORS.len()
            * PEDERSEN_HASH_CHUNKS_PER_GENERATOR
            * 3
            - Personalization::NoteCommitment.get_bits().len();
        pedersen_hash(
            Personalization::NoteCommitment,
            core::iter::repeat_n(true, max_input_bits + 1),
        );
    }

    #[test]
    #[should_panic(expected = "we don't have enough Pedersen hash generators")]
    fn rejects_infinite_input_at_generator_capacity() {
        pedersen_hash(Personalization::NoteCommitment, core::iter::repeat(true));
    }
}
