//! Implementation of the Pedersen hash function used in Sapling.

#[cfg(test)]
pub(crate) mod test_vectors;

use alloc::vec::Vec;

use super::constants::PEDERSEN_HASH_CHUNKS_PER_GENERATOR;

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

/// Pedersen hash of `bits` under `personalization`.
///
/// The default implementation is the original 8-bit exp-window evaluation.
/// Enable the `fused-pedersen` feature to use fused chunk-block lookup tables
/// instead; both paths produce the same prime-order point.
///
/// # Panics
///
/// Panics if `personalization` is [`Personalization::MerkleTree`] with a depth
/// of 63 or greater, or if `bits` contains more than 1,128 items.
pub fn pedersen_hash<I>(personalization: Personalization, bits: I) -> jubjub::SubgroupPoint
where
    I: IntoIterator<Item = bool>,
{
    #[cfg(feature = "fused-pedersen")]
    {
        let mut buffer = [false; MAX_PEDERSEN_HASH_BITS];
        let len = collect_bounded_bits(bounded_bits(personalization, bits), &mut buffer);
        fused_pedersen_hash(&buffer[..len])
    }
    #[cfg(not(feature = "fused-pedersen"))]
    {
        windowed_pedersen_hash(bounded_bits(personalization, bits))
    }
}

/// Computes a Pedersen hash without converting the result back to a subgroup
/// point.
///
/// This lets internal callers extract coordinates directly or perform a single
/// subgroup conversion after adding another known prime-order point.
pub(crate) fn pedersen_hash_extended<I>(
    personalization: Personalization,
    bits: I,
) -> jubjub::ExtendedPoint
where
    I: IntoIterator<Item = bool>,
{
    #[cfg(feature = "fused-pedersen")]
    {
        let mut buffer = [false; MAX_PEDERSEN_HASH_BITS];
        let len = collect_bounded_bits(bounded_bits(personalization, bits), &mut buffer);
        fused_pedersen_hash_extended(&buffer[..len])
    }
    #[cfg(not(feature = "fused-pedersen"))]
    {
        jubjub::ExtendedPoint::from(windowed_pedersen_hash(bounded_bits(personalization, bits)))
    }
}

// The fixed six-generator input capacity, including personalization bits.
const MAX_PEDERSEN_HASH_BITS: usize =
    crate::constants::PEDERSEN_HASH_GENERATORS.len() * PEDERSEN_HASH_CHUNKS_PER_GENERATOR * 3;

// Limits both evaluators without forcing the default path to buffer its input.
fn bounded_bits<I>(personalization: Personalization, bits: I) -> impl Iterator<Item = bool>
where
    I: IntoIterator<Item = bool>,
{
    personalization
        .get_bits()
        .into_iter()
        .chain(bits)
        .enumerate()
        .map(|(index, bit)| {
            assert!(
                index < MAX_PEDERSEN_HASH_BITS,
                "we don't have enough Pedersen hash generators"
            );
            bit
        })
}

#[cfg(feature = "fused-pedersen")]
fn collect_bounded_bits<I>(bits: I, buffer: &mut [bool; MAX_PEDERSEN_HASH_BITS]) -> usize
where
    I: IntoIterator<Item = bool>,
{
    let mut len = 0;
    for bit in bits {
        buffer[len] = bit;
        len += 1;
    }
    len
}

#[cfg(not(feature = "fused-pedersen"))]
fn windowed_pedersen_hash<I>(bits: I) -> jubjub::SubgroupPoint
where
    I: Iterator<Item = bool>,
{
    use core::ops::{AddAssign, Neg};
    use ff::{Field, PrimeField};
    use group::Group;

    use super::constants::PEDERSEN_HASH_EXP_WINDOW_SIZE;

    let mut bits = bits;
    let mut result = jubjub::SubgroupPoint::identity();
    let mut generators = crate::constants::pedersen_hash_exp_table().iter();

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
                tmp = tmp.neg();
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

        let mut table: &[Vec<jubjub::SubgroupPoint>] =
            generators.next().expect("we don't have enough generators");
        let window = PEDERSEN_HASH_EXP_WINDOW_SIZE as usize;
        let window_mask = (1u64 << window) - 1;

        let acc = acc.to_repr();
        let num_limbs: usize = acc.as_ref().len() / 8;
        let mut limbs = vec![0u64; num_limbs + 1];
        for (src, dst) in acc
            .as_chunks::<8>()
            .0
            .iter()
            .zip(limbs[..num_limbs].iter_mut())
        {
            *dst = u64::from_le_bytes(*src);
        }

        let mut tmp = jubjub::SubgroupPoint::identity();

        let mut pos = 0;
        while pos < jubjub::Fr::NUM_BITS as usize {
            let u64_idx = pos / 64;
            let bit_idx = pos % 64;
            let i = (if bit_idx + window < 64 {
                limbs[u64_idx] >> bit_idx
            } else {
                (limbs[u64_idx] >> bit_idx) | (limbs[u64_idx + 1] << (64 - bit_idx))
            } & window_mask) as usize;

            tmp += table[0][i];

            pos += window;
            table = &table[1..];
        }

        result += tmp;
    }

    result
}

#[cfg(feature = "fused-pedersen")]
fn fused_pedersen_hash(bits: &[bool]) -> jubjub::SubgroupPoint {
    use group::cofactor::CofactorGroup;

    fused_pedersen_hash_scaled(bits).clear_cofactor()
}

#[cfg(feature = "fused-pedersen")]
fn fused_pedersen_hash_extended(bits: &[bool]) -> jubjub::ExtendedPoint {
    fused_pedersen_hash_scaled(bits).mul_by_cofactor()
}

// The tables are scaled by the inverse Jubjub cofactor. Multiplying their sum
// by the cofactor recovers the hash and constructs a subgroup point without a
// full torsion check.
#[cfg(feature = "fused-pedersen")]
fn fused_pedersen_hash_scaled(bits: &[bool]) -> jubjub::ExtendedPoint {
    // The final chunk is zero-padded, but chunks beyond the message are not
    // added.
    let bit = |i: usize| -> usize { usize::from(bits.get(i).copied().unwrap_or(false)) };

    let total_chunks = bits.len().div_ceil(3);

    let block_tables = &*PEDERSEN_HASH_BLOCK_TABLE;
    let single_tables = &*PEDERSEN_HASH_SINGLE_TABLE;

    // Accumulate the precomputed-addition points with fast mixed additions.
    let mut result = jubjub::ExtendedPoint::identity();

    // Walk the chunks segment by segment (one generator per segment of
    // `PEDERSEN_HASH_CHUNKS_PER_GENERATOR` chunks).
    let mut chunk = 0;
    let mut generator = 0;
    while chunk < total_chunks {
        let block_table = block_tables
            .get(generator)
            .expect("we don't have enough generators");
        let single_table = &single_tables[generator];

        let segment_end = core::cmp::min(chunk + PEDERSEN_HASH_CHUNKS_PER_GENERATOR, total_chunks);

        // `position` is the chunk index within this segment.
        let mut position = 0;

        // Fold each whole block with a single lookup.
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

        // Add chunks that do not fill a block one at a time.
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

// Number of 3-bit chunks folded into one table lookup. Larger values trade
// memory for fewer point additions.
#[cfg(feature = "fused-pedersen")]
const PEDERSEN_HASH_CHUNKS_PER_BLOCK: usize = 3;

#[cfg(feature = "fused-pedersen")]
lazy_static::lazy_static! {
    // `SINGLE[g][j][raw]` is `8^{-1} * enc * 2^{4j} * G_g`, where
    // `8^{-1}` is the inverse Jubjub cofactor in the scalar field.
    static ref PEDERSEN_HASH_SINGLE_TABLE:
        Vec<Vec<[jubjub::AffineNielsPoint; 8]>> =
            generate_pedersen_hash_single_table();

    // `BLOCK[g][b][raw]` sums one block's inverse-cofactor-scaled
    // single-table entries.
    static ref PEDERSEN_HASH_BLOCK_TABLE:
        Vec<Vec<Vec<jubjub::AffineNielsPoint>>> =
            generate_pedersen_hash_block_table();
}

#[cfg(feature = "fused-pedersen")]
fn pedersen_hash_single_extended() -> Vec<Vec<[jubjub::ExtendedPoint; 8]>> {
    let inverse_cofactor = jubjub::Fr::from(8u64).invert().unwrap();

    crate::constants::PEDERSEN_HASH_GENERATORS
        .iter()
        .map(|generator| {
            // `base` tracks `2^{4j} * G` as `j` advances.
            let mut base = jubjub::ExtendedPoint::from(*generator * inverse_cofactor);

            (0..PEDERSEN_HASH_CHUNKS_PER_GENERATOR)
                .map(|_| {
                    let double = base.double();
                    let triple = double + base;
                    let quad = double.double();

                    // Indexed by `a | b << 1 | c << 2`, with values +1 through
                    // +4 followed by -1 through -4.
                    let entries = [base, double, triple, quad, -base, -double, -triple, -quad];

                    base = quad.double().double();
                    entries
                })
                .collect()
        })
        .collect()
}

#[cfg(feature = "fused-pedersen")]
fn to_niels(mut points: Vec<jubjub::ExtendedPoint>) -> Vec<jubjub::AffineNielsPoint> {
    jubjub::batch_normalize(&mut points)
        .map(|affine| affine.to_niels())
        .collect()
}

#[cfg(feature = "fused-pedersen")]
fn generate_pedersen_hash_single_table() -> Vec<Vec<[jubjub::AffineNielsPoint; 8]>> {
    pedersen_hash_single_extended()
        .into_iter()
        .map(|generator| {
            // Batch-normalize all entries for this generator, then split them
            // back into per-position arrays.
            let flat: Vec<jubjub::ExtendedPoint> = generator.into_iter().flatten().collect();
            let niels = to_niels(flat);
            let (positions, remainder) = niels.as_chunks::<8>();
            assert!(remainder.is_empty(), "exactly 8 entries per position");
            positions.to_vec()
        })
        .collect()
}

#[cfg(feature = "fused-pedersen")]
fn generate_pedersen_hash_block_table() -> Vec<Vec<Vec<jubjub::AffineNielsPoint>>> {
    let blocks_per_generator = PEDERSEN_HASH_CHUNKS_PER_GENERATOR / PEDERSEN_HASH_CHUNKS_PER_BLOCK;
    let entries_per_block = 1usize << (3 * PEDERSEN_HASH_CHUNKS_PER_BLOCK);

    PEDERSEN_HASH_SINGLE_TABLE
        .iter()
        .map(|generator| {
            // Normalize each generator's block sums with one batched inversion.
            let sums: Vec<jubjub::ExtendedPoint> = (0..blocks_per_generator)
                .flat_map(|block| {
                    let first_chunk = block * PEDERSEN_HASH_CHUNKS_PER_BLOCK;
                    (0..entries_per_block).map(move |raw| {
                        let mut acc = jubjub::ExtendedPoint::identity();
                        for offset in 0..PEDERSEN_HASH_CHUNKS_PER_BLOCK {
                            let chunk_bits = (raw >> (3 * offset)) & 0b111;
                            acc += generator[first_chunk + offset][chunk_bits];
                        }
                        acc
                    })
                })
                .collect();
            to_niels(sums)
                .chunks_exact(entries_per_block)
                .map(<[_]>::to_vec)
                .collect()
        })
        .collect()
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

            let p = jubjub::ExtendedPoint::from(pedersen_hash(
                v.personalization,
                input_bools.into_iter().skip(6),
            ))
            .to_affine();

            assert_eq!(p.get_u().to_string(), v.hash_u);
            assert_eq!(p.get_v().to_string(), v.hash_v);
        }
    }

    /// Straightforward reference implementation that accumulates each
    /// segment's scalar and multiplies the generator directly.
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
        // Small inline xorshift PRNG; the fixed seed keeps the inputs
        // reproducible.
        let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut next_bit = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state & 1 == 1
        };

        // Cover sub-chunk and generator boundaries, Merkle hashes, and the
        // six-generator capacity. Personalization shifts each input boundary
        // by six bits.
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
                let expected = reference_pedersen_hash(personalization, &input);
                let public = jubjub::ExtendedPoint::from(pedersen_hash(
                    personalization,
                    input.iter().copied(),
                ));
                let internal = pedersen_hash_extended(personalization, input.iter().copied());
                assert!(
                    bool::from(internal.is_torsion_free()),
                    "torsion at input length {len}",
                );
                assert_eq!(
                    public, expected,
                    "public API mismatch at input length {len}",
                );
                assert_eq!(
                    internal, expected,
                    "internal path mismatch at input length {len}",
                );
            }
        }
    }

    #[test]
    #[should_panic(expected = "we don't have enough Pedersen hash generators")]
    fn rejects_one_bit_over_generator_capacity() {
        let max_input_bits =
            MAX_PEDERSEN_HASH_BITS - Personalization::NoteCommitment.get_bits().len();
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
