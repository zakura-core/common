//! Word and running-sum checks with independent byte-encoding references.

use crate::native::test_support::reduced_values;

use crate::{
    Error,
    native::field::{Fp, Fq},
};

use super::super::decomposition::{
    decompose_words, running_sum, words_with_running_sums, write_running_sum,
};
use super::super::fixed_base::scalar_windows;
use super::super::variable_base::{scalar_to_k, variable_base_bits};
use super::super::{RowMap, WitnessWriter, bitrange};

fn encoded_bit(bytes: &[u8; 32], index: usize) -> bool {
    bytes[index / 8] & (1 << (index % 8)) != 0
}

fn encoded_window(bytes: &[u8; 32], offset: usize, width: usize) -> u64 {
    (0..width).fold(0, |value, index| {
        value | (u64::from(encoded_bit(bytes, offset + index)) << index)
    })
}

fn encoded_bitrange(bytes: &[u8; 32], offset: usize, width: usize) -> [u8; 32] {
    let mut result = [0; 32];
    for index in 0..width {
        if encoded_bit(bytes, offset + index) {
            result[index / 8] |= 1 << (index % 8);
        }
    }
    result
}

fn encoded_add_u128(bytes: [u8; 32], increment: u128) -> [u8; 32] {
    let mut limbs: [u64; 4] = core::array::from_fn(|index| {
        u64::from_le_bytes(bytes[index * 8..(index + 1) * 8].try_into().unwrap())
    });
    let low = u128::from(limbs[0]) + (increment & u128::from(u64::MAX));
    limbs[0] = low as u64;
    let high = u128::from(limbs[1]) + (increment >> 64) + (low >> 64);
    limbs[1] = high as u64;
    let mut carry = high >> 64;
    for limb in &mut limbs[2..] {
        let value = u128::from(*limb) + carry;
        *limb = value as u64;
        carry = value >> 64;
    }
    assert_eq!(carry, 0);

    let mut result = [0; 32];
    for (chunk, limb) in result.chunks_exact_mut(8).zip(limbs) {
        chunk.copy_from_slice(&limb.to_le_bytes());
    }
    result
}

#[test]
fn fixed_running_sum_uses_little_endian_words_and_enforces_strictness() {
    let value =
        <Fp>::from_bytes_reduced(&[0x21, 0x43, 0x65, 0x87, 0xa9, 0xcb, 0xed, 0x0f, 0x11, 0x22]);
    let sums = running_sum(&value, 10, 8).unwrap();
    assert_eq!(sums.len(), 9);
    let encoded = value.to_bytes();
    for (index, sum) in sums.iter().enumerate() {
        assert_eq!(
            (sum).reduce(),
            <Fp>::from_bytes_reduced(&encoded_bitrange(&encoded, index * 10, 256 - index * 10,))
                .reduce()
        );
    }

    // Column 9, region 297: two ten-bit words, requiring a zero final sum.
    let mut writer = WitnessWriter::with_shadow();
    write_running_sum(
        &mut writer,
        RowMap::load(),
        9,
        297,
        &<Fp>::from_u64((1 << 20) - 1),
        10,
        2,
        true,
    )
    .unwrap();
    let matrix = writer.finish().unwrap().into_matrix().unwrap();
    assert_eq!(
        (matrix.columns()[9][0]).reduce(),
        (<Fp>::from_u64((1 << 20) - 1)).reduce()
    );
    assert_eq!(
        (matrix.columns()[9][1]).reduce(),
        (<Fp>::from_u64((1 << 10) - 1)).reduce()
    );
    assert_eq!((matrix.columns()[9][2]).reduce(), (<Fp>::ZERO).reduce());

    // The same strict two-word layout rejects a nonzero final remainder.
    let mut non_strict = WitnessWriter::with_shadow();
    assert_eq!(
        write_running_sum(
            &mut non_strict,
            RowMap::load(),
            9,
            297,
            &<Fp>::from_u64(1 << 20),
            10,
            2,
            true,
        ),
        Err(Error::UnsatisfiedWitness)
    );
}

#[test]
fn fixed_limb_witness_decomposition_matches_encoded_reference() {
    let values = [
        <Fp>::ZERO,
        <Fp>::ONE,
        <Fp>::from_u64(u64::MAX),
        <Fp>::from_bytes_reduced(&[
            0x13, 0x57, 0x9b, 0xdf, 0x24, 0x68, 0xac, 0xe0, 0xff, 0xee, 0xdd, 0xcc, 0xbb, 0xaa,
            0x99, 0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11,
        ]),
        <Fp>::ONE.neg(),
    ];

    for value in values {
        let encoded = value.to_bytes();
        for (start, end) in [
            (0, 1),
            (0, 250),
            (4, 254),
            (63, 127),
            (127, 255),
            (254, 255),
        ] {
            assert_eq!(
                (bitrange(&value, start, end).unwrap()).reduce(),
                (<Fp>::from_bytes_reduced(&encoded_bitrange(&encoded, start, end - start)))
                    .reduce()
            );
        }

        let words = decompose_words(&value, 25).unwrap();
        let windows = scalar_windows::<85>(value.to_canonical_uint()).unwrap();
        for (index, word) in words.iter().enumerate() {
            let expected = encoded_window(&encoded, index * 10, 10);
            assert_eq!(*word as u64, expected);
        }
        for (index, window) in windows.iter().enumerate() {
            let expected = encoded_window(&encoded, index * 3, 3);
            assert_eq!(*window as u64, expected);
        }

        // The fused single-pass decomposition matches the single-view
        // reference helpers word-for-word and sum-for-sum.
        let (fused_words, fused_sums) = words_with_running_sums(&value, 10, 25).unwrap();
        assert_eq!(fused_words, words);
        assert_eq!(
            reduced_values(&(fused_sums)),
            reduced_values(&(running_sum(&value, 10, 25).unwrap()))
        );
        let (fused_windows, fused_window_sums) = words_with_running_sums(&value, 3, 85).unwrap();
        assert_eq!(fused_windows, windows);
        assert_eq!(
            reduced_values(&(fused_window_sums)),
            reduced_values(&(running_sum(&value, 3, 85).unwrap()))
        );
    }

    assert!(decompose_words(&<Fp>::ONE, 0).is_err());
    assert!(scalar_windows::<0>(<Fp>::ONE.to_canonical_uint()).is_err());
    assert!(words_with_running_sums(&<Fp>::ONE, 10, 0).is_err());
    assert!(words_with_running_sums(&<Fp>::ONE, 0, 25).is_err());
    assert!(words_with_running_sums(&<Fp>::ONE, 10, 26).is_err());

    for scalar in [
        <Fq>::ZERO,
        <Fq>::ONE,
        <Fq>::from_u64(u64::MAX),
        <Fq>::ONE.neg(),
    ] {
        let encoded = encoded_add_u128(scalar.to_bytes(), super::super::T_Q);
        let k = scalar_to_k(&scalar).unwrap();
        let bits = variable_base_bits(k).unwrap();
        assert_eq!(bits.len(), 255);
        for bit in 0..255 {
            let expected = encoded_bit(&encoded, bit);
            assert_eq!(k.bit(bit), Some(expected));
            assert_eq!(bits[254 - bit], expected);
        }
    }
}
