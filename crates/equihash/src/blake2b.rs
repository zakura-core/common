// Copyright (c) 2020-2022 The Zcash developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or https://www.opensource.org/licenses/mit-license.php .

// Rust BLAKE2b callbacks used by the C Tromp solver.
#![allow(unsafe_code)]

use blake2b_simd::{PERSONALBYTES, State};

use std::boxed::Box;
use std::ptr;
use std::slice;

#[unsafe(no_mangle)]
extern "C" fn blake2b_init(
    output_len: usize,
    personalization: *const [u8; PERSONALBYTES],
) -> *mut State {
    let personalization = unsafe { personalization.as_ref().unwrap() };

    Box::into_raw(Box::new(
        blake2b_simd::Params::new()
            .hash_length(output_len)
            .personal(personalization)
            .to_state(),
    ))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn blake2b_clone(state: *const State) -> *mut State {
    unsafe { state.as_ref() }
        .map(|state| Box::into_raw(Box::new(state.clone())))
        .unwrap_or(ptr::null_mut())
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn blake2b_free(state: *mut State) {
    if !state.is_null() {
        drop(unsafe { Box::from_raw(state) });
    }
}

/// Generates hashes for consecutive Equihash block indices using [`State`].
/// Each hash starts from a stack clone of the same prehashed header and nonce.
///
/// # Safety
///
/// `state` must point to a valid, aligned [`State`] and remain unmodified
/// for the duration of this call.
/// `output` must point to a writable allocation of `count * hash_len` bytes
/// that does not overlap `state`. This length must fit in [`isize`],
/// `hash_len` must match the state's digest length, and the last block index
/// must fit in [`u32`].
pub(super) unsafe extern "C" fn blake2b_generate_hashes(
    state: *const State,
    first_index: u32,
    count: u32,
    output: *mut u8,
    hash_len: usize,
) {
    // SAFETY: the C caller supplies a live state and a disjoint output buffer
    // with enough space for every digest in this batch.
    let state = unsafe { &*state };
    let output = unsafe { slice::from_raw_parts_mut(output, count as usize * hash_len) };
    for (offset, output) in output.chunks_exact_mut(hash_len).enumerate() {
        let mut hash_state = state.clone();
        hash_state.update(&(first_index + offset as u32).to_le_bytes());
        output.copy_from_slice(hash_state.finalize().as_bytes());
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use super::blake2b_generate_hashes;
    use crate::verify::initialise_state;

    #[test]
    fn generated_hashes_match_reference() {
        let hash_len = 50;
        let mut state = initialise_state(200, 9, hash_len);
        let header: Vec<_> = (0..108).map(|i| i as u8).collect();
        state.update(&header);
        state.update(&[0x5a; 32]);
        let original_digest = state.finalize();

        // Include a batch spanning more than one C-side buffer and an empty
        // batch. Guard bytes check that the callback respects the buffer size.
        for (first_index, count, expected) in REFERENCE_BATCHES {
            let mut output = vec![0xa5; count as usize * hash_len as usize + 2];
            // SAFETY: the state is live, the output has exactly enough space
            // between its guards, and all reference indices fit in u32.
            unsafe {
                blake2b_generate_hashes(
                    &state,
                    first_index,
                    count,
                    output[1..].as_mut_ptr(),
                    hash_len as usize,
                );
            }
            assert_eq!(output[0], 0xa5);
            assert_eq!(*output.last().unwrap(), 0xa5);
            assert_eq!(state.finalize(), original_digest);
            assert_eq!(
                hex::encode(blake2b_simd::blake2b(&output[1..output.len() - 1]).as_bytes()),
                expected,
            );
        }
    }

    // Computed independently with Python hashlib.blake2b: each personalized
    // 50-byte digest hashes header || nonce || little-endian block index;
    // expected is the unpersonalized BLAKE2b-512 of all concatenated digests.
    const REFERENCE_BATCHES: [(u32, u32, &str); 4] = [
        (
            0,
            0,
            "786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419d25e1031afee585313896444934eb04b903a685b1448b755d56f701afe9be2ce",
        ),
        (
            0,
            1,
            "d9357728d3b5b2def8d93d65f5f1e2abc0c3f750f938420cafaf33cc52bb02085b4d59b86e053253f919926e255c3b31a3dce8b05aa16eb9eead70958ec260ee",
        ),
        (
            63,
            67,
            "1e1404082f43cb2f355e29e8c8380ed61d241dba4b97dac5449104e7965d91c6bfbec08b65c05d9f829ff873f24220b11849b130129822453452d98d6d1e930f",
        ),
        (
            4294967293,
            3,
            "98e65ac93b4fc20b2f5cdc3ee39220a6762fc565bbf2568f06d75c9e2ef759f8e1e12b51c758a1844c54efde55a131f6468340c2708556e8dbcbc74b945c98a7",
        ),
    ];
}
