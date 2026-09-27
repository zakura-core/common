// Copyright (c) 2020-2022 The Zcash developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or https://www.opensource.org/licenses/mit-license.php .

// Rust BLAKE2b callbacks used by the C Tromp solver.
#![allow(unsafe_code)]

use blake2b_simd::{PERSONALBYTES, State};

use std::boxed::Box;
use std::ptr;
use std::slice;

use crate::params::Params;

#[cfg(target_arch = "x86_64")]
mod native;

/// Owns the reference state and an optional cache for solver hash batches.
#[derive(Clone)]
pub(super) struct SolverHashState {
    reference: State,
    #[cfg(target_arch = "x86_64")]
    native: Option<native::Context>,
}

impl SolverHashState {
    /// The owned state must already include `input` and `nonce` with `params`.
    pub(super) fn new(reference: State, input: &[u8], nonce: &[u8], params: Params) -> Self {
        #[cfg(not(target_arch = "x86_64"))]
        let _ = (input, nonce, params);
        Self {
            reference,
            #[cfg(target_arch = "x86_64")]
            native: native::Context::new(
                input,
                nonce,
                params.n,
                params.k,
                params.hash_output() as usize,
            ),
        }
    }
}

#[unsafe(no_mangle)]
extern "C" fn blake2b_init(
    output_len: usize,
    personalization: *const [u8; PERSONALBYTES],
) -> *mut SolverHashState {
    let personalization = unsafe { personalization.as_ref().unwrap() };

    Box::into_raw(Box::new(SolverHashState {
        reference: blake2b_simd::Params::new()
            .hash_length(output_len)
            .personal(personalization)
            .to_state(),
        #[cfg(target_arch = "x86_64")]
        native: None,
    }))
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn blake2b_clone(state: *const SolverHashState) -> *mut SolverHashState {
    unsafe { state.as_ref() }
        .map(|state| Box::into_raw(Box::new(state.clone())))
        .unwrap_or(ptr::null_mut())
}

#[unsafe(no_mangle)]
pub(super) extern "C" fn blake2b_free(state: *mut SolverHashState) {
    if !state.is_null() {
        drop(unsafe { Box::from_raw(state) });
    }
}

/// Generates hashes for consecutive Equihash block indices.
/// Uses cached SIMD compression where available, or stack clones of [`State`].
///
/// # Safety
///
/// `state` must point to a valid, aligned [`SolverHashState`] and remain unmodified
/// for the duration of this call.
/// `output` must point to a writable allocation of `count * hash_len` bytes
/// that does not overlap `state`. This length must fit in [`isize`],
/// `hash_len` must match the state's digest length, and the last block index
/// must fit in [`u32`].
pub(super) unsafe extern "C" fn blake2b_generate_hashes(
    state: *const SolverHashState,
    first_index: u32,
    count: u32,
    output: *mut u8,
    hash_len: usize,
) {
    // SAFETY: the C caller supplies a live state and a disjoint output buffer
    // with enough space for every digest in this batch.
    let state = unsafe { &*state };
    let output = unsafe { slice::from_raw_parts_mut(output, count as usize * hash_len) };
    #[cfg(target_arch = "x86_64")]
    if let Some(native) = &state.native {
        native.generate(first_index, output);
        return;
    }
    for (offset, output) in output.chunks_exact_mut(hash_len).enumerate() {
        let mut hash_state = state.reference.clone();
        hash_state.update(&(first_index + offset as u32).to_le_bytes());
        output.copy_from_slice(hash_state.finalize().as_bytes());
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use super::{SolverHashState, blake2b_generate_hashes};
    use crate::params::Params;
    use crate::verify::initialise_state;

    #[test]
    fn generated_hashes_match_reference() {
        let hash_len = 50;
        let mut state = initialise_state(200, 9, hash_len);
        let header: Vec<_> = (0..108).map(|i| i as u8).collect();
        state.update(&header);
        state.update(&[0x5a; 32]);
        let original_digest = state.finalize();
        let states = [
            SolverHashState {
                reference: state.clone(),
                #[cfg(target_arch = "x86_64")]
                native: None,
            },
            SolverHashState::new(state, &header, &[0x5a; 32], Params { n: 200, k: 9 }),
        ];

        // Include a batch spanning more than one C-side buffer and an empty
        // batch. Guard bytes check that the callback respects the buffer size.
        for state in states {
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
                assert_eq!(state.reference.finalize(), original_digest);
                assert_eq!(
                    hex::encode(blake2b_simd::blake2b(&output[1..output.len() - 1]).as_bytes()),
                    expected,
                );
            }
        }
    }

    #[test]
    fn boundary_prefixes_match_reference() {
        let params = Params { n: 200, k: 9 };
        for prefix_len in [124, 125, 126, 127, 128, 2048, 2049] {
            let prefix: Vec<_> = (0..prefix_len).map(|i| (i * 197) as u8).collect();
            let split = prefix_len / 2;
            let mut reference = initialise_state(params.n, params.k, params.hash_output());
            reference.update(&prefix);
            let state = SolverHashState::new(
                reference.clone(),
                &prefix[..split],
                &prefix[split..],
                params,
            );
            let mut output = vec![0; 7 * params.hash_output() as usize];
            // SAFETY: both objects are live, the output is disjoint and sized
            // for seven digests, and these consecutive indices fit in u32.
            unsafe {
                blake2b_generate_hashes(
                    &state,
                    65534,
                    7,
                    output.as_mut_ptr(),
                    params.hash_output() as usize,
                );
            }
            for (offset, digest) in output
                .chunks_exact(params.hash_output() as usize)
                .enumerate()
            {
                let mut expected = reference.clone();
                expected.update(&(65534 + offset as u32).to_le_bytes());
                assert_eq!(digest, expected.finalize().as_bytes());
            }
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
