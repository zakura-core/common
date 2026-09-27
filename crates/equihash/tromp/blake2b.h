// Copyright (c) 2020-2022 The Zcash developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or https://www.opensource.org/licenses/mit-license.php .

#ifndef ZCASH_RUST_INCLUDE_RUST_BLAKE2B_H
#define ZCASH_RUST_INCLUDE_RUST_BLAKE2B_H

#include <stddef.h>
#include <stdint.h>

struct BLAKE2bState;
typedef struct BLAKE2bState BLAKE2bState;
#define BLAKE2bPersonalBytes 16U

/// Initializes a BLAKE2b state with no key and no salt.
///
/// `personalization` MUST be a pointer to a 16-byte array.
///
/// Please free this with `blake2b_free` when you are done.
typedef BLAKE2bState* (*blake2b_init)(
    size_t output_len,
    const unsigned char* personalization);

/// Clones the given BLAKE2b state.
///
/// Both states need to be separately freed with `blake2b_free` when you are
/// done.
typedef BLAKE2bState* (*blake2b_clone)(const BLAKE2bState* state);

/// Frees a BLAKE2b state returned by `blake2b_init`.
typedef void (*blake2b_free)(BLAKE2bState* state);

/// Generates consecutive block-index hashes from a prehashed header and nonce.
///
/// `state` is borrowed and must remain live throughout the call. `output`
/// must have room for `count * hash_len` bytes and must not overlap `state`.
/// `hash_len` must match the state's digest length and the last index must
/// fit in uint32_t.
typedef void (*blake2b_generate_hashes)(
    const BLAKE2bState* state,
    uint32_t first_index,
    uint32_t count,
    unsigned char* output,
    size_t hash_len);

#endif // ZCASH_RUST_INCLUDE_RUST_BLAKE2B_H
