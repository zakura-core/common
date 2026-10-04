//! ZIP 316's reversible byte scrambling for Unified Addresses and viewing keys.
//!
//! Adapted from `f4jumble` 0.1.1 in `zcash/librustzcash`, commit
//! d660a771749cd7bb202560966458988b88ac65ed, `components/f4jumble`.
//! Copyright (c) 2021 Electric Coin Company. Licensed under MIT OR Apache-2.0;
//! see this crate's LICENSE-MIT and LICENSE-APACHE.

use alloc::vec::Vec;
use blake2b_simd::{OUTBYTES, Params as Blake2bParams};
use core::{cmp::min, fmt, ops::RangeInclusive};

#[cfg(test)]
mod test_vectors;
#[cfg(all(test, feature = "std"))]
mod test_vectors_long;
#[cfg(test)]
mod tests;

const VALID_LENGTH: RangeInclusive<usize> = 48..=4_194_368;
const H_PERSONALIZATION: [u8; 16] = *b"UA_F4Jumble_H\0\0\0";
const G_PERSONALIZATION: [u8; 16] = *b"UA_F4Jumble_G\0\0\0";
const ROUND_OFFSET: usize = 13;

#[derive(Debug)]
pub(super) enum Error {
    InvalidLength,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidLength => write!(
                f,
                "Message length must be in interval ({}..={})",
                *VALID_LENGTH.start(),
                *VALID_LENGTH.end()
            ),
        }
    }
}

fn h_personalization(round: u8) -> [u8; 16] {
    let mut personalization = H_PERSONALIZATION;
    personalization[ROUND_OFFSET] = round;
    personalization
}

fn g_personalization(round: u8, block: u16) -> [u8; 16] {
    let mut personalization = G_PERSONALIZATION;
    personalization[ROUND_OFFSET] = round;
    personalization[ROUND_OFFSET + 1..].copy_from_slice(&block.to_le_bytes());
    personalization
}

struct State<'a> {
    left: &'a mut [u8],
    right: &'a mut [u8],
}

impl<'a> State<'a> {
    fn new(message: &'a mut [u8]) -> Self {
        let left_length = min(OUTBYTES, message.len() / 2);
        let (left, right) = message.split_at_mut(left_length);
        State { left, right }
    }

    fn h_round(&mut self, round: u8) {
        let hash = Blake2bParams::new()
            .hash_length(self.left.len())
            .personal(&h_personalization(round))
            .hash(self.right);
        xor(self.left, hash.as_bytes());
    }

    fn g_round(&mut self, round: u8) {
        for (block, chunk) in self.right.chunks_mut(OUTBYTES).enumerate() {
            let block = u16::try_from(block)
                .expect("validated message length limits the block index to u16");
            let hash = Blake2bParams::new()
                .hash_length(OUTBYTES)
                .personal(&g_personalization(round, block))
                .hash(self.left);
            xor(chunk, hash.as_bytes());
        }
    }

    fn apply_f4jumble(&mut self) {
        self.g_round(0);
        self.h_round(0);
        self.g_round(1);
        self.h_round(1);
    }

    fn apply_f4jumble_inv(&mut self) {
        self.h_round(1);
        self.g_round(1);
        self.h_round(0);
        self.g_round(0);
    }
}

fn xor(target: &mut [u8], source: &[u8]) {
    for (source, target) in source.iter().zip(target.iter_mut()) {
        *target ^= source;
    }
}

/// Encodes a message, preserving the upstream length checks and error text.
pub(super) fn f4jumble(message: &[u8]) -> Result<Vec<u8>, Error> {
    let mut result = message.to_vec();
    f4jumble_mut(&mut result).map(|()| result)
}

/// Encodes a message in place, leaving invalid inputs unmodified.
fn f4jumble_mut(message: &mut [u8]) -> Result<(), Error> {
    if VALID_LENGTH.contains(&message.len()) {
        State::new(message).apply_f4jumble();
        Ok(())
    } else {
        Err(Error::InvalidLength)
    }
}

/// Decodes a message in place, leaving invalid inputs unmodified.
pub(super) fn f4jumble_inv_mut(message: &mut [u8]) -> Result<(), Error> {
    if VALID_LENGTH.contains(&message.len()) {
        State::new(message).apply_f4jumble_inv();
        Ok(())
    } else {
        Err(Error::InvalidLength)
    }
}
