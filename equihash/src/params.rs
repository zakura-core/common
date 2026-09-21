#[derive(Clone, Copy)]
pub(crate) struct Params {
    pub(crate) n: u32,
    pub(crate) k: u32,
}

impl Params {
    /// Returns `None` if the parameters are invalid.
    pub(crate) fn new(n: u32, k: u32) -> Option<Self> {
        // We place the following requirements on the parameters:
        // - n is a multiple of 8, so the hash output has an exact byte length.
        // - k >= 3 so the encoded solutions have an exact byte length.
        // - k < n, so the collision bit length is at least 1.
        // - n is a multiple of k + 1, so we have an integer collision bit length.
        if n > 512 || !n.is_multiple_of(8) || k < 3 || k >= n || !n.is_multiple_of(k + 1) {
            return None;
        }

        let params = Params { n, k };
        let collision_bits = params.collision_bit_length();
        // Hash expansion requires at least 8 bits. Index expansion adds one bit
        // and requires at most 25 bits for its 32-bit accumulator.
        if !(8..=24).contains(&collision_bits) {
            return None;
        }

        let indices = 1usize.checked_shl(k)?;
        let encoded_len = indices.checked_mul(collision_bits + 1)? / 8;
        // Both decoding paths multiply the encoded length by 32 before division.
        // This bound also covers the expanded bytes and the current index-vector
        // reservation, whose allocation sizes must fit in isize.
        if encoded_len.checked_mul(32)? > isize::MAX as usize {
            return None;
        }

        Some(params)
    }

    pub(crate) fn indices_per_hash_output(&self) -> u32 {
        512 / self.n
    }
    pub(crate) fn hash_output(&self) -> u8 {
        (self.indices_per_hash_output() * self.n / 8) as u8
    }
    pub(crate) fn collision_bit_length(&self) -> usize {
        (self.n / (self.k + 1)) as usize
    }
    pub(crate) fn collision_byte_length(&self) -> usize {
        self.collision_bit_length().div_ceil(8)
    }
    #[cfg(test)]
    pub(crate) fn hash_length(&self) -> usize {
        ((self.k as usize) + 1) * self.collision_byte_length()
    }
}

#[cfg(test)]
mod tests {
    use super::Params;

    #[test]
    fn supported_consensus_parameters() {
        assert!(Params::new(48, 5).is_some());
        assert!(Params::new(200, 9).is_some());
    }

    #[test]
    fn decoder_size_limits() {
        // With eight collision bits, k determines every decoder buffer size.
        // Exercise the target's allocation bound without allocating those buffers.
        let k = usize::BITS - 7;
        assert!(Params::new(8 * (k + 1), k).is_some());
        let k = usize::BITS - 6;
        assert!(Params::new(8 * (k + 1), k).is_none());
        let k = usize::BITS - 1;
        assert!(Params::new(8 * (k + 1), k).is_none());
    }
}
