//! Implementation of Sinsemilla outside the circuit.

#![no_std]

// We require `alloc` for now.
#[macro_use]
extern crate alloc;

use alloc::vec::Vec;
use group::{Curve, Wnaf};
use lazy_static::lazy_static;
use pasta_curves::{
    arithmetic::{CurveAffine, CurveExt},
    pallas,
};
use subtle::CtOption;

mod addition;
use self::addition::IncompletePoint;
mod sinsemilla_s;
pub use sinsemilla_s::SINSEMILLA_S;
pub mod weighted;

lazy_static! {
    static ref SINSEMILLA_S_AFFINE: Vec<pallas::Affine> = SINSEMILLA_S
        .iter()
        .map(|(x, y)| pallas::Affine::from_xy(*x, *y).unwrap())
        .collect();
}

/// Number of bits of each message piece in $\mathsf{SinsemillaHashToPoint}$
pub const K: usize = 10;

/// $\frac{1}{2^K}$
pub const INV_TWO_POW_K: [u8; 32] = [
    1, 0, 192, 196, 160, 229, 70, 82, 221, 165, 74, 202, 85, 7, 62, 34, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 240, 63,
];

/// The largest integer such that $2^c \leq (r_P - 1) / 2$, where $r_P$ is the order
/// of Pallas.
pub const C: usize = 253;

// Sinsemilla Q generators

/// SWU hash-to-curve personalization for Sinsemilla $Q$ generators.
pub const Q_PERSONALIZATION: &str = "z.cash:SinsemillaQ";

// Sinsemilla S generators

/// SWU hash-to-curve personalization for Sinsemilla $S$ generators.
pub const S_PERSONALIZATION: &str = "z.cash:SinsemillaS";

/// Converts a little-endian [`K`]-bit string into an integer.
pub fn lebs2ip_k(bits: [bool; K]) -> u32 {
    bits.iter()
        .enumerate()
        .fold(0u32, |acc, (i, b)| acc + if *b { 1 << i } else { 0 })
}

/// Coordinate extractor for Pallas.
///
/// Defined in [Zcash Protocol Spec § 5.4.9.7: Coordinate Extractor for Pallas][concreteextractorpallas].
///
/// [concreteextractorpallas]: https://zips.z.cash/protocol/nu5.pdf#concreteextractorpallas
fn extract_p_bottom(point: CtOption<pallas::Point>) -> CtOption<pallas::Base> {
    point.map(|p| {
        p.to_affine()
            .coordinates()
            .map(|c| *c.x())
            .unwrap_or_else(pallas::Base::zero)
    })
}

/// Pads the given iterator (which MUST have length $\leq K * C$) with zero-bits
/// to a multiple of $K$ bits.
struct Pad<I: Iterator<Item = bool>> {
    /// The iterator we are padding.
    inner: I,
    /// The measured length of the inner iterator.
    ///
    /// This starts as a lower bound, and will be accurate once
    /// `padding_left.is_some()`.
    len: usize,
    /// The amount of padding that remains to be emitted.
    padding_left: Option<usize>,
}

impl<I: Iterator<Item = bool>> Pad<I> {
    fn new(inner: I) -> Self {
        Pad {
            inner,
            len: 0,
            padding_left: None,
        }
    }
}

impl<I: Iterator<Item = bool>> Iterator for Pad<I> {
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // If we have identified the required padding, the inner iterator
            // has ended, and we will never poll it again.
            if let Some(n) = self.padding_left.as_mut() {
                if *n == 0 {
                    // Either we already emitted all necessary padding, or there
                    // was no padding required.
                    break None;
                } else {
                    // Emit the next padding bit.
                    *n -= 1;
                    break Some(false);
                }
            } else if let Some(ret) = self.inner.next() {
                // We haven't reached the end of the inner iterator yet.
                self.len += 1;
                assert!(self.len <= K * C);
                break Some(ret);
            } else {
                // Inner iterator just ended, so we now know its length.
                let rem = self.len % K;
                if rem > 0 {
                    // The inner iterator requires padding in the range [1,K).
                    self.padding_left = Some(K - rem);
                } else {
                    // No padding required.
                    self.padding_left = Some(0);
                }
            }
        }
    }
}

/// Converts a bit iterator into zero-padded [`K`]-bit words.
struct MessageWords<I: Iterator<Item = bool>> {
    inner: I,
    bits_read: usize,
    finished: bool,
}

impl<I: Iterator<Item = bool>> MessageWords<I> {
    fn new(inner: I) -> Self {
        Self {
            inner,
            bits_read: 0,
            finished: false,
        }
    }
}

impl<I: Iterator<Item = bool>> Iterator for MessageWords<I> {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }

        let mut word = 0;
        for bit_index in 0..K {
            match self.inner.next() {
                Some(bit) => {
                    self.bits_read += 1;
                    assert!(self.bits_read <= K * C);
                    word |= u32::from(bit) << bit_index;
                }
                None => {
                    self.finished = true;
                    return (bit_index > 0).then_some(word);
                }
            }
        }

        Some(word)
    }
}

/// A domain in which $\mathsf{SinsemillaHashToPoint}$ and $\mathsf{SinsemillaHash}$ can
/// be used.
#[derive(Debug, Clone)]
#[allow(non_snake_case)]
pub struct HashDomain {
    Q: pallas::Point,
}

impl HashDomain {
    /// Constructs a new `HashDomain` with a specific prefix string.
    pub fn new(domain: &str) -> Self {
        HashDomain {
            Q: pallas::Point::hash_to_curve(Q_PERSONALIZATION)(domain.as_bytes()),
        }
    }

    /// $\mathsf{SinsemillaHashToPoint}$ from [§ 5.4.1.9][concretesinsemillahash].
    ///
    /// [concretesinsemillahash]: https://zips.z.cash/protocol/nu5.pdf#concretesinsemillahash
    pub fn hash_to_point(&self, msg: impl Iterator<Item = bool>) -> CtOption<pallas::Point> {
        self.hash_to_point_inner(msg).into()
    }

    #[allow(non_snake_case)]
    fn hash_to_point_inner(&self, msg: impl Iterator<Item = bool>) -> IncompletePoint {
        let generators = &*SINSEMILLA_S_AFFINE;
        MessageWords::new(msg).fold(IncompletePoint::from(self.Q), |acc, word| {
            let S_chunk = generators[word as usize];
            acc.double_and_add(S_chunk)
        })
    }

    /// $\mathsf{SinsemillaHash}$ from [§ 5.4.1.9][concretesinsemillahash].
    ///
    /// [concretesinsemillahash]: https://zips.z.cash/protocol/nu5.pdf#concretesinsemillahash
    ///
    /// # Panics
    ///
    /// This panics if the message length is greater than [`K`] * [`C`]
    pub fn hash(&self, msg: impl Iterator<Item = bool>) -> CtOption<pallas::Base> {
        extract_p_bottom(self.hash_to_point(msg))
    }

    /// Constructs a new `HashDomain` from a given `Q`.
    ///
    /// This is only for testing use.
    #[cfg(any(test, feature = "test-dependencies"))]
    #[cfg_attr(docsrs, doc(cfg(feature = "test-dependencies")))]
    #[allow(non_snake_case)]
    pub fn from_Q(Q: pallas::Point) -> Self {
        HashDomain { Q }
    }

    /// Returns the Sinsemilla $Q$ constant for this domain.
    #[cfg(any(test, feature = "test-dependencies"))]
    #[cfg_attr(docsrs, doc(cfg(feature = "test-dependencies")))]
    #[allow(non_snake_case)]
    pub fn Q(&self) -> pallas::Point {
        self.Q
    }
}

/// A domain in which $\mathsf{SinsemillaCommit}$ and $\mathsf{SinsemillaShortCommit}$ can
/// be used.
#[derive(Debug)]
#[allow(non_snake_case)]
pub struct CommitDomain {
    M: HashDomain,
    R: pallas::Point,
}

impl CommitDomain {
    /// Constructs a new `CommitDomain` with a specific prefix string.
    pub fn new(domain: &str) -> Self {
        let m_prefix = format!("{}-M", domain);
        let r_prefix = format!("{}-r", domain);
        let hasher_r = pallas::Point::hash_to_curve(&r_prefix);
        CommitDomain {
            M: HashDomain::new(&m_prefix),
            R: hasher_r(&[]),
        }
    }

    /// $\mathsf{SinsemillaCommit}$ from [§ 5.4.8.4][concretesinsemillacommit].
    ///
    /// [concretesinsemillacommit]: https://zips.z.cash/protocol/nu5.pdf#concretesinsemillacommit
    #[allow(non_snake_case)]
    pub fn commit(
        &self,
        msg: impl Iterator<Item = bool>,
        r: &pallas::Scalar,
    ) -> CtOption<pallas::Point> {
        // We use complete addition for the blinding factor.
        CtOption::<pallas::Point>::from(self.M.hash_to_point_inner(msg))
            .map(|p| p + Wnaf::new().scalar(r).base(self.R))
    }

    /// $\mathsf{SinsemillaShortCommit}$ from [§ 5.4.8.4][concretesinsemillacommit].
    ///
    /// [concretesinsemillacommit]: https://zips.z.cash/protocol/nu5.pdf#concretesinsemillacommit
    pub fn short_commit(
        &self,
        msg: impl Iterator<Item = bool>,
        r: &pallas::Scalar,
    ) -> CtOption<pallas::Base> {
        extract_p_bottom(self.commit(msg, r))
    }

    /// Returns the Sinsemilla $R$ constant for this domain.
    #[cfg(any(test, feature = "test-dependencies"))]
    #[cfg_attr(docsrs, doc(cfg(feature = "test-dependencies")))]
    #[allow(non_snake_case)]
    pub fn R(&self) -> pallas::Point {
        self.R
    }

    /// Returns the Sinsemilla $Q$ constant for this domain.
    #[cfg(any(test, feature = "test-dependencies"))]
    #[cfg_attr(docsrs, doc(cfg(feature = "test-dependencies")))]
    #[allow(non_snake_case)]
    pub fn Q(&self) -> pallas::Point {
        self.M.Q
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use super::{HashDomain, IncompletePoint, MessageWords, C, K};
    use group::Curve;
    use pasta_curves::{arithmetic::CurveExt, pallas};
    use subtle::CtOption;

    fn hash_to_point_with_two_additions(
        domain: &HashDomain,
        msg: impl Iterator<Item = bool>,
    ) -> CtOption<pallas::Point> {
        MessageWords::new(msg)
            .fold(IncompletePoint::from(domain.Q), |acc, word| {
                let generator = super::SINSEMILLA_S_AFFINE[word as usize];
                (acc + generator) + acc
            })
            .into()
    }

    fn assert_same_point(expected: CtOption<pallas::Point>, actual: CtOption<pallas::Point>) {
        let expected_is_some = bool::from(expected.is_some());
        assert_eq!(bool::from(actual.is_some()), expected_is_some);
        if expected_is_some {
            assert_eq!(actual.unwrap(), expected.unwrap());
        }
    }

    #[test]
    fn message_words_zero_pad_the_final_word() {
        assert_eq!(
            MessageWords::new([].into_iter()).collect::<Vec<_>>(),
            vec![]
        );
        assert_eq!(
            MessageWords::new([true].into_iter()).collect::<Vec<_>>(),
            vec![1]
        );
        assert_eq!(
            MessageWords::new([true, true].into_iter()).collect::<Vec<_>>(),
            vec![3]
        );
        assert_eq!(
            MessageWords::new([true, true, true].into_iter()).collect::<Vec<_>>(),
            vec![7]
        );
        assert_eq!(
            MessageWords::new(
                [true, true, false, true, false, true, false, true, false, true].into_iter()
            )
            .collect::<Vec<_>>(),
            vec![683]
        );
        assert_eq!(
            MessageWords::new(
                [true, true, false, true, false, true, false, true, false, true, true].into_iter()
            )
            .collect::<Vec<_>>(),
            vec![683, 1]
        );
    }

    #[test]
    fn message_words_match_padded_bit_chunks_at_every_valid_length() {
        for bit_len in 0..=K * super::C {
            let bits = (0..bit_len)
                .map(|index| index % 5 == 2 || index % 11 == 7)
                .collect::<Vec<_>>();
            let expected = bits
                .chunks(K)
                .map(|chunk| {
                    chunk
                        .iter()
                        .enumerate()
                        .fold(0, |word, (index, bit)| word | (u32::from(*bit) << index))
                })
                .collect::<Vec<_>>();

            assert_eq!(
                MessageWords::new(bits.into_iter()).collect::<Vec<_>>(),
                expected
            );
        }
    }

    #[test]
    fn message_words_accept_the_maximum_message_length() {
        let words =
            MessageWords::new((0..K * super::C).map(|index| index % 5 == 2)).collect::<Vec<_>>();
        assert_eq!(words.len(), super::C);
    }

    #[test]
    #[should_panic]
    fn message_words_reject_messages_past_the_maximum_length() {
        MessageWords::new(core::iter::repeat_n(false, K * super::C + 1)).for_each(drop);
    }

    #[test]
    fn sinsemilla_s() {
        use super::sinsemilla_s::SINSEMILLA_S;
        use pasta_curves::arithmetic::CurveAffine;

        let hasher = pallas::Point::hash_to_curve(super::S_PERSONALIZATION);

        for j in 0..(1u32 << K) {
            let computed = {
                let point = hasher(&j.to_le_bytes()).to_affine().coordinates().unwrap();
                (*point.x(), *point.y())
            };
            let actual = SINSEMILLA_S[j as usize];
            assert_eq!(computed, actual);

            let decoded = super::SINSEMILLA_S_AFFINE[j as usize]
                .coordinates()
                .unwrap();
            assert_eq!((*decoded.x(), *decoded.y()), actual);
        }
    }

    #[test]
    fn hash_to_point_matches_two_additions() {
        const ORCHARD_COMMIT_IVK_BITS: usize = 510;
        const ORCHARD_MERKLE_CRH_BITS: usize = 520;
        const ORCHARD_NOTE_COMMITMENT_BITS: usize = 1_086;
        const MESSAGE_LENGTHS: [usize; 12] = [
            0,
            1,
            K - 1,
            K,
            K + 1,
            ORCHARD_COMMIT_IVK_BITS - 1,
            ORCHARD_COMMIT_IVK_BITS,
            ORCHARD_COMMIT_IVK_BITS + 1,
            ORCHARD_MERKLE_CRH_BITS,
            ORCHARD_NOTE_COMMITMENT_BITS,
            K * C - 1,
            K * C,
        ];

        let domain = HashDomain::new("sinsemilla-fused-step-test");
        for message_len in MESSAGE_LENGTHS {
            let message: Vec<_> = (0..message_len)
                .map(|index| (index + message_len) % 5 < 2)
                .collect();
            let expected = hash_to_point_with_two_additions(&domain, message.iter().copied());
            let actual = domain.hash_to_point(message.iter().copied());
            assert_same_point(expected, actual);
        }
    }
}
