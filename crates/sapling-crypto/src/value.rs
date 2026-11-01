//! Monetary values within the Sapling shielded pool.
//!
//! Values are represented in three places within the Sapling protocol:
//! - [`NoteValue`], the value of an individual note. It is an unsigned 64-bit integer
//!   (with maximum value [`MAX_NOTE_VALUE`]), and is serialized in a note plaintext.
//! - [`ValueSum`], the sum of note values within a Sapling [`Bundle`]. It is represented
//!   as an `i128` and places an upper bound on the maximum number of notes within a
//!   single [`Bundle`].
//! - `valueBalanceSapling`, which is a signed 63-bit integer. This is represented
//!   by a user-defined type parameter on [`Bundle`], returned by
//!   [`Bundle::value_balance`] and [`Builder::value_balance`].
//!
//! If your specific instantiation of the Sapling protocol requires a smaller bound on
//! valid note values (for example, Zcash's `MAX_MONEY` fits into a 51-bit integer), you
//! should enforce this in two ways:
//!
//! - Define your `valueBalanceSapling` type to enforce your valid value range. This can
//!   be checked in its `TryFrom<i64>` implementation.
//! - Define your own "amount" type for note values, and convert it to `NoteValue` prior
//!   to calling [`Builder::add_output`].
//!
//! Inside the circuit, note values are constrained to be unsigned 64-bit integers.
//!
//! # Caution!
//!
//! An `i64` is _not_ a signed 64-bit integer! The [Rust documentation] calls `i64` the
//! 64-bit signed integer type, which is true in the sense that its encoding in memory
//! takes up 64 bits. Numerically, however, `i64` is a signed 63-bit integer.
//!
//! Fortunately, users of this crate should never need to construct [`ValueSum`] directly;
//! you should only need to interact with [`NoteValue`] (which can be safely constructed
//! from a `u64`) and `valueBalanceSapling` (which can be represented as an `i64`).
//!
//! [`Bundle`]: crate::Bundle
//! [`Bundle::value_balance`]: crate::Bundle::value_balance
//! [`Builder::value_balance`]: crate::builder::Builder::value_balance
//! [`Builder::add_output`]: crate::builder::Builder::add_output
//! [Rust documentation]: https://doc.rust-lang.org/stable/std/primitive.i64.html

use ff::{Field, PrimeField};
use group::GroupEncoding;
use rand::Rng;
use subtle::CtOption;

use super::{
    constants::{VALUE_COMMITMENT_RANDOMNESS_GENERATOR, VALUE_COMMITMENT_VALUE_GENERATOR},
    spec::leos2bsp,
};

mod sums;
pub use sums::{BalanceError, CommitmentSum, TrapdoorSum, ValueSum};

/// Maximum note value.
pub const MAX_NOTE_VALUE: u64 = u64::MAX;

/// The non-negative value of an individual Sapling note.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct NoteValue(u64);

impl NoteValue {
    /// The zero note value.
    pub const ZERO: NoteValue = NoteValue(0);

    /// Returns the raw underlying value.
    pub fn inner(&self) -> u64 {
        self.0
    }

    /// Creates a note value from its raw numeric value.
    ///
    /// This only enforces that the value is an unsigned 64-bit integer. Callers should
    /// enforce any additional constraints on the value's valid range themselves.
    pub fn from_raw(value: u64) -> Self {
        NoteValue(value)
    }

    pub(crate) fn from_bytes(bytes: [u8; 8]) -> Self {
        NoteValue(u64::from_le_bytes(bytes))
    }

    pub(crate) fn to_le_bits(self) -> impl Iterator<Item = bool> {
        leos2bsp(self.0.to_le_bytes())
    }
}

/// The blinding factor for a [`ValueCommitment`].
#[derive(Clone, Debug)]
pub struct ValueCommitTrapdoor(jubjub::Scalar);

impl ValueCommitTrapdoor {
    /// Generates a new value commitment trapdoor.
    ///
    /// This is public for access by `zcash_proofs`.
    pub fn random(mut rng: impl Rng) -> Self {
        ValueCommitTrapdoor(jubjub::Scalar::random(&mut rng))
    }

    /// Constructs `ValueCommitTrapdoor` from the byte representation of a scalar.
    ///
    /// Returns a `None` [`CtOption`] if `bytes` is not a canonical representation of a
    /// Jubjub scalar.
    ///
    /// This is a low-level API, requiring a detailed understanding of the
    /// [use of value commitment trapdoors][saplingbalance] in the Zcash protocol
    /// to use correctly and securely. It is intended to be used in combination
    /// with [`ValueCommitment::derive`].
    ///
    /// [saplingbalance]: https://zips.z.cash/protocol/protocol.pdf#saplingbalance
    pub fn from_bytes(bytes: [u8; 32]) -> CtOption<Self> {
        jubjub::Scalar::from_repr(bytes).map(ValueCommitTrapdoor)
    }

    /// Returns the inner Jubjub scalar representing this trapdoor.
    ///
    /// This is public for access by `zcash_proofs`.
    pub fn inner(&self) -> jubjub::Scalar {
        self.0
    }
}

/// A commitment to a [`ValueSum`].
///
/// # Consensus rules
///
/// The Zcash Protocol Spec requires Sapling Spend Descriptions and Output Descriptions to
/// not contain a small order `ValueCommitment`. However, the `ValueCommitment` type as
/// specified (and implemented here) may contain a small order point. In practice, it will
/// not occur:
/// - [`ValueCommitment::derive`] will only produce a small order point if both the given
///   [`NoteValue`] and [`ValueCommitTrapdoor`] are zero. However, the only constructor
///   available for `ValueCommitTrapdoor` is [`ValueCommitTrapdoor::random`], which will
///   produce zero with negligible probability (assuming a non-broken PRNG).
/// - [`ValueCommitment::from_bytes_not_small_order`] enforces this by definition.
/// - Data received over the network may also be wrapped with
///   [`ValueCommitment::from_bytes_unvalidated`] (transaction parsing does this), but must
///   then pass [`ValueCommitment::try_point`] before it is used as a point.
///
/// # Representation
///
/// Held as its 32-byte encoding. Nearly every consumer of a value commitment wants exactly
/// those bytes - the txid digest, the outgoing cipher key, serialization - and a wallet never
/// wants anything else, while decompressing the point costs a field square root and
/// compressing it back an inversion. The point is recovered, and the "not small order" rule
/// checked, only by [`ValueCommitment::try_point`], which proof and binding-signature
/// verification call before they use it.
#[derive(Clone, Debug)]
pub struct ValueCommitment {
    bytes: [u8; 32],
}

impl ValueCommitment {
    /// Derives a `ValueCommitment` by $\mathsf{ValueCommit^{Sapling}}$.
    ///
    /// Defined in [Zcash Protocol Spec § 5.4.8.3: Homomorphic Pedersen commitments (Sapling and Orchard)][concretehomomorphiccommit].
    ///
    /// [concretehomomorphiccommit]: https://zips.z.cash/protocol/protocol.pdf#concretehomomorphiccommit
    pub fn derive(value: NoteValue, rcv: ValueCommitTrapdoor) -> Self {
        let cv = (VALUE_COMMITMENT_VALUE_GENERATOR * jubjub::Scalar::from(value.0))
            + (VALUE_COMMITMENT_RANDOMNESS_GENERATOR * rcv.0);

        ValueCommitment {
            bytes: jubjub::ExtendedPoint::from(cv).to_bytes(),
        }
    }

    /// Wraps a value commitment's byte representation without validating it.
    ///
    /// The encoding is checked - canonical, on the curve, not of small order - when a point
    /// is asked for via [`ValueCommitment::try_point`]. This is what transaction parsing uses,
    /// so that a wallet decoding a transaction it will only ever trial-decrypt does not pay a
    /// square root per spend and output for a check that verification performs anyway.
    pub fn from_bytes_unvalidated(bytes: [u8; 32]) -> Self {
        ValueCommitment { bytes }
    }

    /// Deserializes a value commitment from its byte representation, validating it.
    ///
    /// Returns `None` if `bytes` is an invalid representation of a Jubjub point, or the
    /// resulting point is of small order.
    ///
    /// This method can be used to enforce the "not small order" consensus rules defined
    /// in [Zcash Protocol Spec § 4.4: Spend Descriptions][spenddesc] and
    /// [§ 4.5: Output Descriptions][outputdesc].
    ///
    /// [spenddesc]: https://zips.z.cash/protocol/protocol.pdf#spenddesc
    /// [outputdesc]: https://zips.z.cash/protocol/protocol.pdf#outputdesc
    pub fn from_bytes_not_small_order(bytes: &[u8; 32]) -> CtOption<ValueCommitment> {
        let cv = ValueCommitment { bytes: *bytes };
        cv.try_point().map(|_| cv)
    }

    /// Recovers the Jubjub point this value commitment encodes.
    ///
    /// Returns `None` if the encoding is not a valid Jubjub point, or the point is of small
    /// order - the consensus rules of [Zcash Protocol Spec § 4.4][spenddesc] and
    /// [§ 4.5][outputdesc], enforced here rather than at parse time.
    ///
    /// [spenddesc]: https://zips.z.cash/protocol/protocol.pdf#spenddesc
    /// [outputdesc]: https://zips.z.cash/protocol/protocol.pdf#outputdesc
    pub fn try_point(&self) -> CtOption<jubjub::ExtendedPoint> {
        jubjub::ExtendedPoint::from_bytes(&self.bytes)
            .and_then(|cv| CtOption::new(cv, !cv.is_small_order()))
    }

    /// Serializes this value commitment to its canonical byte representation.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.bytes
    }
}

/// Generators for property testing.
#[cfg(any(test, feature = "test-dependencies"))]
#[cfg_attr(docsrs, doc(cfg(feature = "test-dependencies")))]
pub mod testing {
    use proptest::prelude::*;

    use super::{MAX_NOTE_VALUE, NoteValue, ValueCommitTrapdoor};

    prop_compose! {
        /// Generate an arbitrary value in the range of valid nonnegative amounts.
        pub fn arb_note_value()(value in 0u64..MAX_NOTE_VALUE) -> NoteValue {
            NoteValue(value)
        }
    }

    prop_compose! {
        /// Generate an arbitrary value in the range of valid positive amounts less than a
        /// specified value.
        pub fn arb_note_value_bounded(max: u64)(value in 0u64..max) -> NoteValue {
            NoteValue(value)
        }
    }

    prop_compose! {
        /// Generate an arbitrary value in the range of valid positive amounts less than a
        /// specified value.
        pub fn arb_positive_note_value(max: u64)(value in 1u64..max) -> NoteValue {
            NoteValue(value)
        }
    }

    prop_compose! {
        /// Generate an arbitrary Jubjub scalar.
        fn arb_scalar()(bytes in prop::array::uniform32(0u8..)) -> jubjub::Scalar {
            // Instead of rejecting out-of-range bytes, let's reduce them.
            let mut buf = [0; 64];
            buf[..32].copy_from_slice(&bytes);
            jubjub::Scalar::from_bytes_wide(&buf)
        }
    }

    prop_compose! {
        /// Generate an arbitrary ValueCommitTrapdoor
        pub fn arb_trapdoor()(rcv in arb_scalar()) -> ValueCommitTrapdoor {
            ValueCommitTrapdoor(rcv)
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use proptest::prelude::*;

    use ff::{Field, PrimeField};
    use group::GroupEncoding;

    use super::{
        BalanceError, CommitmentSum, NoteValue, TrapdoorSum, ValueCommitTrapdoor, ValueCommitment,
        ValueSum,
        testing::{arb_note_value_bounded, arb_trapdoor},
    };

    /// The rule transaction parsing applied before value commitments were held as bytes: a
    /// canonical (ZIP 216) encoding of a Jubjub point that is not of small order.
    fn parse_time_rule(bytes: [u8; 32]) -> bool {
        Option::<jubjub::AffinePoint>::from(jubjub::AffinePoint::from_bytes(bytes))
            .is_some_and(|p| !bool::from(jubjub::ExtendedPoint::from(p).is_small_order()))
    }

    /// The little-endian encoding of a field's modulus.
    fn modulus<F: PrimeField<Repr = [u8; 32]>>() -> [u8; 32] {
        add_le(&(-F::ONE).to_repr(), 1)
    }

    fn add_le(bytes: &[u8; 32], mut carry: u16) -> [u8; 32] {
        let mut out = *bytes;
        for b in out.iter_mut() {
            let sum = u16::from(*b) + carry;
            *b = sum as u8;
            carry = sum >> 8;
        }
        out
    }

    /// The eight points of Jubjub's torsion subgroup, as `[r]P` for points `P` decoded from
    /// successive encodings, where `r` is the order of the prime-order subgroup.
    fn small_order_points() -> Vec<jubjub::ExtendedPoint> {
        let r = modulus::<jubjub::Fr>();
        let mut points: Vec<jubjub::ExtendedPoint> = Vec::new();
        for v in 0u8..=255 {
            let mut bytes = [0u8; 32];
            bytes[0] = v;
            let Some(p) =
                Option::<jubjub::AffinePoint>::from(jubjub::AffinePoint::from_bytes(bytes))
            else {
                continue;
            };
            let p = jubjub::ExtendedPoint::from(p);
            let mut torsion = jubjub::ExtendedPoint::identity();
            for bit in (0..256).rev().map(|i| (r[i / 8] >> (i % 8)) & 1 == 1) {
                torsion = torsion.double();
                if bit {
                    torsion += p;
                }
            }
            if !points.contains(&torsion) {
                points.push(torsion);
            }
            if points.len() == 8 {
                return points;
            }
        }
        panic!("found only {} small-order points", points.len());
    }

    /// `try_point` accepts exactly the encodings that parsing used to accept, and a value
    /// commitment keeps the bytes it was given.
    #[test]
    fn try_point_matches_the_parse_time_rule() {
        let small_order = small_order_points();
        let identity = jubjub::ExtendedPoint::identity().to_bytes();
        let minus_one = (-jubjub::Fq::ONE).to_repr();
        assert!(small_order.iter().any(|p| p.to_bytes() == identity));
        assert!(small_order.iter().any(|p| p.to_bytes() == minus_one));

        let with_sign = |mut b: [u8; 32]| {
            b[31] |= 0x80;
            b
        };
        let q = modulus::<jubjub::Fq>();

        let mut invalid = small_order.iter().map(|p| p.to_bytes()).collect::<Vec<_>>();
        // The ZIP 216 non-canonical encodings of (0, 1) and (0, -1).
        invalid.push(with_sign(identity));
        invalid.push(with_sign(minus_one));
        // `v` at or beyond the field modulus.
        invalid.push(q);
        invalid.push(add_le(&q, 1));
        invalid.push(with_sign(q));
        invalid.push([0xff; 32]);
        // Field elements that are the `v` of no curve point.
        invalid.extend(
            (2u8..=255)
                .map(|v| {
                    let mut b = [0u8; 32];
                    b[0] = v;
                    b
                })
                .filter(|b| bool::from(jubjub::AffinePoint::from_bytes(*b).is_none()))
                .take(5),
        );
        assert_eq!(invalid.len(), 8 + 2 + 4 + 5);

        let mut rcv = jubjub::Fr::from(0x9e37_79b9_7f4a_7c15);
        let valid = (0u64..300)
            .map(|i| {
                rcv = rcv.square() + jubjub::Fr::ONE;
                ValueCommitment::derive(NoteValue(i * 1_000_003), ValueCommitTrapdoor(rcv))
                    .to_bytes()
            })
            .collect::<Vec<_>>();

        for (bytes, expected) in invalid
            .iter()
            .map(|b| (b, false))
            .chain(valid.iter().map(|b| (b, true)))
        {
            let cv = ValueCommitment::from_bytes_unvalidated(*bytes);
            let point = cv.try_point();
            assert_eq!(bool::from(point.is_some()), parse_time_rule(*bytes));
            assert_eq!(bool::from(point.is_some()), expected);
            assert_eq!(
                bool::from(ValueCommitment::from_bytes_not_small_order(bytes).is_some()),
                expected
            );
            assert_eq!(cv.to_bytes(), *bytes);
            if expected {
                assert_eq!(point.unwrap().to_bytes(), *bytes);
            }
        }

        // Small-order points are on the curve; only the small-order rule rejects them.
        for p in &small_order {
            assert!(bool::from(p.is_small_order()));
            assert!(bool::from(
                jubjub::AffinePoint::from_bytes(p.to_bytes()).is_some()
            ));
        }
    }

    proptest! {
        #[test]
        fn bsk_consistent_with_bvk(
            values in (1usize..10).prop_flat_map(|n_values| prop::collection::vec(
                (arb_note_value_bounded((i64::MAX as u64) / (n_values as u64)), arb_trapdoor()),
                n_values,
            ))
        ) {
            let value_balance: i64 = values
                .iter()
                .map(|(value, _)| value)
                .sum::<Result<ValueSum, BalanceError>>()
                .expect("we generate values that won't overflow")
                .try_into()
                .unwrap();

            let bsk = values
                .iter()
                .map(|(_, rcv)| rcv)
                .sum::<TrapdoorSum>()
                .into_bsk();

            let cvs = values
                .into_iter()
                .map(|(value, rcv)| ValueCommitment::derive(value, rcv))
                .collect::<Vec<_>>();
            let bvk = CommitmentSum::try_sum(&cvs)
                .expect("derived commitments are valid points")
                .into_bvk(value_balance);

            assert_eq!(redjubjub::VerificationKey::from(&bsk), bvk);
        }
    }
}
