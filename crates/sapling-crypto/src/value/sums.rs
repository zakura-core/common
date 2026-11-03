use core::fmt::{self, Debug};
use core::iter::Sum;
use core::ops::{Add, AddAssign, Sub, SubAssign};

use redjubjub::Binding;

use super::{NoteValue, ValueCommitTrapdoor, ValueCommitment};
use crate::constants::VALUE_COMMITMENT_VALUE_GENERATOR;

/// A type for balance violations in amount addition and subtraction
/// (overflow and underflow of allowed ranges).
#[derive(Debug)]
#[non_exhaustive]
pub enum BalanceError {
    /// Two values were added or subtracted, and the result overflowed the valid range for
    /// the value.
    Overflow,
}

impl fmt::Display for BalanceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Overflow => write!(f, "Sapling value operation overflowed"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for BalanceError {}

/// A sum of Sapling note values.
///
/// [Zcash Protocol Spec § 4.13: Balance and Binding Signature (Sapling)][saplingbalance]
/// constrains the range of this type to between `[-(r_J - 1)/2..(r_J - 1)/2]` in the
/// abstract protocol, and `[−38913406623490299131842..104805176454780817500623]` in the
/// concrete Zcash protocol. We represent it as an `i128`, which has a range large enough
/// to handle Zcash transactions while small enough to ensure the abstract protocol bounds
/// are not breached.
///
/// [saplingbalance]: https://zips.z.cash/protocol/protocol.pdf#saplingbalance
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ValueSum(i128);

impl ValueSum {
    /// Initializes a sum of `NoteValue`s to zero.
    pub fn zero() -> Self {
        ValueSum(0)
    }

    /// Instantiates a value sum from a raw encoding.
    ///
    /// Only intended for use with PCZTs.
    #[cfg(feature = "wallet")]
    pub(crate) fn from_raw(value_sum: i128) -> Self {
        Self(value_sum)
    }

    /// Extracts the raw encoding of this value sum.
    ///
    /// Only intended for use with PCZTs.
    pub fn to_raw(self) -> i128 {
        self.0
    }
}

impl Add<NoteValue> for ValueSum {
    type Output = Option<ValueSum>;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn add(self, rhs: NoteValue) -> Self::Output {
        self.0.checked_add(rhs.0.into()).map(ValueSum)
    }
}

impl Sub<NoteValue> for ValueSum {
    type Output = Option<ValueSum>;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn sub(self, rhs: NoteValue) -> Self::Output {
        self.0.checked_sub(rhs.0.into()).map(ValueSum)
    }
}

impl<'a> Sum<&'a NoteValue> for Result<ValueSum, BalanceError> {
    fn sum<I: Iterator<Item = &'a NoteValue>>(mut iter: I) -> Self {
        iter.try_fold(ValueSum(0), |acc, v| acc + *v)
            .ok_or(BalanceError::Overflow)
    }
}

impl Sum<NoteValue> for Result<ValueSum, BalanceError> {
    fn sum<I: Iterator<Item = NoteValue>>(mut iter: I) -> Self {
        iter.try_fold(ValueSum(0), |acc, v| acc + v)
            .ok_or(BalanceError::Overflow)
    }
}

impl TryFrom<ValueSum> for i64 {
    type Error = BalanceError;

    fn try_from(v: ValueSum) -> Result<i64, Self::Error> {
        i64::try_from(v.0).map_err(|_| BalanceError::Overflow)
    }
}

/// A sum of Sapling value commitment blinding factors.
#[derive(Clone, Copy, Debug)]
pub struct TrapdoorSum(jubjub::Scalar);

impl TrapdoorSum {
    /// Initializes a sum of `ValueCommitTrapdoor`s to zero.
    pub fn zero() -> Self {
        TrapdoorSum(jubjub::Scalar::zero())
    }

    /// Transform this trapdoor sum into the corresponding RedJubjub private key.
    ///
    /// This is public for access by `zcash_proofs`.
    pub fn into_bsk(self) -> redjubjub::SigningKey<Binding> {
        redjubjub::SigningKey::try_from(self.0.to_bytes())
            .expect("valid scalars are valid signing keys")
    }
}

impl Add<&ValueCommitTrapdoor> for ValueCommitTrapdoor {
    type Output = TrapdoorSum;

    fn add(self, rhs: &Self) -> Self::Output {
        TrapdoorSum(self.0 + rhs.0)
    }
}

impl Add<&ValueCommitTrapdoor> for TrapdoorSum {
    type Output = TrapdoorSum;

    fn add(self, rhs: &ValueCommitTrapdoor) -> Self::Output {
        TrapdoorSum(self.0 + rhs.0)
    }
}

impl AddAssign<&ValueCommitTrapdoor> for TrapdoorSum {
    fn add_assign(&mut self, rhs: &ValueCommitTrapdoor) {
        self.0 += rhs.0;
    }
}

impl Sub<&ValueCommitTrapdoor> for ValueCommitTrapdoor {
    type Output = TrapdoorSum;

    fn sub(self, rhs: &Self) -> Self::Output {
        TrapdoorSum(self.0 - rhs.0)
    }
}

impl Sub<TrapdoorSum> for TrapdoorSum {
    type Output = TrapdoorSum;

    fn sub(self, rhs: Self) -> Self::Output {
        TrapdoorSum(self.0 - rhs.0)
    }
}

impl SubAssign<&ValueCommitTrapdoor> for TrapdoorSum {
    fn sub_assign(&mut self, rhs: &ValueCommitTrapdoor) {
        self.0 -= rhs.0;
    }
}

impl<'a> Sum<&'a ValueCommitTrapdoor> for TrapdoorSum {
    fn sum<I: Iterator<Item = &'a ValueCommitTrapdoor>>(iter: I) -> Self {
        iter.fold(TrapdoorSum::zero(), |acc, cv| acc + cv)
    }
}

/// A sum of Sapling value commitments.
#[derive(Clone, Copy, Debug)]
pub struct CommitmentSum(jubjub::ExtendedPoint);

impl CommitmentSum {
    /// Initializes a sum of `ValueCommitment`s to zero.
    pub fn zero() -> Self {
        CommitmentSum(jubjub::ExtendedPoint::identity())
    }

    /// Sums value commitments, or returns `None` if any of them is not a canonical
    /// encoding of a Jubjub point that is not of small order.
    ///
    /// A [`ValueCommitment`] parsed from a transaction is not validated until its point is
    /// recovered, so summing one must be able to fail.
    pub fn try_sum<'a>(cvs: impl IntoIterator<Item = &'a ValueCommitment>) -> Option<Self> {
        cvs.into_iter().try_fold(Self::zero(), |mut acc, cv| {
            acc += &cv.try_point().into_option()?;
            Some(acc)
        })
    }

    /// Transform this value commitment sum into the corresponding RedJubjub public key.
    ///
    /// This is public for access by `zcash_proofs`.
    ///
    /// # Security
    ///
    /// This runs in variable time with respect to `value_balance`, which is public
    /// transaction data.
    pub fn into_bvk<V: Into<i64>>(self, value_balance: V) -> redjubjub::VerificationKey<Binding> {
        let value: i64 = value_balance.into();
        let magnitude = value.unsigned_abs();

        // [|value_balance|] V by double-and-add over only the magnitude's significant
        // bits, adding the generator only at set bits. A negative balance flips the
        // final subtraction rather than multiplying by a full-width negated scalar.
        let generator = jubjub::ExtendedPoint::from(VALUE_COMMITMENT_VALUE_GENERATOR).to_niels();
        let product = (0..u64::BITS - magnitude.leading_zeros()).rev().fold(
            jubjub::ExtendedPoint::identity(),
            |acc, bit| {
                let acc = acc.double();
                if (magnitude >> bit) & 1 == 1 {
                    acc + generator
                } else {
                    acc
                }
            },
        );

        // Subtract `value_balance` from the sum to get the final bvk.
        let bvk = if value.is_negative() {
            self.0 + product
        } else {
            self.0 - product
        };

        redjubjub::VerificationKey::from(bvk)
    }
}

/// Accumulates a value commitment's point. A verifier obtains it with
/// [`ValueCommitment::try_point`] and rejects the description if that fails.
impl AddAssign<&jubjub::ExtendedPoint> for CommitmentSum {
    fn add_assign(&mut self, rhs: &jubjub::ExtendedPoint) {
        self.0 += rhs;
    }
}

/// See [`AddAssign<&jubjub::ExtendedPoint>`].
impl SubAssign<&jubjub::ExtendedPoint> for CommitmentSum {
    fn sub_assign(&mut self, rhs: &jubjub::ExtendedPoint) {
        self.0 -= rhs;
    }
}

impl Sub<CommitmentSum> for CommitmentSum {
    type Output = CommitmentSum;

    fn sub(self, rhs: Self) -> Self::Output {
        CommitmentSum(self.0 - rhs.0)
    }
}
