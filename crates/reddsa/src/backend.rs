//! The small private operation set used by the retained generic signature code.
//!
//! This is a Pallas migration bridge, not a public backend extension API. Jubjub
//! and Pallas delegate to their existing implementations.

use core::{
    fmt::Debug,
    ops::{Add, Mul, Neg, Sub, SubAssign},
};

pub trait Scalar:
    Copy + Debug + Eq + Add<Output = Self> + Mul<Output = Self> + Neg<Output = Self> + SubAssign
{
    const ZERO: Self;
    fn from_repr(bytes: [u8; 32]) -> Option<Self>;
    fn to_repr(&self) -> [u8; 32];
    fn from_bytes_wide(bytes: &[u8; 64]) -> Self;
    fn from_raw(value: [u64; 4]) -> Self;
}

pub trait Point<S>:
    Copy + Debug + PartialEq + Add<Output = Self> + Sub<Output = Self> + Mul<S, Output = Self>
{
    fn from_bytes(bytes: &[u8; 32]) -> Option<Self>;
    fn to_bytes(&self) -> [u8; 32];
    fn is_small_order(&self) -> bool;
}

impl Scalar for jubjub::Scalar {
    const ZERO: Self = <Self as group::ff::Field>::ZERO;
    fn from_repr(bytes: [u8; 32]) -> Option<Self> {
        <Self as group::ff::PrimeField>::from_repr(bytes).into()
    }
    fn to_repr(&self) -> [u8; 32] {
        self.to_bytes()
    }
    fn from_bytes_wide(bytes: &[u8; 64]) -> Self {
        Self::from_bytes_wide(bytes)
    }
    fn from_raw(value: [u64; 4]) -> Self {
        Self::from_raw(value)
    }
}
impl Point<jubjub::Scalar> for jubjub::ExtendedPoint {
    fn from_bytes(bytes: &[u8; 32]) -> Option<Self> {
        <Self as group::GroupEncoding>::from_bytes(bytes).into()
    }
    fn to_bytes(&self) -> [u8; 32] {
        <Self as group::GroupEncoding>::to_bytes(self)
    }
    fn is_small_order(&self) -> bool {
        <Self as group::cofactor::CofactorGroup>::is_small_order(self).into()
    }
}

#[cfg(feature = "pallas-pasta")]
impl Scalar for pasta_curves::pallas::Scalar {
    const ZERO: Self = <Self as group::ff::Field>::ZERO;
    fn from_repr(bytes: [u8; 32]) -> Option<Self> {
        <Self as group::ff::PrimeField>::from_repr(bytes).into()
    }
    fn to_repr(&self) -> [u8; 32] {
        <Self as group::ff::PrimeField>::to_repr(self)
    }
    fn from_bytes_wide(bytes: &[u8; 64]) -> Self {
        <Self as group::ff::FromUniformBytes<64>>::from_uniform_bytes(bytes)
    }
    fn from_raw(value: [u64; 4]) -> Self {
        Self::from_raw(value)
    }
}
#[cfg(feature = "pallas-pasta")]
impl Point<pasta_curves::pallas::Scalar> for pasta_curves::pallas::Point {
    fn from_bytes(bytes: &[u8; 32]) -> Option<Self> {
        <Self as group::GroupEncoding>::from_bytes(bytes).into()
    }
    fn to_bytes(&self) -> [u8; 32] {
        <Self as group::GroupEncoding>::to_bytes(self)
    }
    fn is_small_order(&self) -> bool {
        <Self as group::Group>::is_identity(self).into()
    }
}
