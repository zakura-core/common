//! Native protocol arithmetic, independent of proof and witness runtime.
//!
//! Values retain validated Udon representations. Encoding and decoding happen
//! only at the wire boundary; arithmetic is variable-time.
//!
//! Canonical decoding contracts live on [`Fp::from_bytes`], [`Fq::from_bytes`],
//! [`PallasPoint`], [`NonIdentityPallasPoint`], and [`SpendValidatingKey`]. The
//! field constructors [`Fp::from_raw`] / [`Fq::from_raw`] and
//! [`Fp::from_uniform_bytes`] / [`Fq::from_uniform_bytes`] instead reduce
//! integers modulo the field order. The `from_native` methods take typed Udon
//! values without wire decoding; [`SpendValidatingKey::from_native`] also
//! checks the key restriction documented on [`SpendValidatingKey`].
//!
//! # Lazy data and ownership
//!
//! Primitive and [`RedPallas`](crate::redpallas) operations initialize their own
//! lazy data independently of proof workers, the SRS, and circuit preparation.
//! On targets with pointer atomics (`target_has_atomic = "ptr"`), the static
//! caches below retain one published value for the process lifetime. Without
//! pointer atomics, each access constructs an owned value that is dropped after
//! use; no shared lazy value is retained.
//!
//! | Consumer | Lazy data |
//! | --- | --- |
//! | [`generators::FixedGenerator::multiply`] | One multiplication table per fixed generator. |
//! | [`protocol`] | Incoming-viewing-key and note hash domains, plus the diversification fallback point when needed. |
//! | [`merkle`] | Standard hash domain and the weighted hash domain's prepared tables. |
//! | [`sinsemilla`] | Affine `S` generator vector used by ordinary hashing and weighted-table construction. |
//! | [`crate::redpallas`] | One multiplication table per signature domain, separate from `generators`' tables. |
//!
//! With pointer atomics, ordinary caches use `OnceBox`: concurrent first uses
//! may each run their initializer, but publish one value and drop losing
//! candidates. Sinsemilla's affine `S` vector instead uses `OnceTable` to claim
//! initialization at most once; other callers spin until that initializer
//! publishes. This distinction does not apply without pointer atomics, where
//! both kinds construct a new owned value on every access.
//!
//! Explicitly constructed [`agreement::PreparedBase`] and
//! [`sinsemilla::weighted::UncheckedFixedLengthHashDomain`] values own their
//! tables until dropped on every target. Caller-owned batch workspaces likewise
//! retain their buffers independently of the static caches.
pub mod agreement;
mod arithmetic;
pub(crate) mod cache;
pub mod generators;
mod hash_to_curve;
pub mod merkle;
pub mod pallas;
pub mod poseidon;
pub(crate) mod prepared;
pub mod protocol;
pub mod sinsemilla;
pub(crate) mod tables;
use crate::Error;
use udon::field::{Fp as NativeFp, Fq as NativeFq};
pub(crate) const ENCODED_VALUE_SIZE: usize = 32;

/// $LEOS2BSP_{8N}$: the bits of `bytes`, starting with the least-significant bit
/// of `bytes[0]`.
///
/// Defined in [Zcash Protocol Spec § 5.1: Integers, Bit Sequences, and Endianness][endian].
///
/// [endian]: https://zips.z.cash/protocol/protocol.pdf#endian
pub(crate) fn leos2bsp<const N: usize>(bytes: [u8; N]) -> impl Iterator<Item = bool> {
    (0..N * 8).map(move |i| (bytes[i / 8] >> (i % 8)) & 1 == 1)
}

/// A native Pallas base-field element with a canonical 32-byte little-endian encoding.
///
/// ```
/// use zakura_sensei::Fp;
///
/// let mut bytes = [0; 32];
/// bytes[0] = 42;
/// assert_eq!(Fp::from_bytes(bytes)?.to_bytes(), bytes);
/// assert!(Fp::from_bytes([0xff; 32]).is_err());
/// # Ok::<(), zakura_sensei::Error>(())
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Fp(NativeFp);

/// A native Pallas scalar-field element with a canonical 32-byte little-endian encoding.
#[derive(Clone, Copy, Debug)]
pub struct Fq(NativeFq);

/// An alias for the Pallas scalar-field type [`Fq`].
pub type Fr = Fq;

/// A native affine Pallas point, including identity, with a canonical compressed encoding.
///
/// Encodes the x coordinate in little-endian form with the y sign in the high
/// bit. All-zero bytes encode identity. Construction validates the encoding
/// and curve membership without initializing proof preparation.
///
/// ```
/// use zakura_sensei::{NonIdentityPallasPoint, PallasPoint, SpendValidatingKey};
///
/// let identity = [0; 32];
/// assert_eq!(PallasPoint::from_bytes(identity)?.to_bytes(), identity);
/// assert!(NonIdentityPallasPoint::from_bytes(identity).is_err());
/// assert!(SpendValidatingKey::from_bytes(identity).is_err());
/// # Ok::<(), zakura_sensei::Error>(())
/// ```
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PallasPoint(udon::curve::PallasPoint);

/// A native affine nonidentity Pallas point with a canonical compressed encoding.
///
/// Uses [`PallasPoint`]'s encoding with an additional nonidentity check.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NonIdentityPallasPoint(udon::curve::PallasAffine);

/// A nonidentity Pallas point with the sign required for an Orchard `ak`.
///
/// Uses [`PallasPoint`]'s encoding and requires its high sign bit to be zero.
/// Decoding establishes these point restrictions, not knowledge of a signing
/// key or satisfaction of witness relations.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SpendValidatingKey(udon::curve::PallasAffine);

impl Fp {
    /// Decodes a canonical 32-byte little-endian Pallas base-field element.
    ///
    /// Returns [`Error::InvalidInput`] if the integer is at least the field
    /// modulus. Inputs are not reduced modulo the field order.
    pub fn from_bytes(bytes: [u8; ENCODED_VALUE_SIZE]) -> Result<Self, Error> {
        <NativeFp>::from_bytes(bytes)
            .map(Self)
            .ok_or(Error::InvalidInput)
    }
}

impl Fq {
    /// Decodes a canonical 32-byte little-endian Pallas scalar-field element.
    ///
    /// Returns [`Error::InvalidInput`] if the integer is at least the scalar
    /// field's modulus. Inputs are not reduced modulo the field order.
    ///
    /// [`Self::from_raw`] reduces the same integer that canonical decoding rejects:
    ///
    /// ```
    /// use zakura_sensei::Fq;
    ///
    /// assert!(Fq::from_bytes([0xff; 32]).is_err());
    /// let reduced = Fq::from_raw([u64::MAX; 4]);
    /// assert_eq!(Fq::from_bytes(reduced.to_bytes())?, reduced);
    /// # Ok::<(), zakura_sensei::Error>(())
    /// ```
    pub fn from_bytes(bytes: [u8; ENCODED_VALUE_SIZE]) -> Result<Self, Error> {
        <NativeFq>::from_bytes(bytes)
            .map(Self)
            .ok_or(Error::InvalidInput)
    }
}

impl PallasPoint {
    /// Decodes a canonically compressed Pallas point, including the identity.
    ///
    /// Returns [`Error::InvalidInput`] if the encoding is invalid.
    pub fn from_bytes(bytes: [u8; ENCODED_VALUE_SIZE]) -> Result<Self, Error> {
        udon::curve::PallasPoint::from_bytes(bytes)
            .map(Self)
            .ok_or(Error::InvalidInput)
    }
}

impl NonIdentityPallasPoint {
    /// Decodes a canonically compressed non-identity Pallas point.
    ///
    /// Returns [`Error::InvalidInput`] if the encoding is invalid or represents
    /// the identity.
    pub fn from_bytes(bytes: [u8; ENCODED_VALUE_SIZE]) -> Result<Self, Error> {
        udon::curve::PallasAffine::from_bytes(bytes)
            .map(Self)
            .ok_or(Error::InvalidInput)
    }
}

impl SpendValidatingKey {
    /// Decodes the canonical Orchard encoding of a spend validating key.
    ///
    /// Returns [`Error::InvalidInput`] if the encoding is invalid, represents
    /// the identity, or has a nonzero high sign bit.
    pub fn from_bytes(bytes: [u8; ENCODED_VALUE_SIZE]) -> Result<Self, Error> {
        if bytes[ENCODED_VALUE_SIZE - 1] & 0x80 != 0 {
            return Err(Error::InvalidInput);
        }
        udon::curve::PallasAffine::from_bytes(bytes)
            .map(Self)
            .ok_or(Error::InvalidInput)
    }
}

impl Fp {
    /// Wraps a native field element without encoding or decoding it.
    pub const fn from_native(value: NativeFp) -> Self {
        Self(value)
    }
    /// Returns the native field value without encoding or decoding it.
    pub const fn native(self) -> NativeFp {
        self.0
    }
    /// Returns the canonical little-endian bytes accepted by [`Self::from_bytes`].
    pub fn to_bytes(self) -> [u8; ENCODED_VALUE_SIZE] {
        self.0.to_bytes()
    }
}
impl Fq {
    /// Wraps a native field element without encoding or decoding it.
    pub const fn from_native(value: NativeFq) -> Self {
        Self(value)
    }
    /// Returns the native field value without encoding or decoding it.
    pub const fn native(self) -> NativeFq {
        self.0
    }
    /// Returns the canonical little-endian bytes accepted by [`Self::from_bytes`].
    pub fn to_bytes(self) -> [u8; ENCODED_VALUE_SIZE] {
        self.0.to_bytes()
    }
}
impl PallasPoint {
    /// Wraps a validated native affine point, including identity.
    pub const fn from_native(value: udon::curve::PallasPoint) -> Self {
        Self(value)
    }
    /// Returns the native point without decoding or normalization.
    pub const fn native(self) -> udon::curve::PallasPoint {
        self.0
    }
    /// Returns the canonical compressed bytes accepted by [`Self::from_bytes`].
    pub fn to_bytes(self) -> [u8; ENCODED_VALUE_SIZE] {
        self.0.to_bytes()
    }
}
impl NonIdentityPallasPoint {
    /// Wraps a native point whose type guarantees it is not identity.
    pub const fn from_native(value: udon::curve::PallasAffine) -> Self {
        Self(value)
    }
    /// Returns the native point without decoding or normalization.
    pub const fn native(self) -> udon::curve::PallasPoint {
        self.0.to_point()
    }
    /// Returns the canonical compressed bytes accepted by [`Self::from_bytes`].
    pub fn to_bytes(self) -> [u8; ENCODED_VALUE_SIZE] {
        self.0.to_bytes()
    }
}
impl SpendValidatingKey {
    /// Checks the Orchard sign restriction on an already validated native point.
    pub fn from_native(value: udon::curve::PallasAffine) -> Result<Self, Error> {
        if value.coordinates().1.is_odd() {
            Err(Error::InvalidInput)
        } else {
            Ok(Self(value))
        }
    }
    /// Returns the native point without decoding or normalization.
    pub const fn native(self) -> udon::curve::PallasPoint {
        self.0.to_point()
    }
    /// Returns the canonical compressed bytes accepted by [`Self::from_bytes`].
    pub fn to_bytes(self) -> [u8; ENCODED_VALUE_SIZE] {
        self.0.to_bytes()
    }
}
