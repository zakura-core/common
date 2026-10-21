//! Orchard-compatible RedPallas signing and verification over Udon.
//!
//! [`SpendAuth`] and [`Binding`] select the RedDSA generators for spend
//! authorization and value commitment binding. Keys and signatures carry no
//! domain tag in their encodings; the caller selects the domain through the
//! type parameter. [`BatchItem`] retains that choice when combining domains.
//! Nonces and challenges use BLAKE2b-512 with personalization
//! `Zcash_RedPallasH`, reduced into the Pallas scalar field.
//!
//! # Caller requirements
//!
//! Arithmetic is variable-time: execution time and memory access can depend on
//! signing scalars, nonces, and key randomizers. Secret-key operations assume
//! an environment where attackers cannot observe those side channels. Keys are
//! copyable and are not zeroized on drop. Randomness must satisfy
//! [`RandomSource`]'s cryptographic requirements.
//!
//! Zero signing keys and identity verification keys are representable. This
//! module checks encodings and signature equations; callers enforce protocol
//! restrictions on keys, such as the nonidentity and sign restrictions of
//! [`crate::SpendValidatingKey`].
//!
//! Generator tables follow the primitive
//! [cache ownership](crate::primitives#lazy-data-and-ownership) policy: targets
//! with pointer atomics retain one table per domain for the process lifetime,
//! while targets without them build an owned table per access and drop it after
//! use. Racing first uses on atomic targets may build multiple candidates.
//! Signing and verification do not initialize proof workers, the structured
//! reference string (SRS), or circuit preparation.
//!
//! # Signing and randomization
//!
//! Randomizing a spend signing key and its verification key with the same
//! scalar gives a matching pair. This example adapts a caller-owned `rand`
//! source to [`RandomSource`].
//!
//! ```
//! use rand::Rng;
//! use zakura_sensei::{Fq, redpallas::{Binding, SigningKey, SpendAuth}};
//!
//! let mut rng = rand::rng();
//! let mut randomness = || Ok(rng.next_u64());
//! let key = SigningKey::<SpendAuth>::new(&mut randomness)?;
//! let mut alpha = [0; 32];
//! alpha[0] = 7;
//! let alpha = Fq::from_bytes(alpha)?;
//! let randomized = key.randomize(&alpha);
//! let verification_key = key.verification_key().randomize(&alpha);
//! assert_eq!(randomized.verification_key(), verification_key);
//! let signature = randomized.sign(&mut randomness, b"message")?;
//! verification_key.verify(b"message", &signature)?;
//!
//! // Batch items own the message hash, key, signature, and domain.
//! use zakura_sensei::redpallas::{BatchItem, verify_batch};
//! let binding = SigningKey::<Binding>::new(&mut randomness)?;
//! let binding_signature = binding.sign(&mut randomness, b"binding message")?;
//! let items = [
//!     BatchItem::new(&verification_key, &signature, b"message"),
//!     BatchItem::new(
//!         &binding.verification_key(), &binding_signature, b"binding message",
//!     ),
//! ];
//! verify_batch(&items, &mut randomness)?;
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

use crate::primitives::cache::{Cache as OnceBox, Cached};
use crate::{RandomSource, primitives::prepared::Generator};
use alloc::boxed::Box;
use alloc::{vec, vec::Vec};
use core::{fmt, marker::PhantomData};
use udon::{
    curve::{Pallas, PallasAffine, PallasPoint, PallasProjective},
    exec::{ExecutionOptions, SerialExecutor},
    field::{Fp, Fq},
    msm::{Bases, Input, ScalarStorage, Scratch},
};

mod sealed {
    pub trait Domain {
        const INDEX: usize;
    }
}

/// A sealed RedPallas signature domain.
///
/// Implemented only by [`SpendAuth`] and [`Binding`], which select distinct
/// generators. The domain is supplied by the caller, not decoded from bytes.
pub trait SigType: sealed::Domain + Copy + fmt::Debug + Eq + Send + Sync + 'static {}

/// Spend authorization signatures, with key randomization.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SpendAuth {}
/// Value commitment binding signatures.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Binding {}
impl sealed::Domain for SpendAuth {
    const INDEX: usize = 0;
}
impl sealed::Domain for Binding {
    const INDEX: usize = 1;
}
impl SigType for SpendAuth {}
impl SigType for Binding {}

/// RedPallas decoding, verification, and randomness failures.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Error {
    /// The signing scalar is not canonically encoded.
    MalformedSigningKey,
    /// The verification point is not canonically encoded.
    MalformedVerificationKey,
    /// The signature encoding or verification equation is invalid.
    InvalidSignature,
    /// The batch's storage dimensions cannot be represented.
    InvalidInput,
    /// The caller's randomness source failed.
    RngFailure,
    /// A batch weight was zero; retry with fresh randomness.
    RetryRandomness,
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
impl core::error::Error for Error {}

fn base(index: usize) -> PallasAffine {
    use sensei_shared::generators::{SPEND_AUTH_G_GENERATOR, VALUE_COMMIT_R_GENERATOR};
    [SPEND_AUTH_G_GENERATOR, VALUE_COMMIT_R_GENERATOR][index]
}
fn generator(index: usize) -> Cached<Generator<Pallas>> {
    static SPEND: OnceBox<Generator<Pallas>> = OnceBox::new();
    static BINDING: OnceBox<Generator<Pallas>> = OnceBox::new();
    [&SPEND, &BINDING][index].get_or_init(|| Box::new(Generator::new(base(index))))
}
fn hash(parts: &[&[u8]]) -> Fq {
    let mut state = blake2b_simd::Params::new()
        .hash_length(64)
        .personal(b"Zcash_RedPallasH")
        .to_state();
    for part in parts {
        state.update(part);
    }
    Fq::from_wide_bytes_reduced(
        state
            .finalize()
            .as_bytes()
            .try_into()
            .expect("64-byte hash"),
    )
}
fn random_bytes<const N: usize>(rng: &mut dyn RandomSource) -> Result<[u8; N], Error> {
    let mut bytes = [0; N];
    for chunk in bytes.chunks_exact_mut(8) {
        chunk.copy_from_slice(&rng.next_u64().map_err(|_| Error::RngFailure)?.to_le_bytes());
    }
    Ok(bytes)
}

/// A Pallas signing scalar and its derived verification key.
///
/// Zero is accepted. Copies contain the secret scalar and are not zeroized on
/// drop; [`core::fmt::Debug`] redacts it. See the module's
/// [caller requirements](crate::redpallas#caller-requirements) for timing
/// assumptions.
#[derive(Clone, Copy)]
pub struct SigningKey<T: SigType> {
    scalar: Fq,
    key: VerificationKey<T>,
}
impl<T: SigType> fmt::Debug for SigningKey<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SigningKey")
            .field("scalar", &"<redacted>")
            .field("key", &self.key)
            .finish()
    }
}
impl<T: SigType> SigningKey<T> {
    /// Constructs a signing key from a validated native scalar, including zero.
    pub fn from_native(scalar: crate::Fq) -> Self {
        Self::from_scalar(scalar.native())
    }
    fn from_scalar(scalar: Fq) -> Self {
        Self {
            scalar,
            key: VerificationKey::from_point(generator(T::INDEX).mul(&scalar).to_point()),
        }
    }
    /// Decodes a canonical little-endian scalar, including zero.
    ///
    /// Returns [`Error::MalformedSigningKey`] if the integer is at least the
    /// scalar-field modulus. Derives and caches the verification key.
    pub fn from_bytes(bytes: [u8; 32]) -> Result<Self, Error> {
        Fq::from_bytes(bytes)
            .map(Self::from_scalar)
            .ok_or(Error::MalformedSigningKey)
    }
    /// Samples a key by reducing 64 random bytes (eight little-endian words).
    ///
    /// `rng` must satisfy [`RandomSource`]. Returns [`Error::RngFailure`] on
    /// source failure; already consumed words are not restored. Zero is not
    /// rejected or resampled.
    pub fn new(rng: &mut dyn RandomSource) -> Result<Self, Error> {
        Ok(Self::from_scalar(Fq::from_wide_bytes_reduced(
            &random_bytes::<64>(rng)?,
        )))
    }
    /// Returns the secret scalar as a canonical 32-byte little-endian integer.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.scalar.to_bytes()
    }
    /// Returns the derived verification key.
    pub fn verification_key(&self) -> VerificationKey<T> {
        self.key
    }
    /// Signs arbitrary message bytes with fresh randomness.
    ///
    /// Consumes ten [`RandomSource`] words, each encoded little-endian in draw
    /// order, to form the 80-byte nonce randomness. Returns
    /// [`Error::RngFailure`] on source failure without returning a signature;
    /// consumed words are not restored. The key is unchanged.
    pub fn sign(&self, rng: &mut dyn RandomSource, message: &[u8]) -> Result<Signature<T>, Error> {
        let random = random_bytes::<80>(rng)?;
        let nonce = hash(&[&random, &self.key.bytes, message]);
        let r = generator(T::INDEX).mul(&nonce).to_point().to_bytes();
        let challenge = hash(&[&r, &self.key.bytes, message]);
        let s = nonce.add(&challenge.mul(&self.scalar)).to_bytes();
        let mut bytes = [0; 64];
        bytes[..32].copy_from_slice(&r);
        bytes[32..].copy_from_slice(&s);
        Ok(Signature::from_bytes(bytes))
    }
}
impl SigningKey<SpendAuth> {
    /// Adds `randomizer` modulo the scalar-field order and derives the new key.
    ///
    /// The original key is unchanged. The result may be zero. Its verification
    /// key equals [`VerificationKey::randomize`] applied to the original
    /// verification key with the same scalar.
    pub fn randomize(&self, randomizer: &crate::Fq) -> Self {
        Self::from_scalar(self.scalar.add(&randomizer.native()))
    }
}
impl<T: SigType> TryFrom<[u8; 32]> for SigningKey<T> {
    type Error = Error;
    fn try_from(bytes: [u8; 32]) -> Result<Self, Error> {
        Self::from_bytes(bytes)
    }
}
impl<T: SigType> From<SigningKey<T>> for [u8; 32] {
    fn from(key: SigningKey<T>) -> Self {
        key.to_bytes()
    }
}

/// A canonical Pallas verification point; identity is permitted.
///
/// Encoding validation does not impose a protocol's nonidentity or point-sign
/// restrictions. See the module's
/// [caller requirements](crate::redpallas#caller-requirements).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct VerificationKey<T: SigType> {
    point: PallasPoint,
    bytes: [u8; 32],
    marker: PhantomData<T>,
}
impl<T: SigType> VerificationKey<T> {
    /// Constructs a verification key from a validated native point, including identity.
    pub fn from_native(point: crate::PallasPoint) -> Self {
        Self::from_point(point.native())
    }
    /// Returns the validated native point without decoding its cached encoding.
    pub fn point(&self) -> crate::PallasPoint {
        crate::PallasPoint::from_native(self.point)
    }
    fn from_point(point: PallasPoint) -> Self {
        Self {
            bytes: point.to_bytes(),
            point,
            marker: PhantomData,
        }
    }
    /// Decodes a canonical compressed point, including identity.
    ///
    /// Uses the 32-byte Pallas encoding: little-endian x with the y sign in the
    /// high bit, and all-zero bytes for identity. Returns
    /// [`Error::MalformedVerificationKey`] for a noncanonical encoding or a
    /// value that does not decode to a curve point.
    pub fn from_bytes(bytes: [u8; 32]) -> Result<Self, Error> {
        PallasPoint::from_bytes(bytes)
            .map(Self::from_point)
            .ok_or(Error::MalformedVerificationKey)
    }
    /// Returns the canonical compressed point encoding.
    pub const fn to_bytes(&self) -> [u8; 32] {
        self.bytes
    }
    /// Checks canonical signature components and the RedPallas equation.
    ///
    /// Returns [`Error::InvalidSignature`] if either check fails. No randomness
    /// is required, and neither the key nor the signature is changed.
    pub fn verify(&self, message: &[u8], signature: &Signature<T>) -> Result<(), Error> {
        BatchItem::new(self, signature, message).verify()
    }
}
impl VerificationKey<SpendAuth> {
    /// Adds the spend generator multiplied by `randomizer` to this key.
    ///
    /// The original key is unchanged. Identity results are accepted. Matches
    /// [`SigningKey::randomize`] for the same scalar.
    pub fn randomize(&self, randomizer: &crate::Fq) -> Self {
        Self::from_point(
            self.point
                .to_projective()
                .add(&generator(0).mul(&randomizer.native()))
                .to_point(),
        )
    }
}
impl<T: SigType> From<&SigningKey<T>> for VerificationKey<T> {
    fn from(key: &SigningKey<T>) -> Self {
        key.key
    }
}
impl<T: SigType> TryFrom<[u8; 32]> for VerificationKey<T> {
    type Error = Error;
    fn try_from(bytes: [u8; 32]) -> Result<Self, Error> {
        Self::from_bytes(bytes)
    }
}
impl<T: SigType> From<VerificationKey<T>> for [u8; 32] {
    fn from(key: VerificationKey<T>) -> Self {
        key.bytes
    }
}

/// Raw signature bytes. Canonical `R` and `s` are checked during verification.
///
/// The first 32 bytes encode the nonce point `R` in compressed Pallas form;
/// the last 32 encode the response scalar `s` as a little-endian integer.
/// Neither component is reduced or otherwise changed when storing bytes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Signature<T: SigType> {
    bytes: [u8; 64],
    marker: PhantomData<T>,
}
impl<T: SigType> Signature<T> {
    /// Stores all 64 bytes without validation.
    ///
    /// Use [`VerificationKey::verify`] or [`verify_batch`] to validate the
    /// encoding and its signature equation. Infallible construction alone
    /// does not establish either property.
    pub const fn from_bytes(bytes: [u8; 64]) -> Self {
        Self {
            bytes,
            marker: PhantomData,
        }
    }
    /// Returns the original bytes, including for malformed signatures.
    pub const fn to_bytes(&self) -> [u8; 64] {
        self.bytes
    }
}
impl<T: SigType> From<[u8; 64]> for Signature<T> {
    fn from(bytes: [u8; 64]) -> Self {
        Self::from_bytes(bytes)
    }
}
impl<T: SigType> From<Signature<T>> for [u8; 64] {
    fn from(signature: Signature<T>) -> Self {
        signature.bytes
    }
}

/// An owned, prehashed verification item, usable in a mixed-domain batch.
///
/// Owns the key, signature, and challenge scalar, without retaining the message
/// or borrowing inputs. Construction hashes the message but does not validate
/// the signature. Use [`Self::verify`] or [`verify_batch`] for validation.
#[derive(Clone, Debug)]
pub struct BatchItem {
    key: PallasPoint,
    signature: [u8; 64],
    challenge: Fq,
    domain: usize,
}
impl BatchItem {
    /// Hashes the message now; the returned item borrows neither it nor the key.
    pub fn new<T: SigType>(
        key: &VerificationKey<T>,
        signature: &Signature<T>,
        message: &[u8],
    ) -> Self {
        Self {
            key: key.point,
            signature: signature.bytes,
            challenge: hash(&[&signature.bytes[..32], &key.bytes, message]),
            domain: T::INDEX,
        }
    }
    fn components(&self) -> Result<(PallasPoint, Fq), Error> {
        let r = PallasPoint::from_bytes(self.signature[..32].try_into().unwrap())
            .ok_or(Error::InvalidSignature)?;
        let s = Fq::from_bytes(self.signature[32..].try_into().unwrap())
            .ok_or(Error::InvalidSignature)?;
        Ok((r, s))
    }
    /// Verifies this prehashed item without randomness.
    ///
    /// Returns [`Error::InvalidSignature`] if the signature components are
    /// noncanonical or the verification equation fails.
    pub fn verify(&self) -> Result<(), Error> {
        let (r, s) = self.components()?;
        let result = generator(self.domain)
            .mul(&s)
            .sub(&self.key.mul_projective(&self.challenge))
            .sub(&r.to_projective());
        if result.is_identity() {
            Ok(())
        } else {
            Err(Error::InvalidSignature)
        }
    }
}

/// Verifies a batch that may contain both [`SpendAuth`] and [`Binding`] items.
///
/// Empty batches succeed and singleton batches use [`BatchItem::verify`];
/// neither consumes randomness. Larger batches validate every signature's
/// encoding before drawing independent nonzero 128-bit weights, using two
/// little-endian [`RandomSource`] words per item in slice order. Soundness
/// requires fresh cryptographically secure weights independent of all items;
/// predictable weights can allow invalid signatures to cancel in the equation.
///
/// Returns [`Error::InvalidSignature`] for invalid encodings or a failed batch
/// equation, [`Error::InvalidInput`] for unrepresentable storage dimensions,
/// and [`Error::RngFailure`] if the source fails. A zero weight returns
/// [`Error::RetryRandomness`] without resampling; retry the entire batch with
/// fresh randomness. Errors leave `items` unchanged but do not restore any
/// consumed randomness. An invalid batch does not identify its failing items.
///
/// Allocates temporary storage proportional to the number of items. Dimension
/// checks do not guarantee sufficient memory; allocation failure follows the
/// allocator's behavior.
pub fn verify_batch(items: &[BatchItem], rng: &mut dyn RandomSource) -> Result<(), Error> {
    match items {
        [] => return Ok(()),
        [item] => return item.verify(),
        _ => {}
    }
    let terms = items
        .len()
        .checked_mul(2)
        .and_then(|n| n.checked_add(2))
        .ok_or(Error::InvalidInput)?;
    if terms > isize::MAX as usize / core::mem::size_of::<PallasPoint>() {
        return Err(Error::InvalidInput);
    }
    let decoded = items
        .iter()
        .map(BatchItem::components)
        .collect::<Result<Vec<_>, _>>()?;
    let mut bases = Vec::with_capacity(terms);
    let mut scalars = Vec::with_capacity(terms);
    let mut sums = [Fq::ZERO; 2];
    for (item, (r, s)) in items.iter().zip(decoded) {
        let bytes = random_bytes::<16>(rng)?;
        let weight: Fq = Fq::from_bytes_reduced(&bytes);
        if weight.is_zero() {
            return Err(Error::RetryRandomness);
        }
        sums[item.domain] = sums[item.domain].add(&weight.mul(&s));
        bases.extend([r, item.key]);
        scalars.extend([weight.neg(), weight.mul(&item.challenge).neg()]);
    }
    bases.extend([base(0).to_point(), base(1).to_point()]);
    scalars.extend(sums);
    let input = Input::new(Bases::Points(&bases), &scalars);
    let options = ExecutionOptions::default();
    let sizes = input
        .requirements(options)
        .map_err(|_| Error::InvalidInput)?;
    let mut records = vec![ScalarStorage::ZERO; sizes.scalars()];
    let mut digits = vec![0; sizes.digits()];
    let mut affine = vec![PallasAffine::GENERATOR; sizes.affine()];
    let mut projective = vec![PallasProjective::IDENTITY; sizes.projective()];
    let mut fields = vec![Fp::ZERO; sizes.field()];
    let mut indices = vec![0; sizes.indices()];
    let result = input
        .execute(
            options,
            &SerialExecutor,
            Scratch::new(
                &mut records,
                &mut digits,
                &mut affine,
                &mut projective,
                &mut fields,
                &mut indices,
            ),
        )
        .map_err(|_| Error::InvalidInput)?;
    if result.is_identity() {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}
