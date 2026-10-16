//! Minimal RedPallas types with private arithmetic supplied by the selected backend.
use crate::backend::pallas;

use crate::backend::prelude::*;
use core::{cmp::Ordering, marker::PhantomData};
use rand::{CryptoRng, Rng};

use crate::backend::reddsa as raw;

use raw::orchard::{Binding as RawBinding, SpendAuth as RawSpendAuth};

#[cfg(feature = "std")]
pub(crate) type BatchItem = raw::batch::Item<RawSpendAuth, RawBinding>;
/// The scalar randomizer of an Orchard spend authorization key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpendAuthRandomizer(pallas::Scalar);

impl SpendAuthRandomizer {
    /// Samples a randomizer from a cryptographically secure source.
    pub fn random(mut rng: impl CryptoRng) -> Self {
        Self(pallas::Scalar::random(&mut rng))
    }

    /// Decodes the canonical scalar encoding used in PCZTs.
    pub fn from_bytes(bytes: [u8; 32]) -> subtle::CtOption<Self> {
        pallas::Scalar::from_repr(bytes).map(Self)
    }

    /// Returns the canonical scalar encoding used in PCZTs.
    pub fn to_bytes(self) -> [u8; 32] {
        self.0.to_repr()
    }

    /// Reads a canonical randomizer.
    pub fn read(mut reader: impl corez::io::Read) -> corez::io::Result<Self> {
        let mut bytes = [0; 32];
        reader.read_exact(&mut bytes)?;
        Self::from_bytes(bytes).into_option().ok_or_else(|| {
            corez::io::Error::new(
                corez::io::ErrorKind::InvalidData,
                "noncanonical spend authorization randomizer",
            )
        })
    }

    /// Writes the canonical randomizer encoding.
    pub fn write(&self, mut writer: impl corez::io::Write) -> corez::io::Result<()> {
        writer.write_all(&self.to_bytes())
    }

    pub(crate) fn from_scalar(scalar: pallas::Scalar) -> Self {
        Self(scalar)
    }
    pub(crate) fn scalar(self) -> pallas::Scalar {
        self.0
    }
}

/// A sealed Orchard signature domain.
pub trait SigType: private::Sealed + Clone + core::fmt::Debug {}

/// The Orchard spend authorization signature domain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpendAuth {}
impl SigType for SpendAuth {}

/// The Orchard binding signature domain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Binding {}
impl SigType for Binding {}

mod private {
    // A supertrait's associated types remain nameable downstream as T::Raw even
    // when its module is private. Keep engine types in the private key storage.
    pub trait Sealed {
        const SPEND_AUTH: bool;
    }
    impl Sealed for super::SpendAuth {
        const SPEND_AUTH: bool = true;
    }
    impl Sealed for super::Binding {
        const SPEND_AUTH: bool = false;
    }
}

#[derive(Clone, Debug)]
enum SigningKeyInner {
    SpendAuth(raw::SigningKey<RawSpendAuth>),
    Binding(raw::SigningKey<RawBinding>),
}

/// A RedPallas signing key.
#[derive(Clone, Debug)]
pub struct SigningKey<T: SigType>(SigningKeyInner, PhantomData<T>);

impl<T: SigType> From<SigningKey<T>> for [u8; 32] {
    fn from(sk: SigningKey<T>) -> Self {
        (&sk).into()
    }
}
impl<T: SigType> From<&SigningKey<T>> for [u8; 32] {
    fn from(sk: &SigningKey<T>) -> Self {
        match &sk.0 {
            SigningKeyInner::SpendAuth(sk) => (*sk).into(),
            SigningKeyInner::Binding(sk) => (*sk).into(),
        }
    }
}
impl<T: SigType> TryFrom<[u8; 32]> for SigningKey<T> {
    type Error = Error;
    fn try_from(bytes: [u8; 32]) -> Result<Self, Error> {
        let key = if T::SPEND_AUTH {
            bytes.try_into().map(SigningKeyInner::SpendAuth)
        } else {
            bytes.try_into().map(SigningKeyInner::Binding)
        };
        key.map(|key| Self(key, PhantomData))
            .map_err(|_| Error::MalformedSigningKey)
    }
}
impl<T: SigType> SigningKey<T> {
    pub(crate) fn from_scalar(scalar: pallas::Scalar) -> Self {
        {
            scalar
                .to_repr()
                .try_into()
                .expect("canonical signing scalar")
        }
    }
    /// Signs `msg` using fresh randomness from `rng`.
    pub fn sign<R: Rng + CryptoRng>(&self, mut rng: R, msg: &[u8]) -> Signature<T> {
        let bytes = match &self.0 {
            SigningKeyInner::SpendAuth(key) => key.sign(&mut rng, msg).into(),
            SigningKeyInner::Binding(key) => key.sign(&mut rng, msg).into(),
        };
        Signature(bytes, PhantomData)
    }
}
impl SigningKey<SpendAuth> {
    /// Randomizes this spend authorization key.
    pub fn randomize(&self, randomizer: &SpendAuthRandomizer) -> Self {
        let SigningKeyInner::SpendAuth(key) = &self.0 else {
            unreachable!("domain is fixed at construction")
        };
        Self(
            SigningKeyInner::SpendAuth(key.randomize(&randomizer.0)),
            PhantomData,
        )
    }
}

#[derive(Clone, Debug)]
enum VerificationKeyInner {
    SpendAuth(raw::VerificationKey<RawSpendAuth>),
    Binding(raw::VerificationKey<RawBinding>),
}

/// A RedPallas verification key.
#[derive(Clone, Debug)]
pub struct VerificationKey<T: SigType>(VerificationKeyInner, PhantomData<T>);
impl<T: SigType> From<VerificationKey<T>> for [u8; 32] {
    fn from(vk: VerificationKey<T>) -> Self {
        (&vk).into()
    }
}
impl<T: SigType> From<&VerificationKey<T>> for [u8; 32] {
    fn from(vk: &VerificationKey<T>) -> Self {
        match &vk.0 {
            VerificationKeyInner::SpendAuth(vk) => (*vk).into(),
            VerificationKeyInner::Binding(vk) => (*vk).into(),
        }
    }
}
impl<T: SigType> TryFrom<[u8; 32]> for VerificationKey<T> {
    type Error = Error;
    fn try_from(bytes: [u8; 32]) -> Result<Self, Error> {
        let key = if T::SPEND_AUTH {
            bytes.try_into().map(VerificationKeyInner::SpendAuth)
        } else {
            bytes.try_into().map(VerificationKeyInner::Binding)
        };
        key.map(|key| Self(key, PhantomData))
            .map_err(|_| Error::MalformedVerificationKey)
    }
}
impl<T: SigType> From<&SigningKey<T>> for VerificationKey<T> {
    fn from(sk: &SigningKey<T>) -> Self {
        let key = match &sk.0 {
            SigningKeyInner::SpendAuth(sk) => VerificationKeyInner::SpendAuth(sk.into()),
            SigningKeyInner::Binding(sk) => VerificationKeyInner::Binding(sk.into()),
        };
        Self(key, PhantomData)
    }
}
impl<T: SigType> PartialEq for VerificationKey<T> {
    fn eq(&self, other: &Self) -> bool {
        <[u8; 32]>::from(self) == <[u8; 32]>::from(other)
    }
}
impl<T: SigType> Eq for VerificationKey<T> {}
impl<T: SigType> PartialOrd for VerificationKey<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl<T: SigType> Ord for VerificationKey<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        <[u8; 32]>::from(self).cmp(&<[u8; 32]>::from(other))
    }
}
impl<T: SigType> VerificationKey<T> {
    pub(crate) fn from_point(point: pallas::Point) -> Self {
        {
            point
                .to_bytes()
                .try_into()
                .expect("canonical verification point")
        }
    }

    /// Verifies a signature over `msg`.
    pub fn verify(&self, msg: &[u8], signature: &Signature<T>) -> Result<(), Error> {
        match &self.0 {
            VerificationKeyInner::SpendAuth(key) => key.verify(msg, &signature.0.into()),
            VerificationKeyInner::Binding(key) => key.verify(msg, &signature.0.into()),
        }
        .map_err(|_| Error::InvalidSignature)
    }
    /// Whether this is the identity Pallas point, which is invalid as an action's `rk`.
    pub fn is_identity(&self) -> bool {
        <[u8; 32]>::from(self) == [0; 32]
    }
}
impl VerificationKey<SpendAuth> {
    #[cfg(test)]
    pub(crate) fn dummy() -> Self {
        Self::from(&SigningKey::from_scalar(pallas::Scalar::random(
            &mut crate::rng_compat::OsRng,
        )))
    }
    /// Randomizes this spend authorization verification key.
    pub fn randomize(&self, randomizer: &SpendAuthRandomizer) -> Self {
        let VerificationKeyInner::SpendAuth(key) = &self.0 else {
            unreachable!("domain is fixed at construction")
        };
        Self(
            VerificationKeyInner::SpendAuth(key.randomize(&randomizer.0)),
            PhantomData,
        )
    }
    #[cfg(feature = "std")]
    pub(crate) fn create_batch_item<M: AsRef<[u8]>>(
        &self,
        sig: Signature<SpendAuth>,
        msg: &M,
    ) -> BatchItem {
        let VerificationKeyInner::SpendAuth(key) = &self.0 else {
            unreachable!("domain is fixed at construction")
        };

        BatchItem::from_spendauth((*key).into(), sig.0.into(), msg)
    }
}
impl VerificationKey<Binding> {
    #[cfg(feature = "std")]
    pub(crate) fn create_batch_item<M: AsRef<[u8]>>(
        &self,
        sig: Signature<Binding>,
        msg: &M,
    ) -> BatchItem {
        let VerificationKeyInner::Binding(key) = &self.0 else {
            unreachable!("domain is fixed at construction")
        };

        BatchItem::from_binding((*key).into(), sig.0.into(), msg)
    }
}

/// A RedPallas signature in its canonical wire representation.
#[derive(Debug, Clone)]
pub struct Signature<T: SigType>([u8; 64], PhantomData<T>);
impl<T: SigType> From<[u8; 64]> for Signature<T> {
    fn from(bytes: [u8; 64]) -> Self {
        Self(bytes, PhantomData)
    }
}
impl<T: SigType> From<&Signature<T>> for [u8; 64] {
    fn from(sig: &Signature<T>) -> Self {
        sig.0
    }
}

#[cfg(feature = "std")]
pub(crate) fn verify_batch(items: &[BatchItem], mut rng: impl CryptoRng) -> Result<(), Error> {
    {
        let mut verifier = raw::batch::Verifier::new();
        for item in items {
            verifier.queue(item.clone());
        }
        verifier
            .verify(&mut rng)
            .map_err(|_| Error::InvalidSignature)
    }
}
use core::fmt;

/// An error related to RedDSA signatures.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Error {
    /// The encoding of a signing key was malformed.
    MalformedSigningKey,
    /// The encoding of a verification key was malformed.
    MalformedVerificationKey,
    /// Signature verification failed.
    InvalidSignature,
}

impl core::error::Error for Error {}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MalformedSigningKey => write!(f, "Malformed signing key encoding."),
            Self::MalformedVerificationKey => write!(f, "Malformed verification key encoding."),
            Self::InvalidSignature => write!(f, "Invalid signature."),
        }
    }
}
/// Generators for property testing.
#[cfg(any(test, feature = "test-dependencies"))]
#[cfg_attr(docsrs, doc(cfg(feature = "test-dependencies")))]
pub mod testing {
    #[allow(unused_imports)]
    use crate::backend::prelude::*;
    use proptest::prelude::*;

    use super::{Binding, SigningKey, SpendAuth, VerificationKey};

    /// Generate a canonical Orchard spend authorization randomizer.
    pub fn arb_spend_auth_randomizer() -> impl Strategy<Value = super::SpendAuthRandomizer> {
        use crate::backend::prelude::*;
        any::<[u8; 64]>().prop_map(|bytes| {
            super::SpendAuthRandomizer::from_scalar(
                crate::backend::pallas::Scalar::from_uniform_bytes(&bytes),
            )
        })
    }

    prop_compose! {
        /// Generate a uniformly distributed RedDSA spend authorization signing key.
        pub fn arb_spendauth_signing_key()(
            sk in prop::array::uniform32(prop::num::u8::ANY)
                .prop_map(SigningKey::try_from)
                .prop_filter("Values must be parseable as valid signing keys", |r| r.is_ok())
        ) -> SigningKey<SpendAuth> {
            sk.unwrap()
        }
    }

    prop_compose! {
        /// Generate a uniformly distributed RedDSA binding signing key.
        pub fn arb_binding_signing_key()(
            sk in prop::array::uniform32(prop::num::u8::ANY)
                .prop_map(SigningKey::try_from)
                .prop_filter("Values must be parseable as valid signing keys", |r| r.is_ok())
        ) -> SigningKey<Binding> {
            sk.unwrap()
        }
    }

    prop_compose! {
        /// Generate a uniformly distributed RedDSA spend authorization verification key.
        pub fn arb_spendauth_verification_key()(sk in arb_spendauth_signing_key()) -> VerificationKey<SpendAuth> {
            VerificationKey::from(&sk)
        }
    }

    prop_compose! {
        /// Generate a uniformly distributed RedDSA binding verification key.
        pub fn arb_binding_verification_key()(sk in arb_binding_signing_key()) -> VerificationKey<Binding> {
            VerificationKey::from(&sk)
        }
    }

    prop_compose! {
        /// Generate a uniformly distributed valid RedDSA spend authorization key pair
        /// (rsk, rk), with nonidentity rk and nonzero rsk.
        pub fn arb_valid_spendauth_keypair()(
            rsk_and_rk in arb_spendauth_signing_key()
                .prop_filter_map("rk must not be the identity", |sk| {
                    let vk = VerificationKey::from(&sk);
                    (!vk.is_identity()).then_some((sk, vk))
                }),
        ) -> (SigningKey<SpendAuth>, VerificationKey<SpendAuth>) {
            rsk_and_rk
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        SpendAuthRandomizer, VerificationKey,
        testing::{arb_spend_auth_randomizer, arb_spendauth_signing_key},
    };
    use proptest::prelude::*;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    /// Exercise empty messages through the largest short application message in this test.
    const MESSAGE_LENGTH_LIMIT: usize = 128;

    proptest! {
        #[test]
        fn randomized_keys_and_canonical_codec_agree(
            key in arb_spendauth_signing_key(),
            randomizer in arb_spend_auth_randomizer(),
            seed in any::<[u8; 32]>(),
            message in prop::collection::vec(any::<u8>(), 0..MESSAGE_LENGTH_LIMIT),
        ) {
            let mut encoded = alloc::vec::Vec::new();
            randomizer.write(&mut encoded).unwrap();
            let decoded = SpendAuthRandomizer::read(encoded.as_slice()).unwrap();
            prop_assert_eq!(decoded, randomizer);
            prop_assert_eq!(encoded.as_slice(), randomizer.to_bytes());
            let signing_key = key.randomize(&decoded);
            let verifying_key = VerificationKey::from(&key).randomize(&randomizer);
            prop_assert_eq!(&VerificationKey::from(&signing_key), &verifying_key);
            let signature = signing_key.sign(ChaCha20Rng::from_seed(seed), &message);
            prop_assert!(verifying_key.verify(&message, &signature).is_ok());
            let mut changed = message;
            changed.push(0);
            prop_assert!(verifying_key.verify(&changed, &signature).is_err());
        }
    }
}
