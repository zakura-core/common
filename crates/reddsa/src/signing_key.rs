// -*- mode: rust; -*-
//
// This file is part of reddsa.
// Copyright (c) 2019-2021 Zcash Foundation
// See LICENSE for licensing information.
//
// Authors:
// - Deirdre Connolly <deirdre@zfnd.org>
// - Henry de Valence <hdevalence@hdevalence.ca>

use core::{
    convert::{TryFrom, TryInto},
    fmt,
    marker::PhantomData,
};

use crate::{
    Error, Randomizer, SigType, Signature, SpendAuth, VerificationKey, private::SealedScalar,
};

use crate::backend::Point as _;
use rand_core::{CryptoRng, Rng};

/// A RedDSA signing key.
#[derive(Copy, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(try_from = "SerdeHelper"))]
#[cfg_attr(feature = "serde", serde(into = "SerdeHelper"))]
#[cfg_attr(feature = "serde", serde(bound = "T: SigType"))]
pub struct SigningKey<T: SigType> {
    sk: T::Scalar,
    pk: VerificationKey<T>,
}

impl<T: SigType> fmt::Debug for SigningKey<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SigningKey")
            .field("sk", &"<redacted>")
            .field("pk", &self.pk)
            .finish()
    }
}

/// Overwrites the secret scalar with zero. The verification key is public and
/// is left intact.
///
/// `SigningKey` is `Copy`, so this does not run on drop and does not reach
/// copies. Owners of a key erase their own copy.
#[cfg(feature = "zeroize-signing-key")]
impl<T: SigType> zeroize::Zeroize for SigningKey<T> {
    fn zeroize(&mut self) {
        self.sk.zeroize();
    }
}

impl<T: SigType> From<&SigningKey<T>> for VerificationKey<T> {
    fn from(sk: &SigningKey<T>) -> VerificationKey<T> {
        sk.pk
    }
}

impl<T: SigType> From<SigningKey<T>> for [u8; 32] {
    fn from(sk: SigningKey<T>) -> [u8; 32] {
        sk.sk.to_repr().as_ref().try_into().unwrap()
    }
}

impl<T: SigType> TryFrom<[u8; 32]> for SigningKey<T> {
    type Error = Error;

    fn try_from(bytes: [u8; 32]) -> Result<Self, Self::Error> {
        let mut repr = [0u8; 32];
        repr.as_mut().copy_from_slice(&bytes);
        let maybe_sk = T::Scalar::from_repr(repr);
        if let Some(sk) = maybe_sk {
            let pk = VerificationKey::from(&sk);
            Ok(SigningKey { sk, pk })
        } else {
            Err(Error::MalformedSigningKey)
        }
    }
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
struct SerdeHelper([u8; 32]);

impl<T: SigType> TryFrom<SerdeHelper> for SigningKey<T> {
    type Error = Error;

    fn try_from(helper: SerdeHelper) -> Result<Self, Self::Error> {
        helper.0.try_into()
    }
}

impl<T: SigType> From<SigningKey<T>> for SerdeHelper {
    fn from(sk: SigningKey<T>) -> Self {
        Self(sk.into())
    }
}

impl<T: SpendAuth> SigningKey<T> {
    /// Randomize this public key with the given `randomizer`.
    pub fn randomize(&self, randomizer: &Randomizer<T>) -> SigningKey<T> {
        let sk = self.sk + *randomizer;
        let pk = VerificationKey::from(&sk);
        SigningKey { sk, pk }
    }
}

impl<T: SigType> SigningKey<T> {
    /// Generate a new signing key.
    pub fn new<R: Rng + CryptoRng>(mut rng: R) -> SigningKey<T> {
        let sk = {
            let mut bytes = [0; 64];
            rng.fill_bytes(&mut bytes);
            T::Scalar::from_bytes_wide(&bytes)
        };
        let pk = VerificationKey::from(&sk);
        SigningKey { sk, pk }
    }

    /// Create a signature of type `T` on `msg` using this `SigningKey`.
    // Similar to signature::Signer but without boxed errors.
    pub fn sign<R: Rng + CryptoRng>(&self, mut rng: R, msg: &[u8]) -> Signature<T> {
        use crate::HStar;

        // Choose a byte sequence uniformly at random of length
        // (\ell_H + 128)/8 bytes.  For RedJubjub and RedPallas this is
        // (512 + 128)/8 = 80.
        let random_bytes = {
            let mut bytes = [0; 80];
            rng.fill_bytes(&mut bytes);
            bytes
        };

        let nonce = HStar::<T>::default()
            .update(&random_bytes[..])
            .update(&self.pk.bytes.bytes[..]) // XXX ugly
            .update(msg)
            .finalize();

        let r: T::Point = T::basepoint() * nonce;
        let r_bytes: [u8; 32] = r.to_bytes().as_ref().try_into().unwrap();

        let c = HStar::<T>::default()
            .update(&r_bytes[..])
            .update(&self.pk.bytes.bytes[..]) // XXX ugly
            .update(msg)
            .finalize();

        let s = nonce + (c * self.sk);
        let s_bytes = s.to_repr().as_ref().try_into().unwrap();

        Signature {
            r_bytes,
            s_bytes,
            _marker: PhantomData,
        }
    }
}

#[cfg(all(test, feature = "zeroize-signing-key"))]
mod zeroize_tests {
    use core::convert::TryFrom;

    use zeroize::Zeroize;

    use crate::{SigningKey, VerificationKey, sapling};

    #[test]
    fn zeroize_erases_the_secret_scalar_and_keeps_the_verification_key() {
        let mut bytes = [0u8; 32];
        bytes[0] = 7;
        let mut sk = SigningKey::<sapling::SpendAuth>::try_from(bytes).unwrap();
        let vk: VerificationKey<sapling::SpendAuth> = (&sk).into();

        sk.zeroize();

        assert_eq!(<[u8; 32]>::from(sk), [0; 32]);
        let vk_after: VerificationKey<sapling::SpendAuth> = (&sk).into();
        assert_eq!(<[u8; 32]>::from(vk_after), <[u8; 32]>::from(vk));
    }
}
