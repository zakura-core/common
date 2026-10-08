#![no_std]
#![deny(missing_docs)]

//! FROST threshold signatures compatible with RedJubjub and RedPallas.
//!
//! The ciphersuites live in [`redjubjub`] and [`redpallas`]. This crate owns
//! threshold signing independently of the ordinary RedDSA implementation.

extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

mod rng_compat;

pub mod redjubjub;
pub mod redpallas;

// Obtain the protocol generator through RedDSA's existing public key API.
// This avoids copying basepoint constants or exposing its private traits.
fn spend_auth_generator<S: reddsa::SpendAuth>() -> [u8; 32] {
    let mut scalar_one = [0; 32];
    scalar_one[0] = 1;
    let key = reddsa::SigningKey::<S>::try_from(scalar_one)
        .expect("one is a canonical scalar in both RedDSA ciphersuites");
    <reddsa::VerificationKey<S> as From<&reddsa::SigningKey<S>>>::from(&key).into()
}

fn hash_to_bytes(personalization: &[u8; 16], message: &[u8]) -> [u8; 64] {
    *blake2b_simd::Params::new()
        .hash_length(64)
        .personal(personalization)
        .to_state()
        .update(message)
        .finalize()
        .as_array()
}
