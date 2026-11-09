//! The canonical single-signer body that an address commits to.
//!
//! A PQ output commits to a body and nothing else, so the same thirty-two bytes could stand
//! for any script at all. That is fine for a receiver who keeps its script, and wrong for an
//! address: an address a wallet hands out should be reproducible from the wallet's seed, so
//! that restoring the seed finds the funds without a separate copy of the script. This module
//! fixes the one body shape that makes that true — a single public key and a signature check —
//! so an address is a function of the derived key alone:
//!
//! ```text
//! seed -> derived key -> body -> commitment -> address
//! ```
//!
//! The body is `PUSH<n>(public key) OP_CHECKSIG`, thirty-four bytes for SHA2-128f and fifty for
//! SHA2-192s. It carries no format or scheme of its own: the output names both and binds them
//! into the signing context, so the same body under a different scheme is a different output
//! that a signature for one cannot authorize.
//!
//! Nothing here restricts what a body may be. Multiple signers, timelocks and recovery branches
//! remain ordinary bodies, indistinguishable from this one in an output or an address, and the
//! wallet that commits to one of those owns its backup. This module only makes the simple case
//! derivable.

use alloc::vec::Vec;
use core::fmt;

use zcash_script::script::Code;

use crate::util::sha256;

use super::{ParameterSet, output};

/// `OP_CHECKSIG`, which the PQ evaluator answers with the output's parameter set.
const OP_CHECKSIG: u8 = 0xac;

/// The largest number of bytes a single byte can push directly.
///
/// A public key of at most this length is pushed by the byte naming its length, exactly as the
/// commitment's thirty-two is pushed by `0x20`, so the body needs no `OP_PUSHDATA` prefix and
/// has one minimal encoding.
const MAX_DIRECT_PUSH: usize = 0x4b;

const _: () = assert!(ParameterSet::Sha2_128f.public_key_bytes() <= MAX_DIRECT_PUSH);
const _: () = assert!(ParameterSet::Sha2_192s.public_key_bytes() <= MAX_DIRECT_PUSH);

/// A public key that is not the length its parameter set defines.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key length does not match the parameter set's.
    PublicKeyLength {
        /// The length this parameter set's keys have.
        expected: usize,
        /// The length supplied.
        actual: usize,
    },
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::PublicKeyLength { expected, actual } => write!(
                f,
                "public key is {actual} bytes, but keys for this parameter set are {expected} bytes"
            ),
        }
    }
}

impl core::error::Error for Error {}

/// The canonical body for a single signer holding `public_key`.
///
/// The key must be exactly the parameter set's public-key length. A key of any other length is
/// rejected here rather than committed to, because the evaluator aborts a spend whose key is
/// the wrong length for the output's parameter set: committing to one would make an output that
/// looks ordinary and can never be spent.
pub fn single_key_body(parameters: ParameterSet, public_key: &[u8]) -> Result<Code, Error> {
    let expected = parameters.public_key_bytes();
    if public_key.len() != expected {
        return Err(Error::PublicKeyLength {
            expected,
            actual: public_key.len(),
        });
    }

    let mut bytes = Vec::with_capacity(expected + 2);
    // The key's length is also its minimal push opcode, as the commitment's thirty-two is.
    bytes.push(expected as u8);
    bytes.extend_from_slice(public_key);
    bytes.push(OP_CHECKSIG);
    Ok(Code(bytes))
}

/// The commitment an output carries for a single signer holding `public_key`.
pub fn single_key_commitment(
    parameters: ParameterSet,
    public_key: &[u8],
) -> Result<[u8; 32], Error> {
    single_key_body(parameters, public_key).map(|body| sha256::hash(&body.0))
}

/// The complete output script paying a single signer holding `public_key`.
///
/// This is what a sender writes for an address that carries this key's commitment, and it is
/// byte-identical to passing [`single_key_commitment`] to
/// [`output::output_script_from_commitment`] — which is the path a sender actually takes, since
/// a sender is given the commitment and never sees the key.
pub fn single_key_output_script(
    parameters: ParameterSet,
    public_key: &[u8],
) -> Result<Code, Error> {
    single_key_commitment(parameters, public_key)
        .map(|commitment| output::output_script_from_commitment(parameters, &commitment))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pq::{sha2_128f, sha2_192s};
    use zcash_address::unified::{Address, Container, Encoding, PqScheme, Receiver};
    use zcash_protocol::consensus::NetworkType;

    fn key_128f() -> [u8; sha2_128f::PUBLIC_KEY_BYTES] {
        sha2_128f::SigningKey::from_seed(&[9; sha2_128f::SEED_BYTES]).public_key()
    }

    fn key_192s() -> [u8; sha2_192s::PUBLIC_KEY_BYTES] {
        sha2_192s::SigningKey::from_seed(&[9; sha2_192s::SEED_BYTES]).public_key()
    }

    #[test]
    fn body_is_a_minimal_push_and_a_signature_check() {
        for (parameters, key) in [
            (ParameterSet::Sha2_128f, key_128f().to_vec()),
            (ParameterSet::Sha2_192s, key_192s().to_vec()),
        ] {
            let body = single_key_body(parameters, &key).expect("key length matches");
            assert_eq!(body.0.len(), key.len() + 2);
            assert_eq!(usize::from(body.0[0]), key.len());
            assert_eq!(&body.0[1..body.0.len() - 1], &key[..]);
            assert_eq!(*body.0.last().expect("body is not empty"), OP_CHECKSIG);
        }
    }

    #[test]
    fn body_lengths_are_the_documented_ones() {
        assert_eq!(
            single_key_body(ParameterSet::Sha2_128f, &key_128f())
                .expect("key length matches")
                .0
                .len(),
            34
        );
        assert_eq!(
            single_key_body(ParameterSet::Sha2_192s, &key_192s())
                .expect("key length matches")
                .0
                .len(),
            50
        );
    }

    #[test]
    fn commitment_hashes_the_body_alone() {
        let key = key_128f();
        let body = single_key_body(ParameterSet::Sha2_128f, &key).expect("key length matches");
        assert_eq!(
            single_key_commitment(ParameterSet::Sha2_128f, &key).expect("key length matches"),
            sha256::hash(&body.0)
        );
    }

    #[test]
    fn output_script_matches_the_payer_path() {
        for (parameters, key) in [
            (ParameterSet::Sha2_128f, key_128f().to_vec()),
            (ParameterSet::Sha2_192s, key_192s().to_vec()),
        ] {
            let commitment = single_key_commitment(parameters, &key).expect("key length matches");
            assert_eq!(
                single_key_output_script(parameters, &key)
                    .expect("key length matches")
                    .0,
                output::output_script_from_commitment(parameters, &commitment).0
            );
        }
    }

    #[test]
    fn output_script_parses_as_the_same_output() {
        for (parameters, key) in [
            (ParameterSet::Sha2_128f, key_128f().to_vec()),
            (ParameterSet::Sha2_192s, key_192s().to_vec()),
        ] {
            let script = single_key_output_script(parameters, &key).expect("key length matches");
            let parsed = output::parse_output(&script)
                .expect("the script is a well-formed PQ output")
                .expect("the script is in the PQ namespace");
            assert_eq!(parsed.parameters(), parameters);
            assert_eq!(
                parsed.commitment(),
                &single_key_commitment(parameters, &key).expect("key length matches")
            );
        }
    }

    #[test]
    fn the_other_parameter_set_s_key_is_rejected() {
        assert_eq!(
            single_key_body(ParameterSet::Sha2_128f, &key_192s()).unwrap_err(),
            Error::PublicKeyLength {
                expected: sha2_128f::PUBLIC_KEY_BYTES,
                actual: sha2_192s::PUBLIC_KEY_BYTES,
            }
        );
        assert_eq!(
            single_key_body(ParameterSet::Sha2_192s, &key_128f()).unwrap_err(),
            Error::PublicKeyLength {
                expected: sha2_192s::PUBLIC_KEY_BYTES,
                actual: sha2_128f::PUBLIC_KEY_BYTES,
            }
        );
    }

    #[test]
    fn the_address_scheme_mapping_is_total() {
        for parameters in [ParameterSet::Sha2_128f, ParameterSet::Sha2_192s] {
            assert_eq!(
                ParameterSet::from_address_scheme(parameters.address_scheme()),
                parameters
            );
        }
        for scheme in [PqScheme::Sha2_128f, PqScheme::Sha2_192s] {
            assert_eq!(
                ParameterSet::from_address_scheme(scheme).address_scheme(),
                scheme
            );
        }
    }

    #[test]
    fn a_public_key_reaches_an_output_through_a_unified_address() {
        // The whole receiving path, with no derivation in it: a key, the canonical body it
        // implies, the commitment an address carries, and the output a payer writes from that
        // address. The last equality is what makes the seed-recovery claim mechanical — an
        // address is a function of the key, so a wallet that can rederive the key can rederive
        // the address and recognize what was paid to it.
        for (parameters, key) in [
            (ParameterSet::Sha2_128f, key_128f().to_vec()),
            (ParameterSet::Sha2_192s, key_192s().to_vec()),
        ] {
            let commitment = single_key_commitment(parameters, &key).expect("key length matches");

            let ua = Address::try_from_items(vec![
                // A shielded receiver, which every Revision 0 unified address must carry. Its
                // bytes are not a valid Orchard address and nothing here parses them as one.
                Receiver::Orchard([0; 43]),
                Receiver::PqTransparent {
                    scheme: parameters.address_scheme(),
                    commitment,
                },
            ])
            .expect("a PQ receiver beside a shielded one is well formed");

            let encoded = ua.encode(&NetworkType::Main);
            let (network, decoded) = Address::decode(&encoded).expect("the address decodes");
            assert_eq!(network, NetworkType::Main);

            let paid = decoded
                .items()
                .into_iter()
                .find_map(|receiver| match receiver {
                    Receiver::PqTransparent { scheme, commitment } => {
                        Some(output::output_script_from_commitment(
                            ParameterSet::from_address_scheme(scheme),
                            &commitment,
                        ))
                    }
                    _ => None,
                })
                .expect("the decoded address still offers the PQ receiver");

            assert_eq!(
                paid.0,
                single_key_output_script(parameters, &key)
                    .expect("key length matches")
                    .0
            );
        }
    }

    #[test]
    fn an_empty_key_is_rejected() {
        assert_eq!(
            single_key_body(ParameterSet::Sha2_128f, &[]).unwrap_err(),
            Error::PublicKeyLength {
                expected: sha2_128f::PUBLIC_KEY_BYTES,
                actual: 0,
            }
        );
    }
}
