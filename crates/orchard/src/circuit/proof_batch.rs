//! Verification of multiple proofs under one version-bound Orchard key.

use alloc::vec::Vec;

#[cfg(feature = "backend-halo2")]
use crate::backend::halo2_proofs::plonk;
#[cfg(feature = "backend-halo2")]
use crate::backend::pasta_curves::vesta;
use rand::{CryptoRng, Rng};

use super::{Instance, Proof, VerifyingKey};

/// A batch of Orchard proofs bound to one verifying key.
///
/// The compiled backend performs all verification. This checks proofs and
/// public instances. Use [`crate::bundle::BatchValidator`] to check the
/// bundles' RedPallas signatures as well.
#[derive(Debug)]
pub struct ProofBatch<'a> {
    vk: &'a VerifyingKey,
    #[cfg(feature = "backend-halo2")]
    native: plonk::BatchVerifier<vesta::Affine>,
    #[cfg(feature = "backend-sensei")]
    sensei: Vec<(Proof, Vec<Instance>)>,
    invalid: bool,
}

impl<'a> ProofBatch<'a> {
    /// Creates an empty batch whose proofs will be verified against `vk`.
    pub fn new(vk: &'a VerifyingKey) -> Self {
        Self {
            vk,
            #[cfg(feature = "backend-halo2")]
            native: plonk::BatchVerifier::new(),
            #[cfg(feature = "backend-sensei")]
            sensei: Vec::new(),
            invalid: false,
        }
    }

    /// Queues a proof and its ordered public instances.
    ///
    /// Invalid proofs, empty instances, and restrictions unsupported by the key
    /// cause [`Self::validate`] to return `false`.
    pub fn add_proof(&mut self, proof: &Proof, instances: Vec<Instance>) {
        if instances.is_empty()
            || (instances.iter().any(Instance::cross_address_disabled)
                && !self.vk.supports_cross_address_restriction())
        {
            self.invalid = true;
            return;
        }
        #[cfg(feature = "backend-sensei")]
        self.sensei.push((proof.clone(), instances));
        #[cfg(feature = "backend-halo2")]
        proof.add_to_batch(&mut self.native, instances);
    }

    /// Verifies every queued proof, using fresh cryptographic randomness for
    /// batch weights. An empty batch succeeds without consuming randomness.
    ///
    /// Sensei uses the supplied RNG, which must be independent of the submitted
    /// proofs; Halo2 uses system randomness internally. Returns `false` on any
    /// verification failure, including Sensei rejecting a zero batch weight.
    pub fn validate<R: Rng + CryptoRng>(self, rng: R) -> bool {
        if self.invalid {
            return false;
        }
        #[cfg(feature = "backend-sensei")]
        {
            super::verify_batch(self.vk.circuit_version(), &self.sensei, rng)
        }
        #[cfg(feature = "backend-halo2")]
        {
            // Halo2 obtains its batch randomness internally.
            let _ = rng;
            self.native.finalize(&self.vk.params, &self.vk.vk)
        }
    }
}
