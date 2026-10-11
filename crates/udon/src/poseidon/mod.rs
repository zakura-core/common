//! Poseidon parameters over the Pasta fields.
//!
//! Width 5 / rate 4 and width 3 / rate 2 instances, with the `x^5` S-box,
//! 8 full rounds, and 56 partial rounds. Round constants and MDS matrices use the
//! Hades/Poseidon reference generator
//! (<https://extgit.isec.tugraz.at/krypto/hadeshash>, through the
//! `daira/pasta-hadeshash` fork). This module carries the parameters only.
//! The permutation and the sponge built over them belong to the protocol
//! that hashes with them. This entire module, including its
//! [`PoseidonPermutation`] trait and its consumer views, requires the `poseidon`
//! feature. That feature enables the unstable `traits` interfaces used by the
//! views; neither interface depends on `ff` or `group`.
//!
//! [`PALLAS_BASE`] and [`PALLAS_SCALAR`] have width five; [`PALLAS_BASE_T3`]
//! and [`PALLAS_SCALAR_T3`] provide the `P128Pow5T3` width-three parameters.
//! Consumer views expose the same constants through [`PoseidonPermutation`]:
//!
//! ```
//! use zakura_udon::poseidon::{PALLAS_BASE_T3, PoseidonFpT3, PoseidonPermutation};
//!
//! assert_eq!(PoseidonFpT3::T, 3);
//! assert_eq!(PoseidonFpT3::RATE, 2);
//! assert_eq!(PoseidonFpT3.round_constants().len(), PALLAS_BASE_T3.rounds());
//! assert_eq!(PoseidonFpT3.mds_matrix().len(), PoseidonFpT3::T);
//! ```

use crate::field::{Fp, Fq};

mod pallas_base;
mod pallas_base_t3;
mod pallas_scalar;
mod pallas_scalar_t3;

/// A Poseidon instance over a field: the shape of the permutation and the
/// tables it runs with, for a state of width `T`.
#[derive(Clone, Copy, Debug)]
pub struct PoseidonParameters<F: 'static, const T: usize> {
    /// The number of full rounds, half before and half after the partial
    /// rounds.
    pub full_rounds: usize,
    /// The number of partial rounds.
    pub partial_rounds: usize,
    /// The S-box exponent.
    pub alpha: u32,
    /// The round constants in application order, one row of `T` per round:
    /// half the full rounds, then the partial rounds, then the remaining full
    /// rounds.
    pub round_constants: &'static [[F; T]],
    /// The MDS matrix.
    pub mds: &'static [[F; T]; T],
}

impl<F: 'static, const T: usize> PoseidonParameters<F, T> {
    /// The state width `T`.
    pub const fn width(&self) -> usize {
        T
    }

    /// The sponge rate: the width less one capacity element.
    pub const fn rate(&self) -> usize {
        T - 1
    }

    /// The total number of rounds.
    pub const fn rounds(&self) -> usize {
        self.full_rounds + self.partial_rounds
    }
}

/// The width-five, rate-four instance over the Pallas base field [`Fp`],
/// which is also the Vesta scalar field.
pub const PALLAS_BASE: PoseidonParameters<Fp, 5> = PoseidonParameters {
    full_rounds: 8,
    partial_rounds: 56,
    alpha: 5,
    round_constants: &pallas_base::ROUND_CONSTANTS,
    mds: &pallas_base::MDS,
};

/// The width-five, rate-four instance over the Pallas scalar field [`Fq`],
/// which is also the Vesta base field.
pub const PALLAS_SCALAR: PoseidonParameters<Fq, 5> = PoseidonParameters {
    full_rounds: 8,
    partial_rounds: 56,
    alpha: 5,
    round_constants: &pallas_scalar::ROUND_CONSTANTS,
    mds: &pallas_scalar::MDS,
};

mod traits;
pub use traits::{PoseidonFp, PoseidonFpT3, PoseidonFq, PoseidonFqT3, PoseidonPermutation};

/// The width-three, rate-two `P128Pow5T3` instance over [`Fp`].
pub const PALLAS_BASE_T3: PoseidonParameters<Fp, 3> = PoseidonParameters {
    full_rounds: 8,
    partial_rounds: 56,
    alpha: 5,
    round_constants: &pallas_base_t3::ROUND_CONSTANTS,
    mds: &pallas_base_t3::MDS,
};

/// The width-three, rate-two `P128Pow5T3` instance over [`Fq`].
pub const PALLAS_SCALAR_T3: PoseidonParameters<Fq, 3> = PoseidonParameters {
    full_rounds: 8,
    partial_rounds: 56,
    alpha: 5,
    round_constants: &pallas_scalar_t3::ROUND_CONSTANTS,
    mds: &pallas_scalar_t3::MDS,
};

#[cfg(test)]
mod tests;
