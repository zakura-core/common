//! Pasta cycle binding and its runtime generator parameters.

use core::marker::PhantomData;

use super::{Cycle, PallasGenerators, Profile, Standard, VestaGenerators};
use crate::{
    curve::{AffineAdapter, Pallas, Vesta},
    field::{FieldAdapter, PallasBase, PallasScalar},
    poseidon::{PoseidonFp, PoseidonFq},
};

/// Runtime parameters of the [`Pasta`] cycle: the generators of both curves.
///
/// The Poseidon instances are compile-time constants and need no storage here.
#[derive(Clone, Copy, Debug)]
pub struct PastaParams {
    pallas: PallasGenerators,
    vesta: VestaGenerators,
}

impl PastaParams {
    /// Binds the generators of both curves.
    pub const fn new(pallas: PallasGenerators, vesta: VestaGenerators) -> Self {
        Self { pallas, vesta }
    }

    /// The Pallas generators.
    pub const fn pallas(&self) -> &PallasGenerators {
        &self.pallas
    }

    /// The Vesta generators.
    pub const fn vesta(&self) -> &VestaGenerators {
        &self.vesta
    }
}

/// The Pasta cycle: Pallas over [`crate::field::Fp`] with scalars in [`crate::field::Fq`] as the nested
/// curve, and Vesta over [`crate::field::Fq`] with scalars in [`crate::field::Fp`] as the host curve,
/// in the recursion profile `P`.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Pasta<P: Profile = Standard>(PhantomData<P>);

impl<P: Profile> Cycle for Pasta<P> {
    type CircuitField = FieldAdapter<PallasBase>;
    type ScalarField = FieldAdapter<PallasScalar>;
    type NestedCurve = AffineAdapter<Pallas>;
    type HostCurve = AffineAdapter<Vesta>;
    type NestedGenerators = PallasGenerators;
    type HostGenerators = VestaGenerators;
    type CircuitPoseidon = PoseidonFp;
    type ScalarPoseidon = PoseidonFq;
    type Params = PastaParams;
    type Profile = P;

    fn nested_generators(params: &PastaParams) -> &PallasGenerators {
        &params.pallas
    }

    fn host_generators(params: &PastaParams) -> &VestaGenerators {
        &params.vesta
    }

    fn circuit_poseidon(_params: &PastaParams) -> &PoseidonFp {
        &PoseidonFp
    }

    fn scalar_poseidon(_params: &PastaParams) -> &PoseidonFq {
        &PoseidonFq
    }
}
