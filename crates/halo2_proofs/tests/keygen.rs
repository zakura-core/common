use ff::Field;
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    pasta::EqAffine,
    plonk::{Circuit, Column, ConstraintSystem, Error, Instance, keygen_pk, keygen_vk},
    poly::commitment::Params,
};

#[derive(Clone, Copy)]
struct InstanceCircuit;

impl<F: Field> Circuit<F> for InstanceCircuit {
    type Config = Column<Instance>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        *self
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        meta.instance_column()
    }

    fn synthesize(&self, _config: Self::Config, _layouter: impl Layouter<F>) -> Result<(), Error> {
        Ok(())
    }
}

#[test]
fn keygen_pk_rejects_mismatched_vk_domain() {
    let vk_params = Params::<EqAffine>::new(12);
    let proving_params = Params::<EqAffine>::new(11);
    let vk = keygen_vk(&vk_params, &InstanceCircuit).unwrap();

    assert!(matches!(
        keygen_pk(&proving_params, vk, &InstanceCircuit),
        Err(Error::InvalidParameters)
    ));
}
