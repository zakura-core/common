//! Independent compatibility fixtures from archived Pasta and Poseidon.
//!
//! Expected bytes must come from the pinned reference revision: linking the
//! candidate arithmetic would make a shared bug invisible to the comparison.
use ff::{Field, FromUniformBytes, PrimeField};
use group::{Group, GroupEncoding};
use halo2_poseidon::{ConstantLength, Hash, P128Pow5T3, Spec};
use pasta_curves::{pallas, vesta};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use std::{fs, path::Path};

fn poseidon<F: FromUniformBytes<64> + Ord>(path: &Path)
where
    P128Pow5T3: Spec<F, 3, 2>,
{
    let (rounds, mds, _) = <P128Pow5T3 as Spec<F, 3, 2>>::constants();
    let mut bytes = Vec::new();
    for value in rounds.iter().flatten().chain(mds.iter().flatten()) {
        bytes.extend_from_slice(value.to_repr().as_ref());
    }
    for n in [0, 1, 2, 42, u64::MAX] {
        let inputs = [F::from(n), -F::from(n)];
        let hash = Hash::<F, P128Pow5T3, ConstantLength<2>, 3, 2>::init().hash(inputs);
        for value in inputs.into_iter().chain([hash]) {
            bytes.extend_from_slice(value.to_repr().as_ref());
        }
    }
    fs::write(path, bytes).unwrap();
}

fn main() {
    let output = std::env::args_os().nth(1).unwrap();
    let output = Path::new(&output);
    poseidon::<pallas::Base>(&output.join("poseidon-fp.bin"));
    poseidon::<vesta::Base>(&output.join("poseidon-fq.bin"));
    let mut rng = ChaCha20Rng::from_seed([42; 32]);
    let mut bytes = Vec::new();
    for i in 0..132 {
        let scalar = match i { 0 => pallas::Scalar::ZERO, 1 => pallas::Scalar::ONE, 2 => -pallas::Scalar::ONE, _ => pallas::Scalar::random(&mut rng) };
        let base = if i == 3 { pallas::Point::identity() } else { pallas::Point::random(&mut rng) };
        let expected = base * scalar;
        let table = pasta_curves::glv::Table::new(&base);
        assert_eq!(table.mul(&scalar), expected);
        bytes.extend_from_slice(&scalar.to_repr());
        bytes.extend_from_slice(&base.to_bytes());
        bytes.extend_from_slice(&expected.to_bytes());
    }
    fs::write(output.join("key-agreement.bin"), bytes).unwrap();
}
