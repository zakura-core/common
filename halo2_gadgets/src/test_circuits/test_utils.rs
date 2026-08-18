//! Functions used for circuit test.

use std::{env, fs, path::Path};

use group::ff::PrimeField;
use rand::rngs::OsRng;

use pasta_curves::{pallas, vesta};

use halo2_proofs::{
    plonk::{
        self, {Circuit, SingleVerifier, VerifyingKey},
    },
    poly::commitment::Params,
    transcript::{Blake2bRead, Blake2bWrite},
};

use crate::ecc::chip::{find_zs_and_us, H};

const TEST_DATA_DIR: &str = "src/test_circuits/circuit_data";
const GEN_ENV_VAR: &str = "CIRCUIT_TEST_GENERATE_NEW_DATA";

#[derive(Clone, Debug)]
pub struct Proof(Vec<u8>);

impl AsRef<[u8]> for Proof {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl Proof {
    /// Creates a proof for a single empty instance of the given circuit.
    pub fn create<C>(
        vk: &VerifyingKey<vesta::Affine>,
        params: &Params<vesta::Affine>,
        circuit: C,
    ) -> Result<Self, plonk::Error>
    where
        C: Circuit<pallas::Base>,
    {
        let pk = plonk::keygen_pk(params, vk.clone(), &circuit).unwrap();

        let mut transcript = Blake2bWrite::<_, vesta::Affine, _>::init(vec![]);
        plonk::create_proof(params, &pk, &[circuit], &[&[]], OsRng, &mut transcript)?;
        let proof = transcript.finalize();

        Ok(Proof(proof))
    }

    /// Verifies this proof  with a single empty instance.
    pub fn verify(
        &self,
        vk: &VerifyingKey<vesta::Affine>,
        params: &Params<vesta::Affine>,
    ) -> Result<(), plonk::Error> {
        let strategy = SingleVerifier::new(params);
        let mut transcript = Blake2bRead::init(&self.0[..]);
        plonk::verify_proof(params, vk, strategy, &[&[]], &mut transcript)
    }

    /// Constructs a new Proof value.
    pub fn new(bytes: Vec<u8>) -> Self {
        Proof(bytes)
    }
}

/// Test the generated vk and the generated proof against the stored vk and the stored proof.
///
/// If the env variable GEN_ENV_VAR is set, save `vk` and `proof` into a file.
pub(crate) fn test_against_stored_circuit<C: Circuit<pallas::Base>>(
    circuit: C,
    circuit_name: &str,
    expected_proof_size: usize,
) {
    let vk_file_path = Path::new(TEST_DATA_DIR)
        .join(format!("vk_{circuit_name}"))
        .with_extension("rdata");

    // Setup phase: generate parameters, vk for the circuit.
    let params: Params<vesta::Affine> = Params::new(11);
    let vk = plonk::keygen_vk(&params, &circuit).unwrap();

    let vk_text = format!("{:#?}\n", vk.pinned());

    if env::var_os(GEN_ENV_VAR).is_some() {
        fs::write(&vk_file_path, &vk_text).expect("Unable to write vk test file");
    } else {
        assert_eq!(
            vk_text,
            fs::read_to_string(vk_file_path)
                .expect("Unable to read vk test file")
                .replace("\r\n", "\n")
        );
    }

    let proof_file_path = Path::new(TEST_DATA_DIR)
        .join(format!("proof_{circuit_name}"))
        .with_extension("bin");

    let proof = if env::var_os(GEN_ENV_VAR).is_some() {
        // Create the proof and save it into a file
        let proof = Proof::create(&vk, &params, circuit).unwrap();
        fs::write(&proof_file_path, proof.as_ref()).expect("Unable to write proof test file");
        proof
    } else {
        // Read the proof from storage
        Proof::new(fs::read(proof_file_path).expect("Unable to read proof test file"))
    };

    // Verify the stored proof with the generated or stored vk.
    assert!(proof.verify(&vk, &params).is_ok());
    assert_eq!(proof.0.len(), expected_proof_size);
}

/// Loads the `(z, u)` window constants for `base` from a stored fixture, or
/// regenerates the fixture when the env variable GEN_ENV_VAR is set.
///
/// `find_zs_and_us` performs a square-root search per window, which is
/// expensive enough on targets with slow field arithmetic (notably the
/// 32-bit CI targets) to dominate the runtime of every test whose circuit
/// uses these constants. The fixtures let those tests load the constants
/// instead. `ecc::chip::constants::tests::zs_and_us_fixtures_match_search`
/// checks every stored fixture against a fresh search.
pub(crate) fn test_zs_and_us(
    base: pallas::Affine,
    num_windows: usize,
    fixture_name: &str,
) -> Vec<(u64, [pallas::Base; H])> {
    let file_path = Path::new(TEST_DATA_DIR)
        .join(format!("zs_and_us_{fixture_name}"))
        .with_extension("bin");

    if env::var_os(GEN_ENV_VAR).is_some() {
        let zs_and_us = find_zs_and_us(base, num_windows).unwrap();
        let mut bytes = Vec::with_capacity(zs_and_us.len() * (8 + H * 32));
        for (z, us) in &zs_and_us {
            bytes.extend_from_slice(&z.to_le_bytes());
            for u in us {
                bytes.extend_from_slice(&u.to_repr());
            }
        }
        fs::write(&file_path, &bytes).expect("Unable to write zs-and-us fixture");
        zs_and_us
    } else {
        let bytes = fs::read(&file_path).expect("Unable to read zs-and-us fixture");
        assert_eq!(bytes.len(), num_windows * (8 + H * 32));
        bytes
            .chunks_exact(8 + H * 32)
            .map(|window| {
                let z = u64::from_le_bytes(window[0..8].try_into().unwrap());
                let us: [pallas::Base; H] = window[8..]
                    .chunks_exact(32)
                    .map(|repr| {
                        pallas::Base::from_repr(repr.try_into().unwrap())
                            .expect("fixture contains valid field elements")
                    })
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();
                (z, us)
            })
            .collect()
    }
}
