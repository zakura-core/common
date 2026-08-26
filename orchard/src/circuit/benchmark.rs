//! Manual benchmarks for the complete Orchard proving and verification paths.

use alloc::vec::Vec;
use ff::{Field, PrimeField};
use halo2_proofs::{
    circuit::{floor_planner, Value},
    plonk::{
        Advice, Any, Assigned, Assignment, BatchVerifier, Circuit as PlonkCircuit, Column,
        ConstraintSystem, Error, Fixed, FloorPlanner, Instance as InstanceColumn, Selector,
    },
};
use pasta_curves::{pallas, vesta};
use rand::{rngs::StdRng, SeedableRng};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs::{self, OpenOptions},
    hint::black_box,
    io::Write,
    ops::RangeTo,
    println,
    string::String,
    time::{Duration, Instant},
};

use super::{
    tests::generate_circuit_instance, Circuit, Instance, OrchardCircuitVersion, Proof, ProvingKey,
    VerifyingKey, INSTANCE_COLUMNS, INSTANCE_ROWS, K,
};
use crate::{
    builder::{Builder, BundleType},
    bundle::{BundleVersion, Flags},
    keys::{FullViewingKey, Scope, SpendingKey},
    value::NoteValue,
    Anchor, Bundle,
};

type Halo2Instances = Vec<Vec<Vec<vesta::Scalar>>>;
type EncodedFixture = (Halo2Instances, Vec<u8>);

const BATCH_BENCH_SIZES: [usize; 4] = [1, 2, 16, 64];
const BATCH_SCREEN_SIZES: [usize; 2] = [1, 64];
const BATCH_BENCH_WARMUPS: usize = 3;
const BATCH_BENCH_SAMPLES: usize = 15;
const BATCH_SCREEN_WARMUPS: usize = 1;
const BATCH_SCREEN_SAMPLES: usize = 7;
const WITNESS_BENCH_ACTION_COUNTS: [usize; 3] = [1, 2, 4];
const WITNESS_BENCH_WARMUPS: usize = 50;
const WITNESS_BENCH_SAMPLES: usize = 1_000;
const PROVER_BENCH_ACTION_COUNTS: [usize; 3] = [1, 2, 4];
const PROVER_BENCH_WARMUPS: usize = 3;
const PROVER_BENCH_SAMPLES: usize = 15;

const FIXTURE_ACTIONS: usize = 1;
const FIXTURE_ADDRESS_INDEX: u32 = 0;
const FIXTURE_NOTE_VALUE: u64 = 10;
/// The Orchard builder API fixes memo fields at 512 bytes.
const FIXTURE_MEMO_SIZE: usize = 512;
const FIXTURE_MEMO: [u8; FIXTURE_MEMO_SIZE] = [0; FIXTURE_MEMO_SIZE];
const FIXTURE_SPENDING_KEY: [u8; 32] = [7; 32];
const FIXTURE_ANCHOR: [u8; 32] = [0; 32];
const FIXTURE_SEED_DOMAIN: u8 = 0x42;
const PROOF_SEED_DOMAIN: u8 = 0x24;
const INDEX_SEED_BYTES: usize = core::mem::size_of::<u64>();

const BATCH_FIXTURE_MAGIC: &[u8] = b"ZAKURA_ORCHARD_BATCH_CORPUS_V1";

// Benchmark analogue of halo2_proofs' private WitnessCollection. This follows
// its advice, instance, and row-bound behavior while leaving fixed columns and
// copy constraints to the already-cached floor plan. A BTreeMap identifies
// advice columns because Column::index is intentionally not public API.
struct BenchmarkWitness<F: Field> {
    k: u32,
    advice: BTreeMap<Column<Advice>, Vec<Assigned<F>>>,
    primary: Column<InstanceColumn>,
    instance: Vec<F>,
    usable_rows: RangeTo<usize>,
}

impl<F: Field> Assignment<F> for BenchmarkWitness<F> {
    fn enter_region<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
    }

    fn exit_region(&mut self) {}

    fn enable_selector<A, AR>(&mut self, _: A, _: &Selector, _: usize) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        Ok(())
    }

    fn query_instance(
        &self,
        column: Column<InstanceColumn>,
        row: usize,
    ) -> Result<Value<F>, Error> {
        if !self.usable_rows.contains(&row) {
            return Err(Error::NotEnoughRowsAvailable { current_k: self.k });
        }

        if column != self.primary {
            return Err(Error::BoundsFailure);
        }

        self.instance
            .get(row)
            .copied()
            .map(Value::known)
            .ok_or(Error::BoundsFailure)
    }

    fn assign_advice<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<Advice>,
        row: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if !self.usable_rows.contains(&row) {
            return Err(Error::NotEnoughRowsAvailable { current_k: self.k });
        }

        let target = self
            .advice
            .get_mut(&column)
            .and_then(|column| column.get_mut(row))
            .ok_or(Error::BoundsFailure)?;
        let mut assigned = false;
        let _ = to().into_field().map(|value| {
            *target = value;
            assigned = true;
        });
        if assigned {
            Ok(())
        } else {
            Err(Error::Synthesis)
        }
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        _: A,
        _: Column<Fixed>,
        _: usize,
        _: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        Ok(())
    }

    fn copy(&mut self, _: Column<Any>, _: usize, _: Column<Any>, _: usize) -> Result<(), Error> {
        Ok(())
    }

    fn fill_from_row(
        &mut self,
        _: Column<Fixed>,
        _: usize,
        _: Value<Assigned<F>>,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
    }

    fn pop_namespace(&mut self, _: Option<String>) {}
}

#[test]
#[ignore = "manual witness-assignment performance benchmark"]
fn benchmark_witness_assignment() {
    let worker_count = std::env::var("RAYON_NUM_THREADS")
        .expect("set RAYON_NUM_THREADS explicitly for this benchmark");
    let worker_count = worker_count
        .parse::<usize>()
        .expect("RAYON_NUM_THREADS must be a positive integer");
    assert_ne!(worker_count, 0, "RAYON_NUM_THREADS must be nonzero");

    let mut meta = ConstraintSystem::<pallas::Base>::default();
    let config = <Circuit as PlonkCircuit<pallas::Base>>::configure(&mut meta);
    let constants = [config.constant];
    let row_count = 1_usize << K;
    let usable_rows = ..row_count - (meta.blinding_factors() + 1);

    for action_count in WITNESS_BENCH_ACTION_COUNTS {
        let (circuits, instances): (Vec<_>, Vec<_>) = (0..action_count)
            .map(|index| {
                generate_circuit_instance(
                    benchmark_rng(FIXTURE_SEED_DOMAIN, index),
                    OrchardCircuitVersion::FixedPostNu6_2,
                )
            })
            .unzip();
        let mut witnesses = instances
            .iter()
            .map(|instance| BenchmarkWitness {
                k: K,
                advice: config
                    .advices
                    .into_iter()
                    .map(|column| (column, vec![Assigned::Zero; row_count]))
                    .collect(),
                primary: config.primary,
                instance: instance
                    .to_halo2_instance()
                    .into_iter()
                    .next()
                    .expect("Orchard has one instance column")
                    .into_iter()
                    .collect(),
                usable_rows,
            })
            .collect::<Vec<_>>();

        let floor_plan = floor_planner::V1::synthesize_batch(
            &mut witnesses,
            &circuits,
            config.clone(),
            &constants,
            None,
        )
        .unwrap()
        .expect("the first synthesis creates a floor plan");

        for _ in 0..WITNESS_BENCH_WARMUPS {
            floor_planner::V1::synthesize_batch(
                &mut witnesses,
                &circuits,
                config.clone(),
                &constants,
                Some(&floor_plan),
            )
            .unwrap();
        }

        let mut elapsed = Duration::ZERO;
        for _ in 0..WITNESS_BENCH_SAMPLES {
            let sample_config = config.clone();
            let started = Instant::now();
            floor_planner::V1::synthesize_batch(
                &mut witnesses,
                &circuits,
                sample_config,
                &constants,
                Some(&floor_plan),
            )
            .unwrap();
            elapsed += started.elapsed();
        }
        black_box(&witnesses);

        println!(
            "ORCHARD_WITNESS_ASSIGNMENT workers={worker_count} actions={action_count} \
             ns_per_synthesis={}",
            elapsed.as_nanos() / WITNESS_BENCH_SAMPLES as u128,
        );
    }
}

#[test]
#[ignore = "manual Orchard prover performance benchmark"]
fn benchmark_orchard_prover() {
    let worker_count = std::env::var("RAYON_NUM_THREADS")
        .expect("set RAYON_NUM_THREADS explicitly for this benchmark");
    let worker_count = worker_count
        .parse::<usize>()
        .expect("RAYON_NUM_THREADS must be a positive integer");
    assert_ne!(worker_count, 0, "RAYON_NUM_THREADS must be nonzero");

    let version = OrchardCircuitVersion::FixedPostNu6_2;
    let pk = ProvingKey::build(version);
    let vk = pk.verifying_key();

    for action_count in PROVER_BENCH_ACTION_COUNTS {
        let (circuits, instances): (Vec<_>, Vec<_>) = (0..action_count)
            .map(|index| {
                generate_circuit_instance(benchmark_rng(FIXTURE_SEED_DOMAIN, index), version)
            })
            .unzip();

        for sample in 0..PROVER_BENCH_WARMUPS {
            black_box(
                Proof::create(
                    &pk,
                    &circuits,
                    &instances,
                    benchmark_rng(PROOF_SEED_DOMAIN, sample),
                )
                .unwrap(),
            );
        }

        let mut samples_ns = Vec::with_capacity(PROVER_BENCH_SAMPLES);
        for sample in 0..PROVER_BENCH_SAMPLES {
            let started = Instant::now();
            let proof = Proof::create(
                &pk,
                &circuits,
                &instances,
                benchmark_rng(PROOF_SEED_DOMAIN, sample + PROVER_BENCH_WARMUPS),
            )
            .unwrap();
            samples_ns.push(started.elapsed().as_nanos());
            if sample == 0 {
                proof.verify(&vk, &instances).unwrap();
            }
            black_box(proof);
        }

        println!(
            "ORCHARD_PROVER workers={worker_count} actions={action_count} \
             samples_ns={samples_ns:?}",
        );
    }
}

fn benchmark_rng(domain: u8, index: usize) -> StdRng {
    let mut seed = [domain; 32];
    let index = u64::try_from(index).expect("fixture index fits into u64");
    seed[..INDEX_SEED_BYTES].copy_from_slice(&index.to_le_bytes());
    StdRng::from_seed(seed)
}

fn take_fixture_bytes<'a>(input: &mut &'a [u8], len: usize) -> &'a [u8] {
    assert!(input.len() >= len, "truncated batch fixture corpus");
    let (head, tail) = input.split_at(len);
    *input = tail;
    head
}

fn take_fixture_u64(input: &mut &[u8]) -> u64 {
    u64::from_le_bytes(
        take_fixture_bytes(input, INDEX_SEED_BYTES)
            .try_into()
            .expect("eight-byte fixture integer"),
    )
}

fn encode_batch_fixtures(encoded: &[EncodedFixture]) -> Vec<u8> {
    let mut corpus = Vec::new();
    corpus.extend_from_slice(BATCH_FIXTURE_MAGIC);
    corpus.extend_from_slice(
        &u64::try_from(encoded.len())
            .expect("fixture count fits into u64")
            .to_le_bytes(),
    );

    for (instances, proof) in encoded {
        assert_eq!(instances.len(), FIXTURE_ACTIONS);
        assert_eq!(instances[0].len(), INSTANCE_COLUMNS);
        assert_eq!(instances[0][0].len(), INSTANCE_ROWS);
        for scalar in &instances[0][0] {
            corpus.extend_from_slice(scalar.to_repr().as_ref());
        }
        corpus.extend_from_slice(
            &u64::try_from(proof.len())
                .expect("proof length fits into u64")
                .to_le_bytes(),
        );
        corpus.extend_from_slice(proof);
    }

    corpus
}

fn write_batch_fixtures(path: &std::path::Path, encoded: &[EncodedFixture]) {
    let corpus = encode_batch_fixtures(encoded);

    let mut output = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .expect("batch fixture corpus path must not exist");
    output
        .write_all(&corpus)
        .expect("write batch fixture corpus");
}

fn decode_batch_fixtures(corpus: &[u8]) -> Vec<EncodedFixture> {
    let mut input = corpus;
    assert_eq!(
        take_fixture_bytes(&mut input, BATCH_FIXTURE_MAGIC.len()),
        BATCH_FIXTURE_MAGIC,
    );
    let proof_count =
        usize::try_from(take_fixture_u64(&mut input)).expect("fixture count fits usize");

    let fixtures = (0..proof_count)
        .map(|_| {
            let column = (0..INSTANCE_ROWS)
                .map(|_| {
                    let mut repr = <vesta::Scalar as PrimeField>::Repr::default();
                    let repr_bytes = repr.as_mut();
                    let encoded = take_fixture_bytes(&mut input, repr_bytes.len());
                    repr_bytes.copy_from_slice(encoded);
                    Option::<vesta::Scalar>::from(vesta::Scalar::from_repr(repr))
                        .expect("canonical fixture scalar")
                })
                .collect::<Vec<_>>();
            let proof_len =
                usize::try_from(take_fixture_u64(&mut input)).expect("proof length fits usize");
            let proof = take_fixture_bytes(&mut input, proof_len).to_vec();
            (vec![vec![column]], proof)
        })
        .collect::<Vec<_>>();
    assert!(input.is_empty(), "trailing batch fixture bytes");
    fixtures
}

fn read_batch_fixtures(path: &std::path::Path) -> Vec<EncodedFixture> {
    let corpus = fs::read(path).expect("read batch fixture corpus");
    decode_batch_fixtures(&corpus)
}

fn create_batch_fixtures(
    version: OrchardCircuitVersion,
    vk: &VerifyingKey,
    proof_count: usize,
) -> Vec<EncodedFixture> {
    let pk = ProvingKey::build(version);
    let sk = SpendingKey::from_bytes(FIXTURE_SPENDING_KEY).unwrap();
    let recipient = FullViewingKey::from(&sk).address_at(FIXTURE_ADDRESS_INDEX, Scope::External);

    (0..proof_count)
        .map(|index| {
            let mut fixture_rng = benchmark_rng(FIXTURE_SEED_DOMAIN, index);
            let mut builder = Builder::new(
                BundleType::Coinbase,
                BundleVersion::orchard_v2(),
                Flags::SPENDS_DISABLED,
                Anchor::from_bytes(FIXTURE_ANCHOR).unwrap(),
            )
            .unwrap();
            builder
                .add_output(
                    None,
                    recipient,
                    NoteValue::from_raw(FIXTURE_NOTE_VALUE),
                    FIXTURE_MEMO,
                )
                .unwrap();
            let bundle: Bundle<_, i64> = builder
                .build(&mut fixture_rng)
                .unwrap()
                .expect("one output produces an Orchard bundle")
                .0;
            assert_eq!(bundle.actions().len(), FIXTURE_ACTIONS);

            let instances = bundle
                .actions()
                .iter()
                .map(|action| action.to_instance(*bundle.flags(), *bundle.anchor()))
                .collect::<Vec<_>>();
            let proof = bundle
                .authorization()
                .create_proof(&pk, &instances, benchmark_rng(PROOF_SEED_DOMAIN, index))
                .expect("proof creation should succeed");
            proof
                .verify(vk, &instances)
                .expect("benchmark proof should verify");

            let instances = instances
                .iter()
                .map(Instance::to_halo2_instance)
                .map(|columns| {
                    columns
                        .into_iter()
                        .map(|column| column.into_iter().collect())
                        .collect()
                })
                .collect();
            (instances, proof.as_ref().to_vec())
        })
        .collect()
}

fn validate_batch_fixtures(encoded: &[EncodedFixture], vk: &VerifyingKey, expected_count: usize) {
    assert_eq!(encoded.len(), expected_count);
    let unique_proofs = encoded
        .iter()
        .map(|(_, proof)| proof.as_slice())
        .collect::<BTreeSet<_>>();
    assert_eq!(unique_proofs.len(), expected_count);

    let mut batch = BatchVerifier::new();
    for (instances, proof) in encoded.iter().cloned() {
        batch.add_proof(instances, proof);
    }
    assert!(batch.finalize(&vk.params, &vk.vk));
}

#[test]
fn batch_fixture_encoding_roundtrips() {
    const TEST_PROOF: &[u8] = b"fixture-codec-test";

    let column = (0..INSTANCE_ROWS)
        .map(|index| {
            vesta::Scalar::from(u64::try_from(index).expect("instance row index fits into u64"))
        })
        .collect::<Vec<_>>();
    let encoded = vec![(vec![vec![column]], TEST_PROOF.to_vec())];

    assert_eq!(
        decode_batch_fixtures(&encode_batch_fixtures(&encoded)),
        encoded
    );
}

#[test]
#[ignore = "manual single-thread performance benchmark"]
fn benchmark_batch_verifier() {
    assert_eq!(K, 11, "Orchard's protocol-fixed circuit size changed");
    assert_eq!(
        std::env::var("RAYON_NUM_THREADS").ok().as_deref(),
        Some("1"),
        "run this benchmark with RAYON_NUM_THREADS=1",
    );

    let version = OrchardCircuitVersion::FixedPostNu6_2;
    let vk = VerifyingKey::build(version);
    let proof_count = *BATCH_BENCH_SIZES.last().expect("batch sizes are nonempty");
    let fixture_path = std::env::var_os("ORCHARD_BATCH_FIXTURE_CORPUS")
        .map(std::path::PathBuf::from)
        .expect("set ORCHARD_BATCH_FIXTURE_CORPUS");
    let encoded = if std::env::var_os("ORCHARD_BATCH_FIXTURE_GENERATE").is_some() {
        let fixtures = create_batch_fixtures(version, &vk, proof_count);
        write_batch_fixtures(&fixture_path, &fixtures);
        fixtures
    } else {
        read_batch_fixtures(&fixture_path)
    };

    // Corpus loading and full proof validation are deliberately outside every
    // timed sample. Each benchmark binary independently performs this check.
    validate_batch_fixtures(&encoded, &vk, proof_count);

    let screen = std::env::var_os("ORCHARD_BATCH_SCREEN").is_some();
    let batch_sizes: &[usize] = if screen {
        &BATCH_SCREEN_SIZES
    } else {
        &BATCH_BENCH_SIZES
    };
    let (warmups, sample_count) = if screen {
        (BATCH_SCREEN_WARMUPS, BATCH_SCREEN_SAMPLES)
    } else {
        (BATCH_BENCH_WARMUPS, BATCH_BENCH_SAMPLES)
    };

    for &batch_size in batch_sizes {
        let mut samples = Vec::with_capacity(sample_count);
        for sample in 0..warmups + sample_count {
            let entries = encoded.iter().take(batch_size).cloned().collect::<Vec<_>>();

            let start = Instant::now();
            let mut batch = BatchVerifier::<vesta::Affine>::new();
            for (instances, proof) in entries {
                batch.add_proof(instances, proof);
            }
            assert!(batch.finalize(&vk.params, &vk.vk));
            let elapsed = start.elapsed();

            if sample >= warmups {
                samples.push(elapsed.as_nanos());
            }
        }
        println!("BATCH_BENCH size={batch_size} samples_ns={samples:?}");
    }
}
