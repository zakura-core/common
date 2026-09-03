//! Manual benchmarks for complete Ironwood proving and verification paths.

use alloc::vec::Vec;
use ff::{Field, PrimeField};
use halo2_proofs::{
    circuit::{Value, floor_planner},
    plonk::{
        Advice, Any, Assigned, Assignment, BatchVerifier, Circuit as PlonkCircuit, Column,
        ConstraintSystem, Error, Fixed, FloorPlanner, Instance as InstanceColumn, Selector,
    },
};
use incrementalmerkletree::{Hashable, Level};
use pasta_curves::{pallas, vesta};
use rand::{Rng, RngExt, SeedableRng, rngs::StdRng};
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
    Circuit, INSTANCE_COLUMNS, INSTANCE_ROWS, Instance, K, OrchardCircuitVersion, ProvingKey,
    VerifyingKey,
};
use crate::{
    BenchmarkCircuitWitnesses as _, Bundle, NOTE_COMMITMENT_TREE_DEPTH,
    builder::{Builder, BundleType, UnauthorizedBundle},
    bundle::BundleVersion,
    keys::{FullViewingKey, Scope, SpendingKey},
    note::{ExtractedNoteCommitment, Note, Nullifier, Rho},
    tree::{MerkleHashOrchard, MerklePath},
    value::NoteValue,
};

type Halo2Instances = Vec<Vec<Vec<vesta::Scalar>>>;
type EncodedIronwoodFixture = (Halo2Instances, Vec<u8>);

const IRONWOOD_BATCH_BENCH_SIZES: [usize; 4] = [1, 2, 16, 64];
const IRONWOOD_BATCH_SCREEN_SIZES: [usize; 2] = [1, 64];
const IRONWOOD_BATCH_BENCH_WARMUPS: usize = 3;
const IRONWOOD_BATCH_BENCH_SAMPLES: usize = 15;
const IRONWOOD_BATCH_SCREEN_WARMUPS: usize = 1;
const IRONWOOD_BATCH_SCREEN_SAMPLES: usize = 7;
const IRONWOOD_WITNESS_BENCH_ACTION_COUNTS: [usize; 5] = [1, 2, 4, 5, 6];
const IRONWOOD_WITNESS_BENCH_WARMUPS: usize = 50;
const IRONWOOD_WITNESS_BENCH_SAMPLES: usize = 1_000;

/// A two-Action fixture exercises a fully populated Ironwood payment.
const IRONWOOD_FIXTURE_ACTIONS: usize = 2;
const IRONWOOD_FIXTURE_SPEND_ADDRESS_INDEX: u32 = 0;
const IRONWOOD_FIXTURE_OUTPUT_ADDRESS_INDEX: u32 = 0;
const IRONWOOD_FIXTURE_MIN_VALUE_BITS: u32 = 24;
const IRONWOOD_FIXTURE_VALUE_BIT_WIDTH_COUNT: usize = 25;
/// Coprime to the bit-width count, so Actions traverse every width.
const IRONWOOD_FIXTURE_ACTION_MAGNITUDE_STRIDE: usize = 11;
/// The Orchard builder API fixes memo fields at 512 bytes.
const IRONWOOD_FIXTURE_MEMO_SIZE: usize = 512;
const IRONWOOD_FIXTURE_MEMO: [u8; IRONWOOD_FIXTURE_MEMO_SIZE] = [0; IRONWOOD_FIXTURE_MEMO_SIZE];
const IRONWOOD_FIXTURE_SPENDING_KEY: [u8; 32] = [7; 32];
const IRONWOOD_FIXTURE_RECEIVER_SPENDING_KEY: [u8; 32] = [8; 32];
const IRONWOOD_FIXTURE_SEED_DOMAIN: u8 = 0x42;
const IRONWOOD_VALUE_SEED_DOMAIN: u8 = 0x43;
const IRONWOOD_PROOF_SEED_DOMAIN: u8 = 0x24;
const ZIP317_MARGINAL_FEE: u64 = 5_000;
const ZIP317_GRACE_ACTIONS: usize = 2;
const INDEX_SEED_BYTES: usize = core::mem::size_of::<u64>();
/// Orchard's note-commitment tree is binary.
const MERKLE_ARITY: usize = 2;
/// Flipping the low path-index bit selects the sibling node.
const MERKLE_SIBLING_MASK: usize = 1;

const IRONWOOD_BATCH_FIXTURE_MAGIC: &[u8] = b"ZAKURA_IRONWOOD_BATCH_CORPUS_V2";

// Benchmark analogue of halo2_proofs' private WitnessCollection. This follows
// its advice, instance, and row-bound behavior while leaving fixed columns and
// copy constraints to the already-cached floor plan. A BTreeMap identifies
// advice columns because Column::index is intentionally not public API.
struct IronwoodBenchmarkWitness<F: Field> {
    k: u32,
    advice: BTreeMap<Column<Advice>, Vec<Assigned<F>>>,
    primary: Column<InstanceColumn>,
    instance: Vec<F>,
    usable_rows: RangeTo<usize>,
}

impl<F: Field> Assignment<F> for IronwoodBenchmarkWitness<F> {
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

    fn assign_advice_batch<V, A, AR>(
        &mut self,
        _: A,
        column: Column<Advice>,
        row: usize,
        len: usize,
        mut to: V,
    ) -> Result<(), Error>
    where
        V: FnMut(usize) -> Value<Assigned<F>>,
        A: Fn(usize) -> AR,
        AR: Into<String>,
    {
        if len == 0 {
            return Ok(());
        }

        let end = row.checked_add(len).ok_or(Error::BoundsFailure)?;
        if !self.usable_rows.contains(&row) || end > self.usable_rows.end {
            return Err(Error::NotEnoughRowsAvailable { current_k: self.k });
        }

        let targets = self
            .advice
            .get_mut(&column)
            .and_then(|column| column.get_mut(row..end))
            .ok_or(Error::BoundsFailure)?;
        for (index, target) in targets.iter_mut().enumerate() {
            let mut assigned = false;
            let _ = to(index).map(|value| {
                *target = value;
                assigned = true;
            });
            if !assigned {
                return Err(Error::Synthesis);
            }
        }
        Ok(())
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

struct IronwoodPaymentFixture {
    bundle: UnauthorizedBundle<i64>,
    instances: Vec<Instance>,
}

fn extracted_commitment(note: &Note) -> ExtractedNoteCommitment {
    ExtractedNoteCommitment::from(note.commitment())
}

/// Builds authentication paths for notes scattered through one populated tree.
///
/// Keep this aligned with `shared_anchor_witnesses` in
/// `benches/support/mod.rs`; benchmark targets cannot share private helpers.
fn ironwood_spend_witnesses(
    notes: Vec<Note>,
    rng: &mut impl Rng,
) -> (crate::Anchor, Vec<(Note, MerklePath)>) {
    assert!(
        !notes.is_empty(),
        "a payment fixture has at least one spend"
    );
    let arity = u64::try_from(MERKLE_ARITY).expect("the Merkle arity fits into u64");
    let sibling_mask =
        u64::try_from(MERKLE_SIBLING_MASK).expect("the Merkle sibling mask fits into u64");
    let mut positions = BTreeSet::new();
    while positions.len() < notes.len() {
        positions.insert(rng.random::<u32>());
    }
    let positions = positions.into_iter().collect::<Vec<_>>();
    let leaves = positions
        .iter()
        .copied()
        .zip(notes.iter())
        .map(|(position, note)| {
            (
                u64::from(position),
                MerkleHashOrchard::from_cmx(&extracted_commitment(note)),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut levels = Vec::with_capacity(NOTE_COMMITMENT_TREE_DEPTH + 1);
    levels.push(leaves);
    for level_index in 0..NOTE_COMMITMENT_TREE_DEPTH {
        let level =
            Level::from(u8::try_from(level_index).expect("the Orchard Merkle level fits into u8"));
        let mut current = levels[level_index].clone();
        let parents = current
            .keys()
            .map(|index| index / arity)
            .collect::<BTreeSet<_>>();
        for parent in &parents {
            let left = parent * arity;
            for child in [left, left + sibling_mask] {
                // Authentication paths expose sibling subtree roots, but not
                // their preimages. Model a populated tree with independent
                // canonical nodes instead of repeated empty roots.
                current.entry(child).or_insert_with(|| {
                    let value = pallas::Base::random(&mut *rng).to_repr();
                    MerkleHashOrchard::from_bytes(&value).unwrap()
                });
            }
        }
        levels[level_index] = current;
        let parents = parents
            .into_iter()
            .map(|parent| {
                let left = parent * arity;
                let current = &levels[level_index];
                (
                    parent,
                    MerkleHashOrchard::combine(
                        level,
                        &current[&left],
                        &current[&(left + sibling_mask)],
                    ),
                )
            })
            .collect::<BTreeMap<_, _>>();
        levels.push(parents);
    }

    let witnesses = notes
        .into_iter()
        .zip(positions)
        .map(|(note, position)| {
            let auth_path = core::array::from_fn(|level_index| {
                let sibling = (u64::from(position) >> level_index) ^ sibling_mask;
                levels[level_index]
                    .get(&sibling)
                    .copied()
                    .expect("every authentication-path sibling is populated")
            });
            (note, MerklePath::from_parts(position, auth_path))
        })
        .collect::<Vec<_>>();
    let anchor = witnesses[0].1.root(extracted_commitment(&witnesses[0].0));
    for (note, path) in &witnesses {
        assert_eq!(
            path.root(extracted_commitment(note)),
            anchor,
            "benchmark spend witnesses share one anchor",
        );
    }

    (anchor, witnesses)
}

/// Creates varied payment values without consuming the cryptographic fixture RNG.
fn ironwood_payment_values(
    action_count: usize,
    fixture_index: usize,
) -> (Vec<NoteValue>, Vec<NoteValue>, u64) {
    let action_count_u64 =
        u64::try_from(action_count).expect("the benchmark Action count fits into u64");
    let total_fee = ZIP317_MARGINAL_FEE
        .checked_mul(
            u64::try_from(action_count.max(ZIP317_GRACE_ACTIONS))
                .expect("the ZIP 317 logical Action count fits into u64"),
        )
        .expect("the benchmark fee fits into u64");
    let fee_per_action = total_fee / action_count_u64;
    let fee_remainder = total_fee % action_count_u64;
    let mut value_rng = ironwood_benchmark_rng(IRONWOOD_VALUE_SEED_DOMAIN, fixture_index);

    let spend_values = (0..action_count)
        .map(|action_index| {
            let width_offset = (fixture_index % IRONWOOD_FIXTURE_VALUE_BIT_WIDTH_COUNT
                + (IRONWOOD_FIXTURE_ACTION_MAGNITUDE_STRIDE
                    * (action_index % IRONWOOD_FIXTURE_VALUE_BIT_WIDTH_COUNT))
                    % IRONWOOD_FIXTURE_VALUE_BIT_WIDTH_COUNT)
                % IRONWOOD_FIXTURE_VALUE_BIT_WIDTH_COUNT;
            let width = IRONWOOD_FIXTURE_MIN_VALUE_BITS
                + u32::try_from(width_offset).expect("the value bit width fits into u32");
            let top_bit = 1_u64 << (width - 1);
            NoteValue::from_raw(top_bit | (value_rng.random::<u64>() & (top_bit - 1)))
        })
        .collect::<Vec<_>>();
    let output_values = spend_values
        .iter()
        .enumerate()
        .map(|(action_index, spend_value)| {
            let action_index = u64::try_from(action_index).expect("the Action index fits into u64");
            let fee = fee_per_action + u64::from(action_index < fee_remainder);
            NoteValue::from_raw(
                spend_value
                    .inner()
                    .checked_sub(fee)
                    .expect("the benchmark output value is nonzero"),
            )
        })
        .collect::<Vec<_>>();
    let spend_sum = spend_values
        .iter()
        .map(|value| u128::from(value.inner()))
        .sum::<u128>();
    let output_sum = output_values
        .iter()
        .map(|value| u128::from(value.inner()))
        .sum::<u128>();
    assert_eq!(spend_sum - output_sum, u128::from(total_fee));

    (spend_values, output_values, total_fee)
}

/// Builds a deterministic Ironwood payment with fully populated Actions.
///
/// Spent notes share one external payer IVK but use distinct receivers.
fn ironwood_payment_fixture(
    action_count: usize,
    fixture_index: usize,
    mut rng: impl Rng,
) -> IronwoodPaymentFixture {
    assert_ne!(action_count, 0, "a payment has at least one Action");
    let bundle_version = BundleVersion::ironwood_v3();
    let spend_key = SpendingKey::from_bytes(IRONWOOD_FIXTURE_SPENDING_KEY).unwrap();
    let spend_fvk = FullViewingKey::from(&spend_key);
    let spend_recipients = (0..action_count)
        .map(|action_index| {
            let address_index = IRONWOOD_FIXTURE_SPEND_ADDRESS_INDEX
                .checked_add(u32::try_from(action_index).unwrap())
                .unwrap();
            spend_fvk.address_at(address_index, Scope::External)
        })
        .collect::<Vec<_>>();
    assert!(
        spend_recipients
            .iter()
            .enumerate()
            .all(|(index, recipient)| spend_recipients[..index]
                .iter()
                .all(|previous| !recipient.same_expanded_receiver(previous))),
        "the benchmark payment uses a distinct spent-note receiver for each Action",
    );
    let receiver_key = SpendingKey::from_bytes(IRONWOOD_FIXTURE_RECEIVER_SPENDING_KEY).unwrap();
    let receiver_fvk = FullViewingKey::from(&receiver_key);
    let receivers = (0..action_count)
        .map(|action_index| {
            let address_index = IRONWOOD_FIXTURE_OUTPUT_ADDRESS_INDEX
                .checked_add(u32::try_from(action_index).unwrap())
                .unwrap();
            if action_count > 1 && action_index + 1 == action_count {
                // Model the final output as change back to the payer.
                spend_fvk.address_at(address_index, Scope::Internal)
            } else {
                receiver_fvk.address_at(address_index, Scope::External)
            }
        })
        .collect::<Vec<_>>();
    assert!(
        spend_recipients.iter().all(|spend_recipient| receivers
            .iter()
            .all(|receiver| !spend_recipient.same_expanded_receiver(receiver))),
        "the benchmark payment exercises Ironwood cross-address Actions",
    );
    assert_eq!(
        receivers
            .iter()
            .map(|receiver| receiver.to_raw_address_bytes())
            .collect::<BTreeSet<_>>()
            .len(),
        action_count,
        "the benchmark payment uses a distinct receiver for each Action",
    );

    let (spend_values, output_values, total_fee) =
        ironwood_payment_values(action_count, fixture_index);

    let spend_notes = spend_values
        .iter()
        .copied()
        .zip(spend_recipients.iter().copied())
        .map(|(spend_value, spend_recipient)| {
            let rho = Rho::from_nf_old(Nullifier::dummy(&mut rng));
            Note::new(
                spend_recipient,
                spend_value,
                rho,
                bundle_version.note_version(),
                &mut rng,
            )
        })
        .collect::<Vec<_>>();
    let (anchor, spend_witnesses) = ironwood_spend_witnesses(spend_notes, &mut rng);

    let bundle_type = if action_count < ZIP317_GRACE_ACTIONS {
        // Keep the explicit one-Action witness case from being padded to two.
        BundleType::UNPADDED
    } else {
        BundleType::DEFAULT
    };
    let mut builder = Builder::new(
        bundle_type,
        bundle_version,
        bundle_version.default_flags(),
        anchor,
    )
    .unwrap();
    for (note, path) in spend_witnesses {
        builder.add_spend(spend_fvk.clone(), note, path).unwrap();
    }
    for (output_value, receiver) in output_values.iter().copied().zip(receivers) {
        if spend_fvk.scope_for_address(&receiver).is_some() {
            builder
                .add_change_output(
                    spend_fvk.clone(),
                    Some(spend_fvk.to_ovk(Scope::Internal)),
                    receiver,
                    output_value,
                    IRONWOOD_FIXTURE_MEMO,
                )
                .unwrap();
        } else {
            builder
                .add_output(
                    Some(spend_fvk.to_ovk(Scope::External)),
                    receiver,
                    output_value,
                    IRONWOOD_FIXTURE_MEMO,
                )
                .unwrap();
        }
    }
    let (bundle, metadata): (Bundle<_, i64>, _) = builder
        .build(&mut rng)
        .unwrap()
        .expect("real spends and outputs produce an Ironwood bundle");
    assert_eq!(bundle.bundle_version(), bundle_version);
    assert_eq!(bundle.actions().len(), action_count);
    assert_eq!(bundle.circuit_version(), OrchardCircuitVersion::PostNu6_3,);
    assert!(bundle.flags().spends_enabled());
    assert!(bundle.flags().outputs_enabled());
    assert!(bundle.flags().cross_address_enabled());
    let spend_actions = (0..action_count)
        .map(|index| metadata.spend_action_index(index).unwrap())
        .collect::<Vec<_>>();
    let output_actions = (0..action_count)
        .map(|index| metadata.output_action_index(index).unwrap())
        .collect::<Vec<_>>();
    assert_eq!(
        spend_actions.iter().copied().collect::<BTreeSet<_>>(),
        (0..action_count).collect(),
    );
    assert_eq!(
        output_actions.iter().copied().collect::<BTreeSet<_>>(),
        (0..action_count).collect(),
    );
    let expected_balance = i64::try_from(total_fee).expect("the fixture balance fits into i64");
    assert_eq!(*bundle.value_balance(), expected_balance);
    let circuits = bundle.benchmark_circuits();
    for ((spend_value, spend_recipient), action_index) in spend_values
        .iter()
        .zip(&spend_recipients)
        .zip(spend_actions)
    {
        let expected_g_d = spend_recipient.g_d();
        circuits[action_index]
            .g_d_old
            .assert_if_known(|value| value == &expected_g_d);
        circuits[action_index]
            .pk_d_old
            .assert_if_known(|value| value == spend_recipient.pk_d());
        circuits[action_index]
            .v_old
            .assert_if_known(|value| value == spend_value);
    }
    for (output_value, action_index) in output_values.iter().zip(output_actions) {
        circuits[action_index]
            .v_new
            .assert_if_known(|value| value == output_value);
    }
    let instances = bundle
        .actions()
        .iter()
        .map(|action| action.to_instance(*bundle.flags(), *bundle.anchor()))
        .collect();

    IronwoodPaymentFixture { bundle, instances }
}

#[test]
fn ironwood_payment_values_cover_fixture_magnitudes() {
    let widths = (0..IRONWOOD_FIXTURE_VALUE_BIT_WIDTH_COUNT)
        .map(|fixture_index| {
            let (spend_values, _, _) = ironwood_payment_values(1, fixture_index);
            spend_values[0].inner().ilog2() + 1
        })
        .collect::<BTreeSet<_>>();
    let expected_widths = (0..IRONWOOD_FIXTURE_VALUE_BIT_WIDTH_COUNT)
        .map(|offset| {
            IRONWOOD_FIXTURE_MIN_VALUE_BITS
                + u32::try_from(offset).expect("the value bit width fits into u32")
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(widths, expected_widths);

    for action_count in IRONWOOD_WITNESS_BENCH_ACTION_COUNTS {
        let (spend_values, output_values, total_fee) =
            ironwood_payment_values(action_count, action_count);
        assert!(spend_values.iter().all(|value| *value != NoteValue::ZERO));
        assert!(output_values.iter().all(|value| *value != NoteValue::ZERO));
        assert_eq!(
            total_fee,
            ZIP317_MARGINAL_FEE
                * u64::try_from(action_count.max(ZIP317_GRACE_ACTIONS))
                    .expect("the ZIP 317 logical Action count fits into u64"),
        );
    }
}

#[test]
fn ironwood_payment_fixtures_have_distinct_fully_populated_actions() {
    for action_count in IRONWOOD_WITNESS_BENCH_ACTION_COUNTS {
        let fixture = ironwood_payment_fixture(
            action_count,
            action_count,
            ironwood_benchmark_rng(IRONWOOD_FIXTURE_SEED_DOMAIN, action_count),
        );
        assert_eq!(fixture.instances.len(), action_count);
        let circuits = fixture.bundle.benchmark_circuits();
        assert_eq!(circuits.len(), action_count);
        for (index, circuit) in circuits.iter().enumerate() {
            for previous in &circuits[..index] {
                circuit
                    .g_d_old
                    .as_ref()
                    .zip(previous.g_d_old.as_ref())
                    .assert_if_known(|(current, previous)| current != previous);
                circuit
                    .pk_d_old
                    .as_ref()
                    .zip(previous.pk_d_old.as_ref())
                    .assert_if_known(|(current, previous)| current != previous);
            }
        }
    }
}

#[test]
fn ironwood_payment_fixture_proves() {
    let fixture = ironwood_payment_fixture(
        IRONWOOD_FIXTURE_ACTIONS,
        IRONWOOD_FIXTURE_ACTIONS,
        ironwood_benchmark_rng(IRONWOOD_FIXTURE_SEED_DOMAIN, IRONWOOD_FIXTURE_ACTIONS),
    );
    let keys = crate::cached_test_keys(OrchardCircuitVersion::PostNu6_3);
    let proof = fixture
        .bundle
        .authorization()
        .create_proof(
            keys.proving_key(),
            &fixture.instances,
            ironwood_benchmark_rng(IRONWOOD_PROOF_SEED_DOMAIN, IRONWOOD_FIXTURE_ACTIONS),
        )
        .expect("the benchmark payment fixture proves");
    proof
        .verify(keys.verifying_key(), &fixture.instances)
        .expect("the benchmark payment fixture verifies");
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
    let action_counts = std::env::var("IRONWOOD_WITNESS_ACTION_COUNT")
        .map(|action_count| {
            vec![
                action_count
                    .parse::<usize>()
                    .expect("IRONWOOD_WITNESS_ACTION_COUNT must be a positive integer"),
            ]
        })
        .unwrap_or_else(|_| IRONWOOD_WITNESS_BENCH_ACTION_COUNTS.to_vec());

    for action_count in action_counts {
        let fixture = ironwood_payment_fixture(
            action_count,
            action_count,
            ironwood_benchmark_rng(IRONWOOD_FIXTURE_SEED_DOMAIN, action_count),
        );
        let circuits = fixture.bundle.benchmark_circuits();
        let mut witnesses = fixture
            .instances
            .iter()
            .map(|instance| IronwoodBenchmarkWitness {
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

        // Generate the canonical plan, as key generation does.
        let floor_plan = floor_planner::V1::synthesize_batch(
            &mut witnesses,
            circuits,
            config.clone(),
            &constants,
            None,
        );
        let floor_plan = floor_plan
            .unwrap()
            .expect("the first synthesis creates a floor plan");

        for _ in 0..IRONWOOD_WITNESS_BENCH_WARMUPS {
            floor_planner::V1::synthesize_batch(
                &mut witnesses,
                circuits,
                config.clone(),
                &constants,
                Some(&floor_plan),
            )
            .unwrap();
        }

        let mut elapsed = Duration::ZERO;
        let mut samples = Vec::with_capacity(IRONWOOD_WITNESS_BENCH_SAMPLES);
        for _ in 0..IRONWOOD_WITNESS_BENCH_SAMPLES {
            let sample_config = config.clone();
            let started = Instant::now();
            floor_planner::V1::synthesize_batch(
                &mut witnesses,
                circuits,
                sample_config,
                &constants,
                Some(&floor_plan),
            )
            .unwrap();
            let sample = started.elapsed();
            elapsed += sample;
            samples.push(sample.as_nanos());
        }
        black_box(&witnesses);
        samples.sort_unstable();

        println!(
            "IRONWOOD_WITNESS_ASSIGNMENT workers={worker_count} actions={action_count} \
             ns_per_synthesis={} p50_ns={} p95_ns={}",
            elapsed.as_nanos() / IRONWOOD_WITNESS_BENCH_SAMPLES as u128,
            samples[IRONWOOD_WITNESS_BENCH_SAMPLES / 2],
            samples[IRONWOOD_WITNESS_BENCH_SAMPLES * 95 / 100],
        );
    }
}

fn ironwood_benchmark_rng(domain: u8, index: usize) -> StdRng {
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

fn encode_ironwood_batch_fixtures(encoded: &[EncodedIronwoodFixture]) -> Vec<u8> {
    let mut corpus = Vec::new();
    corpus.extend_from_slice(IRONWOOD_BATCH_FIXTURE_MAGIC);
    corpus.extend_from_slice(
        &u64::try_from(encoded.len())
            .expect("fixture count fits into u64")
            .to_le_bytes(),
    );

    for (instances, proof) in encoded {
        assert_eq!(instances.len(), IRONWOOD_FIXTURE_ACTIONS);
        for instance in instances {
            assert_eq!(instance.len(), INSTANCE_COLUMNS);
            assert_eq!(instance[0].len(), INSTANCE_ROWS);
            for scalar in &instance[0] {
                corpus.extend_from_slice(scalar.to_repr().as_ref());
            }
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

fn write_ironwood_batch_fixtures(path: &std::path::Path, encoded: &[EncodedIronwoodFixture]) {
    let corpus = encode_ironwood_batch_fixtures(encoded);

    let mut output = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .expect("batch fixture corpus path must not exist");
    output
        .write_all(&corpus)
        .expect("write batch fixture corpus");
}

fn decode_ironwood_batch_fixtures(corpus: &[u8]) -> Vec<EncodedIronwoodFixture> {
    let mut input = corpus;
    assert_eq!(
        take_fixture_bytes(&mut input, IRONWOOD_BATCH_FIXTURE_MAGIC.len()),
        IRONWOOD_BATCH_FIXTURE_MAGIC,
    );
    let proof_count =
        usize::try_from(take_fixture_u64(&mut input)).expect("fixture count fits usize");

    let fixtures = (0..proof_count)
        .map(|_| {
            let instances = (0..IRONWOOD_FIXTURE_ACTIONS)
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
                    vec![column]
                })
                .collect::<Vec<_>>();
            let proof_len =
                usize::try_from(take_fixture_u64(&mut input)).expect("proof length fits usize");
            let proof = take_fixture_bytes(&mut input, proof_len).to_vec();
            (instances, proof)
        })
        .collect::<Vec<_>>();
    assert!(input.is_empty(), "trailing batch fixture bytes");
    fixtures
}

fn read_ironwood_batch_fixtures(path: &std::path::Path) -> Vec<EncodedIronwoodFixture> {
    let corpus = fs::read(path).expect("read batch fixture corpus");
    decode_ironwood_batch_fixtures(&corpus)
}

fn create_ironwood_batch_fixtures(
    version: OrchardCircuitVersion,
    vk: &VerifyingKey,
    proof_count: usize,
) -> Vec<EncodedIronwoodFixture> {
    let pk = ProvingKey::build(version);

    (0..proof_count)
        .map(|index| {
            let fixture = ironwood_payment_fixture(
                IRONWOOD_FIXTURE_ACTIONS,
                index,
                ironwood_benchmark_rng(IRONWOOD_FIXTURE_SEED_DOMAIN, index),
            );
            let proof = fixture
                .bundle
                .authorization()
                .create_proof(
                    &pk,
                    &fixture.instances,
                    ironwood_benchmark_rng(IRONWOOD_PROOF_SEED_DOMAIN, index),
                )
                .expect("proof creation should succeed");
            proof
                .verify(vk, &fixture.instances)
                .expect("benchmark proof should verify");

            let instances = fixture
                .instances
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

fn validate_ironwood_batch_fixtures(
    encoded: &[EncodedIronwoodFixture],
    vk: &VerifyingKey,
    expected_count: usize,
) {
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
fn ironwood_batch_fixture_encoding_roundtrips() {
    const TEST_PROOF: &[u8] = b"fixture-codec-test";

    let encoded = vec![(
        (0..IRONWOOD_FIXTURE_ACTIONS)
            .map(|action_index| {
                let column = (0..INSTANCE_ROWS)
                    .map(|row_index| {
                        let index = action_index * INSTANCE_ROWS + row_index;
                        vesta::Scalar::from(
                            u64::try_from(index).expect("instance index fits into u64"),
                        )
                    })
                    .collect::<Vec<_>>();
                vec![column]
            })
            .collect::<Vec<_>>(),
        TEST_PROOF.to_vec(),
    )];
    assert_ne!(encoded[0].0[0], encoded[0].0[1]);

    assert_eq!(
        decode_ironwood_batch_fixtures(&encode_ironwood_batch_fixtures(&encoded)),
        encoded
    );
}

#[test]
#[ignore = "manual single-thread performance benchmark"]
fn benchmark_ironwood_batch_verifier() {
    assert_eq!(K, 11, "Orchard's protocol-fixed circuit size changed");
    assert_eq!(
        std::env::var("RAYON_NUM_THREADS").ok().as_deref(),
        Some("1"),
        "run this benchmark with RAYON_NUM_THREADS=1",
    );

    let version = OrchardCircuitVersion::PostNu6_3;
    let vk = VerifyingKey::build(version);
    let proof_count = *IRONWOOD_BATCH_BENCH_SIZES
        .last()
        .expect("batch sizes are nonempty");
    let fixture_path = std::env::var_os("IRONWOOD_BATCH_FIXTURE_CORPUS")
        .map(std::path::PathBuf::from)
        .expect("set IRONWOOD_BATCH_FIXTURE_CORPUS");
    let encoded = if std::env::var_os("IRONWOOD_BATCH_FIXTURE_GENERATE").is_some() {
        let fixtures = create_ironwood_batch_fixtures(version, &vk, proof_count);
        write_ironwood_batch_fixtures(&fixture_path, &fixtures);
        fixtures
    } else {
        read_ironwood_batch_fixtures(&fixture_path)
    };

    // Corpus loading and full proof validation are deliberately outside every
    // timed sample. Each benchmark binary independently performs this check.
    validate_ironwood_batch_fixtures(&encoded, &vk, proof_count);

    let screen = std::env::var_os("IRONWOOD_BATCH_SCREEN").is_some();
    let batch_sizes: &[usize] = if screen {
        &IRONWOOD_BATCH_SCREEN_SIZES
    } else {
        &IRONWOOD_BATCH_BENCH_SIZES
    };
    let (warmups, sample_count) = if screen {
        (IRONWOOD_BATCH_SCREEN_WARMUPS, IRONWOOD_BATCH_SCREEN_SAMPLES)
    } else {
        (IRONWOOD_BATCH_BENCH_WARMUPS, IRONWOOD_BATCH_BENCH_SAMPLES)
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
        println!("IRONWOOD_BATCH_BENCH size={batch_size} samples_ns={samples:?}");
    }
}
