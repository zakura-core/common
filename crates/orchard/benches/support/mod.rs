use std::collections::{BTreeMap, BTreeSet};

use ff::{Field, PrimeField};
use incrementalmerkletree::{Hashable, Level};
use orchard::{
    Anchor, Bundle, NOTE_COMMITMENT_TREE_DEPTH,
    builder::{Builder, BundleType, UnauthorizedBundle},
    bundle::{BundleVersion, Flags},
    circuit::{Instance, OrchardCircuitVersion},
    keys::{FullViewingKey, IncomingViewingKey, Scope, SpendAuthorizingKey, SpendingKey},
    note::{ExtractedNoteCommitment, Note},
    tree::{MerkleHashOrchard, MerklePath},
    value::NoteValue,
};
use pasta_curves::pallas;
use rand::{Rng, RngExt, SeedableRng, rngs::StdRng};

const MEMO_SIZE: usize = 512;
const MEMO: [u8; MEMO_SIZE] = [0; MEMO_SIZE];
const PAYER_SPENDING_KEY: [u8; 32] = [7; 32];
const RECIPIENT_SPENDING_KEY: [u8; 32] = [8; 32];
const FUNDING_SEED_DOMAIN: u8 = 0x40;
const PAYMENT_SEED_DOMAIN: u8 = 0x41;
const VALUE_SEED_DOMAIN: u8 = 0x43;
const MERKLE_SEED_DOMAIN: u8 = 0x44;
const MIN_VALUE_BITS: u32 = 24;
const VALUE_BIT_WIDTH_COUNT: usize = 25;
/// Coprime to the bit-width count, so Actions traverse every width.
const ACTION_MAGNITUDE_STRIDE: usize = 11;
const ZIP317_MARGINAL_FEE: u64 = 5_000;
const ZIP317_GRACE_ACTIONS: usize = 2;
/// Orchard's note-commitment tree is binary.
const MERKLE_ARITY: usize = 2;
/// Flipping the low path-index bit selects the sibling node.
const MERKLE_SIBLING_MASK: usize = 1;

#[allow(
    dead_code,
    reason = "each benchmark target selects only the payment shapes it needs"
)]
#[derive(Clone, Copy)]
enum PaymentShape {
    AllRealSingleRecipient,
    AllRealRecipientAndChange,
    PaddedRecipientAndChange,
}

#[allow(
    dead_code,
    reason = "independent benchmark targets use different fixture capabilities"
)]
pub(super) struct PaymentFixture {
    bundle: UnauthorizedBundle<i64>,
    instances: Vec<Instance>,
    recipient_ivk: IncomingViewingKey,
    spend_authorizing_key: SpendAuthorizingKey,
}

#[allow(
    dead_code,
    reason = "independent benchmark targets use different fixture capabilities"
)]
impl PaymentFixture {
    pub(super) fn bundle(&self) -> &UnauthorizedBundle<i64> {
        &self.bundle
    }

    pub(super) fn instances(&self) -> &[Instance] {
        &self.instances
    }

    pub(super) fn recipient_ivk(&self) -> &IncomingViewingKey {
        &self.recipient_ivk
    }

    pub(super) fn into_bundle_and_signing_key(
        self,
    ) -> (UnauthorizedBundle<i64>, SpendAuthorizingKey) {
        (self.bundle, self.spend_authorizing_key)
    }
}

fn fixture_rng(domain: u8, action_count: usize, fixture_index: u64) -> StdRng {
    let mut seed = [domain; 32];
    seed[..8].copy_from_slice(
        &u64::try_from(action_count)
            .expect("Action count fits into u64")
            .to_le_bytes(),
    );
    seed[8..16].copy_from_slice(&fixture_index.to_le_bytes());
    StdRng::from_seed(seed)
}

fn fixture_fee(action_count: usize) -> u64 {
    ZIP317_MARGINAL_FEE
        .checked_mul(
            u64::try_from(action_count.max(ZIP317_GRACE_ACTIONS))
                .expect("ZIP 317 logical Action count fits into u64"),
        )
        .expect("fixture fee fits into u64")
}

fn fixture_bundle_type(action_count: usize) -> BundleType {
    if action_count < ZIP317_GRACE_ACTIONS {
        // Keep the explicit one-Action benchmark from being padded to two.
        BundleType::UNPADDED
    } else {
        BundleType::DEFAULT
    }
}

/// Creates varied values without consuming either cryptographic fixture RNG.
fn payment_values(
    action_count: usize,
    fixture_index: u64,
) -> (Vec<NoteValue>, Vec<NoteValue>, u64) {
    let action_count_u64 = u64::try_from(action_count).expect("Action count fits into u64");
    let total_fee = fixture_fee(action_count);
    let fee_per_action = total_fee / action_count_u64;
    let fee_remainder = total_fee % action_count_u64;
    let width_count_u64 =
        u64::try_from(VALUE_BIT_WIDTH_COUNT).expect("value bit-width count fits into u64");
    let fixture_offset = usize::try_from(fixture_index % width_count_u64)
        .expect("value bit-width offset fits into usize");
    let mut value_rng = fixture_rng(VALUE_SEED_DOMAIN, action_count, fixture_index);

    let spend_values = (0..action_count)
        .map(|action_index| {
            let width_offset = (fixture_offset
                + (ACTION_MAGNITUDE_STRIDE * (action_index % VALUE_BIT_WIDTH_COUNT))
                    % VALUE_BIT_WIDTH_COUNT)
                % VALUE_BIT_WIDTH_COUNT;
            let width = MIN_VALUE_BITS
                + u32::try_from(width_offset).expect("value bit width fits into u32");
            let top_bit = 1_u64 << (width - 1);
            NoteValue::from_raw(top_bit | (value_rng.random::<u64>() & (top_bit - 1)))
        })
        .collect::<Vec<_>>();
    let output_values = spend_values
        .iter()
        .enumerate()
        .map(|(action_index, spend_value)| {
            let action_index = u64::try_from(action_index).expect("Action index fits into u64");
            let action_fee = fee_per_action + u64::from(action_index < fee_remainder);
            let output_value = spend_value
                .inner()
                .checked_sub(action_fee)
                .expect("fixture spend covers its fee share");
            assert_ne!(output_value, 0, "fixture outputs are nonzero");
            NoteValue::from_raw(output_value)
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
    assert_eq!(
        spend_sum
            .checked_sub(output_sum)
            .expect("fixture spends cover its outputs"),
        u128::from(total_fee),
    );

    (spend_values, output_values, total_fee)
}

/// Creates funding notes with one external payer IVK and distinct receivers.
fn funding_notes(
    spend_values: &[NoteValue],
    fixture_index: u64,
    payer_fvk: &FullViewingKey,
) -> Vec<Note> {
    let action_count = spend_values.len();
    let bundle_version = BundleVersion::ironwood_v3();
    let recipients = (0..action_count)
        .map(|action_index| {
            payer_fvk.address_at(
                u32::try_from(action_index).expect("Action index fits into u32"),
                Scope::External,
            )
        })
        .collect::<Vec<_>>();
    let mut builder = Builder::new(
        fixture_bundle_type(action_count),
        bundle_version,
        Flags::SPENDS_DISABLED,
        Anchor::empty_tree(),
    )
    .expect("Ironwood permits output-only funding bundles");

    for (value, recipient) in spend_values.iter().zip(&recipients) {
        builder
            .add_output(
                Some(payer_fvk.to_ovk(Scope::External)),
                *recipient,
                *value,
                MEMO,
            )
            .expect("Ironwood funding outputs are valid");
    }

    let mut rng = fixture_rng(FUNDING_SEED_DOMAIN, action_count, fixture_index);
    let (funding_bundle, metadata): (Bundle<_, i64>, _) = builder
        .build(&mut rng)
        .expect("funding bundle construction succeeds")
        .expect("nonempty funding bundle is produced");
    assert_eq!(funding_bundle.bundle_version(), bundle_version);
    assert_eq!(funding_bundle.actions().len(), action_count);

    let ivk = payer_fvk.to_ivk(Scope::External);
    let mut funded_notes = spend_values
        .iter()
        .zip(&recipients)
        .enumerate()
        .map(|(output_index, (expected_value, expected_recipient))| {
            let action_index = metadata
                .output_action_index(output_index)
                .expect("each funding output has an Action");
            let (note, decrypted_to, memo) = funding_bundle
                .decrypt_output_with_key(action_index, &ivk)
                .expect("the payer decrypts each funding note");
            assert_eq!(note.version(), bundle_version.note_version());
            assert_eq!(note.value(), *expected_value);
            assert_eq!(decrypted_to, *expected_recipient);
            assert_eq!(
                payer_fvk.scope_for_address(&decrypted_to),
                Some(Scope::External),
            );
            assert_eq!(memo, MEMO);
            (action_index, note)
        })
        .collect::<Vec<_>>();
    assert_eq!(
        funded_notes
            .iter()
            .map(|(action_index, _)| *action_index)
            .collect::<BTreeSet<_>>(),
        (0..action_count).collect(),
    );
    assert_eq!(
        funded_notes
            .iter()
            .map(|(_, note)| *note.recipient().diversifier().as_array())
            .collect::<BTreeSet<_>>()
            .len(),
        action_count,
        "multi-spend fixtures use distinct old-note diversifiers",
    );
    funded_notes.sort_unstable_by_key(|(action_index, _)| *action_index);
    funded_notes.into_iter().map(|(_, note)| note).collect()
}

fn extracted_commitment(note: &Note) -> ExtractedNoteCommitment {
    ExtractedNoteCommitment::from(note.commitment())
}

// Keep this aligned with `ironwood_spend_witnesses` in
// `src/circuit/benchmark.rs`; benchmark targets cannot share private helpers.
fn shared_anchor_witnesses(
    notes: Vec<Note>,
    rng: &mut impl Rng,
) -> (Anchor, Vec<(Note, MerklePath)>) {
    assert!(
        !notes.is_empty(),
        "a payment fixture has at least one spend"
    );

    let arity = u64::try_from(MERKLE_ARITY).expect("Merkle arity fits into u64");
    let sibling_mask =
        u64::try_from(MERKLE_SIBLING_MASK).expect("Merkle sibling mask fits into u64");
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
            Level::from(u8::try_from(level_index).expect("Orchard Merkle level fits into u8"));
        let mut current = levels[level_index].clone();
        let parents = current
            .keys()
            .map(|index| index / arity)
            .collect::<BTreeSet<_>>();
        for parent in &parents {
            let left = parent * arity;
            for child in [left, left + sibling_mask] {
                // A spend reveals sibling subtree roots but not their
                // preimages, so independent canonical nodes accurately model
                // a populated tree.
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
            .collect();
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
        assert_eq!(path.root(extracted_commitment(note)), anchor);
    }

    (anchor, witnesses)
}

#[allow(
    dead_code,
    reason = "indexed fixtures are used directly by some benchmark targets"
)]
pub(super) fn payment_fixture(action_count: usize) -> PaymentFixture {
    payment_fixture_with_shape(action_count, 0, PaymentShape::AllRealRecipientAndChange)
}

#[allow(dead_code, reason = "used by the full-prover benchmark target")]
pub(super) fn padded_two_action_payment_fixture() -> PaymentFixture {
    payment_fixture_with_shape(2, 0, PaymentShape::PaddedRecipientAndChange)
}

#[allow(dead_code, reason = "used by the full-prover benchmark target")]
pub(super) fn two_real_spends_payment_fixture() -> PaymentFixture {
    payment_fixture_with_shape(2, 0, PaymentShape::AllRealRecipientAndChange)
}

#[allow(
    dead_code,
    reason = "indexed fixtures are used directly by some benchmark targets"
)]
pub(super) fn payment_fixture_with_index(
    action_count: usize,
    fixture_index: u64,
) -> PaymentFixture {
    payment_fixture_with_shape(
        action_count,
        fixture_index,
        PaymentShape::AllRealSingleRecipient,
    )
}

fn payment_fixture_with_shape(
    action_count: usize,
    fixture_index: u64,
    shape: PaymentShape,
) -> PaymentFixture {
    assert_ne!(action_count, 0, "a payment has at least one Action");
    if matches!(shape, PaymentShape::PaddedRecipientAndChange) {
        assert_eq!(action_count, 2, "the named prover fixtures are two-Action");
    }

    let bundle_version = BundleVersion::ironwood_v3();
    let payer_sk = SpendingKey::from_bytes(PAYER_SPENDING_KEY).unwrap();
    let payer_fvk = FullViewingKey::from(&payer_sk);
    let recipient_fvk =
        FullViewingKey::from(&SpendingKey::from_bytes(RECIPIENT_SPENDING_KEY).unwrap());
    let payer_address = payer_fvk.address_at(0u32, Scope::External);
    let recipient = recipient_fvk.address_at(0u32, Scope::External);
    assert_ne!(
        payer_address.to_raw_address_bytes(),
        recipient.to_raw_address_bytes(),
        "the fixture uses distinct payer and recipient addresses",
    );

    let (mut spend_values, output_values, total_fee) = payment_values(action_count, fixture_index);
    if matches!(shape, PaymentShape::PaddedRecipientAndChange) {
        let second = spend_values.pop().unwrap();
        let first = spend_values.pop().unwrap();
        spend_values.push(NoteValue::from_raw(
            first
                .inner()
                .checked_add(second.inner())
                .expect("the combined fixture spend fits into u64"),
        ));
    }
    let output_recipients = match shape {
        PaymentShape::AllRealSingleRecipient => vec![recipient; action_count],
        PaymentShape::AllRealRecipientAndChange | PaymentShape::PaddedRecipientAndChange => (0
            ..action_count)
            .map(|action_index| {
                if action_count > 1 && action_index + 1 == action_count {
                    payer_fvk.address_at(
                        u32::try_from(action_index).expect("Action index fits into u32"),
                        Scope::Internal,
                    )
                } else {
                    recipient_fvk.address_at(
                        u32::try_from(action_index).expect("Action index fits into u32"),
                        Scope::External,
                    )
                }
            })
            .collect(),
    };
    let notes = funding_notes(&spend_values, fixture_index, &payer_fvk);
    let mut merkle_rng = fixture_rng(MERKLE_SEED_DOMAIN, action_count, fixture_index);
    let (anchor, spend_notes) = shared_anchor_witnesses(notes, &mut merkle_rng);
    let mut builder = Builder::new(
        fixture_bundle_type(action_count),
        bundle_version,
        bundle_version.default_flags(),
        anchor,
    )
    .expect("unrestricted Ironwood payment flags are valid");

    for (note, path) in spend_notes {
        builder
            .add_spend(payer_fvk.clone(), note, path)
            .expect("each real spend is owned and anchored");
    }
    for (output_value, recipient) in output_values.iter().zip(&output_recipients) {
        if payer_fvk.scope_for_address(recipient).is_some() {
            builder
                .add_change_output(
                    payer_fvk.clone(),
                    Some(payer_fvk.to_ovk(Scope::Internal)),
                    *recipient,
                    *output_value,
                    MEMO,
                )
                .expect("the payer owns its Ironwood change output");
        } else {
            builder
                .add_output(
                    Some(payer_fvk.to_ovk(Scope::External)),
                    *recipient,
                    *output_value,
                    MEMO,
                )
                .expect("each cross-address Ironwood payment output is valid");
        }
    }

    let mut rng = fixture_rng(PAYMENT_SEED_DOMAIN, action_count, fixture_index);
    let (bundle, metadata) = builder
        .build(&mut rng)
        .expect("payment bundle construction succeeds")
        .expect("nonempty payment bundle is produced");

    assert_eq!(bundle.bundle_version(), bundle_version);
    assert_eq!(bundle.circuit_version(), OrchardCircuitVersion::PostNu6_3);
    assert!(bundle.flags().spends_enabled());
    assert!(bundle.flags().outputs_enabled());
    assert!(bundle.flags().cross_address_enabled());
    assert_eq!(bundle.actions().len(), action_count);
    assert_eq!(
        *bundle.value_balance(),
        i64::try_from(total_fee).expect("fixture fee fits into i64"),
    );

    let spend_action_indices = (0..spend_values.len())
        .map(|index| {
            metadata
                .spend_action_index(index)
                .expect("each requested spend has an Action")
        })
        .collect::<BTreeSet<_>>();
    let output_action_indices = (0..action_count)
        .map(|index| {
            metadata
                .output_action_index(index)
                .expect("each requested output has an Action")
        })
        .collect::<BTreeSet<_>>();
    let all_action_indices = (0..action_count).collect::<BTreeSet<_>>();
    assert_eq!(spend_action_indices.len(), spend_values.len());
    assert!(spend_action_indices.is_subset(&all_action_indices));
    assert_eq!(output_action_indices, all_action_indices);

    let payer_internal_ivk = payer_fvk.to_ivk(Scope::Internal);
    let recipient_ivk = recipient_fvk.to_ivk(Scope::External);
    for (output_index, (expected_output_value, expected_recipient)) in
        output_values.iter().zip(&output_recipients).enumerate()
    {
        let action_index = metadata
            .output_action_index(output_index)
            .expect("each requested output has an Action");
        let (decrypting_ivk, other_ivk) = if recipient_fvk
            .scope_for_address(expected_recipient)
            .is_some()
        {
            (&recipient_ivk, &payer_internal_ivk)
        } else {
            (&payer_internal_ivk, &recipient_ivk)
        };
        let (note, decrypted_to, memo) = bundle
            .decrypt_output_with_key(action_index, decrypting_ivk)
            .expect("the intended recipient decrypts each payment output");
        assert_eq!(note.version(), bundle_version.note_version());
        assert_eq!(note.value(), *expected_output_value);
        assert_eq!(decrypted_to, *expected_recipient);
        assert_eq!(memo, MEMO);
        assert!(
            bundle
                .decrypt_output_with_key(action_index, other_ivk)
                .is_none(),
            "the other fixture wallet must not decrypt the output",
        );
    }

    let instances = bundle
        .actions()
        .iter()
        .map(|action| action.to_instance(*bundle.flags(), *bundle.anchor()))
        .collect();

    PaymentFixture {
        bundle,
        instances,
        recipient_ivk,
        spend_authorizing_key: SpendAuthorizingKey::from(&payer_sk),
    }
}
