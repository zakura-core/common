use std::collections::BTreeSet;

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
use rand::{RngExt, SeedableRng, rngs::StdRng};

const MEMO_SIZE: usize = 512;
const MEMO: [u8; MEMO_SIZE] = [0; MEMO_SIZE];
const PAYER_SPENDING_KEY: [u8; 32] = [7; 32];
const RECIPIENT_SPENDING_KEY: [u8; 32] = [8; 32];
const FUNDING_SEED_DOMAIN: u8 = 0x40;
const PAYMENT_SEED_DOMAIN: u8 = 0x41;
const VALUE_SEED_DOMAIN: u8 = 0x43;
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

fn funding_notes(
    spend_values: &[NoteValue],
    fixture_index: u64,
    payer_fvk: &FullViewingKey,
) -> Vec<Note> {
    let action_count = spend_values.len();
    let bundle_version = BundleVersion::ironwood_v3();
    let recipient = payer_fvk.address_at(0u32, Scope::External);
    let mut builder = Builder::new(
        fixture_bundle_type(action_count),
        bundle_version,
        Flags::SPENDS_DISABLED,
        Anchor::empty_tree(),
    )
    .expect("Ironwood permits output-only funding bundles");

    for value in spend_values {
        builder
            .add_output(
                Some(payer_fvk.to_ovk(Scope::External)),
                recipient,
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
    spend_values
        .iter()
        .enumerate()
        .map(|(output_index, expected_value)| {
            let action_index = metadata
                .output_action_index(output_index)
                .expect("each funding output has an Action");
            let (note, decrypted_to, memo) = funding_bundle
                .decrypt_output_with_key(action_index, &ivk)
                .expect("the payer decrypts each funding note");
            assert_eq!(note.version(), bundle_version.note_version());
            assert_eq!(note.value(), *expected_value);
            assert_eq!(decrypted_to, recipient);
            assert_eq!(memo, MEMO);
            note
        })
        .collect()
}

fn extracted_commitment(note: &Note) -> ExtractedNoteCommitment {
    ExtractedNoteCommitment::from(note.commitment())
}

fn shared_anchor_witnesses(notes: Vec<Note>) -> (Anchor, Vec<(Note, MerklePath)>) {
    assert!(
        !notes.is_empty(),
        "a payment fixture has at least one spend"
    );

    let leaves = notes
        .iter()
        .map(|note| MerkleHashOrchard::from_cmx(&extracted_commitment(note)))
        .collect::<Vec<_>>();
    let mut levels = Vec::with_capacity(NOTE_COMMITMENT_TREE_DEPTH + 1);
    levels.push(leaves);

    for level_index in 0..NOTE_COMMITMENT_TREE_DEPTH {
        let level =
            Level::from(u8::try_from(level_index).expect("Orchard Merkle level fits into u8"));
        let current = &levels[level_index];
        let parents = current
            .chunks(MERKLE_ARITY)
            .map(|children| {
                let right = children
                    .get(1)
                    .copied()
                    .unwrap_or_else(|| MerkleHashOrchard::empty_root(level));
                MerkleHashOrchard::combine(level, &children[0], &right)
            })
            .collect();
        levels.push(parents);
    }

    let anchor = Anchor::from(levels[NOTE_COMMITMENT_TREE_DEPTH][0]);
    let witnesses = notes
        .into_iter()
        .enumerate()
        .map(|(position, note)| {
            let auth_path = core::array::from_fn(|level_index| {
                let level = Level::from(
                    u8::try_from(level_index).expect("Orchard Merkle level fits into u8"),
                );
                let sibling = (position >> level_index) ^ MERKLE_SIBLING_MASK;
                levels[level_index]
                    .get(sibling)
                    .copied()
                    .unwrap_or_else(|| MerkleHashOrchard::empty_root(level))
            });
            let path = MerklePath::from_parts(
                u32::try_from(position).expect("fixture position fits into u32"),
                auth_path,
            );
            assert_eq!(path.root(extracted_commitment(&note)), anchor);
            (note, path)
        })
        .collect();

    (anchor, witnesses)
}

#[allow(
    dead_code,
    reason = "indexed fixtures are used directly by some benchmark targets"
)]
pub(super) fn payment_fixture(action_count: usize) -> PaymentFixture {
    payment_fixture_with_index(action_count, 0)
}

pub(super) fn payment_fixture_with_index(
    action_count: usize,
    fixture_index: u64,
) -> PaymentFixture {
    assert_ne!(action_count, 0, "a payment has at least one Action");

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

    let (spend_values, output_values, total_fee) = payment_values(action_count, fixture_index);
    let (anchor, spend_notes) =
        shared_anchor_witnesses(funding_notes(&spend_values, fixture_index, &payer_fvk));
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
    for output_value in &output_values {
        builder
            .add_output(
                Some(payer_fvk.to_ovk(Scope::External)),
                recipient,
                *output_value,
                MEMO,
            )
            .expect("each cross-address Ironwood payment output is valid");
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

    let spend_action_indices = (0..action_count)
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
    assert_eq!(spend_action_indices, all_action_indices);
    assert_eq!(output_action_indices, all_action_indices);

    let payer_ivk = payer_fvk.to_ivk(Scope::External);
    let recipient_ivk = recipient_fvk.to_ivk(Scope::External);
    for output_index in 0..action_count {
        let action_index = metadata
            .output_action_index(output_index)
            .expect("each requested output has an Action");
        let (note, decrypted_to, memo) = bundle
            .decrypt_output_with_key(action_index, &recipient_ivk)
            .expect("the recipient decrypts each payment output");
        assert_eq!(note.version(), bundle_version.note_version());
        assert_eq!(note.value(), output_values[output_index]);
        assert_eq!(decrypted_to, recipient);
        assert_eq!(memo, MEMO);
        assert!(
            bundle
                .decrypt_output_with_key(action_index, &payer_ivk)
                .is_none(),
            "the payer must not decrypt the cross-address output",
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
