use alloc::vec::Vec;

use super::scheme::{SlhDsa, WotsPlus};
use super::*;

const MASTER_SEED: &[u8] = b"account rules test seed";
const PAYEE: [u8; 25] = [0x76; 25];

fn master() -> [u8; 32] {
    master_from_seed(MASTER_SEED)
}

fn keys(step: u32) -> KeySet {
    KeySet::derive(&master(), 0, step).unwrap()
}

fn account() -> AccountScript {
    AccountScript::derive(&master(), 0).unwrap()
}

fn deposit_script(account: &AccountScript) -> Vec<u8> {
    [&[0xa9, 0x14][..], &account.account_hash(), &[0x87]].concat()
}

fn control(step: u32) -> ControlOutput {
    ControlOutput::new(account().account_hash(), keys(step).root(), step)
}

/// Each input's digest differs, so a signature only verifies on the input it was made for.
fn digest(index: usize) -> Option<[u8; 32]> {
    Some([u8::try_from(index).unwrap() + 1; 32])
}

fn authorize(step: u32, spare: u8, index: usize) -> Authorization {
    let key = signing_key(&master(), 0, step, spare).unwrap();
    Authorization::sign(key, &keys(step), spare, digest(index).unwrap()).unwrap()
}

fn control_sig(authorization: &Authorization) -> Vec<u8> {
    let mut bytes = Vec::new();
    authorization.push_into(&mut bytes);
    bytes
}

fn signing_deposit_sig(authorization: &Authorization) -> Vec<u8> {
    let mut bytes = control_sig(authorization);
    push(&mut bytes, &account().to_bytes());
    bytes
}

fn covered_sig() -> Vec<u8> {
    let mut bytes = Vec::new();
    push(&mut bytes, &account().to_bytes());
    bytes
}

/// Each input's script signature and spent script, and each output's script.
type Transaction = (Vec<(Vec<u8>, Vec<u8>)>, Vec<Vec<u8>>);

fn check(inputs: &[(Vec<u8>, Vec<u8>)], outputs: &[Vec<u8>]) -> Result<AccountCheck, AccountError> {
    let inputs: Vec<_> = inputs
        .iter()
        .map(|(sig, spent)| (sig.as_slice(), spent.as_slice()))
        .collect();
    let outputs: Vec<_> = outputs.iter().map(Vec::as_slice).collect();
    check_accounts(&inputs, &outputs, digest)
}

/// A first spend: a deposit carrying the step-0 authorization plus a covered deposit.
fn first_spend() -> Transaction {
    let deposit = deposit_script(&account());
    (
        vec![
            (signing_deposit_sig(&authorize(0, 0, 0)), deposit.clone()),
            (covered_sig(), deposit),
        ],
        vec![PAYEE.to_vec(), control(1).to_bytes().to_vec()],
    )
}

/// A spend at `step` by `spare`: the control input plus a covered deposit.
fn step_spend(step: u32, spare: u8) -> Transaction {
    (
        vec![
            (
                control_sig(&authorize(step, spare, 0)),
                control(step).to_bytes().to_vec(),
            ),
            (covered_sig(), deposit_script(&account())),
        ],
        vec![PAYEE.to_vec(), control(step + 1).to_bytes().to_vec()],
    )
}

#[test]
fn key_set_roots_match_known_answers_and_every_spare_proves_membership() {
    let keys = keys(0);
    assert_eq!(
        hex::encode(keys.root()),
        "4efebdb4f423c62e9b1d47b88336434acd8b02956960ee5608fdf517157f9c5f",
        "derivation, leaf or node hashing changed; this pins the SLH-DSA keys"
    );
    for spare in 0..4 {
        let leaf = leaf_commit(keys.key(spare).unwrap());
        let path = keys.path(spare).unwrap();
        assert_eq!(root_from_path(leaf, spare, &path), Some(keys.root()));
        assert_ne!(root_from_path(leaf, spare ^ 1, &path), Some(keys.root()));
    }
    assert!(keys.path(4).is_none());
    assert_eq!(root_from_path([0; 32], 4, &[[0; 32]; 2]), None);
    assert_ne!(keys.root(), self::keys(1).root());
    assert_ne!(keys.root(), KeySet::derive(&master(), 1, 0).unwrap().root());
}

#[test]
fn templates_round_trip_and_reject_every_changed_fixed_byte() {
    let account = account();
    assert_eq!(AccountScript::parse(&account.to_bytes()), Some(account));
    let control = control(7);
    assert_eq!(ControlOutput::parse(&control.to_bytes()), Some(control));
    assert_eq!(control.to_bytes().len(), ControlOutput::SIZE);
    for index in [0, 2, 35] {
        let mut bytes = account.to_bytes();
        bytes[index] ^= 1;
        assert!(AccountScript::parse(&bytes).is_none());
    }
    for index in [0, 2, 23, 56, 61] {
        let mut bytes = control.to_bytes();
        bytes[index] ^= 1;
        assert!(ControlOutput::parse(&bytes).is_none());
    }
    assert!(AccountScript::parse(&account.to_bytes()[..35]).is_none());
    assert!(ControlOutput::parse(&[control.to_bytes().as_slice(), &[0]].concat()).is_none());
}

#[test]
fn script_signature_sizes_match_their_constants() {
    let authorization = authorize(0, 0, 0);
    assert_eq!(control_sig(&authorization).len(), CONTROL_SCRIPT_SIG_SIZE);
    assert_eq!(
        signing_deposit_sig(&authorization).len(),
        SIGNING_DEPOSIT_SCRIPT_SIG_SIZE
    );
    assert_eq!(covered_sig().len(), COVERED_DEPOSIT_SCRIPT_SIG_SIZE);
    // The SLH-DSA-SHA2-128s witness is a 7856-byte signature and a 32-byte public key.
    assert_eq!(CONTROL_SCRIPT_SIG_SIZE, 8002);
    assert_eq!(input_size(CONTROL_SCRIPT_SIG_SIZE), 8045);
}

#[test]
fn only_the_canonical_push_encoding_is_accepted() {
    assert_eq!(pushes(&[2, 7, 8]), Some(vec![&[7, 8][..]]));
    // The same 2-byte value through PUSHDATA1, and an opcode that is not a push.
    assert_eq!(pushes(&[0x4c, 2, 7, 8]), None);
    assert_eq!(pushes(&[0x51]), None);
    assert_eq!(pushes(&[3, 7, 8]), None);
}

#[test]
fn a_first_spend_and_later_steps_are_accepted() {
    let (inputs, outputs) = first_spend();
    assert_eq!(
        check(&inputs, &outputs),
        Ok(AccountCheck {
            account_inputs: vec![0, 1],
            authorizations: 1
        })
    );
    for spare in 0..4 {
        let (inputs, outputs) = step_spend(1, spare);
        assert_eq!(check(&inputs, &outputs).unwrap().authorizations, 1);
    }
}

#[test]
fn other_inputs_and_outputs_are_left_to_the_interpreter() {
    let p2pkh = [&[0x76, 0xa9, 0x14][..], &[1; 20], &[0x88, 0xac]].concat();
    let other_p2sh = [&[0xa9, 0x14][..], &[2; 20], &[0x87]].concat();
    let inputs = [(vec![1, 1], p2pkh), (covered_sig(), other_p2sh)];
    assert_eq!(
        check(&inputs, &[PAYEE.to_vec()]),
        Ok(AccountCheck::default())
    );
}

#[test]
fn spends_need_exactly_one_authorization() {
    let deposit = deposit_script(&account());
    let covered_only = [(covered_sig(), deposit.clone())];
    let outputs = [control(1).to_bytes().to_vec()];
    assert_eq!(
        check(&covered_only, &outputs),
        Err(AccountError::Authorizations)
    );

    let (mut inputs, outputs) = step_spend(1, 0);
    inputs.push((signing_deposit_sig(&authorize(0, 1, 2)), deposit));
    assert_eq!(check(&inputs, &outputs), Err(AccountError::Authorizations));
}

#[test]
fn the_successor_must_be_exactly_one_control_output_at_the_next_step() {
    let (inputs, mut outputs) = first_spend();
    outputs.pop();
    assert_eq!(check(&inputs, &outputs), Err(AccountError::Successor));
    for step in [0, 2] {
        let wrong = [PAYEE.to_vec(), control(step).to_bytes().to_vec()];
        assert_eq!(check(&inputs, &wrong), Err(AccountError::Successor));
    }
    let twice = [
        control(1).to_bytes().to_vec(),
        control(1).to_bytes().to_vec(),
    ];
    assert_eq!(check(&inputs, &twice), Err(AccountError::Successor));
}

#[test]
fn the_last_step_cannot_advance() {
    let mut last = control(1);
    last.step = u32::MAX;
    let inputs = [(control_sig(&authorize(1, 0, 0)), last.to_bytes().to_vec())];
    assert_eq!(check(&inputs, &[]), Err(AccountError::StepOverflow));
}

#[test]
fn control_outputs_need_the_accounts_authorization() {
    // As in a coinbase transaction, which has no inputs the rules recognize.
    let forged = [control(1).to_bytes().to_vec()];
    assert_eq!(
        check(&[], &forged),
        Err(AccountError::UnauthorizedControlOutput)
    );

    let (inputs, mut outputs) = first_spend();
    let mut other = control(1);
    other.account = [9; 20];
    outputs.push(other.to_bytes().to_vec());
    assert_eq!(
        check(&inputs, &outputs),
        Err(AccountError::UnauthorizedControlOutput)
    );
}

#[test]
fn unknown_versions_are_rejected() {
    let (inputs, mut outputs) = first_spend();
    let mut successor = control(1);
    successor.version = 2;
    *outputs.last_mut().unwrap() = successor.to_bytes().to_vec();
    assert_eq!(check(&inputs, &outputs), Err(AccountError::Version));

    let mut spent = control(1);
    spent.version = 2;
    let inputs = [(control_sig(&authorize(1, 0, 0)), spent.to_bytes().to_vec())];
    assert_eq!(check(&inputs, &[]), Err(AccountError::Version));
}

#[test]
fn signatures_must_match_the_step_input_and_spare() {
    // Signed for another input's digest.
    let inputs = [(
        control_sig(&authorize(1, 0, 1)),
        control(1).to_bytes().to_vec(),
    )];
    let outputs = [control(2).to_bytes().to_vec()];
    assert_eq!(check(&inputs, &outputs), Err(AccountError::Signature));

    // Signed by a key of the next step.
    let inputs = [(
        control_sig(&authorize(2, 0, 0)),
        control(1).to_bytes().to_vec(),
    )];
    assert_eq!(check(&inputs, &outputs), Err(AccountError::Signature));

    // An altered signature, and a spare index outside the key set.
    let mut altered = authorize(1, 0, 0);
    altered.witness[0] ^= 1;
    let inputs = [(control_sig(&altered), control(1).to_bytes().to_vec())];
    assert_eq!(check(&inputs, &outputs), Err(AccountError::Signature));
    let mut outside = authorize(1, 3, 0);
    outside.spare = 4;
    let inputs = [(control_sig(&outside), control(1).to_bytes().to_vec())];
    assert_eq!(check(&inputs, &outputs), Err(AccountError::Spare));

    // A valid authorization whose path claims another spare.
    let mut moved = authorize(1, 1, 0);
    moved.spare = 0;
    let inputs = [(control_sig(&moved), control(1).to_bytes().to_vec())];
    assert_eq!(check(&inputs, &outputs), Err(AccountError::Signature));
}

#[test]
fn malformed_forms_and_missing_digests_are_rejected() {
    // The authorization without its path, followed by the account script.
    let (mut inputs, outputs) = first_spend();
    let mut short = control_sig(&authorize(0, 0, 0));
    short.truncate(CONTROL_SCRIPT_SIG_SIZE - 65);
    push(&mut short, &account().to_bytes());
    inputs[0].0 = short;
    assert_eq!(
        check(&inputs, &outputs),
        Err(AccountError::Form {
            input: 0,
            error: FormError::DepositScriptSig
        })
    );

    let inputs = [(covered_sig(), control(1).to_bytes().to_vec())];
    assert_eq!(
        check(&inputs, &[]),
        Err(AccountError::Form {
            input: 0,
            error: FormError::ControlScriptSig
        })
    );

    let (inputs, outputs) = first_spend();
    let inputs: Vec<_> = inputs
        .iter()
        .map(|(sig, spent)| (sig.as_slice(), spent.as_slice()))
        .collect();
    let outputs: Vec<_> = outputs.iter().map(Vec::as_slice).collect();
    assert_eq!(
        check_accounts(&inputs, &outputs, |_| None),
        Err(AccountError::Digest)
    );
}

#[test]
fn signing_with_a_key_that_is_not_the_named_spare_fails() {
    let key = signing_key(&master(), 0, 1, 2).unwrap();
    assert!(Authorization::sign(key, &keys(1), 0, [0; 32]).is_err());
}

#[test]
fn every_scheme_recovers_only_the_signing_key() {
    // The contract every scheme behind `Scheme` must meet.
    fn check<S: SignatureScheme>() {
        let key = S::derive(&KeySeed::new(&master(), 0, 0, 0)).unwrap();
        let public = S::public_key(&key);
        let witness = S::sign(key, &[7; 32]);
        assert_eq!(witness.len(), S::WITNESS_BYTES);
        assert_eq!(S::recover(&[7; 32], &witness), Some(public.clone()));
        assert_ne!(S::recover(&[8; 32], &witness), Some(public.clone()));
        let mut tampered = witness.clone();
        tampered[0] ^= 1;
        assert_ne!(S::recover(&[7; 32], &tampered), Some(public));
        assert_eq!(S::recover(&[7; 32], &witness[1..]), None);
    }
    check::<Scheme>();
    check::<WotsPlus>();
    check::<SlhDsa<slh_dsa::Sha2_128f>>();
    check::<SlhDsa<slh_dsa::Sha2_256s>>();
}
