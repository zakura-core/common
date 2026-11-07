use crate::transaction::{
    Authorization, TransactionData, TxVersion,
    sighash::{SignableInput, signature_hash},
    txid::TxIdDigester,
};
use alloc::vec::Vec;
use transparent::{
    address::Script,
    bundle::{self, OutPoint, TxIn, TxOut},
    pq::{self, ParameterSet, native},
    sighash::{SighashType, TransparentAuthorizingContext},
};
use zcash_protocol::{consensus::BranchId, value::Zatoshis};
use zcash_script::{
    interpreter::{CallbackTransactionSignatureChecker, Flags},
    script::Code,
};

#[derive(Clone, Debug)]
struct Inputs(Vec<TxOut>);
impl bundle::Authorization for Inputs {
    type ScriptSig = Script;
}
impl TransparentAuthorizingContext for Inputs {
    fn input_amounts(&self) -> Vec<Zatoshis> {
        self.0.iter().map(TxOut::value).collect()
    }
    fn input_scriptpubkeys(&self) -> Vec<Script> {
        self.0.iter().map(|o| o.script_pubkey().clone()).collect()
    }
}
struct TestAuth;
impl Authorization for TestAuth {
    type TransparentAuth = Inputs;
    type SaplingAuth = sapling::bundle::Authorized;
    type OrchardAuth = orchard::bundle::Authorized;
}
fn push(value: &[u8]) -> Vec<u8> {
    let mut bytes = vec![0x4d];
    bytes.extend(u16::try_from(value.len()).unwrap().to_le_bytes());
    bytes.extend(value);
    bytes
}
fn transaction(first: &Code, second: &Code) -> TransactionData<TestAuth> {
    TransactionData::from_parts(
        TxVersion::V5,
        BranchId::Nu5,
        0,
        100u32.into(),
        Some(bundle::Bundle {
            vin: vec![
                TxIn::from_parts(OutPoint::new([7; 32], 0), Script::default(), 0),
                TxIn::from_parts(OutPoint::new([8; 32], 1), Script::default(), 0),
            ],
            vout: vec![
                TxOut::new(Zatoshis::const_from_u64(90), Script(Code(vec![0x51]))),
                TxOut::new(Zatoshis::const_from_u64(190), Script(Code(vec![0x51]))),
            ],
            authorization: Inputs(vec![
                TxOut::new(Zatoshis::const_from_u64(100), Script(first.clone())),
                TxOut::new(Zatoshis::const_from_u64(200), Script(second.clone())),
            ]),
        }),
        None,
        None,
        None,
    )
}
fn digest(tx: &TransactionData<TestAuth>, code: &Code, index: usize, raw: u8) -> Option<[u8; 32]> {
    let mode = SighashType::parse(raw)?;
    let bundle = tx.transparent_bundle.as_ref()?;
    if raw & 0x1f == 3 && index >= bundle.vout.len() {
        return None;
    }
    let script = Script(code.clone());
    let prev = &bundle.authorization.0[index];
    let input = transparent::sighash::SignableInput::from_parts(
        bundle,
        mode,
        index,
        &script,
        prev.script_pubkey(),
        prev.value(),
    )
    .ok()?;
    Some(
        *signature_hash(
            tx,
            &SignableInput::Transparent(input),
            &tx.digest(TxIdDigester),
        )
        .as_ref(),
    )
}
fn check(
    tx: &TransactionData<TestAuth>,
    code: &Code,
    index: usize,
    input: &[u8],
) -> Result<bool, native::Error> {
    let callback = |script: &Code, mode: &zcash_script::signature::HashType| {
        assert_eq!(script.0, code.0);
        digest(tx, script, index, mode.raw_bits().try_into().ok()?)
    };
    native::parse_output(code).unwrap().unwrap().verify_spend(
        input,
        Flags::NullDummy | Flags::CleanStack,
        &CallbackTransactionSignatureChecker {
            sighash: &callback,
            lock_time: i64::from(tx.lock_time),
            is_final: false,
        },
    )
}
fn output(parameters: ParameterSet, key: &[u8]) -> Code {
    let mut body = vec![u8::try_from(key.len()).unwrap()];
    body.extend(key);
    body.push(0xba);
    native::output_script(parameters, &Code(body)).unwrap()
}

macro_rules! transaction_cases {
    ($name:ident,$algorithm:ident,$parameters:expr) => {
        mod $name {
            use super::*;
            use pq::$algorithm as crypto;
            const PARAMETERS: ParameterSet = $parameters;
            #[test]
            fn existing_signing_modes_preserve_field_selection_and_other_input_rules() {
                let key = crypto::SigningKey::from_seed(&[1; crypto::SEED_BYTES]);
                let code = output(PARAMETERS, &key.public_key());
                for raw in [1u8, 2, 3, 0x81, 0x82, 0x83] {
                    let tx = transaction(&code, &code);
                    let message = digest(&tx, &code, 0, raw).unwrap();
                    let mut sig = key
                        .sign(&message, native::signing_context(PARAMETERS))
                        .unwrap();
                    sig.push(raw);
                    let input = push(&sig);
                    assert_eq!(check(&tx, &code, 0, &input), Ok(true));
                    let mut changed = transaction(&code, &code);
                    changed.transparent_bundle.as_mut().unwrap().vout[1] =
                        TxOut::new(Zatoshis::const_from_u64(189), Script(Code(vec![0x51])));
                    assert_eq!(check(&changed, &code, 0, &input), Ok(raw & 0x1f != 1));
                    let mut changed = transaction(&code, &code);
                    changed.transparent_bundle.as_mut().unwrap().authorization.0[1] =
                        TxOut::new(Zatoshis::const_from_u64(201), Script(code.clone()));
                    assert_eq!(check(&changed, &code, 0, &input), Ok(raw & 0x80 != 0));
                    let mut changed = transaction(&code, &code);
                    changed.lock_time = 1;
                    assert_eq!(check(&changed, &code, 0, &input), Ok(false));
                }
                let mut tx = transaction(&code, &code);
                tx.transparent_bundle.as_mut().unwrap().vout.truncate(1);
                let mut argument = vec![0; crypto::SIGNATURE_BYTES];
                argument.push(3);
                assert_eq!(check(&tx, &code, 1, &push(&argument)), Ok(false));
            }
            #[test]
            fn transaction_prevouts_amounts_branch_and_complete_native_output_are_bound() {
                let key = crypto::SigningKey::from_seed(&[2; crypto::SEED_BYTES]);
                let code = output(PARAMETERS, &key.public_key());
                let tx = transaction(&code, &code);
                let mut sig = key
                    .sign(
                        &digest(&tx, &code, 0, 1).unwrap(),
                        native::signing_context(PARAMETERS),
                    )
                    .unwrap();
                sig.push(1);
                let input = push(&sig);
                for mutate in [
                    |t: &mut TransactionData<TestAuth>| t.expiry_height = 101u32.into(),
                    |t: &mut TransactionData<TestAuth>| t.consensus_branch_id = BranchId::Nu6,
                    |t: &mut TransactionData<TestAuth>| {
                        t.transparent_bundle.as_mut().unwrap().vin[0] =
                            TxIn::from_parts(OutPoint::new([9; 32], 0), Script::default(), 0)
                    },
                ] {
                    let mut changed = transaction(&code, &code);
                    mutate(&mut changed);
                    assert_eq!(check(&changed, &code, 0, &input), Ok(false));
                }
                let mut changed = transaction(&code, &code);
                changed.transparent_bundle.as_mut().unwrap().authorization.0[0] =
                    TxOut::new(Zatoshis::const_from_u64(101), Script(code.clone()));
                assert_eq!(check(&changed, &code, 0, &input), Ok(false));
                let mut changed_code = code.clone();
                changed_code.0.push(0x61);
                assert_eq!(
                    check(&transaction(&changed_code, &code), &changed_code, 0, &input),
                    Ok(false)
                );
                let body_message = digest(&tx, &Code(code.0[7..].to_vec()), 0, 1).unwrap();
                let mut body_sig = key
                    .sign(&body_message, native::signing_context(PARAMETERS))
                    .unwrap();
                body_sig.push(1);
                // ZIP244 binds the previous output; scriptCode is not a substitute for that binding.
                assert_eq!(
                    digest(&tx, &code, 0, 1),
                    digest(&tx, &Code(code.0[7..].to_vec()), 0, 1)
                );
                assert_eq!(check(&tx, &code, 0, &push(&body_sig)), Ok(true));
            }
        }
    };
}
transaction_cases!(fast, sha2_128f, ParameterSet::Sha2_128f);
transaction_cases!(small, sha2_192s, ParameterSet::Sha2_192s);

#[test]
fn inputs_with_different_native_versions_share_one_transaction() {
    let fast = pq::sha2_128f::SigningKey::from_seed(&[3; pq::sha2_128f::SEED_BYTES]);
    let small = pq::sha2_192s::SigningKey::from_seed(&[3; pq::sha2_192s::SEED_BYTES]);
    let first = output(ParameterSet::Sha2_128f, &fast.public_key());
    let second = output(ParameterSet::Sha2_192s, &small.public_key());
    let tx = transaction(&first, &second);
    let mut a = fast
        .sign(
            &digest(&tx, &first, 0, 1).unwrap(),
            native::signing_context(ParameterSet::Sha2_128f),
        )
        .unwrap();
    a.push(1);
    let mut b = small
        .sign(
            &digest(&tx, &second, 1, 1).unwrap(),
            native::signing_context(ParameterSet::Sha2_192s),
        )
        .unwrap();
    b.push(1);
    assert_eq!(check(&tx, &first, 0, &push(&a)), Ok(true));
    assert_eq!(check(&tx, &second, 1, &push(&b)), Ok(true));
    assert!(check(&tx, &first, 0, &push(&b)).is_err());
    assert!(check(&tx, &second, 1, &push(&a)).is_err());
    assert!(check(&tx, &second, 1, &push(&[0])).is_err());
}
