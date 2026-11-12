use super::*;
use crate::{
    interpreter::NullSignatureChecker,
    script::{Asm, Evaluable},
};
use core::cell::Cell;

fn push(bytes: &[u8]) -> Vec<u8> {
    let mut result = vec![0x4d];
    result.extend(u16::try_from(bytes.len()).unwrap().to_le_bytes());
    result.extend(bytes);
    result
}
fn run(input: &[u8], body: &[u8], flags: Flags) -> Result<bool, Error> {
    let code = script::Code(body.to_vec());
    eval(input, &code, &code, flags, &NullSignatureChecker())
}
struct Counting(Cell<usize>);
impl SignatureChecker for Counting {
    fn check_pq_signature(
        &self,
        _: &[u8],
        _: &[u8],
        _: &script::Code,
    ) -> Result<bool, interpreter::Error> {
        self.0.set(self.0.get() + 1);
        Ok(true)
    }
    fn check_sig(&self, _: &crate::signature::Decoded, _: &[u8], _: &script::Code) -> bool {
        panic!("PQ opcode called ECDSA")
    }
    fn check_lock_time(&self, _: i64) -> bool {
        false
    }
}

#[test]
fn opcode_family_roundtrips_rejects_legacy_and_preserves_legacy_counts() {
    for (op, name, accurate, conservative) in [
        (0xba, "OP_CHECKSIG_PQ", 1, 1),
        (0xbb, "OP_CHECKSIGVERIFY_PQ", 1, 1),
        (0xbc, "OP_CHECKMULTISIG_PQ", 2, 20),
        (0xbd, "OP_CHECKMULTISIGVERIFY_PQ", 2, 20),
    ] {
        let code = script::Code(vec![op]);
        assert_eq!(code.to_bytes(), vec![op]);
        assert_eq!(code.to_asm(false), name);
        let checker = Counting(Cell::new(0));
        assert!(matches!(
            code.eval(Flags::empty(), &checker, Stack::new()),
            Err(script::Error::Interpreter(_, interpreter::Error::BadOpcode))
        ));
        let inactive = script::Code(vec![0, 0x63, 0x52, op, 0x68, 0x51]);
        assert_eq!(
            script::Raw::from_raw_parts(vec![], inactive.0.clone()).eval(Flags::empty(), &checker),
            Ok(true)
        );
        assert_eq!(inactive.sig_op_count(true), 0);
        assert_eq!(sig_op_count(&inactive, true), accurate);
        assert_eq!(sig_op_count(&inactive, false), conservative);
        assert_eq!(checker.0.get(), 0);
    }
}

#[test]
fn operation_budget_stops_before_the_extra_signature_attempt() {
    for count in [201, 202] {
        let code = script::Code([0, 0, 0xba].repeat(count));
        let checker = Counting(Cell::new(0));
        let result = eval(&[], &code, &code, Flags::empty(), &checker);
        if count == 201 {
            assert_eq!(result, Ok(true));
        } else {
            assert!(matches!(
                result,
                Err(Error::Script(script::Error::Interpreter(
                    _,
                    interpreter::Error::OpCount
                )))
            ));
        }
        assert_eq!(checker.0.get(), 201);
    }
}

#[test]
fn serialized_argument_limits_and_minimal_pushes_are_enforced() {
    assert_eq!(
        run(
            &push(&vec![1; MAX_PUSH_BYTES]),
            &[0x75, 0x51],
            Flags::MinimalData
        ),
        Ok(true)
    );
    assert_eq!(
        run(&push(&vec![1; MAX_PUSH_BYTES + 1]), &[0x51], Flags::empty()),
        Err(Error::PushSize)
    );
    for input in [vec![0x4c], vec![0x4d, 1], vec![0x4d, 1, 0], vec![0x01]] {
        assert_eq!(
            run(&input, &[0x51], Flags::empty()),
            Err(Error::TruncatedPush)
        );
    }
    assert_eq!(
        run(&[0xac], &[0x51], Flags::empty()),
        Err(Error::NotPushOnly)
    );
    assert_eq!(
        run(&[0x4e, 255, 255, 255, 255], &[0x51], Flags::empty()),
        Err(Error::PushSize)
    );
    for (canonical, alternate) in [
        (vec![0], vec![0x4c, 0]),
        (vec![0x51], vec![1, 1]),
        (vec![0x4f], vec![1, 0x81]),
    ] {
        assert_eq!(run(&canonical, &[0x75, 0x51], Flags::MinimalData), Ok(true));
        assert!(matches!(
            run(&alternate, &[0x51], Flags::MinimalData),
            Err(Error::Script(script::Error::Interpreter(
                _,
                interpreter::Error::MinimalData
            )))
        ));
        assert_eq!(run(&alternate, &[0x51], Flags::empty()), Ok(true));
    }
}

#[test]
fn exact_total_input_and_stack_element_boundaries() {
    let mut input = Vec::new();
    while input.len() + MAX_PUSH_BYTES + 3 < MAX_INPUT_BYTES {
        input.extend(push(&vec![1; MAX_PUSH_BYTES]));
    }
    input.extend(push(&vec![1; MAX_INPUT_BYTES - input.len() - 3]));
    assert_eq!(input.len(), MAX_INPUT_BYTES);
    assert_eq!(run(&input, &[0x51], Flags::empty()), Ok(true));
    input.push(0);
    assert_eq!(run(&input, &[0x51], Flags::empty()), Err(Error::InputSize));
    assert_eq!(run(&vec![0; 1000], &[], Flags::empty()), Ok(false));
    assert!(matches!(
        run(&vec![0; 1001], &[], Flags::empty()),
        Err(Error::Script(script::Error::Interpreter(
            _,
            interpreter::Error::StackSize(_)
        )))
    ));
    assert_eq!(run(&[0x51], &[], Flags::CleanStack), Ok(true));
    assert_eq!(
        run(&[0x51, 0x51], &[], Flags::CleanStack),
        Err(Error::Script(script::Error::CleanStack))
    );
}

#[test]
fn combined_stack_bytes_include_the_alternate_stack() {
    let input = push(&vec![1; MAX_PUSH_BYTES]);
    let copies = MAX_STACK_BYTES / MAX_PUSH_BYTES;
    let mut body = vec![0x76; copies - 1];
    body.extend([0x6b, 0x51]); // TOALTSTACK, true: payload is still under the bound.
    assert_eq!(run(&input, &body, Flags::empty()), Ok(true));
    body.pop();
    body.push(0x76); // Another DUP exceeds the combined bound.
    assert!(matches!(
        run(&input, &body, Flags::empty()),
        Err(Error::Script(script::Error::Interpreter(
            _,
            interpreter::Error::PqStackBytes
        )))
    ));
}

#[test]
fn new_operations_reject_without_a_pq_checker_even_when_flag_is_enabled() {
    let checker = NullSignatureChecker();
    let code = script::Code(vec![0, 0, 0xba]);
    assert!(matches!(
        eval(&[], &code, &code, Flags::empty(), &checker),
        Err(Error::Script(script::Error::Interpreter(
            _,
            interpreter::Error::BadOpcode
        )))
    ));
}
