use super::*;
use crate::interpreter::{Flags, NullSignatureChecker, SignatureChecker, Stack, State};

fn blob(size: usize, offset: u8) -> Vec<u8> {
    (0..size)
        .map(|index| offset + u8::try_from(index / 512).unwrap())
        .collect()
}

fn chunks() -> Vec<Vec<u8>> {
    blob(2144, 10)
        .chunks(512)
        .map(|chunk| chunk.to_vec())
        .chain(core::iter::once(vec![20; 32]))
        .chain(core::iter::once(vec![3; 32]))
        .collect()
}

fn state(values: Vec<Vec<u8>>) -> State {
    let mut stack = Stack::new();
    for value in values {
        stack.push(value);
    }
    State::initial(stack)
}

struct Checker;
impl SignatureChecker for Checker {
    fn check_sig(&self, _: &crate::signature::Decoded, _: &[u8], _: &script::Code) -> bool {
        panic!("WOTS execution must not request an EC signature check")
    }
    fn check_lock_time(&self, _: i64) -> bool {
        false
    }
    fn check_wots(&self, signature: &[u8], public_seed: &[u8], commitment: &[u8]) -> bool {
        signature == blob(2144, 10) && public_seed == [20; 32] && commitment == [3; 32]
    }
}

fn run(
    state: State,
    flags: Flags,
    checker: &dyn SignatureChecker,
) -> Result<State, interpreter::Error> {
    PossiblyBad::Bad(Bad::Unknown(0xba)).eval(flags, &script::Code(vec![]), checker, state)
}

#[test]
fn wots_reassembles_chunks_in_order_and_requires_runtime_activation() {
    assert!(run(state(chunks()), Flags::empty(), &Checker).is_err());
    let result = run(state(chunks()), Flags::CHECKWOTS, &Checker).unwrap();
    assert_eq!(result.stack.len(), 1);
    assert_eq!(result.stack.last().unwrap(), &vec![1]);
}

#[test]
fn a_checker_without_wots_support_rejects_the_authorization() {
    let result = run(state(chunks()), Flags::CHECKWOTS, &NullSignatureChecker()).unwrap();
    assert!(result.stack.last().unwrap().is_empty());
}

#[test]
fn wrong_chunk_and_commitment_lengths_fail_before_verification() {
    for index in 0..7 {
        for extra in [false, true] {
            let mut values = chunks();
            if extra {
                values[index].push(0);
            } else {
                values[index].pop();
            }
            assert!(run(state(values), Flags::CHECKWOTS, &Checker).is_err());
        }
    }
    assert!(run(state(vec![]), Flags::CHECKWOTS, &Checker).is_err());
}

#[test]
fn an_unselected_wots_instruction_consumes_no_values_but_counts_toward_the_limit() {
    let mut state = state(vec![]);
    state.vexec.push(false);
    for _ in 0..201 {
        state = run(state, Flags::CHECKWOTS, &Checker).unwrap();
        assert_eq!(state.stack.len(), 0);
    }
    assert!(matches!(
        run(state, Flags::CHECKWOTS, &Checker),
        Err(interpreter::Error::OpCount)
    ));
}
