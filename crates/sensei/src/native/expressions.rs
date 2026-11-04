//! Test-only expression imports and historical audit encoding.

use alloc::vec::Vec;
pub(crate) use sensei_shared::expressions::*;

const CONTAINER_MAGIC: &[u8; 4] = b"IWXP";
const CONTAINER_FORMAT_VERSION: u16 = 1;
const CONTAINER_HEADER_LEN: usize = 8;

fn compile_into(expression: &Expression, bytecode: &mut Vec<u8>) {
    match expression {
        Expression::Fixed(index) => bytecode.extend([3, *index]),
        Expression::Advice(index) => bytecode.extend([4, *index]),
        Expression::Instance(index) => bytecode.extend([5, *index]),
        Expression::Constant(index) => bytecode.extend([6, *index]),
        Expression::Sum(left, right) => {
            compile_into(left, bytecode);
            compile_into(right, bytecode);
            bytecode.push(0);
        }
        Expression::Product(left, right) => {
            compile_into(left, bytecode);
            compile_into(right, bytecode);
            bytecode.push(1);
        }
        Expression::Negated(inner) => {
            compile_into(inner, bytecode);
            bytecode.push(2);
        }
        Expression::ConstantScaled(inner, index) => {
            compile_into(inner, bytecode);
            bytecode.extend([7, *index]);
        }
    }
}

/// Serializes the frozen-spec pin in the historical `IWXP/1` encoding:
/// magic, version, program count, the `u16` length table, then the
/// concatenated program bytes. `None` when the program count or a program
/// length is out of the container's range.
pub fn encode_container(programs: &[Expression]) -> Option<Vec<u8>> {
    if programs.len() != PROGRAM_COUNT {
        return None;
    }
    let mut bodies = Vec::with_capacity(PROGRAM_COUNT);
    for program in programs {
        let mut bytecode = Vec::new();
        compile_into(program, &mut bytecode);
        u16::try_from(bytecode.len()).ok()?;
        bodies.push(bytecode);
    }
    let mut container = Vec::with_capacity(
        CONTAINER_HEADER_LEN + 2 * PROGRAM_COUNT + bodies.iter().map(Vec::len).sum::<usize>(),
    );
    container.extend(CONTAINER_MAGIC);
    container.extend(CONTAINER_FORMAT_VERSION.to_le_bytes());
    container.extend((PROGRAM_COUNT as u16).to_le_bytes());
    for body in &bodies {
        container.extend((body.len() as u16).to_le_bytes());
    }
    for body in &bodies {
        container.extend(body);
    }
    Some(container)
}
