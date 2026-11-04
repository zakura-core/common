//! Test-only transform adapters and polynomial division references.
//!
//! The transform adapters share Udon FFTs and domain metadata with production.
//! The allocating synthetic division and sparse vanishing recurrence remain
//! separate algorithms from the production division paths they check.

use super::{
    CosetTiles, EXTENDED_TILE_COUNT, EXTENDED_TILE_LEN, ExtendedCosetTiles,
    base_coefficients_to_extended_coset_tiles, expansion, plan, residue_transforms,
};
use alloc::{sync::Arc, vec, vec::Vec};
use udon::{
    exec::{ExecutionOptions, SerialExecutor},
    field::{PastaField, PrimeModulus},
};

#[cfg(test)]
pub(crate) fn ifft<M: PrimeModulus>(values: &mut [PastaField<M>]) -> bool {
    plan(values.len(), false).is_some_and(|p| {
        p.inverse(
            values,
            ExecutionOptions::default(),
            &SerialExecutor,
            &mut [],
        )
        .is_ok()
    })
}
#[cfg(test)]
pub(crate) fn fft<M: PrimeModulus>(values: &mut [PastaField<M>]) -> bool {
    plan(values.len(), false).is_some_and(|p| {
        p.forward(
            values,
            ExecutionOptions::default(),
            &SerialExecutor,
            &mut [],
        )
        .is_ok()
    })
}
#[cfg(test)]
pub(crate) fn coset_fft<M: PrimeModulus>(values: &mut [PastaField<M>]) -> bool {
    plan(values.len(), true).is_some_and(|p| {
        p.forward(
            values,
            ExecutionOptions::default(),
            &SerialExecutor,
            &mut [],
        )
        .is_ok()
    })
}
#[cfg(test)]
pub(crate) fn coset_ifft<M: PrimeModulus>(values: &mut [PastaField<M>]) -> bool {
    plan(values.len(), true).is_some_and(|p| {
        p.inverse(
            values,
            ExecutionOptions::default(),
            &SerialExecutor,
            &mut [],
        )
        .is_ok()
    })
}
#[cfg(test)]
pub(crate) fn coset_fft_with_nonzero_prefix<M: PrimeModulus>(
    values: &mut [PastaField<M>],
    prefix: usize,
) -> bool {
    use udon::fft::{Direction, InputSupport, TransformRequest};

    let Some(plan) = plan(values.len(), true) else {
        return false;
    };
    if prefix > values.len() {
        return false;
    }
    plan.execute(
        TransformRequest {
            support: InputSupport::Prefix(prefix),
            ..TransformRequest::new(Direction::Forward)
        },
        None,
        values,
        ExecutionOptions::default(),
        &SerialExecutor,
        &mut [],
    )
    .is_ok()
}

#[cfg(test)]
pub(crate) fn base_coefficients_to_class_2n_coset_tiles<M: PrimeModulus>(
    coefficients: &[PastaField<M>],
) -> Option<CosetTiles<M, 2>> {
    residue_transforms(coefficients)
}
#[cfg(test)]
pub(crate) fn short_coefficients_times_factor_coset_tiles<M: PrimeModulus>(
    short: &[PastaField<M>],
    factor: Arc<ExtendedCosetTiles<M>>,
) -> Option<ExtendedCosetTiles<M>> {
    let expansion = expansion(EXTENDED_TILE_COUNT)?;
    let mut output = vec![PastaField::ZERO; factor.values.len()];
    expansion
        .short_product(
            short,
            expansion.view(&factor.values),
            &mut output,
            ExecutionOptions::default(),
            &SerialExecutor,
            &mut [],
        )
        .ok()?;
    CosetTiles::from_flat(output)
}
#[cfg(test)]
pub(crate) fn base_lagrange_to_extended_coset_tiles<M: PrimeModulus>(
    values: &[PastaField<M>],
) -> Option<ExtendedCosetTiles<M>> {
    let mut output = vec![PastaField::ZERO; EXTENDED_TILE_COUNT * EXTENDED_TILE_LEN];
    expansion(EXTENDED_TILE_COUNT)?
        .evaluations(
            values,
            &mut output,
            ExecutionOptions::default(),
            &SerialExecutor,
            &mut [],
        )
        .ok()?;
    CosetTiles::from_flat(output)
}
#[cfg(test)]
pub(crate) fn base_lagrange_to_extended_coset<M: PrimeModulus>(
    values: &mut Vec<PastaField<M>>,
) -> bool {
    match base_lagrange_to_extended_coset_tiles(values) {
        Some(output) => {
            *values = output.to_dense_rows();
            true
        }
        None => false,
    }
}
#[cfg(test)]
pub(crate) fn base_coefficients_to_extended_coset<M: PrimeModulus>(
    values: &[PastaField<M>],
) -> Option<Vec<PastaField<M>>> {
    Some(base_coefficients_to_extended_coset_tiles(values)?.to_dense_rows())
}
/// Divides `polynomial(X) - polynomial(point)` by `X - point`.
///
/// Returns the quotient in ascending coefficient order and the evaluation
/// that was subtracted.
#[cfg(test)]
pub(crate) fn synthetic_division<M: PrimeModulus>(
    coefficients: &[PastaField<M>],
    point: &PastaField<M>,
) -> (Vec<PastaField<M>>, PastaField<M>) {
    let Some(highest) = coefficients.last() else {
        return (Vec::with_capacity(0), PastaField::ZERO);
    };
    if coefficients.len() == 1 {
        return (Vec::with_capacity(0), *highest);
    }

    let mut quotient = alloc::vec![ PastaField::ZERO; coefficients.len() - 1];
    quotient[coefficients.len() - 2] = *highest;
    for index in (1..coefficients.len() - 1).rev() {
        quotient[index - 1] = point.mul_add(&quotient[index], &coefficients[index]);
    }
    let evaluation = point.mul_add(&quotient[0], &coefficients[0]);
    (quotient, evaluation)
}

/// Divides `polynomial(X) - polynomial(point)` by `X - point` in place.
///
/// The input is replaced with the quotient in ascending coefficient order;
/// the returned value is the evaluation that was subtracted.
#[cfg(test)]
pub(crate) fn synthetic_division_in_place<M: PrimeModulus>(
    coefficients: &mut Vec<PastaField<M>>,
    point: &PastaField<M>,
) -> PastaField<M> {
    let remainder_len = udon::polynomial::divide_linear_in_place(coefficients, point);
    let remainder = coefficients.first().copied().unwrap_or(PastaField::ZERO);
    coefficients.copy_within(remainder_len.., 0);
    coefficients.truncate(coefficients.len() - remainder_len);
    remainder
}

/// Converts a numerator from extended-coset evaluations to coefficients and
/// divides it by `X^block_len - 1` using the sparse inverse in the coset ring.
///
/// Test-only: production divides by the constant per-sub-coset
/// vanishing values inside the fold and interpolates through prepared tiled
/// transforms; the telescope remains the independent reference the
/// algebra tests pin both paths against.
#[cfg(test)]
pub(crate) fn quotient_numerator_to_coefficients<M: PrimeModulus>(
    mut evaluations: Vec<PastaField<M>>,
    block_len: usize,
) -> Option<Vec<PastaField<M>>> {
    if block_len == 0
        || evaluations.len() <= block_len
        || !evaluations.len().is_multiple_of(block_len)
    {
        return None;
    }
    if !coset_ifft(&mut evaluations) {
        return None;
    }

    let block_count = evaluations.len() / block_len;
    let sparse_divisor = PastaField::<M>::ZETA
        .pow_u64(evaluations.len() as u64)
        .sub(&PastaField::<M>::ONE)
        .invert()?;
    for column in 0..block_len {
        let mut block_sum = evaluations[column];
        for block in 1..block_count {
            block_sum = block_sum.add(&evaluations[block * block_len + column]);
        }

        let h_last = block_sum.mul(&sparse_divisor);
        let mut h_next = h_last;
        let mut numerator = evaluations[(block_count - 1) * block_len + column];
        for block in (1..block_count).rev() {
            let output = (block - 1) * block_len + column;
            let previous_numerator = evaluations[output];
            let h_previous = numerator.add(&h_next);
            evaluations[output] = h_previous;
            numerator = previous_numerator;
            h_next = h_previous;
        }
        evaluations[(block_count - 1) * block_len + column] = h_last;
    }
    Some(evaluations)
}
