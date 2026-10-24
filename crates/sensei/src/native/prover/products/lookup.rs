//! Lookup grand-product construction with a zero-preserving fallback.

#[cfg(test)]
use super::two_lane_exclusive_walk;
use crate::Error;
use crate::native::curve::VestaPoint;
use crate::native::field::Fp;
#[cfg(test)]
use crate::native::prover::PermutedLookup;
use crate::native::prover::{LookupProduct, ProductForms};
use crate::native::randomness::ProductBlinding;
use crate::native::target::{BLINDING_FACTORS, N};
use crate::native::worker::Execution;

/// Builds one lookup's exclusive grand product
/// `z_i = Π_{j<i} (a_j+β)(s_j+γ) / ((a'_j+β)(s'_j+γ))` over the scanned rows.
///
/// The numerator prefix products are accumulated forward into the column and
/// the denominator prefix product is inverted once; a backward walk then
/// recovers every exclusive denominator-prefix inverse from the row
/// denominators, so each row costs six multiplications instead of the seven
/// of a batch inversion followed by a ratio scan — in two interleaved lanes
/// ([`two_lane_exclusive_walk`]). Field arithmetic is exact,
/// so the field values equal the ratio scan's. A zero denominator,
/// which the grouped inverter left in place as a zero inverse, is negligible
/// for honest challenges and keeps that reference behaviour through the
/// fallback.
#[cfg(test)]
pub(super) fn prepare_lookup_product(
    permuted: &PermutedLookup,
    compressed_table: &[Fp],
    blinding: ProductBlinding,
    beta: &Fp,
    gamma: &Fp,
    execution: Execution<'_>,
) -> Result<LookupProduct, Error> {
    const SCAN_ROWS: usize = N - BLINDING_FACTORS;
    if permuted.compressed_input.len() != N
        || permuted.permuted_input.len() != N
        || permuted.permuted_table.len() != N
        || compressed_table.len() != N
        || blinding.rows.len() != BLINDING_FACTORS
    {
        return Err(Error::InternalInvariant);
    }

    let mut denominators = execution.buffer(SCAN_ROWS, false);
    let mut column = execution.buffer(N, false);
    let walk = two_lane_exclusive_walk(
        SCAN_ROWS,
        |row| {
            let numerator = permuted.compressed_input[row]
                .add(beta)
                .mul(&compressed_table[row].add(gamma));
            let denominator = permuted.permuted_input[row]
                .add(beta)
                .mul(&permuted.permuted_table[row].add(gamma));
            Ok((numerator, denominator))
        },
        &mut column[..SCAN_ROWS],
        &mut denominators,
    )?;

    match walk {
        Some(_) => {}
        None => {
            // Reference form: zero denominators invert to zero and zero the
            // running product from the following row on.
            let mut prefixes = execution.buffer(denominators.len(), false);
            crate::native::field::batch_invert(&mut denominators, &mut prefixes);
            let inverses = &denominators;
            let mut state = <Fp>::ONE;
            for row in 0..SCAN_ROWS {
                let numerator = permuted.compressed_input[row]
                    .add(beta)
                    .mul(&compressed_table[row].add(gamma));
                column[row] = state;
                state = state.mul(&numerator).mul(&inverses[row]);
            }
        }
    }
    column[SCAN_ROWS..].clone_from_slice(&blinding.rows);

    Ok(LookupProduct {
        forms: ProductForms::staged_rows(column)?,
        blind: blinding.blind,
        commitment: VestaPoint::IDENTITY,
    })
}

/// Builds the row product of a lookup paired with its own compressed table.
///
/// The certificate guarantees separate input/table permutations on the first
/// `USABLE_ROWS_END` rows. Their shifted factor products therefore agree for
/// every challenge, including zero factors. The last published exclusive
/// state does not depend on the next (masked) row's factor.
pub(super) fn prepare_certified_lookup_product(
    input: &crate::native::prover::lookup::CertifiedLookupProductInput,
    blinding: ProductBlinding,
    beta: &Fp,
    gamma: &Fp,
    execution: Execution<'_>,
) -> Result<LookupProduct, Error> {
    use crate::native::target::USABLE_ROWS_END;
    const SCAN_ROWS: usize = N - BLINDING_FACTORS;
    const _: () = assert!(USABLE_ROWS_END + 1 == SCAN_ROWS);
    let (permuted, compressed_table) = input.parts();
    if permuted.compressed_input.len() != N
        || permuted.permuted_input.len() != N
        || permuted.permuted_table.len() != N
        || compressed_table.len() != N
        || blinding.rows.len() != BLINDING_FACTORS
    {
        return Err(Error::InternalInvariant);
    }

    let mut denominators = execution.buffer(SCAN_ROWS, false);
    let mut column = execution.buffer(N, false);
    paired_equal_product(
        USABLE_ROWS_END,
        |row| {
            let numerator = permuted.compressed_input[row]
                .add(beta)
                .mul(&compressed_table[row].add(gamma));
            let denominator = permuted.permuted_input[row]
                .add(beta)
                .mul(&permuted.permuted_table[row].add(gamma));
            (numerator, denominator)
        },
        &mut column[..SCAN_ROWS],
        &mut denominators,
    );
    column[SCAN_ROWS..].clone_from_slice(&blinding.rows);

    Ok(LookupProduct {
        forms: ProductForms::staged_rows(column)?,
        blind: blinding.blind,
        commitment: VestaPoint::IDENTITY,
    })
}

// The caller guarantees equal total factors through the input/table
// permutations; equality of challenge products does not establish eligibility.
fn paired_equal_product(
    n: usize,
    mut factors: impl FnMut(usize) -> (Fp, Fp),
    states: &mut [Fp],
    denominators: &mut [Fp],
) {
    assert!(states.len() > n);
    assert!(denominators.len() >= n);
    if n == 0 {
        states[0] = <Fp>::ONE;
        return;
    }

    // Materialize both factors exactly once per row in a single pass.
    // The paired walk reuses these buffers for prefixes and denominator pairs.
    for row in 0..n {
        let (numerator, denominator) = factors(row);
        states[row] = numerator;
        denominators[row] = denominator;
    }

    let mut numerator_prefix = <Fp>::ONE;
    let first_numerator = states[0];
    states[0] = numerator_prefix;
    numerator_prefix = numerator_prefix.mul(&first_numerator);

    let mut pair_count = 0;
    let mut low_row = 1;
    while low_row + 1 < n {
        let high_row = low_row + 1;
        let low = denominators[low_row];
        let high = denominators[high_row];
        let pair = low.mul(&high);
        pair_count += 1;
        // Retain raw low when high is zero: fallback can still identify the
        // first original zero and recover the nonzero prefix without a backup.
        if !high.is_zero() {
            denominators[low_row] = pair;
        }
        let low_numerator = states[low_row];
        states[low_row] = numerator_prefix;
        numerator_prefix = numerator_prefix.mul(&low_numerator);
        let high_numerator = states[high_row];
        states[high_row] = numerator_prefix;
        numerator_prefix = numerator_prefix.mul(&high_numerator);
        low_row += 2;
    }
    if low_row < n {
        let numerator = states[low_row];
        states[low_row] = numerator_prefix;
        numerator_prefix = numerator_prefix.mul(&numerator);
    }

    // Equal factor products make this the denominator total, including zero.
    if let Some(inverse) = numerator_prefix.invert() {
        states[n] = <Fp>::ONE;
        apply_paired_prefix::<true>(states, denominators, n, inverse);
    } else {
        let mut denominator_prefix = <Fp>::ONE;
        let mut first_zero = None;
        if denominators[0].is_zero() {
            first_zero = Some(0);
        } else {
            denominator_prefix = denominators[0];
            for pair_index in 0..pair_count {
                let low_row = 1 + 2 * pair_index;
                let high_row = low_row + 1;
                let low_or_pair = denominators[low_row];
                let high = denominators[high_row];
                if low_or_pair.is_zero() {
                    first_zero = Some(low_row);
                    break;
                }
                denominator_prefix = denominator_prefix.mul(&low_or_pair);
                if high.is_zero() {
                    first_zero = Some(high_row);
                    break;
                }
            }
        }
        let remainder_row = 1 + 2 * pair_count;
        if first_zero.is_none() && remainder_row < n {
            if denominators[remainder_row].is_zero() {
                first_zero = Some(remainder_row);
            } else {
                denominator_prefix = denominator_prefix.mul(&denominators[remainder_row]);
            }
        }
        let first_zero = first_zero.expect("equal zero product has a zero denominator");
        if first_zero > 0 {
            apply_paired_prefix::<false>(
                states,
                denominators,
                first_zero,
                denominator_prefix
                    .invert()
                    .expect("prefix before first zero"),
            );
        }
        states[first_zero + 1..=n].fill(<Fp>::ZERO);
    }
}

fn apply_paired_prefix<const EQUAL_ENDPOINT: bool>(
    states: &mut [Fp],
    denominators: &[Fp],
    n: usize,
    mut inverse: Fp,
) {
    debug_assert!(n > 0);
    if !EQUAL_ENDPOINT {
        states[n] = states[n].mul(&inverse);
    }
    let pair_count = (n - 1) / 2;
    let remainder_row = 1 + 2 * pair_count;
    if remainder_row < n {
        inverse = inverse.mul(&denominators[remainder_row]);
        states[remainder_row] = states[remainder_row].mul(&inverse);
    }
    for pair_index in (0..pair_count).rev() {
        let low_row = 1 + 2 * pair_index;
        let high_row = low_row + 1;
        let high_inverse = inverse.mul(&denominators[high_row]);
        let next_inverse = inverse.mul(&denominators[low_row]);
        states[high_row] = states[high_row].mul(&high_inverse);
        states[low_row] = states[low_row].mul(&next_inverse);
        inverse = next_inverse;
    }
}

#[cfg(test)]
mod certified_tests {
    use super::*;
    use crate::native::buffer::BufferPool;
    use crate::native::polynomial::SharedPoly;
    use crate::native::prover::{LookupPrefix, lookup::permute_usable_values};
    use crate::native::target::USABLE_ROWS_END;
    use crate::native::test_support::reduced_values;
    use alloc::{vec, vec::Vec};
    use udon::field::{PallasBase, PrimeModulus};

    fn prefix(all_zero: bool) -> LookupPrefix {
        let loose_zero = <Fp>::from_montgomery_limbs(PallasBase::MODULUS);
        assert!(loose_zero.is_zero());
        assert_ne!(loose_zero.montgomery_limbs(), <Fp>::ZERO.montgomery_limbs());
        assert_ne!(
            <Fp>::ONE.add(&loose_zero).montgomery_limbs(),
            <Fp>::ONE.montgomery_limbs()
        );
        let mut tables = Vec::new();
        let lookups = core::array::from_fn(|lookup| {
            let values = (0..USABLE_ROWS_END)
                .map(|row| {
                    let value = if all_zero {
                        <Fp>::ZERO
                    } else {
                        <Fp>::from_u64((lookup * 10_000 + row) as u64)
                    };
                    if row % 2 == 0 {
                        value.add(&loose_zero)
                    } else {
                        value
                    }
                })
                .collect::<Vec<_>>();
            let mut input = values.iter().rev().copied().collect::<Vec<_>>();
            let mut table = values;
            let (mut permuted_input, mut permuted_table) =
                permute_usable_values(input.clone(), table.clone()).unwrap();
            // The six masked rows need not be permutations of their originals.
            for row in USABLE_ROWS_END..N {
                input.push(<Fp>::from_u64((900_000 + lookup * 100 + row) as u64));
                table.push(<Fp>::from_u64((800_000 + lookup * 100 + row) as u64));
                permuted_input.push(<Fp>::from_u64((700_000 + lookup * 100 + row) as u64));
                permuted_table.push(<Fp>::from_u64((600_000 + lookup * 100 + row) as u64));
            }
            tables.push(SharedPoly::new(table));
            PermutedLookup {
                compressed_input: SharedPoly::new(input),
                permuted_input: SharedPoly::new(permuted_input),
                permuted_table: SharedPoly::new(permuted_table),
                input_blind: <Fp>::from_u64(31),
                table_blind: <Fp>::from_u64(37),
                input_commitment: VestaPoint::IDENTITY,
                table_commitment: VestaPoint::IDENTITY,
            }
        });
        LookupPrefix {
            lookups: vec![lookups],
            compressed_tables: tables.try_into().ok().unwrap(),
            beta: <Fp>::ONE,
            gamma: <Fp>::from_u64(7),
        }
    }

    fn raw_input(
        input: &crate::native::prover::lookup::CertifiedLookupProductInput,
    ) -> Vec<[u64; 4]> {
        let (permuted, table) = input.parts();
        permuted
            .compressed_input
            .iter()
            .chain(permuted.permuted_input.iter())
            .chain(permuted.permuted_table.iter())
            .chain(table.iter())
            .map(|value| value.montgomery_limbs())
            .collect()
    }

    #[test]
    fn certified_lookup_rows_match_literal_scan_with_dirty_zero_and_masked_tails() {
        let pool = BufferPool::default();
        pool.provision(N, 3, <Fp>::ONE);
        let inventory = pool.inventory();
        let execution = crate::test_codec::execution().with_buffers(&pool);
        for all_zero in [false, true] {
            let prefix = prefix(all_zero);
            for (lookup, input) in prefix.certified_product_inputs(0).unwrap().enumerate() {
                let before = raw_input(&input);
                let (permuted, table) = input.parts();
                // Normal -> early/low/high/last/extra-only zero -> zero challenges -> normal.
                for case in 0..8 {
                    pool.dirty(<Fp>::from_u64((97 + case) as u64));
                    let zero_at = match case {
                        1 => Some(0),
                        2 => Some(1),
                        3 => Some(2),
                        4 => Some(USABLE_ROWS_END - 1),
                        5 => Some(USABLE_ROWS_END),
                        _ => None,
                    };
                    let beta = if case == 6 {
                        <Fp>::ZERO
                    } else {
                        zero_at.map_or(<Fp>::ONE, |row| permuted.permuted_input[row].neg())
                    };
                    let gamma = if case == 6 {
                        <Fp>::ZERO
                    } else {
                        <Fp>::from_u64(7)
                    };
                    let blinding = || ProductBlinding {
                        rows: core::array::from_fn(|row| {
                            <Fp>::from_u64((11 + row + lookup * 17) as u64)
                        }),
                        blind: <Fp>::from_u64((73 + lookup) as u64),
                    };
                    let mut expected = Vec::with_capacity(N);
                    let mut state = <Fp>::ONE;
                    for (row, table_value) in table[..N - BLINDING_FACTORS].iter().enumerate() {
                        expected.push(state);
                        let numerator = permuted.compressed_input[row]
                            .add(&beta)
                            .mul(&table_value.add(&gamma));
                        let denominator = permuted.permuted_input[row]
                            .add(&beta)
                            .mul(&permuted.permuted_table[row].add(&gamma));
                        state = state
                            .mul(&numerator)
                            .mul(&denominator.invert().unwrap_or(<Fp>::ZERO));
                    }
                    expected.extend_from_slice(&blinding().rows);
                    let actual = prepare_certified_lookup_product(
                        &input,
                        blinding(),
                        &beta,
                        &gamma,
                        execution,
                    )
                    .unwrap();
                    assert_eq!(
                        reduced_values(&actual.forms.staged().unwrap()[..]),
                        reduced_values(&expected)
                    );
                    assert_eq!(
                        actual.blind.montgomery_limbs(),
                        blinding().blind.montgomery_limbs()
                    );
                    assert_eq!(raw_input(&input), before);
                    drop(actual);
                    assert_eq!(pool.inventory(), inventory);
                    // The general construction is an independent oracle, including
                    // zeros in the unused factor that trigger its fallback.
                    let general = prepare_lookup_product(
                        permuted,
                        table,
                        blinding(),
                        &beta,
                        &gamma,
                        execution,
                    )
                    .unwrap();
                    assert_eq!(
                        reduced_values(&general.forms.staged().unwrap()[..]),
                        reduced_values(&expected)
                    );
                    drop(general);
                    assert_eq!(pool.inventory(), inventory);
                    assert_eq!(raw_input(&input), before);
                }
            }
        }
    }
}
