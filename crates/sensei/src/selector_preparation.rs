//! Sensei's complete selector rows, shared by warmup and its local generator.

use sensei_shared::{constants::constant, queries::GATE_QUERY_COUNT};
use udon::field::Fp;

pub(crate) const PREPARED_GATE_SELECTOR_COUNT: usize = 50;
pub(crate) const PREPARED_GATE_SELECTOR_ROW: usize = PREPARED_GATE_SELECTOR_COUNT;
pub(crate) use sensei_shared::selectors::PREPARED_GATE_SELECTOR_FIXED_QUERY;

// Gate-frame query slots paired with shared selector-row prefix slots,
// in the order their four remaining selectors occupy the complete row.
const SEVEN_ROOT_QUERY_PREFIX_SLOTS: [(usize, usize); 3] = [(46, 40), (47, 38), (48, 39)];
// Constant-pool indices for roots 4, 5, 6, and 7, in that order.
const REMAINING_ROOT_CONSTANT_INDICES: [usize; 4] = [2, 3, 4, 12];

/// The shared recipe's first 38 selectors, followed by the four remaining
/// seven-root selectors for frame slots 46, 47, and 48, in that order.
/// Completing these fixed polynomials here removes 25 products per fold row.
pub(crate) fn prepare_gate_selectors(q: &[Fp; GATE_QUERY_COUNT]) -> [Fp; 50] {
    let partial = sensei_shared::selectors::prepare_gate_selectors(q);
    let mut result = [Fp::ZERO; 50];
    result[..38].copy_from_slice(&partial[..38]);
    for (bank, (frame_slot, prefix_slot)) in SEVEN_ROOT_QUERY_PREFIX_SLOTS.into_iter().enumerate() {
        let [a, b, c, d] = REMAINING_ROOT_CONSTANT_INDICES.map(|i| constant(i).sub(&q[frame_slot]));
        let ab = partial[prefix_slot].mul(&a).mul(&b);
        let cd = partial[prefix_slot].mul(&c).mul(&d);
        result[38 + bank * 4..42 + bank * 4].copy_from_slice(&[
            cd.mul(&b),
            cd.mul(&a),
            ab.mul(&d),
            ab.mul(&c),
        ]);
    }
    result
}
