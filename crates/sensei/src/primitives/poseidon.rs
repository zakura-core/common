//! Orchard's width-three, rate-two Poseidon permutation and hash.
use super::Fp;
use udon::field::Fp as Native;

/// Applies the Orchard `P128Pow5T3` permutation in place.
pub fn permute(state: &mut [Fp; 3]) {
    let mut native = state.map(Fp::native);
    permute_native(&mut native);
    *state = native.map(Fp::from_native);
}
fn permute_native(state: &mut [Native; 3]) {
    let parameters = udon::poseidon::PALLAS_BASE_T3;
    let half = parameters.full_rounds / 2;
    let sbox = |x: Native| x.square().square().mul(&x);
    for (round, constants) in parameters.round_constants.iter().enumerate() {
        for (value, constant) in state.iter_mut().zip(constants) {
            *value = value.add(constant);
        }
        if round < half || round >= half + parameters.partial_rounds {
            *state = state.map(sbox);
        } else {
            state[0] = sbox(state[0]);
        }
        *state = parameters
            .mds
            .map(|row| Native::sum_of_products(&row, state));
    }
}

/// Hashes two field elements using Orchard's constant-length domain separation.
pub fn hash(input: [Fp; 2]) -> Fp {
    // ConstantLength<2>: the message length occupies the high half of capacity.
    const CAPACITY: u128 = 2 << 64;
    let mut state = [
        input[0].native(),
        input[1].native(),
        Native::from_u128(CAPACITY),
    ];
    permute_native(&mut state);
    Fp::from_native(state[0])
}
