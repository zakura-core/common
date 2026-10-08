use super::*;
use crate::field::pasta::{montgomery, word};

#[cfg(all(udon_asm, not(miri)))]
#[test]
fn assembly_mul_accumulate_matches_full_width_integer_arithmetic() {
    fn check(accumulator: [u64; 8], lhs: [u64; 4], rhs: [u64; 4]) {
        let (wide, overflow) = crate::field::asm::mul_accumulate(accumulator, &lhs, &rhs);
        assert!(overflow <= 1);
        assert_eq!(
            integer(&wide) + (BigUint::from(overflow) << 512usize),
            integer(&accumulator) + integer(&lhs) * integer(&rhs)
        );
    }
    let operands = [
        [0; 4],
        [1, 0, 0, 0],
        [u64::MAX; 4],
        [0, 0, 0, u64::MAX],
        [u64::MAX, 0, u64::MAX, 0],
        [0, u64::MAX, 0, u64::MAX],
    ];
    for lhs in operands {
        for rhs in operands {
            check([0; 8], lhs, rhs);
            check([u64::MAX; 8], lhs, rhs);
            for limb in 0..8 {
                let mut accumulator = [0; 8];
                accumulator[limb] = u64::MAX;
                check(accumulator, lhs, rhs);
            }
        }
    }
    let mut state = 0x510e_527f_ade6_82d1;
    for _ in 0..4096 {
        let accumulator = limbs(&BigUint::from_bytes_le(&deterministic_bytes::<64>(
            &mut state,
        )));
        let lhs = limbs(&BigUint::from_bytes_le(&deterministic_bytes::<32>(
            &mut state,
        )));
        let rhs = limbs(&BigUint::from_bytes_le(&deterministic_bytes::<32>(
            &mut state,
        )));
        check(accumulator, lhs, rhs);
    }
}

#[cfg(all(udon_asm, not(miri)))]
#[test]
fn assembly_partial_reduce_matches_full_width_integer_arithmetic() {
    fn check(wide: [u64; 8], carry: u64, b448: [u64; 4], r2: [u64; 4]) {
        let folded = crate::field::asm::partial_reduce(wide, carry, &b448, &r2);
        assert!(folded[7] <= 1);
        assert_eq!(
            integer(&folded),
            integer(&wide[..7])
                + BigUint::from(wide[7]) * integer(&b448)
                + BigUint::from(carry) * integer(&r2)
        );
    }
    fn check_field_constants<M: PrimeModulus>(state: &mut u64) {
        for _ in 0..64 {
            let wide = limbs(&BigUint::from_bytes_le(&deterministic_bytes::<64>(state)));
            check(wide, xorshift64(state), M::B448, M::R2);
        }
    }
    // Exercise the entire permitted range, b448 < 2^253 and r2 < 2^252,
    // not only the particular residues of the two fields.
    let folding_terms = [
        ([0; 4], [0; 4]),
        (
            [u64::MAX, u64::MAX, u64::MAX, (1 << 61) - 1],
            [u64::MAX, u64::MAX, u64::MAX, (1 << 60) - 1],
        ),
    ];
    for (b448, r2) in folding_terms {
        for carry in [0, 1, u64::MAX] {
            check([0; 8], carry, b448, r2);
            check([u64::MAX; 8], carry, b448, r2);
            for limb in 0..8 {
                let mut wide = [0; 8];
                wide[limb] = u64::MAX;
                check(wide, carry, b448, r2);
            }
        }
    }
    let mut state = 0x9b05_688c_2b3e_6c1f;
    check_field_constants::<PallasBase>(&mut state);
    check_field_constants::<PallasScalar>(&mut state);
    for _ in 0..4096 {
        let wide = limbs(&BigUint::from_bytes_le(&deterministic_bytes::<64>(
            &mut state,
        )));
        let carry = xorshift64(&mut state);
        let mut b448 = limbs::<4>(&BigUint::from_bytes_le(&deterministic_bytes::<32>(
            &mut state,
        )));
        b448[3] &= (1 << 61) - 1;
        let mut r2 = limbs::<4>(&BigUint::from_bytes_le(&deterministic_bytes::<32>(
            &mut state,
        )));
        r2[3] &= (1 << 60) - 1;
        check(wide, carry, b448, r2);
    }
}

#[test]
fn limb_kernels_match_full_width_integer_arithmetic() {
    for a in [0, 1, 1 << 63, u64::MAX] {
        for b in [0, 1, 1 << 63, u64::MAX] {
            for carry in [0, 1, u64::MAX] {
                let (low, high) = word::adc(a, b, carry);
                assert_eq!(integer(&[low, high]), BigUint::from(a) + b + carry);
                for accumulator in [0, 1, u64::MAX] {
                    let (low, high) = word::mac(accumulator, a, b, carry);
                    assert_eq!(
                        integer(&[low, high]),
                        BigUint::from(a) * b + accumulator + carry
                    );
                }
            }
            for borrow in [0, 1] {
                let difference = BigInt::from(a) - b - borrow;
                let (low, high) = word::sbb(a, b, borrow);
                assert_eq!(high != 0, difference < BigInt::from(0));
                assert_eq!(
                    BigUint::from(low),
                    signed_mod(difference, &(BigUint::from(1u8) << 64usize))
                );
            }
        }
    }
    let mut values = vec![[0; 4], [1, 0, 0, 0], [u64::MAX; 4], [0, 0, 0, 1 << 63]];
    let mut state = 0xa54f_f53a_5f1d_36f1;
    values.extend(
        (0..64).map(|_| CanonicalUint::from_le_bytes(deterministic_bytes(&mut state)).limbs()),
    );
    let radix = BigUint::from(1u8) << 256usize;
    for a in &values {
        let x = integer(a);
        assert_eq!(integer(&word::square_wide(a)), &x * &x);
        for b in &values {
            let y = integer(b);
            assert_eq!(integer(&word::multiply_wide(a, b)), &x * &y);
            assert_eq!(word::compare_limbs(a, b), x.cmp(&y));
            let (sum, carry) = word::add_limbs(a, b);
            assert_eq!(carry != 0, &x + &y >= radix);
            assert_eq!(integer(&sum), (&x + &y) % &radix);
            let (difference, borrow) = word::subtract_limbs(a, b);
            assert_eq!(borrow != 0, x < y);
            assert_eq!(integer(&difference), (&x + &radix - &y) % &radix);
        }
    }
}

fn check_montgomery<M: PrimeModulus>() {
    let p = modulus::<M>();
    let radix = BigUint::from(1u8) << 256usize;
    let inverse_r = radix.modpow(&(&p - 2u8), &p);
    let mut values = samples::<M>(64)
        .into_iter()
        .map(|(_, x)| x)
        .collect::<Vec<_>>();
    values.extend([p.clone(), &p + 1u8, &radix - 1u8]);
    for a in &values {
        for b in &values {
            let product = a * b;
            if product >= &p * &radix {
                continue;
            }
            let expected = &product * &inverse_r % &p;
            assert_eq!(
                integer(&montgomery::montgomery_multiply::<M>(&limbs(a), &limbs(b))) % &p,
                expected
            );
            if a < &(&p * 2u8) && b < &(&p * 2u8) {
                // The field kernel computes the same integer as the general
                // kernel for loose inputs, and that integer stays below 2p.
                let loose = montgomery::montgomery_multiply_loose::<M>(&limbs(a), &limbs(b));
                assert_eq!(
                    loose,
                    montgomery::montgomery_multiply::<M>(&limbs(a), &limbs(b))
                );
                assert!(integer(&loose) < &p * 2u8);
            }
            assert_eq!(
                integer(&montgomery::montgomery_reduce::<M>(limbs(&product))),
                expected
            );
        }
    }
    for input in [
        BigUint::from(0u8),
        &p * &radix - 1u8,
        &p * &radix,
        &p * (&radix + &p) - 1u8,
    ] {
        let raw = integer(&montgomery::montgomery_reduce_unreduced::<M>(limbs(&input)));
        assert!(raw < &p * 3u8);
        assert_eq!(&raw % &p, &input * &inverse_r % &p);
        let reduced = montgomery::reduce_once::<M>(montgomery::reduce_once::<M>(limbs(&raw)));
        assert_eq!(integer(&reduced), &input * &inverse_r % &p);
    }
}

/// The assembly multiply must agree limb for limb with the portable kernel on
/// loose inputs, including values in `[p, 2p)`.
#[cfg(all(udon_asm, not(miri)))]
#[test]
fn assembly_multiply_matches_portable_kernel_on_loose_inputs() {
    fn check<M: PrimeModulus>() {
        let mut state = 0x6a09_e667_f3bc_c908;
        let p = modulus::<M>();
        let twice = &p * 2u8;
        let mut values: Vec<[u64; 4]> = Vec::new();
        while values.len() < 512 {
            let x = CanonicalUint::from_le_bytes(deterministic_bytes(&mut state)).limbs();
            let x = integer(&x) % &twice;
            values.push(limbs(&x));
        }
        values.extend([
            limbs(&BigUint::from(0u8)),
            limbs(&p),
            limbs(&(&twice - 1u8)),
        ]);
        for a in &values {
            for b in values.iter().step_by(7) {
                assert_eq!(
                    montgomery::montgomery_multiply_loose::<M>(a, b),
                    montgomery::montgomery_multiply_loose_rust::<M>(a, b)
                );
            }
        }
    }
    check::<PallasBase>();
    check::<PallasScalar>();
}

/// Deterministic loose residues in `[0, 2p)`, with the boundary values.
fn loose_samples<M: PrimeModulus>(mut state: u64) -> Vec<[u64; 4]> {
    let p = modulus::<M>();
    let twice = &p * 2u8;
    let mut values: Vec<[u64; 4]> = Vec::new();
    while values.len() < 512 {
        let x = CanonicalUint::from_le_bytes(deterministic_bytes(&mut state)).limbs();
        values.push(limbs(&(integer(&x) % &twice)));
    }
    values.extend([
        limbs(&BigUint::from(0u8)),
        limbs(&(&p - 1u8)),
        limbs(&p),
        limbs(&(&twice - 1u8)),
    ]);
    values
}

/// The loose addition and subtraction kernels reduce modulo `2p` exactly,
/// including the sums that carry past the radix.
#[test]
fn loose_add_and_sub_kernels_reduce_modulo_twice_modulus() {
    fn check<M: PrimeModulus>() {
        let twice = modulus::<M>() * 2u8;
        let values = loose_samples::<M>(0xbb67_ae85_84ca_a73b);
        for a in &values {
            for b in values.iter().step_by(5) {
                let (x, y) = (integer(a), integer(b));
                assert_eq!(
                    integer(&montgomery::add_twice_modulus_rust::<M>(a, b)),
                    (&x + &y) % &twice
                );
                assert_eq!(
                    integer(&montgomery::sub_twice_modulus_rust::<M>(a, b)),
                    (&x + &twice - &y) % &twice
                );
            }
        }
    }
    check::<PallasBase>();
    check::<PallasScalar>();
}

/// The assembly addition and subtraction compute the same limbs as the
/// portable kernels on loose inputs, including values in `[p, 2p)`.
#[cfg(all(udon_asm, not(miri)))]
#[test]
fn assembly_add_and_sub_match_portable_kernels_on_loose_inputs() {
    fn check<M: PrimeModulus>() {
        let values = loose_samples::<M>(0x3c6e_f372_fe94_f82b);
        for a in &values {
            for b in values.iter().step_by(5) {
                assert_eq!(
                    crate::field::asm::add_loose(a, b, &M::TWICE_MODULUS),
                    montgomery::add_twice_modulus_rust::<M>(a, b)
                );
                assert_eq!(
                    crate::field::asm::sub_loose(a, b, &M::TWICE_MODULUS),
                    montgomery::sub_twice_modulus_rust::<M>(a, b)
                );
            }
        }
    }
    check::<PallasBase>();
    check::<PallasScalar>();
}

#[test]
fn montgomery_kernels_cover_their_full_input_bounds() {
    check_montgomery::<PallasBase>();
    check_montgomery::<PallasScalar>();
}

fn check_lazy_squares<M: PrimeModulus>() {
    let p = modulus::<M>();
    let radix = BigUint::from(1u8) << 256usize;
    // Check the actual unreduced intermediates against exact REDC, not just
    // field equality, at every supported run length.
    let negative_inverse = (&radix - p.modinv(&radix).unwrap()) % &radix;
    let mut values: Vec<_> = samples::<M>(32)
        .into_iter()
        .map(|(value, _)| value)
        .collect();
    values.extend(
        [p.clone(), &p + 1u8, &p * 2u8 - 1u8].map(|x| PastaField::<M>::from_montgomery(limbs(&x))),
    );
    for value in values {
        let mut raw = value.limbs;
        let mut expected = integer(&raw);
        for count in 0..=1024 {
            assert_eq!(integer(&raw), expected);
            assert!(expected < &p * 2u8);
            if count <= 260 || count == 512 || count == 513 || count == 1024 {
                assert_eq!(
                    integer(&montgomery::square_run::<M>(&value.limbs, count, None)),
                    expected,
                );
                let factor = limbs(&(&p * 2u8 - 1u8));
                let product = &expected * integer(&factor);
                let q = &product * &negative_inverse % &radix;
                assert_eq!(
                    integer(&montgomery::square_run::<M>(
                        &value.limbs,
                        count,
                        Some(&factor)
                    )),
                    (&product + q * &p) / &radix,
                );
            }
            if count != 1024 {
                let square = &expected * &expected;
                let q = &square * &negative_inverse % &radix;
                expected = (&square + q * &p) / &radix;
                raw = montgomery::montgomery_reduce_unreduced::<M>(word::square_wide(&raw));
            }
        }
    }
}

#[test]
fn lazy_squares_preserve_exact_redc_bounds_for_every_run_length() {
    check_lazy_squares::<PallasBase>();
    check_lazy_squares::<PallasScalar>();
}

// Check feature selection independently of the build script's custom cfgs so a
// missing backend cannot silently turn the native assembly run into a fallback.
#[test]
fn assembly_feature_selects_the_supported_native_backend() {
    assert_eq!(
        cfg!(udon_aarch64_asm),
        cfg!(all(
            feature = "aarch64-asm",
            target_arch = "aarch64",
            target_endian = "little",
            target_pointer_width = "64",
            any(target_family = "unix", target_os = "none"),
        )),
    );
    // The x86-64 backend is forced by its feature or selected from the
    // compiler's resolved target features, and `portable` overrides both.
    assert_eq!(
        cfg!(udon_x86_64_asm),
        cfg!(all(
            target_arch = "x86_64",
            target_pointer_width = "64",
            not(feature = "portable"),
            any(
                feature = "x86_64-asm",
                all(target_feature = "bmi2", target_feature = "adx"),
            ),
        )),
    );
    assert_eq!(cfg!(udon_asm), cfg!(any(udon_aarch64_asm, udon_x86_64_asm)));
}

fn check_loose_arithmetic<M: PrimeModulus>() {
    let p = modulus::<M>();
    let twice = &p * 2u8;
    let radix = BigUint::from(1u8) << 256usize;
    let inverse_r = radix.modinv(&p).unwrap();
    let negative_inverse = &radix - p.modinv(&radix).unwrap();
    let redc = |product: BigUint| {
        let q = &product * &negative_inverse % &radix;
        (product + q * &p) / &radix
    };
    let mut values = vec![
        BigUint::from(0u8),
        BigUint::from(1u8),
        &p - 1u8,
        p.clone(),
        &p + 1u8,
        &twice - 1u8,
        &radix / 2u8,
        &radix / 2u8 - 1u8,
    ];
    for bit in [64usize, 128, 192] {
        let power = BigUint::from(1u8) << bit;
        values.extend([&power - 1u8, power.clone(), &twice - power]);
    }
    let mut state = 0x3c6e_f372_fe94_f82b;
    values.extend(
        (0..64).map(|_| BigUint::from_bytes_le(&deterministic_bytes::<32>(&mut state)) % &twice),
    );
    for x in &values {
        let a = PastaField::<M>::from_montgomery(limbs(x));
        if x < &p {
            assert_eq!(
                integer(&PastaField::<M>::from_canonical_limbs(limbs(x)).limbs),
                redc(x * integer(&M::R2)),
            );
        }
        assert_eq!(integer(&a.double().limbs), x * 2u8 % &twice);
        assert_eq!(integer(&a.neg().limbs), (&twice - x) % &twice);
        assert_eq!(integer(&a.square().limbs), redc(x * x));
        assert_eq!(integer(&a.canonical_limbs()), x * &inverse_r % &p);
        for y in &values {
            let b = PastaField::<M>::from_montgomery(limbs(y));
            assert_eq!(integer(&a.add(&b).limbs), (x + y) % &twice);
            assert_eq!(integer(&a.sub(&b).limbs), (x + &twice - y) % &twice);
            let expected = redc(x * y);
            assert!(expected < twice);
            assert_eq!(integer(&a.mul(&b).limbs), expected);
            assert_eq!(
                a.mul(&b).limbs,
                montgomery::montgomery_multiply::<M>(&a.limbs, &b.limbs)
            );
        }
    }
    let limit = &p * (&radix + &p);
    let mut wide = vec![
        BigUint::from(0u8),
        &p * &radix - 1u8,
        &p * &radix,
        &limit - 1u8,
    ];
    for _ in 0..128 {
        let low = BigUint::from_bytes_le(&deterministic_bytes::<32>(&mut state));
        let high = BigUint::from_bytes_le(&deterministic_bytes::<32>(&mut state));
        wide.push(((high << 256usize) + low) % &limit);
    }
    for input in wide {
        let actual = integer(&montgomery::montgomery_reduce_unreduced::<M>(limbs(&input)));
        assert_eq!(actual, redc(input));
        assert!(actual < &p * 3u8);
    }
}

#[test]
fn loose_arithmetic_preserves_exact_integer_results() {
    check_loose_arithmetic::<PallasBase>();
    check_loose_arithmetic::<PallasScalar>();
}

#[cfg(all(udon_asm, not(miri)))]
#[test]
fn assembly_wrapping_subtraction_matches_integer_arithmetic() {
    let modulus = BigUint::from(1u8) << 256usize;
    let check = |a: [u64; 4], b: [u64; 4]| {
        let actual = crate::field::asm::subtract_wrapping(&a, &b);
        assert_eq!(
            integer(&actual),
            (integer(&a) + &modulus - integer(&b)) % &modulus
        );
    };
    let endpoints = [
        [0; 4],
        [u64::MAX; 4],
        [1, 0, 0, 0],
        [0, 0, 0, 1],
        [0, u64::MAX, 0, u64::MAX],
        [u64::MAX, 0, u64::MAX, 0],
    ];
    for a in endpoints {
        for b in endpoints {
            check(a, b);
        }
    }
    let mut state = 0xa54f_f53a_5f1d_36f1;
    for _ in 0..4096 {
        let a = core::array::from_fn(|_| xorshift64(&mut state));
        let b = core::array::from_fn(|_| xorshift64(&mut state));
        check(a, b);
    }
}
