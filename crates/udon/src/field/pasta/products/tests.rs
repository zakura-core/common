use super::*;
use crate::field::pasta::test_support::*;

struct Hint<I>(I, (usize, Option<usize>));
impl<I: Iterator> Iterator for Hint<I> {
    type Item = I::Item;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.1
    }
}

fn check_sum_states<M: PrimeModulus, S: ReductionState, T: ReductionState, const N: usize>(
    lhs: &[PastaField<M, S>; N],
    rhs: &[PastaField<M, T>; N],
    expected: &BigUint,
) {
    assert_value(PastaField::sum_of_products(lhs, rhs), expected);
    assert_value(PastaField::sum_of_products_slice(lhs, rhs), expected);
    assert_value(
        PastaField::sum_of_product_pairs(lhs.iter().zip(rhs)),
        expected,
    );
}

fn check_products<M: PrimeModulus>() {
    let p = modulus::<M>();
    let mut values = samples::<M>(64);
    let inverse_r = (BigUint::from(1u8) << 256usize).modinv(&p).unwrap();
    for raw in [BigUint::from(1u8), &p - 1u8, &p - 2u8] {
        values.push((
            PastaField::from_montgomery_limbs(limbs(&raw)),
            &raw * &inverse_r % &p,
        ));
    }
    for (index, (a, x)) in values.iter().enumerate() {
        let (b, y) = &values[(index * 7 + 3) % values.len()];
        for (other, (c, z)) in values.iter().enumerate() {
            let (d, w) = &values[(other * 13 + 5) % values.len()];
            let product = z * w % &p;
            assert_value(a.mul_sub_product(b, c, d), &(x * y + &p - &product));
            assert_value(
                a.mul_sub_double_product(b, c, d),
                &(x * y + &p * 2u8 - &product * 2u8),
            );
        }
        assert_value(a.mul_sub_product(a, a, a), &BigUint::from(0u8));
        assert_value(a.mul_sub_double_product(a, a, a), &(&p - x * x % &p));
        assert_value(a.mul_sub_product(a, &PastaField::<_>::ZERO, a), &(x * x));
    }
    for length in [
        0, 1, 2, 3, 4, 7, 11, 12, 23, 31, 32, 33, 63, 64, 65, 66, 67, 68, 69, 257, 4096,
    ] {
        let mut expected = BigUint::from(0u8);
        let mut mixed_expected = BigUint::from(0u8);
        let mut mixed = ProductSum::<M>::new();
        let mut partials = [const { ProductSum::<M>::new() }; 3];
        let mut lhs = Vec::new();
        let mut rhs = Vec::new();
        for index in 0..length {
            let (a, x) = &values[index % values.len()];
            let (b, y) = &values[(index * 13 + 5) % values.len()];
            lhs.push(*a);
            rhs.push(*b);
            expected += x * y;
            for sum in [&mut mixed, &mut partials[index % 3]] {
                match index % 4 {
                    0 => sum.add_term(a),
                    1 => sum.add_square(a),
                    2 => sum.add_square(&a.reduce()),
                    _ => sum.add_product(a, b),
                }
            }
            mixed_expected += match index % 4 {
                0 => x.clone(),
                1 | 2 => x * x,
                _ => x * y,
            };
        }
        assert_value(
            PastaField::<M>::sum_of_products_slice(&lhs, &rhs),
            &expected,
        );
        assert_value(
            PastaField::<M>::sum_of_product_pairs(lhs.iter().zip(&rhs)),
            &expected,
        );
        // Dispatch and overflow bounds must use actual entries, even when a
        // safe iterator reports an incorrect length or supplies strided data.
        for hint in [(0, None), (0, Some(0)), (usize::MAX, Some(usize::MAX))] {
            assert_value(
                PastaField::<M>::sum_of_product_pairs(Hint(lhs.iter().zip(&rhs), hint)),
                &expected,
            );
        }
        let stride_expected = (0..length).step_by(3).fold(BigUint::from(0u8), |sum, i| {
            sum + &values[i % values.len()].1 * &values[(i * 13 + 5) % values.len()].1
        });
        assert_value(
            PastaField::<M>::sum_of_product_pairs(lhs.iter().step_by(3).zip(rhs.iter().step_by(3))),
            &stride_expected,
        );
        assert_value(mixed.finish(), &mixed_expected);
        for order in [[0, 1, 2], [2, 1, 0], [1, 0, 2]] {
            let mut merged = ProductSum::new();
            for index in order {
                merged.merge(&partials[index]);
            }
            assert_value(merged.finish(), &mixed_expected);
        }
        let [mut first, second, mut third] = partials;
        third.merge(&second);
        first.merge(&third);
        assert_value(first.finish(), &mixed_expected);
        let maximal = PastaField::<M>::from_montgomery_limbs(limbs(&(&p * 2u8 - 1u8)));
        let maximal_integer = BigUint::from_bytes_le(&maximal.to_bytes());
        let repeated = vec![maximal; length];
        assert_value(
            PastaField::<M>::sum_of_products_slice(&repeated, &repeated),
            &(&maximal_integer * &maximal_integer * length),
        );
    }
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ =
                PastaField::<M>::sum_of_products_slice(&[PastaField::ONE], &[] as &[PastaField<M>]);
        }))
        .is_err()
    );
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = PastaField::<M>::sum_of_products_slice(&[], &[PastaField::<M>::ONE]);
        }))
        .is_err()
    );

    // Literal lengths instantiate each array API specialization.
    macro_rules! check_arrays {
        ($($length:literal),* $(,)?) => {$(
            let lhs = core::array::from_fn::<_, $length, _>(|i| values[i % values.len()].0);
            let rhs = core::array::from_fn::<_, $length, _>(|i| values[(i * 7 + 1) % values.len()].0);
            let expected = (0..$length).fold(BigUint::from(0u8), |sum, i| sum + &values[i % values.len()].1 * &values[(i * 7 + 1) % values.len()].1);
            check_sum_states(&lhs, &rhs, &expected);
            check_sum_states(&lhs.map(PastaField::reduce), &rhs, &expected);
            check_sum_states(&lhs, &rhs.map(PastaField::reduce), &expected);
            check_sum_states(&lhs.map(PastaField::reduce), &rhs.map(PastaField::reduce), &expected);
            // In particular, three maximal loose products exceed pR and need
            // the high-half fold; reducing either operand selects another path.
            let maximum = PastaField::<M>::from_montgomery_limbs(limbs(&(&p * 2u8 - 1u8)));
            let integer = BigUint::from_bytes_le(&maximum.to_bytes());
            let expected = &integer * &integer * ($length as usize);
            let loose = [maximum; $length];
            let reduced = loose.map(PastaField::reduce);
            check_sum_states(&loose, &loose, &expected);
            check_sum_states(&loose, &reduced, &expected);
            check_sum_states(&reduced, &loose, &expected);
            check_sum_states(&reduced, &reduced, &expected);
        )*};
    }
    check_arrays!(0, 1, 2, 3, 4, 11, 12, 23, 31, 32, 33, 64, 65);
}

#[test]
fn product_differences_and_sums_match_integer_arithmetic() {
    check_products::<PallasBase>();
    check_products::<PallasScalar>();
}

fn check_squares<M: PrimeModulus>() {
    let p = modulus::<M>();
    let inverse_r = (BigUint::from(1u8) << 256usize).modinv(&p).unwrap();
    let mut values = samples::<M>(64);
    for bits in [64usize, 128, 192, 254, 255] {
        let boundary = BigUint::from(1u8) << bits;
        for raw in [&boundary - 1u8, boundary.clone(), &boundary + 1u8] {
            values.push((
                PastaField::from_montgomery_limbs(limbs(&raw)),
                raw * &inverse_r % &p,
            ));
        }
    }
    let mut sum = ProductSum::<M>::new();
    let mut reduced_sum = ProductSum::<M>::new();
    let mut expected = BigUint::from(0u8);
    for (value, integer) in values {
        let square = &integer * &integer;
        let mut singleton = ProductSum::new();
        singleton.add_square(&value);
        assert_value(singleton.finish(), &square);
        let mut singleton = ProductSum::new();
        singleton.add_square(&value.reduce());
        assert_value(singleton.finish(), &square);
        sum.add_square(&value);
        reduced_sum.add_square(&value.reduce());
        expected += square;
    }
    assert_value(sum.finish(), &expected);
    assert_value(reduced_sum.finish(), &expected);

    let maximum = PastaField::<M>::from_montgomery_limbs(limbs(&(&p * 2u8 - 1u8)));
    let integer = (&p * 2u8 - 1u8) * inverse_r % &p;
    for length in [0usize, 1, 2, 3, 4, 31, 32, 33, 64, 65, 257, 4096] {
        let mut sum = ProductSum::new();
        for _ in 0..length {
            sum.add_square(&maximum);
        }
        assert_value(sum.finish(), &(&integer * &integer * length));
    }
}

#[test]
fn deferred_squares_match_integer_arithmetic() {
    check_squares::<PallasBase>();
    check_squares::<PallasScalar>();
}

fn check_difference<M: PrimeModulus>(
    a: &PastaField<M, impl ReductionState>,
    b: &PastaField<M, impl ReductionState>,
    c: &PastaField<M, impl ReductionState>,
    d: &PastaField<M, impl ReductionState>,
    expected: &BigUint,
    doubled: &BigUint,
) {
    assert_value(a.mul_sub_product(b, c, d), expected);
    assert_value(a.mul_sub_double_product(b, c, d), doubled);
}

fn check_mixed_differences<M: PrimeModulus>() {
    let p = modulus::<M>();
    let values = samples::<M>(64);
    for (index, (a, x)) in values.iter().enumerate() {
        let (b, y) = &values[(index * 7 + 3) % values.len()];
        let (c, z) = &values[(index * 13 + 5) % values.len()];
        let (d, w) = &values[(index * 17 + 7) % values.len()];
        let product = z * w % &p;
        let expected = x * y + &p - &product;
        let doubled = x * y + &p * 2u8 - &product * 2u8;
        // Cover all sixteen static state combinations independently of the
        // numeric representatives; each reduction preserves the oracle value.
        macro_rules! check_right_states {
            ($a:expr, $b:expr) => {
                check_difference($a, $b, c, d, &expected, &doubled);
                check_difference($a, $b, &c.reduce(), d, &expected, &doubled);
                check_difference($a, $b, c, &d.reduce(), &expected, &doubled);
                check_difference($a, $b, &c.reduce(), &d.reduce(), &expected, &doubled);
            };
        }
        check_right_states!(a, b);
        check_right_states!(&a.reduce(), b);
        check_right_states!(a, &b.reduce());
        check_right_states!(&a.reduce(), &b.reduce());
    }
}

#[test]
fn product_differences_accept_all_reduction_states() {
    check_mixed_differences::<PallasBase>();
    check_mixed_differences::<PallasScalar>();
}

#[test]
fn repeatedly_merging_product_sums_preserves_the_field_value() {
    fn check<M: PrimeModulus>() {
        let mut sum = ProductSum::<M>::new();
        sum.add_term(&PastaField::<_>::ONE);
        let mut expected = PastaField::<M>::ONE;
        for _ in 0..1024 {
            let mut doubled = ProductSum::new();
            doubled.merge(&sum);
            doubled.merge(&sum);
            sum = doubled;
            expected = expected.double();
        }
        assert_eq!((sum.finish()).reduce(), (expected).reduce());
    }
    check::<PallasBase>();
    check::<PallasScalar>();
}

fn check_overflow<M: PrimeModulus>() {
    let p = modulus::<M>();
    let radix = BigUint::from(1u8) << 256usize;
    let inverse_r = radix.modpow(&(&p - 2u8), &p);
    // The accumulator stores products scaled by R²; finish returns a field
    // element scaled by R, which assert_value compares to an ordinary integer.
    let inverse_r_squared = &inverse_r * &inverse_r % &p;
    let maximum = (BigUint::from(1u8) << 576usize) - 1u8;
    let full = || ProductSum::<M> {
        wide: [u64::MAX; 8],
        carry: u64::MAX,
        marker: PhantomData,
    };
    let term = PastaField::<M>::from_montgomery_limbs(limbs(&(&p * 2u8 - 1u8)));
    let stored = integer(&term.montgomery_limbs());
    for (value, _) in samples::<M>(8) {
        let raw = integer(&value.montgomery_limbs());
        let square = &raw * &raw;
        let mut starts = vec![maximum.clone(), &maximum - &square];
        if square != BigUint::from(0u8) {
            starts.push(&maximum - &square + 1u8);
        }
        for start in starts {
            let raw = limbs::<9>(&start);
            let mut sum = ProductSum::<M> {
                wide: raw[..8].try_into().unwrap(),
                carry: raw[8],
                marker: PhantomData,
            };
            sum.add_square(&value);
            assert_value(sum.finish(), &((&start + &square) * &inverse_r_squared));
        }
    }
    let mut sum = full();
    sum.add_product(&term, &term);
    assert_value(
        sum.finish(),
        &((&maximum + &stored * &stored) * &inverse_r_squared),
    );
    let mut sum = full();
    sum.add_term(&term);
    assert_value(
        sum.finish(),
        &((&maximum + &stored * &radix) * &inverse_r_squared),
    );
    let mut sum = full();
    sum.merge(&full());
    sum.add_product(&term, &term);
    sum.add_square(&term);
    sum.add_term(&term);
    assert_value(
        sum.finish(),
        &((&maximum * 2u8 + &stored * &stored * 2u8 + &stored * &radix) * &inverse_r_squared),
    );
    assert_value(full().finish(), &(&maximum * &inverse_r_squared));
    assert_value(ProductSum::<M>::default().finish(), &BigUint::from(0u8));
}

#[test]
fn all_accumulator_mutations_preserve_overflow_bits() {
    check_overflow::<PallasBase>();
    check_overflow::<PallasScalar>();
}

fn check_partial_reduce<M: PrimeModulus>() {
    let p = modulus::<M>();
    let inverse_r_squared = (BigUint::from(1u8) << 512usize).modinv(&p).unwrap();
    let check = |wide: [u64; 8], carry: u64| {
        let sum = ProductSum::<M> {
            wide,
            carry,
            marker: PhantomData,
        };
        let folded = sum.partial_reduce();
        assert!(folded[7] <= 1);
        assert_eq!(
            integer(&folded),
            integer(&wide[..7])
                + BigUint::from(wide[7]) * integer(&M::B448)
                + BigUint::from(carry) * integer(&M::R2)
        );
        let accumulator = integer(&wide) + (BigUint::from(carry) << 512usize);
        assert_value(sum.finish(), &(accumulator * &inverse_r_squared));
    };
    for carry in [0, 1, u64::MAX] {
        check([0; 8], carry);
        check([u64::MAX; 8], carry);
        for limb in 0..8 {
            let mut wide = [0; 8];
            wide[limb] = u64::MAX;
            check(wide, carry);
        }
    }
    let mut state = 0x1f83_d9ab_fb41_bd6b;
    for _ in 0..1024 {
        let wide = limbs(&BigUint::from_bytes_le(&deterministic_bytes::<64>(
            &mut state,
        )));
        check(wide, xorshift64(&mut state));
    }
}

// Check the exact fold and final field value across the full accumulator range,
// including zero and maximum carries, against independent integer arithmetic.
#[test]
fn full_accumulator_reductions_match_integer_arithmetic() {
    check_partial_reduce::<PallasBase>();
    check_partial_reduce::<PallasScalar>();
}
