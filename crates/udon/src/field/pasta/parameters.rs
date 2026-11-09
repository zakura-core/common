//! Sealed Pasta moduli and compile-time field parameter derivation.

use bento::const_arithmetic::{m255, u256};

use super::word::{add_limbs, compare_limbs, multiply_wide, subtract_limbs};
use super::{PastaField, Reduced, ReductionState};
use crate::field::pasta::safegcd::to_signed62;

// Derive the remaining field constants from these inputs and each modulus.
// Tests compare independent integer derivations and fixed literal vectors.
pub(super) const TWO_ADICITY: u32 = 32;
const GENERATOR: u64 = 5;

/// Marker for the Pallas base field, which is also the Vesta scalar field.
#[derive(Clone, Copy, Eq, PartialEq)]
pub enum PallasBase {}

/// Marker for the Pallas scalar field, which is also the Vesta base field.
#[derive(Clone, Copy, Eq, PartialEq)]
pub enum PallasScalar {}

// The sparse Montgomery kernels and divstep bounds require the Pasta moduli.
mod sealed {
    use super::{INVERSE_POWER_TABLE_LEN, PastaField, Reduced};

    pub trait Sealed {}

    pub(in crate::field) trait Parameters<M: super::PrimeModulus>: Sized {
        /// Field values for [`PastaField::root_of_unity`], indexed by `log_size`.
        const ROOTS: &'static [PastaField<M, Reduced>; INVERSE_POWER_TABLE_LEN];
        /// Inverses of the corresponding forward roots.
        const INVERSE_ROOTS: &'static [PastaField<M, Reduced>; INVERSE_POWER_TABLE_LEN];
        /// Twice the modulus, the exclusive bound for loose residues.
        const TWICE_MODULUS: [u64; 4];
        /// `-p^-1 mod 2^64`, used to cancel each low limb during reduction.
        const MONTGOMERY_INV: u64;
        /// `2^256 mod p`, also the Montgomery representation of one.
        const R: [u64; 4];
        /// `2^512 mod p`, used to enter Montgomery form.
        const R2: [u64; 4];
        /// `2^768 mod p`, used by wide decoding.
        const R3: [u64; 4];
        /// `2^448 mod p`, used to fold the upper limb of a product sum.
        const B448: [u64; 4];
        /// The Montgomery representation of `2^-1`.
        const TWO_INVERSE: [u64; 4];
        /// The Montgomery representation of `5^(2^32)`.
        const DELTA: [u64; 4];
        /// The protocol-selected primitive cube root of unity in Montgomery form.
        const ZETA: [u64; 4];
        /// The inverse of `ZETA`, in Montgomery form.
        const ZETA_INVERSE: [u64; 4];
        /// The modulus in the signed-62 representation the safegcd core runs on.
        const MODULUS_SIGNED62: [i64; 5];
        /// Montgomery `2^-k` for `k <= TWO_ADICITY`: the inverse domain sizes of
        /// every supported transform.
        const POWER_OF_TWO_INVERSES: [[u64; 4]; INVERSE_POWER_TABLE_LEN];

        /// Raises `value` to `(t - 1) / 2`, where `p - 1 = t * 2^32`.
        ///
        /// `bento::addition_chain!` plans the multiplication schedule at
        /// compile time; only powers of the base are computed at runtime.
        fn pow_sqrt_exponent(value: &PastaField<M>) -> PastaField<M>;

        /// Raises every lane to `(t - 1) / 2`, where `p - 1 = t * 2^32`.
        ///
        /// Runs [`Self::pow_sqrt_exponent`]'s schedule on all lanes together,
        /// interleaving the otherwise serial per-lane multiplication chains.
        fn pow_sqrt_exponent_lanes<const L: usize>(
            values: &[PastaField<M>; L],
        ) -> [PastaField<M>; L];

        /// Computes a square root using this modulus's larger table.
        ///
        /// Requires a nonzero `value` and `w = pow_sqrt_exponent(value)`.
        #[cfg(feature = "sqrt-table-large")]
        fn sqrt_large(
            value: &PastaField<M, Reduced>,
            w: PastaField<M>,
        ) -> Option<PastaField<M, Reduced>>;

        /// Corrects `x` with `x^2 = a * t` for nonzero `a` and order-2^32
        /// subgroup element `t`. Returns a root of `a`, or of `a * ROOTS[32]`
        /// with a false flag when `a` is nonsquare.
        #[cfg(feature = "sqrt-table-large")]
        fn sqrt_finish_large(x: PastaField<M>, t: PastaField<M>) -> (bool, PastaField<M, Reduced>);
    }
}

/// Selects one of the two Pasta primes.
///
/// Only [`PallasBase`] and [`PallasScalar`] implement this sealed trait.
/// Field-valued parameters are available through [`PastaField`] constants and
/// lookup methods.
///
/// ```compile_fail
/// #[derive(Clone, Copy, Eq, PartialEq)]
/// enum Foreign {}
/// impl zakura_udon::field::PrimeModulus for Foreign {
///     const MODULUS: [u64; 4] = [97, 0, 0, 0];
/// }
/// ```
#[expect(private_bounds, reason = "implementation parameters are crate-private")]
pub trait PrimeModulus:
    sealed::Sealed + sealed::Parameters<Self> + Copy + Eq + Send + Sync + 'static
{
    /// The prime modulus as four ordinary little-endian 64-bit limbs.
    const MODULUS: [u64; 4];
}

// Derive each field's constants from its modulus and generator. The two cube
// roots have opposite orientations relative to 5^((p - 1)/3); verify their
// inverse pairing at compile time. The chain macro derives its exponent from
// the same modulus literal.
macro_rules! pasta_field_parameters {
    ($marker:ty, modulus: $modulus:literal, sqrt_hash: $hash:literal,
     zeta: canonical_root $(,)?) => {
        pasta_field_parameters! {
            @impl $marker, $modulus, $hash,
            const ZETA: [u64; 4] = m255::cube_root_of_unity!(&Self::MODULUS, GENERATOR);
            const ZETA_INVERSE: [u64; 4] =
                m255::mul!(&Self::MODULUS, &Self::ZETA, &Self::ZETA);
        }
    };
    ($marker:ty, modulus: $modulus:literal, sqrt_hash: $hash:literal,
     zeta: squared_canonical_root $(,)?) => {
        pasta_field_parameters! {
            @impl $marker, $modulus, $hash,
            const ZETA: [u64; 4] =
                m255::mul!(&Self::MODULUS, &Self::ZETA_INVERSE, &Self::ZETA_INVERSE);
            const ZETA_INVERSE: [u64; 4] = m255::cube_root_of_unity!(&Self::MODULUS, GENERATOR);
        }
    };
    (@impl $marker:ty, $modulus:literal, $hash:literal, $($zeta:item)*) => {
        impl sealed::Sealed for $marker {}

        impl PrimeModulus for $marker {
            const MODULUS: [u64; 4] = u256::from_hex!($modulus);
        }

        impl $marker {
            // A named static shares one validated table across lookups; the
            // associated const only borrows it.
            const ROOT_TABLES: &'static (
                [PastaField<Self, Reduced>; INVERSE_POWER_TABLE_LEN],
                [PastaField<Self, Reduced>; INVERSE_POWER_TABLE_LEN],
            ) = {
                static TABLES: (
                    [PastaField<$marker, Reduced>; INVERSE_POWER_TABLE_LEN],
                    [PastaField<$marker, Reduced>; INVERSE_POWER_TABLE_LEN],
                ) = {
                    let roots = m255::two_adic_root_tables!(&<$marker>::MODULUS, GENERATOR, TWO_ADICITY);
                    (super::sqrt::field_elements(roots.0), super::sqrt::field_elements(roots.1))
                };
                &TABLES
            };

            #[cfg(feature = "sqrt-table-large")]
            pub(super) const SQRT_TABLE: &'static super::sqrt::LargeSqrtTable<PastaField<Self, Reduced>> = {
                static TABLE: super::sqrt::LargeSqrtTable<PastaField<$marker, Reduced>> =
                    super::sqrt::LargeSqrtTable::from_powers([
                        m255::powers!(&<$marker>::MODULUS, &<$marker>::ROOT_TABLES.0[32].montgomery_limbs(); 256),
                        m255::powers!(&<$marker>::MODULUS, &<$marker>::ROOT_TABLES.0[24].montgomery_limbs(); 256),
                        m255::powers!(&<$marker>::MODULUS, &<$marker>::ROOT_TABLES.0[16].montgomery_limbs(); 256),
                        m255::powers!(&<$marker>::MODULUS, &<$marker>::ROOT_TABLES.0[8].montgomery_limbs(); 256),
                    ], $hash);
                &TABLE
            };
        }

        impl sealed::Parameters<Self> for $marker {
            const ROOTS: &'static [PastaField<Self, Reduced>; INVERSE_POWER_TABLE_LEN] =
                &Self::ROOT_TABLES.0;
            const INVERSE_ROOTS: &'static [PastaField<Self, Reduced>; INVERSE_POWER_TABLE_LEN] =
                &Self::ROOT_TABLES.1;
            const TWICE_MODULUS: [u64; 4] = add_limbs(&Self::MODULUS, &Self::MODULUS).0;
            const MONTGOMERY_INV: u64 = m255::reduction_coefficient!(Self::MODULUS[0]);
            const R: [u64; 4] = m255::one!(&Self::MODULUS);
            const R2: [u64; 4] = m255::r2!(&Self::MODULUS);
            const R3: [u64; 4] = m255::mul!(&Self::MODULUS, &Self::R2, &Self::R2);
            const B448: [u64; 4] = m255::from_u256!(&Self::MODULUS, &[0, 0, 0, 1]);
            const TWO_INVERSE: [u64; 4] = Self::POWER_OF_TWO_INVERSES[1];
            const DELTA: [u64; 4] = m255::odd_order_generator!(&Self::MODULUS, GENERATOR, TWO_ADICITY);
            const MODULUS_SIGNED62: [i64; 5] = to_signed62(&Self::MODULUS);
            const POWER_OF_TWO_INVERSES: [[u64; 4]; INVERSE_POWER_TABLE_LEN] =
                m255::inverse_powers_of_two!(&Self::MODULUS);
            $($zeta)*

            fn pow_sqrt_exponent(value: &PastaField<Self>) -> PastaField<Self> {
                bento::addition_chain!(Power(*value), tonelli_shanks($modulus, 32),
                    emission = batched).0
            }

            fn pow_sqrt_exponent_lanes<const L: usize>(
                values: &[PastaField<Self>; L],
            ) -> [PastaField<Self>; L] {
                bento::addition_chain!(PowerLanes(*values), tonelli_shanks($modulus, 32),
                    emission = batched).0
            }

            #[cfg(feature = "sqrt-table-large")]
            fn sqrt_large(value: &PastaField<Self, Reduced>, w: PastaField<Self>) -> Option<PastaField<Self, Reduced>> {
                Self::SQRT_TABLE.sqrt(value, w, $hash)
            }

            #[cfg(feature = "sqrt-table-large")]
            fn sqrt_finish_large(x: PastaField<Self>, t: PastaField<Self>) -> (bool, PastaField<Self, Reduced>) {
                let (is_square, root) = Self::SQRT_TABLE.finish(x, t, $hash);
                (is_square, root.reduce())
            }
        }

        const _: () = {
            // These bounds justify the runtime kernels' reduction shortcuts.
            assert_kernel_bounds(
                &<$marker as PrimeModulus>::MODULUS,
                &<$marker as sealed::Parameters<$marker>>::R2,
                &<$marker as sealed::Parameters<$marker>>::R3,
            );
            m255::assert_modulus!(&<$marker as PrimeModulus>::MODULUS);
            let modulus = <$marker as PrimeModulus>::MODULUS;
            assert!(
                modulus[2] == 0 && modulus[3] == 1 << 62,
                "Montgomery kernels require p = 2^254 plus a 128-bit integer"
            );
            assert!(
                modulus[0] as u32 == 1,
                "FFT division requires p = 1 mod 2^32"
            );
            // Each orientation arm must pair zeta with its actual inverse.
            let product = m255::mul!(
                &<$marker as PrimeModulus>::MODULUS,
                &<$marker as sealed::Parameters<$marker>>::ZETA,
                &<$marker as sealed::Parameters<$marker>>::ZETA_INVERSE,
            );
            let one = <$marker as sealed::Parameters<$marker>>::R;
            assert!(
                product[0] == one[0]
                    && product[1] == one[1]
                    && product[2] == one[2]
                    && product[3] == one[3],
                "the pinned zeta and its declared inverse must multiply to one"
            );
        };
    };
}

// Batched emission and the planner's smaller odd-power table matched the
// supplied chains in local measurements; keep the generated schedules.
// Hash multipliers apply to reduced R = 2^256 Montgomery representatives.
// Each larger table checks all 256 subgroup hashes during constant evaluation;
// a representation change requires revalidating these multipliers.
pasta_field_parameters! {
    PallasBase,
    modulus: "0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001",
    sqrt_hash: 0x54c1_1db5,
    zeta: squared_canonical_root,
}

pasta_field_parameters! {
    PallasScalar,
    modulus: "0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001",
    sqrt_hash: 0x4b7f_dd31,
    zeta: canonical_root,
}

/// Number of inverse domain sizes from `2^0` through `2^TWO_ADICITY`.
const INVERSE_POWER_TABLE_LEN: usize = TWO_ADICITY as usize + 1;

impl<M: PrimeModulus, S: ReductionState> PastaField<M, S> {
    /// The inverse of two.
    pub const TWO_INVERSE: Self = Self::from_montgomery(M::TWO_INVERSE);

    /// Returns `2^-log_size` for any `u32` exponent, including zero.
    pub fn power_of_two_inverse(log_size: u32) -> Self {
        if let Some(entry) = M::POWER_OF_TWO_INVERSES.get(log_size as usize) {
            return Self::from_montgomery(*entry);
        }
        // The table covers supported transform sizes. Exponentiation handles
        // the rest of the u32 input range without extending that table.
        Self::from_loose(Self::TWO_INVERSE.pow_u64(u64::from(log_size)).limbs)
    }

    /// The generator `5` of the multiplicative group of nonzero elements.
    ///
    /// The two-adic roots of unity, [`Self::DELTA`], and [`Self::ZETA`] are
    /// powers of this element.
    pub const MULTIPLICATIVE_GENERATOR: Self =
        Self::from_montgomery(m255::from_u64!(&M::MODULUS, GENERATOR));

    /// `5^(2^32)`, a generator of the odd-order multiplicative subgroup.
    ///
    /// This subgroup has order `(p - 1) / 2^32`, where `p` is the field's
    /// [`PrimeModulus::MODULUS`].
    pub const DELTA: Self = Self::from_montgomery(M::DELTA);

    /// The selected primitive cube root of unity.
    ///
    /// For [`PallasBase`] this is `5^(2 * (p - 1) / 3)`; for
    /// [`PallasScalar`] it is `5^((p - 1) / 3)`. In each case, `p` is that
    /// field's [`PrimeModulus::MODULUS`] and exponentiation is in the field.
    pub const ZETA: Self = Self::from_montgomery(M::ZETA);

    /// The inverse of [`Self::ZETA`], the other primitive cube root.
    pub const ZETA_INVERSE: Self = Self::from_montgomery(M::ZETA_INVERSE);
}

// Multiplicative interpretation of an addition chain, kept distinct from the
// field's additive operations.
#[derive(Clone)]
struct Power<M: PrimeModulus>(PastaField<M>);

impl<M: PrimeModulus> bento::addchain::AdditionChain for Power<M> {
    // Forced inlining duplicates the kernels' debug stack slots throughout
    // the unrolled chain. Let optimized builds decide whether to inline.
    #[inline]
    fn double(&self) -> Self {
        Self(self.0.square())
    }

    #[inline]
    fn add(&self, rhs: &Self) -> Self {
        Self(self.0.mul(&rhs.0))
    }

    #[inline]
    fn double_n(&self, count: usize) -> Self {
        self.double_n_add_impl(count, None)
    }

    #[inline]
    fn double_n_add(&self, count: usize, rhs: &Self) -> Self {
        self.double_n_add_impl(count, Some(&rhs.0.limbs))
    }
}

impl<M: PrimeModulus> Power<M> {
    #[inline]
    fn double_n_add_impl(&self, count: usize, factor: Option<&[u64; 4]>) -> Self {
        Self(PastaField::from_montgomery(
            super::montgomery::square_run::<M>(&self.0.limbs, count, factor),
        ))
    }
}

// Lane-interleaved multiplicative chain. The planner's schedule runs on every
// lane together so the lanes' independent dependency chains overlap.
#[derive(Clone)]
struct PowerLanes<M: PrimeModulus, const L: usize>([PastaField<M>; L]);

impl<M: PrimeModulus, const L: usize> bento::addchain::AdditionChain for PowerLanes<M, L> {
    #[inline]
    fn double(&self) -> Self {
        Self(core::array::from_fn(|lane| self.0[lane].square()))
    }

    #[inline]
    fn add(&self, rhs: &Self) -> Self {
        Self(core::array::from_fn(|lane| self.0[lane].mul(&rhs.0[lane])))
    }

    // Keep the default double_n and double_n_add: they double all lanes per
    // step, preserving the interleaving that Power's fused square_run would
    // serialize lane by lane.
}

const fn add_wide(a: [u64; 8], b: [u64; 8]) -> [u64; 8] {
    let mut result = [0; 8];
    let mut carry = 0u128;
    let mut i = 0;
    while i < 8 {
        carry += a[i] as u128 + b[i] as u128;
        result[i] = carry as u64;
        carry >>= 64;
        i += 1;
    }
    assert!(carry == 0, "wide sum must fit");
    result
}

const fn assert_redc_bound(value: [u64; 8], modulus: &[u64; 4]) {
    assert!(
        compare_limbs(&[value[4], value[5], value[6], value[7]], modulus).is_lt(),
        "kernel input must be below pR"
    );
}

// Use Udon's integer operations because function parameters cannot cross
// Bento's inline const blocks. Bento has already validated the modulus and
// derived r2 and r3. In these bounds, p = modulus and R = 2^256.
const fn assert_kernel_bounds(modulus: &[u64; 4], r2: &[u64; 4], r3: &[u64; 4]) {
    let minus_one = subtract_limbs(modulus, &[1, 0, 0, 0]).0;
    let (sum, carry) = add_limbs(r2, r3);
    assert!(
        carry == 0 && compare_limbs(&sum, modulus).is_lt(),
        "wide decoder requires R2 + R3 < p"
    );
    let (twice_p, carry) = add_limbs(modulus, modulus);
    assert!(carry == 0);
    let (_, carry) = add_limbs(&twice_p, modulus);
    assert!(carry == 0, "loose kernels require 3p < R");
    let loose_max = subtract_limbs(&twice_p, &[1, 0, 0, 0]).0;
    // The Horner numerator is (V + D)*R2, V < 2p, D < R.
    assert_redc_bound(
        add_wide(
            multiply_wide(&loose_max, r2),
            multiply_wide(&[u64::MAX; 4], r2),
        ),
        modulus,
    );
    let product = multiply_wide(&minus_one, &minus_one);
    assert_redc_bound(add_wide(add_wide(product, product), product), modulus);
    // Three loose products fit eight limbs. Their high half is below 4p;
    // mixed reduced/loose products have a high half below 2p.
    let loose_product = multiply_wide(&loose_max, &loose_max);
    let _ = add_wide(add_wide(loose_product, loose_product), loose_product);
    let mixed = multiply_wide(&minus_one, &loose_max);
    let mixed = add_wide(add_wide(mixed, mixed), mixed);
    assert!(compare_limbs(&[mixed[4], mixed[5], mixed[6], mixed[7]], &twice_p).is_lt());
    // This exact parameter bound proves closure of REDC(a*b) for a,b < 2p;
    // see montgomery::square_run. c occupies only the low 128 bits.
    let c = [modulus[0], modulus[1], 0, 0];
    let c_squared = multiply_wide(&c, &c);
    assert!(c_squared[4] == 0 && c_squared[5] == 0 && c_squared[6] == 0 && c_squared[7] == 0);
    assert!(
        c_squared[3] < 1 << 60,
        "loose Montgomery closure requires 16c² < R"
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use bento::addchain::AdditionChain;

    fn check_runs<M: PrimeModulus>() {
        let value = Power(PastaField::<M>::from_u64(7));
        let factor = Power(PastaField::<M>::from_u64(11));
        let mut expected = value.0;
        for count in 0..=513 {
            if [0, 1, 255, 256, 257, 512, 513].contains(&count) {
                assert_eq!((value.double_n(count).0).reduce(), (expected).reduce());
                assert_eq!(
                    (value.double_n_add(count, &factor).0).reduce(),
                    (expected.mul(&factor.0)).reduce()
                );
            }
            expected = expected.square();
        }
    }

    #[test]
    fn power_hooks_preserve_loose_bounds_across_long_runs() {
        check_runs::<PallasBase>();
        check_runs::<PallasScalar>();
    }
}
