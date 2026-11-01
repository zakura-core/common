//! Conversion between canonical integers/bytes and stored Montgomery residues.
//!
//! Checked decoders reject noncanonical values; explicitly reducing constructors
//! accept wider integers. These are distinct from the raw stored-form accessors.

use core::marker::PhantomData;

use super::montgomery::{
    montgomery_multiply, montgomery_multiply_loose, montgomery_reduce_unreduced,
};
use super::word::{adc, compare_limbs, multiply_wide};
use super::{CanonicalUint, ENCODED_SIZE, PastaField, PrimeModulus, ReductionState};

/// Samples a Pasta field element by reducing 64 bytes from the caller's source.
///
/// Calls `fill` exactly once with the entire buffer. The callback must fill it
/// with uniformly random bytes; cryptographic use requires a cryptographically
/// secure source. Reduction uses [`PastaField::from_wide_bytes_reduced`], without
/// rejection sampling or additional draws. For either Pasta modulus, the
/// statistical distance from uniform is less than `2^-128`.
pub fn random<M: PrimeModulus>(fill: impl FnOnce(&mut [u8; 64])) -> PastaField<M> {
    let mut bytes = [0u8; 64];
    fill(&mut bytes);
    PastaField::from_wide_bytes_reduced(&bytes)
}

/// Returns the low 64 bits of a Pasta value's canonical integer representative.
pub fn low_u64<M: PrimeModulus>(value: &PastaField<M, impl ReductionState>) -> u64 {
    value.to_canonical_uint().limbs()[0]
}

/// Constructs an [`Fp`](crate::field::Fp) constant from hexadecimal text.
///
/// Requires a string literal containing a canonical `0x`-prefixed, 64-digit
/// integer strictly below the field modulus. The most significant digit comes
/// first. Digits may use either case; the prefix must be lowercase `0x`.
/// Parsing and conversion run at compile time; malformed or noncanonical
/// literals fail to build even in a runtime expression.
///
/// For runtime input, use [`Fp::from_bytes`](crate::field::Fp::from_bytes) or
/// [`Fp::from_canonical_uint`](crate::field::Fp::from_canonical_uint).
///
/// ```
/// use zakura_udon::{field::Fp, fp_hex};
///
/// const VALUE: Fp =
///     fp_hex!("0x000000000000000000000000000000000000000000000000000000000000002a");
/// assert_eq!(VALUE.reduce(), Fp::from_u64(42));
/// ```
///
/// ```compile_fail
/// // The modulus itself is not a canonical field element.
/// let _ = zakura_udon::fp_hex!(
///     "0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001"
/// );
/// ```
///
/// ```compile_fail
/// // Hex strings must contain exactly 64 digits after the prefix.
/// let _ = zakura_udon::fp_hex!("0x01");
/// ```
///
/// ```compile_fail
/// // Only literals are accepted, including when a variable holds a literal.
/// let text = "0x0000000000000000000000000000000000000000000000000000000000000001";
/// let _ = zakura_udon::fp_hex!(text);
/// ```
///
/// ```compile_fail
/// let _ = zakura_udon::fp_hex!(
///     "0x000000000000000000000000000000000000000000000000000000000000000g"
/// );
/// ```
#[macro_export]
macro_rules! fp_hex {
    ($value:literal $(,)?) => {
        $crate::__pasta_hex!($crate::field::PallasBase, $crate::field::Fp, $value)
    };
}

/// Constructs an [`Fq`](crate::field::Fq) constant from hexadecimal text.
///
/// Uses the literal format and compile-time evaluation rules of
/// [`fp_hex!`](crate::fp_hex), with the canonical bound of
/// [`Fq`](crate::field::Fq).
///
/// ```compile_fail
/// let _ = zakura_udon::fq_hex!(
///     "0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001"
/// );
/// ```
#[macro_export]
macro_rules! fq_hex {
    ($value:literal $(,)?) => {
        $crate::__pasta_hex!($crate::field::PallasScalar, $crate::field::Fq, $value)
    };
}

/// Expansion support for canonical Pasta field literals.
#[doc(hidden)]
#[macro_export]
macro_rules! __pasta_hex {
    ($modulus:ty, $field:ty, $value:literal) => {
        const {
            const MODULUS: [::core::primitive::u64; 4] =
                <$modulus as $crate::field::PrimeModulus>::MODULUS;
            const CANONICAL: [::core::primitive::u64; 4] = $crate::__u256_from_hex!($value);
            ::core::assert!(
                !$crate::__u256_ge!(&CANONICAL, &MODULUS),
                "field constants must be canonical residues"
            );
            <$field>::from_montgomery_limbs($crate::__m255_from_u256!(&MODULUS, &CANONICAL))
        }
    };
}

impl<M: PrimeModulus, S: ReductionState> PastaField<M, S> {
    pub(super) fn from_canonical_limbs(limbs: [u64; 4]) -> Self {
        debug_assert!(compare_limbs(&limbs, &M::MODULUS).is_lt());
        Self::from_loose(montgomery_multiply_loose::<M>(&limbs, &M::R2))
    }

    pub(super) fn canonical_limbs(&self) -> [u64; 4] {
        #[cfg(all(udon_asm, not(miri)))]
        {
            crate::field::asm::from_mont::<M>(&self.limbs)
        }
        #[cfg(not(all(udon_asm, not(miri))))]
        {
            let mut wide = [0; 8];
            wide[..4].copy_from_slice(&self.limbs);
            super::montgomery::montgomery_reduce::<M>(wide)
        }
    }

    /// Converts an ordinary integer to this field, returning `None` if it is
    /// at least [`M::MODULUS`](PrimeModulus::MODULUS).
    pub fn from_canonical_uint(value: CanonicalUint) -> Option<Self> {
        compare_limbs(&value.limbs(), &M::MODULUS)
            .is_lt()
            .then(|| Self::from_canonical_limbs(value.limbs()))
    }

    /// Reduces an arbitrary 256-bit integer into this field.
    pub fn from_uint_reduced(value: CanonicalUint) -> Self {
        Self::from_loose(montgomery_multiply::<M>(&value.limbs(), &M::R2))
    }

    /// Decodes a canonical 32-byte little-endian field representation.
    ///
    /// Returns `None` if the encoded integer is at least the modulus.
    pub fn from_bytes(bytes: [u8; ENCODED_SIZE]) -> Option<Self> {
        Self::from_canonical_uint(CanonicalUint::from_le_bytes(bytes))
    }

    /// Reduces a little-endian integer of arbitrary width into the field.
    ///
    /// An empty slice represents zero. This is modular reduction, so it
    /// accepts encodings rejected by [`Self::from_bytes`] and does not
    /// guarantee a uniform distribution from random input bytes.
    pub fn from_bytes_reduced(bytes: &[u8]) -> Self {
        if bytes.len() <= ENCODED_SIZE {
            let mut encoded = [0; ENCODED_SIZE];
            encoded[..bytes.len()].copy_from_slice(bytes);
            return Self::from_uint_reduced(CanonicalUint::from_le_bytes(encoded));
        }
        if bytes.len() <= 2 * ENCODED_SIZE {
            let mut wide = [0; 2 * ENCODED_SIZE];
            wide[..bytes.len()].copy_from_slice(bytes);
            return Self::from_wide_bytes_reduced(&wide);
        }

        let mut chunks = bytes.chunks(ENCODED_SIZE).rev();
        let high = chunks.next().unwrap();
        let mut high_bytes = [0; ENCODED_SIZE];
        high_bytes[..high.len()].copy_from_slice(high);
        let mut value =
            PastaField::<M>::from_uint_reduced(CanonicalUint::from_le_bytes(high_bytes));
        for chunk in chunks {
            let digit = CanonicalUint::from_le_bytes(chunk.try_into().unwrap());
            // Stored V=xR and ordinary D yield (V+D)R, representing xR+D.
            value = PastaField::from_montgomery(raw_product_sum::<M>(
                &value.limbs,
                &M::R2,
                &digit.limbs(),
                &M::R2,
            ));
        }
        Self::from_loose(value.limbs)
    }

    /// Reduces a 64-byte little-endian integer into the field.
    ///
    /// This has the same result as [`Self::from_bytes_reduced`].
    pub fn from_wide_bytes_reduced(bytes: &[u8; 2 * ENCODED_SIZE]) -> Self {
        let low = CanonicalUint::from_le_bytes(bytes[..ENCODED_SIZE].try_into().unwrap());
        let high = CanonicalUint::from_le_bytes(bytes[ENCODED_SIZE..].try_into().unwrap());
        Self::from_loose(raw_product_sum::<M>(
            &low.limbs(),
            &M::R2,
            &high.limbs(),
            &M::R3,
        ))
    }

    /// Returns the canonical fixed-width integer representation.
    pub fn to_canonical_uint(self) -> CanonicalUint {
        CanonicalUint::from_limbs(self.canonical_limbs())
    }

    /// Encodes the ordinary field integer as 32 canonical little-endian bytes.
    pub fn to_bytes(self) -> [u8; ENCODED_SIZE] {
        self.to_canonical_uint().to_le_bytes()
    }

    /// Returns the stored little-endian Montgomery limbs without changing them.
    ///
    /// These are storage words; use [`Self::to_bytes`] for protocol encoding.
    #[inline]
    pub const fn montgomery_limbs(&self) -> [u64; 4] {
        self.limbs
    }

    /// Constructs a field element from Montgomery limbs within its type's bound.
    ///
    /// This reverses [`Self::montgomery_limbs`] without changing the limbs.
    ///
    /// # Panics
    ///
    /// Panics if `limbs` is outside `[0, 2p)` for `Loose`, or `[0, p)` for
    /// `Reduced`. In a const expression this produces a compile error.
    pub const fn from_montgomery_limbs(limbs: [u64; 4]) -> Self {
        assert!(
            compare_limbs(&limbs, &Self::BOUND).is_lt(),
            "Montgomery limbs exceed the representation bound"
        );
        Self {
            limbs,
            marker: PhantomData,
        }
    }

    /// Returns the parity of the canonical integer representative.
    pub fn is_odd(&self) -> bool {
        self.to_canonical_uint().bit(0) == Some(true)
    }
}

// Raw operands may exceed p. Compile-time checks in
// parameters::assert_kernel_bounds establish a*b+c*d < pR for both callers,
// where p is the modulus and R = 2^256.
#[inline]
fn raw_product_sum<M: PrimeModulus>(
    a: &[u64; 4],
    b: &[u64; 4],
    c: &[u64; 4],
    d: &[u64; 4],
) -> [u64; 4] {
    let mut sum = multiply_wide(a, b);
    let product = multiply_wide(c, d);
    let mut carry = 0;
    for (limb, term) in sum.iter_mut().zip(product) {
        (*limb, carry) = adc(*limb, term, carry);
    }
    debug_assert_eq!(carry, 0);
    montgomery_reduce_unreduced::<M>(sum)
}
