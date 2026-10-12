#![no_std]
#![forbid(unsafe_code)]

use udon::field::{CanonicalUint, Fp, Fq, PallasBase, PallasScalar, ProductSum, Reduced};

pub fn fp_mul(lhs: &Fp, rhs: &Fp) -> Fp {
    lhs.mul(rhs)
}

pub fn fp_add(lhs: &Fp, rhs: &Fp) -> Fp {
    lhs.add(rhs)
}

pub fn fp_sub(lhs: &Fp, rhs: &Fp) -> Fp {
    lhs.sub(rhs)
}

pub fn fp_neg(value: &Fp) -> Fp {
    value.neg()
}

pub fn fp_square(value: &Fp) -> Fp {
    value.square()
}

pub fn fp_double(value: &Fp) -> Fp {
    value.double()
}

pub fn fp_mul_add(value: &Fp, multiplier: &Fp, extra: &Fp) -> Fp {
    value.mul_add(multiplier, extra)
}

pub fn fp_mul_sub(value: &Fp, multiplier: &Fp, extra: &Fp) -> Fp {
    value.mul_sub(multiplier, extra)
}

pub fn fp_is_zero(value: &Fp) -> bool {
    value.is_zero()
}

pub fn fp_from_u64(value: u64) -> Fp {
    Fp::from_u64(value)
}

pub fn fp_from_u128(value: u128) -> Fp {
    Fp::from_u128(value)
}

pub fn fp_from_i64(value: i64) -> Fp {
    Fp::from_i64(value)
}

pub fn fp_reduce(value: Fp) -> Fp<Reduced> {
    value.reduce()
}

pub fn fp_widen(value: Fp<Reduced>) -> Fp {
    value.into_loose()
}

pub fn fp_pow_u64(value: &Fp, exponent: u64) -> Fp {
    value.pow_u64(exponent)
}

pub fn fp_reduce_reduced(value: Fp<Reduced>) -> Fp<Reduced> {
    value.reduce()
}

pub fn fp_from_u64_reduced(value: u64) -> Fp<Reduced> {
    Fp::from_u64(value)
}

pub fn fp_zero() -> Fp {
    Fp::ZERO
}

pub fn fp_one() -> Fp {
    Fp::ONE
}

pub fn fp_montgomery(value: &Fp) -> [u64; 4] {
    value.montgomery_limbs()
}

pub fn fp_import_montgomery(limbs: [u64; 4]) -> Fp {
    Fp::from_montgomery_limbs(limbs)
}

pub fn fq_mul(lhs: &Fq, rhs: &Fq) -> Fq {
    lhs.mul(rhs)
}

pub fn fq_add(lhs: &Fq, rhs: &Fq) -> Fq {
    lhs.add(rhs)
}

pub fn fq_sub(lhs: &Fq, rhs: &Fq) -> Fq {
    lhs.sub(rhs)
}

pub fn fq_neg(value: &Fq) -> Fq {
    value.neg()
}

pub fn fq_square(value: &Fq) -> Fq {
    value.square()
}

pub fn fq_double(value: &Fq) -> Fq {
    value.double()
}

pub fn fq_mul_add(value: &Fq, multiplier: &Fq, extra: &Fq) -> Fq {
    value.mul_add(multiplier, extra)
}

pub fn fq_mul_sub(value: &Fq, multiplier: &Fq, extra: &Fq) -> Fq {
    value.mul_sub(multiplier, extra)
}

pub fn fq_is_zero(value: &Fq) -> bool {
    value.is_zero()
}

pub fn fq_from_u64(value: u64) -> Fq {
    Fq::from_u64(value)
}

pub fn fq_from_u128(value: u128) -> Fq {
    Fq::from_u128(value)
}

pub fn fq_from_i64(value: i64) -> Fq {
    Fq::from_i64(value)
}

pub fn fq_reduce(value: Fq) -> Fq<Reduced> {
    value.reduce()
}

pub fn fq_widen(value: Fq<Reduced>) -> Fq {
    value.into_loose()
}

pub fn fq_pow_u64(value: &Fq, exponent: u64) -> Fq {
    value.pow_u64(exponent)
}

pub fn fq_reduce_reduced(value: Fq<Reduced>) -> Fq<Reduced> {
    value.reduce()
}

pub fn fq_from_u64_reduced(value: u64) -> Fq<Reduced> {
    Fq::from_u64(value)
}

pub fn fq_zero() -> Fq {
    Fq::ZERO
}

pub fn fq_one() -> Fq {
    Fq::ONE
}

pub fn fq_montgomery(value: &Fq) -> [u64; 4] {
    value.montgomery_limbs()
}

pub fn fq_import_montgomery(limbs: [u64; 4]) -> Fq {
    Fq::from_montgomery_limbs(limbs)
}

pub fn fp_from_canonical(value: CanonicalUint) -> Option<Fp> {
    Fp::from_canonical_uint(value)
}

pub fn fq_from_canonical(value: CanonicalUint) -> Option<Fq> {
    Fq::from_canonical_uint(value)
}

pub fn fp_is_one(value: &Fp) -> bool {
    value.is_one()
}

pub fn fq_is_one(value: &Fq) -> bool {
    value.is_one()
}

pub fn fp_triple(value: &Fp) -> Fp {
    value.triple()
}

pub fn fp_mul_by_4(value: &Fp) -> Fp {
    value.mul_by_4()
}

pub fn fp_mul_by_8(value: &Fp) -> Fp {
    value.mul_by_8()
}

pub fn fq_triple(value: &Fq) -> Fq {
    value.triple()
}

pub fn fq_mul_by_4(value: &Fq) -> Fq {
    value.mul_by_4()
}

pub fn fq_mul_by_8(value: &Fq) -> Fq {
    value.mul_by_8()
}

pub fn fp_from_uint_reduced(value: CanonicalUint) -> Fp {
    Fp::from_uint_reduced(value)
}

pub fn fq_from_uint_reduced(value: CanonicalUint) -> Fq {
    Fq::from_uint_reduced(value)
}

pub fn fp_to_canonical(value: Fp) -> CanonicalUint {
    value.to_canonical_uint()
}

pub fn fq_to_canonical(value: Fq) -> CanonicalUint {
    value.to_canonical_uint()
}

pub fn fp_from_bytes(bytes: [u8; 32]) -> Option<Fp> {
    Fp::from_bytes(bytes)
}

pub fn fq_from_bytes(bytes: [u8; 32]) -> Option<Fq> {
    Fq::from_bytes(bytes)
}

pub fn fp_to_bytes(value: Fp) -> [u8; 32] {
    value.to_bytes()
}

pub fn fq_to_bytes(value: Fq) -> [u8; 32] {
    value.to_bytes()
}

pub fn fp_is_odd(value: &Fp) -> bool {
    value.is_odd()
}

pub fn fq_is_odd(value: &Fq) -> bool {
    value.is_odd()
}

pub fn fp_from_wide_bytes_reduced(bytes: &[u8; 64]) -> Fp {
    Fp::from_wide_bytes_reduced(bytes)
}

pub fn fq_from_wide_bytes_reduced(bytes: &[u8; 64]) -> Fq {
    Fq::from_wide_bytes_reduced(bytes)
}

pub fn fp_from_bytes_reduced(bytes: &[u8]) -> Fp {
    Fp::from_bytes_reduced(bytes)
}

pub fn fq_from_bytes_reduced(bytes: &[u8]) -> Fq {
    Fq::from_bytes_reduced(bytes)
}

pub fn fp_sum_new() -> ProductSum<PallasBase> {
    ProductSum::new()
}

pub fn fp_sum_add_product(sum: &mut ProductSum<PallasBase>, lhs: &Fp, rhs: &Fp) {
    sum.add_product(lhs, rhs)
}

pub fn fp_sum_add_square(sum: &mut ProductSum<PallasBase>, value: &Fp) {
    sum.add_square(value)
}

pub fn fp_sum_add_term(sum: &mut ProductSum<PallasBase>, term: &Fp) {
    sum.add_term(term)
}

pub fn fp_sum_merge(sum: &mut ProductSum<PallasBase>, other: &ProductSum<PallasBase>) {
    sum.merge(other)
}

pub fn fp_sum_finish(sum: ProductSum<PallasBase>) -> Fp {
    sum.finish()
}

pub fn fq_sum_new() -> ProductSum<PallasScalar> {
    ProductSum::new()
}

pub fn fq_sum_add_product(sum: &mut ProductSum<PallasScalar>, lhs: &Fq, rhs: &Fq) {
    sum.add_product(lhs, rhs)
}

pub fn fq_sum_add_square(sum: &mut ProductSum<PallasScalar>, value: &Fq) {
    sum.add_square(value)
}

pub fn fq_sum_add_term(sum: &mut ProductSum<PallasScalar>, term: &Fq) {
    sum.add_term(term)
}

pub fn fq_sum_merge(sum: &mut ProductSum<PallasScalar>, other: &ProductSum<PallasScalar>) {
    sum.merge(other)
}

pub fn fq_sum_finish(sum: ProductSum<PallasScalar>) -> Fq {
    sum.finish()
}

pub fn fp_root_of_unity(log_size: u32) -> Option<Fp> {
    Fp::root_of_unity(log_size)
}

pub fn fp_root_of_unity_inverse(log_size: u32) -> Option<Fp> {
    Fp::root_of_unity_inverse(log_size)
}

pub fn fq_root_of_unity(log_size: u32) -> Option<Fq> {
    Fq::root_of_unity(log_size)
}

pub fn fq_root_of_unity_inverse(log_size: u32) -> Option<Fq> {
    Fq::root_of_unity_inverse(log_size)
}

pub fn fp_mul_sub_product(a: &Fp, b: &Fp, c: &Fp, d: &Fp) -> Fp {
    a.mul_sub_product(b, c, d)
}

pub fn fp_mul_sub_double_product(a: &Fp, b: &Fp, c: &Fp, d: &Fp) -> Fp {
    a.mul_sub_double_product(b, c, d)
}

pub fn fq_mul_sub_product(a: &Fq, b: &Fq, c: &Fq, d: &Fq) -> Fq {
    a.mul_sub_product(b, c, d)
}

pub fn fq_mul_sub_double_product(a: &Fq, b: &Fq, c: &Fq, d: &Fq) -> Fq {
    a.mul_sub_double_product(b, c, d)
}
