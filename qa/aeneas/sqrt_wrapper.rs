#![no_std]
#![forbid(unsafe_code)]

use udon::field::{Fp, Fq, Reduced};

pub fn fp_sqrt(value: &Fp<Reduced>) -> Option<Fp<Reduced>> {
    value.sqrt()
}

pub fn fp_sqrt_alt(value: &Fp<Reduced>) -> (bool, Fp<Reduced>) {
    value.sqrt_alt()
}

pub fn fp_sqrt_ratio(value: &Fp<Reduced>, denominator: &Fp<Reduced>) -> (bool, Fp<Reduced>) {
    value.sqrt_ratio(denominator)
}

pub fn fq_sqrt(value: &Fq<Reduced>) -> Option<Fq<Reduced>> {
    value.sqrt()
}

pub fn fq_sqrt_alt(value: &Fq<Reduced>) -> (bool, Fq<Reduced>) {
    value.sqrt_alt()
}

pub fn fq_sqrt_ratio(value: &Fq<Reduced>, denominator: &Fq<Reduced>) -> (bool, Fq<Reduced>) {
    value.sqrt_ratio(denominator)
}
