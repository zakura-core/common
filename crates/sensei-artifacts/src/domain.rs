//! Scalar domain parameters shared by field and group inverse transforms.
//!
//! Polynomial coefficients and the Lagrange SRS must use the same root
//! convention. Return the inverse root and normalization together so each
//! caller supplies both to `udon::fft::reference::inverse_transform`.

use udon::field::Fp;

use crate::Error;

/// The domain scalars of a size-`2^k` inverse transform: `(ω⁻¹, n⁻¹)`.
pub(crate) fn inverse_domain(size: usize) -> Result<(Fp, Fp), Error> {
    if !size.is_power_of_two() {
        return Err(Error::new(format!(
            "transforms require a power-of-two length, found {size}"
        )));
    }
    let k = size.trailing_zeros();
    let root_inverse = <Fp>::root_of_unity_inverse(k)
        .ok_or_else(|| Error::new(format!("no 2^{k} root of unity for a {size}-point domain")))?;
    Ok((root_inverse, <Fp>::power_of_two_inverse(k)))
}
