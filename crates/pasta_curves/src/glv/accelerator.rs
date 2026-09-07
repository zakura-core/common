//! Process-wide registration of an external multiscalar-multiplication
//! accelerator (for example a GPU backend).
//!
//! The Pasta MSM planner in this module's parent consults the installed
//! accelerator, if any, before choosing one of its CPU backends: an MSM with
//! at least [`MultiexpAccelerator::min_terms`] terms is first offered to the
//! accelerator, and only when it declines (returns `None`) does the CPU
//! planner run. Everything reachable through
//! [`CurveExt::try_multiexp_vartime`](crate::arithmetic::CurveExt::try_multiexp_vartime)
//! — including halo2's `best_multiexp` — therefore uses the accelerator
//! automatically once one is installed.
//!
//! The registry is a write-once global: [`install`] succeeds at most once
//! per process, and the accelerator lives for the rest of the process. This
//! keeps the hot path a single atomic load and lets a host application (a
//! node binary) decide at startup, from its own configuration, whether an
//! accelerator is used at all.
//!
//! # Contract
//!
//! An accelerator returns either the exact multiscalar multiplication
//! $\sum_i \[k_i\] P_i$ or `None`. It must never return an approximation or a
//! result it could not verify came from a healthy device: consumers such as
//! proof verifiers compare the returned point against the identity, so a
//! wrong point is a soundness bug, while `None` merely costs the CPU
//! fallback. Accelerators run in variable time — every input reaching them
//! is public, as documented on `try_multiexp_vartime`.

use alloc::boxed::Box;
use core::fmt;

use once_cell::race::OnceBox;

use crate::{pallas, vesta};

/// An external backend for variable-time Pasta multiscalar multiplications.
///
/// Implementations are consulted from any thread and may be called
/// concurrently, so they must serialize access to a shared device
/// themselves. See the [module docs](self) for the correctness contract.
pub trait MultiexpAccelerator: Send + Sync + fmt::Debug {
    /// A short human-readable backend name, for logging.
    fn name(&self) -> &str;

    /// The smallest term count worth offering to this backend. Smaller MSMs
    /// go straight to the CPU planner without a call.
    fn min_terms(&self) -> usize;

    /// The exact MSM $\sum_i \[k_i\] P_i$ over Pallas, or `None` to decline.
    ///
    /// `scalars` and `bases` have equal length (at least
    /// [`min_terms`](Self::min_terms)).
    fn multiexp_pallas(
        &self,
        scalars: &[pallas::Scalar],
        bases: &[pallas::Affine],
    ) -> Option<pallas::Point>;

    /// The exact MSM $\sum_i \[k_i\] P_i$ over Vesta, or `None` to decline.
    ///
    /// `scalars` and `bases` have equal length (at least
    /// [`min_terms`](Self::min_terms)).
    fn multiexp_vesta(
        &self,
        scalars: &[vesta::Scalar],
        bases: &[vesta::Affine],
    ) -> Option<vesta::Point>;
}

static ACCELERATOR: OnceBox<Box<dyn MultiexpAccelerator>> = OnceBox::new();

/// Installs `accelerator` as the process-wide MSM accelerator.
///
/// Succeeds at most once per process. When an accelerator is already
/// installed the argument is handed back unchanged in the `Err` variant, so
/// a caller can log the conflict or drop the device it opened.
pub fn install(
    accelerator: Box<dyn MultiexpAccelerator>,
) -> Result<(), Box<dyn MultiexpAccelerator>> {
    ACCELERATOR
        .set(Box::new(accelerator))
        .map_err(|rejected| *rejected)
}

/// The installed accelerator, if any.
pub fn installed() -> Option<&'static dyn MultiexpAccelerator> {
    ACCELERATOR.get().map(|boxed| &**boxed)
}

/// Splits `k` as $k = k_1 + k_2 \lambda \pmod n$ with $|k_1|, |k_2| < 2^{127}$,
/// where $\lambda$ = `Scalar::ZETA` is the eigenvalue of the curve
/// endomorphism, returning each half as `(is_negative, magnitude)`.
///
/// This is an internal cross-crate bridge for accelerator backends, which
/// pair $k_2$ with the endomorphism image of the base
/// (`x * Base::ZETA`, `y`) so both halves become ordinary terms with
/// 127-bit scalars. Variable-time in `k`.
#[doc(hidden)]
pub fn split_scalar_vartime<C: super::GlvParams>(k: &C::ScalarExt) -> ((bool, u128), (bool, u128)) {
    super::decompose::<C>(k)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ff::{Field, PrimeField, WithSmallOrderMulGroup};

    fn split_reconstructs<C: super::super::GlvParams>(k: C::ScalarExt) {
        let ((neg1, k1), (neg2, k2)) = split_scalar_vartime::<C>(&k);
        assert!(k1 < 1 << 127);
        assert!(k2 < 1 << 127);
        let signed = |neg: bool, magnitude: u128| {
            let value = C::ScalarExt::from_u128(magnitude);
            if neg { -value } else { value }
        };
        let expected = signed(neg1, k1) + signed(neg2, k2) * C::ScalarExt::ZETA;
        assert_eq!(expected, k);

        // The endomorphism pairing accelerators rely on: k2 * P = k2' * phi(P).
        let p = C::generator() * C::ScalarExt::from(0x1234_5678u64);
        let phi = crate::arithmetic::CurveExt::endo(&p);
        let via_split = p * signed(neg1, k1) + phi * signed(neg2, k2);
        assert_eq!(via_split.to_affine(), (p * k).to_affine());
    }

    #[test]
    fn split_scalar_reconstructs_pallas() {
        for k in [
            pallas::Scalar::ZERO,
            pallas::Scalar::ONE,
            -pallas::Scalar::ONE,
            pallas::Scalar::ZETA,
            pallas::Scalar::from_u128(u128::MAX),
            -pallas::Scalar::from(7u64).invert().unwrap(),
        ] {
            split_reconstructs::<pallas::Point>(k);
        }
    }

    #[test]
    fn split_scalar_reconstructs_vesta() {
        for k in [
            vesta::Scalar::ZERO,
            vesta::Scalar::ONE,
            -vesta::Scalar::ONE,
            vesta::Scalar::ZETA,
            vesta::Scalar::from_u128(u128::MAX),
            -vesta::Scalar::from(7u64).invert().unwrap(),
        ] {
            split_reconstructs::<vesta::Point>(k);
        }
    }
}
