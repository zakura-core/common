//! The process-wide MSM accelerator registry, exercised end to end through
//! `CurveExt::try_multiexp_vartime`. Lives in its own test binary because
//! the registry is write-once per process.

#![cfg(feature = "accelerator")]

use std::sync::atomic::{AtomicUsize, Ordering};

use ff::Field;
use group::Curve;
use pasta_curves::arithmetic::CurveExt;
use pasta_curves::glv::accelerator::{self, MultiexpAccelerator};
use pasta_curves::{pallas, vesta};

/// Calls made to the installed mock (the registry only exposes the trait
/// object, so the counter is global).
static CALLS: AtomicUsize = AtomicUsize::new(0);

/// A mock backend that evaluates the MSM naively and counts its calls.
#[derive(Debug)]
struct Naive {
    decline: bool,
}

const MIN_TERMS: usize = 4;

fn naive<C: CurveExt>(scalars: &[C::ScalarExt], bases: &[C::AffineExt]) -> C {
    scalars
        .iter()
        .zip(bases)
        .fold(C::identity(), |acc, (k, p)| acc + *p * *k)
}

impl MultiexpAccelerator for Naive {
    fn name(&self) -> &str {
        "naive"
    }

    fn min_terms(&self) -> usize {
        MIN_TERMS
    }

    fn multiexp_pallas(
        &self,
        scalars: &[pallas::Scalar],
        bases: &[pallas::Affine],
    ) -> Option<pallas::Point> {
        CALLS.fetch_add(1, Ordering::SeqCst);
        (!self.decline).then(|| naive::<pallas::Point>(scalars, bases))
    }

    fn multiexp_vesta(
        &self,
        scalars: &[vesta::Scalar],
        bases: &[vesta::Affine],
    ) -> Option<vesta::Point> {
        CALLS.fetch_add(1, Ordering::SeqCst);
        (!self.decline).then(|| naive::<vesta::Point>(scalars, bases))
    }
}

fn inputs<C: CurveExt>(terms: usize) -> (Vec<C::ScalarExt>, Vec<C::AffineExt>) {
    let scalars: Vec<_> = (0..terms)
        .map(|i| C::ScalarExt::from(0x9E37_79B9u64 + i as u64).square())
        .collect();
    let bases: Vec<_> = (0..terms)
        .map(|i| (C::generator() * C::ScalarExt::from(i as u64 + 3)).to_affine())
        .collect();
    (scalars, bases)
}

#[test]
fn registry_routes_large_msms_through_the_accelerator() {
    accelerator::install(Box::new(Naive { decline: false })).expect("first install succeeds");
    let installed = accelerator::installed().expect("installed");
    assert_eq!(installed.name(), "naive");
    assert_eq!(installed.min_terms(), MIN_TERMS);

    // A second install is refused and hands the rejected backend back.
    let rejected = accelerator::install(Box::new(Naive { decline: true }))
        .expect_err("second install is refused");
    assert_eq!(rejected.name(), "naive");
    assert_eq!(
        accelerator::installed().map(|a| a.min_terms()),
        Some(MIN_TERMS)
    );

    // Below the threshold the accelerator is never consulted.
    let (scalars, bases) = inputs::<pallas::Point>(MIN_TERMS - 1);
    let expected = naive::<pallas::Point>(&scalars, &bases);
    let cpu = pallas::Point::try_multiexp_vartime(&scalars, &bases).unwrap_or(expected);
    assert_eq!(cpu.to_affine(), expected.to_affine());
    assert_eq!(CALLS.load(Ordering::SeqCst), 0);

    let mut expected_calls = 0;
    for terms in [MIN_TERMS, 17, 300] {
        let (scalars, bases) = inputs::<pallas::Point>(terms);
        let expected = naive::<pallas::Point>(&scalars, &bases);
        let got =
            pallas::Point::try_multiexp_vartime(&scalars, &bases).expect("the accelerator answers");
        assert_eq!(got.to_affine(), expected.to_affine());

        let (scalars, bases) = inputs::<vesta::Point>(terms);
        let expected = naive::<vesta::Point>(&scalars, &bases);
        let got =
            vesta::Point::try_multiexp_vartime(&scalars, &bases).expect("the accelerator answers");
        assert_eq!(got.to_affine(), expected.to_affine());

        expected_calls += 2;
        assert_eq!(CALLS.load(Ordering::SeqCst), expected_calls);
    }
}
