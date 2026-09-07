//! Apple GPU (Metal) multiscalar multiplication for the Pasta curves.
//!
//! This crate is an experimental accelerator backend for the large
//! variable-time multiscalar multiplications (MSMs) behind Halo 2
//! verification and proving on the Pasta curves. It plugs into
//! `pasta_curves` through its process-wide accelerator registry
//! ([`pasta_curves::glv::accelerator`]): once [`install`] succeeds, every
//! MSM reaching `CurveExt::try_multiexp_vartime` with at least
//! [`Config::min_terms`] terms is offered to the GPU first, and the CPU
//! planner remains the fallback whenever the GPU declines or fails.
//!
//! # Layout
//!
//! - [`field`] and [`curve`]: the device field (twenty 13-bit limbs with a
//!   carry-free Montgomery multiplication that stays in native 32-bit
//!   integer arithmetic — Apple GPUs have no fast wide multiply) and
//!   Jacobian curve arithmetic, as portable Rust: the executable
//!   specification of the shader's arithmetic, tested against
//!   `pasta_curves`.
//! - [`pipeline`]: the MSM algorithm (GLV split, signed digits, bucket
//!   sort, bucket accumulation, chunked bucket reduction, Horner
//!   combination), with its two device kernels written as portable
//!   functions and a CPU [`pipeline::Reference`] backend that executes
//!   them over the exact buffers the GPU receives.
//! - `shaders/pasta_msm.metal`: the Metal Shading Language twins of the
//!   kernels, compiled at runtime by the Metal backend.
//! - `metal` (Apple AArch64 targets only): a dependency-free
//!   Objective-C shim and the Metal compute backend.
//!
//! # Status
//!
//! The pipeline and its reference backend are exercised on every platform.
//! The Metal backend can only run on Apple silicon, where the
//! `metal_matches_reference` integration test compares it against the
//! reference backend and `pasta_curves`; it has **not** yet been
//! benchmarked, so [`Config::default`]'s size threshold is a placeholder,
//! and the crate makes no performance claim. See the `msm_bench` example
//! for the measurement harness.

#![deny(missing_docs)]
#![deny(unsafe_op_in_unsafe_fn)]
#![cfg_attr(docsrs, feature(doc_cfg))]

use std::fmt;

use pasta_curves::glv::accelerator::{self, MultiexpAccelerator};
use pasta_curves::{pallas, vesta};

pub mod curve;
pub mod curves;
pub mod field;
#[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
#[cfg_attr(
    docsrs,
    doc(cfg(all(target_vendor = "apple", target_arch = "aarch64")))
)]
pub mod metal;
pub mod pipeline;

pub use pipeline::{Backend, Config, Error};

/// The Metal Shading Language source of the device kernels.
pub const SHADER_SOURCE: &str = include_str!("shaders/pasta_msm.metal");

/// An MSM accelerator over any [`Backend`], implementing
/// `pasta_curves`' [`MultiexpAccelerator`].
pub struct Accelerator<B> {
    name: &'static str,
    config: Config,
    backend: B,
}

impl<B: fmt::Debug> fmt::Debug for Accelerator<B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Accelerator")
            .field("name", &self.name)
            .field("config", &self.config)
            .field("backend", &self.backend)
            .finish()
    }
}

impl<B: Backend> Accelerator<B> {
    /// Wraps `backend` under `config`.
    pub fn new(name: &'static str, config: Config, backend: B) -> Self {
        Accelerator {
            name,
            config,
            backend,
        }
    }

    /// The configuration in force.
    pub fn config(&self) -> &Config {
        &self.config
    }

    /// The wrapped backend.
    pub fn backend(&self) -> &B {
        &self.backend
    }

    /// Runs the pipeline over `C` regardless of the size threshold.
    pub fn multiexp<C: pipeline::PastaCurve>(
        &self,
        scalars: &[C::Scalar],
        bases: &[C::Affine],
    ) -> Option<C::Point> {
        pipeline::multiexp::<C>(&self.backend, &self.config, scalars, bases)
    }
}

impl<B: Backend + 'static> MultiexpAccelerator for Accelerator<B> {
    fn name(&self) -> &str {
        self.name
    }

    fn min_terms(&self) -> usize {
        self.config.min_terms
    }

    fn multiexp_pallas(
        &self,
        scalars: &[pallas::Scalar],
        bases: &[pallas::Affine],
    ) -> Option<pallas::Point> {
        self.multiexp::<curves::Pallas>(scalars, bases)
    }

    fn multiexp_vesta(
        &self,
        scalars: &[vesta::Scalar],
        bases: &[vesta::Affine],
    ) -> Option<vesta::Point> {
        self.multiexp::<curves::Vesta>(scalars, bases)
    }
}

/// The CPU reference accelerator: the pipeline without a GPU. Useful for
/// validating the registry integration on any platform; not a speedup.
pub type ReferenceMsm = Accelerator<pipeline::Reference>;

impl ReferenceMsm {
    /// A reference accelerator under `config`.
    pub fn reference(config: Config) -> Self {
        Accelerator::new("pasta-msm-reference", config, pipeline::Reference)
    }
}

/// The Metal accelerator.
#[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
#[cfg_attr(
    docsrs,
    doc(cfg(all(target_vendor = "apple", target_arch = "aarch64")))
)]
pub type MetalMsm = Accelerator<metal::Metal>;

#[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
impl MetalMsm {
    /// Opens the system default Metal device and compiles the kernels.
    pub fn open(config: Config) -> Result<Self, Error> {
        Ok(Accelerator::new(
            "pasta-msm-metal",
            config,
            metal::Metal::open()?,
        ))
    }
}

/// Why [`install`] could not put a Metal accelerator in place.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstallError {
    /// This build cannot drive a GPU: not an Apple AArch64 target.
    Unsupported,
    /// The device could not be opened or the kernels did not compile.
    Device(Error),
    /// Another accelerator was installed first.
    AlreadyInstalled,
}

impl fmt::Display for InstallError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InstallError::Unsupported => {
                f.write_str("Metal MSM acceleration requires an Apple AArch64 target")
            }
            InstallError::Device(error) => write!(f, "Metal device unavailable: {error}"),
            InstallError::AlreadyInstalled => {
                f.write_str("an MSM accelerator is already installed")
            }
        }
    }
}

impl std::error::Error for InstallError {}

/// Whether this build can open a Metal device at all.
pub const fn is_supported() -> bool {
    cfg!(all(target_vendor = "apple", target_arch = "aarch64"))
}

/// Opens the Metal device and installs it as the process-wide MSM
/// accelerator (see [`pasta_curves::glv::accelerator::install`]).
///
/// Call once at startup. On success, large Pasta MSMs run on the GPU for
/// the rest of the process; on any error nothing changes and the CPU
/// planner keeps serving every MSM.
pub fn install(config: Config) -> Result<(), InstallError> {
    #[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
    {
        let accelerator = MetalMsm::open(config).map_err(InstallError::Device)?;
        accelerator::install(Box::new(accelerator)).map_err(|_| InstallError::AlreadyInstalled)
    }
    #[cfg(not(all(target_vendor = "apple", target_arch = "aarch64")))]
    {
        let _ = config;
        Err(InstallError::Unsupported)
    }
}

/// Installs the CPU reference accelerator process-wide, for tests and
/// integration checks on platforms without Metal.
pub fn install_reference(config: Config) -> Result<(), InstallError> {
    accelerator::install(Box::new(ReferenceMsm::reference(config)))
        .map_err(|_| InstallError::AlreadyInstalled)
}
