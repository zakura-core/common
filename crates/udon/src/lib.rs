//! Pasta field and curve arithmetic and allocation-free field FFTs.
//!
//! [`field::Fp`] and [`field::Fq`] provide field arithmetic, canonical encodings,
//! inversion, square roots and ratios, and product sums without allocation.
//! [`field::PastaField::sqrt_alt`] also returns a root of a fixed nonsquare
//! multiple when the input is nonsquare. Constants and fixed exponentiation
//! schedules use this workspace's `bento` support.
//! [`curve`] provides Pallas and Vesta points, canonical encodings,
//! GLV scalar multiplication, batch normalization, and borrowed compact and
//! expanded fixed-base tables. [`msm`] sums dense or indexed inputs with
//! caller-owned scratch and execution.
//! [`fft`] provides power-of-two transforms, cosets, residue expansion, and fused
//! interpolation with caller-owned tables, buffers, scratch, and execution.
//! [`polynomial`] combines borrowed coefficient slices with caller-supplied
//! weights and implicit zero extension, evaluates polynomials with Horner's rule
//! or retained powers, divides by monic polynomials with retained remainders,
//! constructs vanishing polynomials, and interpolates small distinct point sets.
//! [`exec`] provides scoped fork/join, task budgets, and borrowed work helpers
//! shared by arithmetic and downstream workloads. [`exec::execution`] supplies bounded
//! task claims and typed admission for application schedulers; [`msm::execution`]
//! and [`fft::execution`] expose incremental arithmetic with exclusively leased scratch.
//! The optional `traits` feature adds the unstable generic interfaces described
//! below. The separate `poseidon` feature adds fixed Pasta Poseidon parameters.
//!
//! Field elements, nonidentity [`curve::AffinePoint`] values, and cached
//! [`curve::PreparedAffinePoint`] entries implement [`bento::Pod`] for direct
//! embedded storage. Construction establishes their invariants; embedding
//! preserves their exact representations for immediate use. Field arithmetic
//! returns [`field::Loose`] values; explicit reduction produces [`field::Reduced`]
//! values for equality, ordering, and square roots.
//! [`stored_form!`] names the limb representation; artifact schemas identify
//! the field, reduction state, and curve.
//!
//! Arithmetic is variable-time and provides no constant-time guarantee for
//! secret inputs.
//!
//! ```
//! use zakura_udon::{field::Fp, fp_hex};
//!
//! let value = fp_hex!("0x0000000000000000000000000000000000000000000000000000000000000007");
//! assert_eq!(value.mul(&<Fp>::from_u64(3)).reduce(), <Fp>::from_u64(21).reduce());
//! assert_eq!(value.mul(&value.invert().unwrap()).reduce(), <Fp>::ONE.reduce());
//! assert_eq!(<Fp>::from_bytes(value.to_bytes()).unwrap().reduce(), value.reduce());
//! ```
//!
//! # Features
//!
//! Concrete field, curve, FFT, and MSM APIs are always available without
//! feature flags or an allocator.
//!
//! `traits` enables unstable consumer interfaces at their domain paths:
//! `field::Field` and `FieldAdapter`, `curve::Affine` and `Projective`,
//! and generic field, FFT, and polynomial helpers.
//! `field::FieldAdapter`, `curve::AffineAdapter`, and `curve::ProjectiveAdapter`
//! implement these contracts and Rust arithmetic operators through native methods.
//! Native field, curve, FFT, and MSM kernels do not depend on the consumer traits.
//! Consumers opt in explicitly; these interfaces may change without preserving
//! compatibility. Native field and point types expose explicit arithmetic methods
//! and never implement arithmetic operators, including when `traits` is enabled.
//!
//! `poseidon` enables the fixed Pasta parameter tables, their consumer views,
//! and `cycle`, which binds fields, curves, generators, and Poseidon instances.
//! It enables `traits` because the views use the consumer field interfaces.
//! Enabling `traits` alone does not expose Poseidon parameters or `cycle`.
//! The Poseidon module is likely to move to a separate crate.
//!
//! By default, square roots and ratios use small tables of roots of unity.
//! Enabling `sqrt-table-large` selects a larger table algorithm that reduces
//! work for many square inputs, at the cost of additional static storage.
//! Performance depends on the input and target. Both configurations use
//! compile-time tables without allocation or runtime initialization, and
//! preserve the same public API and stored field representation.
//!
//! `aarch64-asm` enables assembly for loose field multiplication, squaring,
//! addition, subtraction, negation, doubling, FFT butterflies, wide Montgomery
//! reduction, repeated-square chains, canonical integer conversion, and
//! product-sum accumulation. The kernels adapt Supranational's Semolina
//! routines to preserve Udon's exact loose results. Arbitrary full-width
//! integer conversion retains its portable multiplication kernel because it
//! requires wider intermediate bounds.
//! Assembly is selected on little-endian, 64-bit AArch64 Unix and bare-metal
//! targets; unsupported targets and Miri use portable Rust. Supported builds
//! require a C assembler for the square-chain and conversion routines.
//! Unsafe arithmetic is confined to the assembly module: inline blocks operate
//! only on registers, and external routines access fixed-size limb arrays.
//! Field arithmetic keeps its `no_std`, allocation-free, and variable-time
//! contracts. Tests compare exact results against integer and Rust oracles.
//!
//! `x86_64-asm` enables the same kernels on 64-bit x86-64 targets as
//! MULX/ADCX/ADOX inline assembly transcribed from the zakura-pasta-curves
//! backend; no C assembler is needed. The backend is also selected without
//! the feature when the compiler's resolved target features include both
//! BMI2 and ADX, for example with `-C target-cpu=native` on a supporting CPU
//! or `-C target-feature=+adx,+bmi2`. There is no runtime dispatch: the
//! feature forces the backend on, and an assembly-enabled binary faults with
//! an illegal instruction on a CPU without those extensions. `portable`
//! disables the x86-64 backend in either case, including under
//! `--all-features`; it does not undo instructions enabled by Rust's target
//! flags and does not affect `aarch64-asm`. Miri uses portable Rust. Unsafe
//! arithmetic is again confined to the assembly module, whose blocks read
//! only their declared fixed-size operands; negation and doubling keep their
//! portable forms, which x86-64 compiles at least as well.
//!
//! Cargo features are additive: any consumer enabling `sqrt-table-large`,
//! `aarch64-asm`, `x86_64-asm`, or `portable` selects it for that Udon build.

#![no_std]
#![deny(unsafe_code)]
#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]
#![warn(unreachable_pub)]
// Constant-size `chunks_exact` kernels predate `as_chunks`; migrating them is
// upstream work. The pinned toolchain's Clippy predates the lint itself, so
// keep `unknown_lints` allowed until the pin reaches 1.98.
#![allow(unknown_lints)]
#![allow(clippy::chunks_exact_to_as_chunks)]

mod checks;
pub mod curve;
#[cfg(feature = "poseidon")]
pub mod cycle;
pub mod exec;
pub mod fft;
pub mod field;
pub mod msm;
pub mod polynomial;
#[cfg(feature = "poseidon")]
pub mod poseidon;

pub use field::pasta::STORED_FORM;

// Keep macro support anchored to Udon through dependency aliases and re-exports.
// These expose only Bento's const-enforcing macros, never arithmetic functions.
#[doc(hidden)]
pub use bento::const_arithmetic::{
    m255::from_u256 as __m255_from_u256,
    u256::{from_hex as __u256_from_hex, ge as __u256_ge},
};

#[cfg(test)]
extern crate std;

#[cfg(test)]
extern crate self as zakura_udon;
