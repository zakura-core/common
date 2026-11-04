//! Expansion-time code generation for the `sensei` prover.
//!
//! Like `bento-macros`, this crate keeps its entry points thin: parsing
//! delegates to private evaluators returning `syn::Result<TokenStream>`.
//! Circuit recipes and arithmetic belong to [`sensei_shared`] and its supporting
//! crates; validation, scheduling, and Rust token emission belong here.
//!
//! The compiler runs these macros and their dependency copies on the host.
//! Only the emitted Rust is compiled into the prover. This crate never depends
//! on `sensei`, consumes witnesses, or draws proving randomness.
//!
//! Start with [`expression_programs!`] for compact expression schedules, and
//! [`weighted_bilinear_kernel!`] / [`weighted_factor_kernel!`] for the fused
//! gate kernels' integration contracts. Follow
//! [Sensei's crate map](../zakura_sensei/index.html#crate-map) to the target
//! runtime and its test-only tree reference. Embedded data comes from the
//! separate host generator,
//! [`sensei-artifacts`](../zakura_sensei_artifacts/index.html); macro expansion
//! reads the shared recipes directly, not its serialized artifacts.
#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]

mod emit;
mod expression_programs;
mod weighted_bilinear;
mod weighted_factor;

use proc_macro::TokenStream;
use syn::{LitInt, parse::Nothing, parse_macro_input};

/// Generates the fixed circuit's full expressions and fixed-root operands.
///
/// Takes no arguments. This is an internal integration macro for `sensei`:
/// the invoking module supplies `CompiledExpression { id, fixed_only, schedule }`,
/// `CompiledProgram { full, split }`, `ExpressionSchedule`, `ExpressionQuery`,
/// `Instruction`, and `QueryKind`. It emits immutable `PROGRAMS` and private
/// `SCHEDULE_<id>` instruction and query tables, consumed by the prover's
/// single concrete evaluation loop.
///
/// Tree construction, structural interning, fixed-factor analysis, operand
/// validation, and topological scheduling happen during expansion. Each
/// entry's table evaluates every distinct reachable node once per row using
/// local scratch slots; equal source trees retain equal global IDs. Query
/// descriptors are resolved to column indices and modular rotations on the
/// host, then the caller binds validated column slices before row evaluation.
/// No per-entry functions, generic evaluator graph, or runtime compiler is
/// emitted. Repeated nodes share values, so repeated query reads are removed.
#[proc_macro]
pub fn expression_programs(input: TokenStream) -> TokenStream {
    let _ = parse_macro_input!(input as Nothing);
    finish_expansion(expression_programs::evaluate())
}

/// Generates a factored kernel for four consecutive gate constraints whose
/// dynamic bodies form a rank-one bilinear block, `(C · L_a) · R_b`.
///
/// Takes the first constraint's program index as an integer literal. The
/// four entries `first..first + 4` must lie within
/// [`sensei_shared::programs::expression_programs`]. At expansion, each
/// selected tree must be a root product with exactly one fixed-only operand,
/// and all four must share that same structural fixed factor (the selector).
/// Their dynamic bodies must have the nested product shape `(C · L_a) · R_b`
/// with structurally equal operands in `(0,0), (0,1), (1,0), (1,1)` order.
/// Recognition is deliberately narrower than algebraic equivalence: it does
/// not reassociate or commute products to obtain this shape.
///
/// Emits one private `#[inline(always)]` function, with `<first>` replaced by
/// the first index in decimal:
///
/// ```text
/// fn weighted_bilinear_kernel_<first>(
///     q: &[Fp; GATE_QUERY_COUNT],
///     y: &Fp,
///     powers: &[Fp; GATE_CONSTRAINT_COUNT],
/// ) -> (Fp, Fp)
/// ```
///
/// Its returned factors are `C · (powers[first + 1] · L_0 +
/// powers[first + 3] · L_1)` and `y · R_0 + R_1`. Their product equals
/// `Σ body[i] · powers[i]` over the four slots provided that
/// `powers[first] = y · powers[first + 1]` and
/// `powers[first + 2] = y · powers[first + 3]`. These are runtime caller
/// preconditions, separate from expansion-time shape checks. The emitted
/// function compares the reduced field values with `debug_assert_eq!`;
/// builds with debug assertions disabled do not check them. No relationship
/// between the two middle weights is required by this identity.
///
/// Both weighted macros use the same caller context. They are internal
/// integration macros for `sensei`'s fused gate fold: the invoking module
/// supplies Sensei's `Fp`, `RowSum` (a product-sum accumulator with `new`,
/// `add_product`, and `finish`), `GATE_QUERY_COUNT`, `GATE_CONSTRAINT_COUNT`,
/// `constant`, and `scale`. The query array follows
/// [`sensei_shared::queries::GATE_QUERY_DESCRIPTORS`]: `q[slot]` holds the value
/// of that descriptor's query, resolved through its kind's query table and
/// column/rotation. A frame slot is not an absolute column index. The weight
/// array follows absolute gate program indices in protocol order, so
/// `powers[i]` belongs to program `i`, not to a position within the selected
/// group. It must contain every selected index. Neither kernel includes the
/// fixed root factor; the caller applies that selector to the gate's sum.
///
/// For example, these accepted invocations occur in Sensei's
/// `src/native/generated_expressions.rs`. This contextual excerpt narrows the
/// imports to the required names; it relies on Sensei's internal `field` and
/// `expression_layout` modules and is not a standalone Rust example:
///
/// ```text
/// use super::field::{Fp, ProductSum};
/// use super::expression_layout::GATE_CONSTRAINT_COUNT;
/// use sensei_shared::constants::{constant, scale};
/// use sensei_shared::queries::GATE_QUERY_COUNT;
/// type RowSum = ProductSum<super::field::PallasBase>;
///
/// sensei_macros::weighted_bilinear_kernel!(13);
/// sensei_macros::weighted_factor_kernel!([67, 68, 69, 70, 72]);
/// ```
///
/// These generate `weighted_bilinear_kernel_13` and
/// `weighted_factor_kernel_67`. Names depend only on the macro kind and first
/// index: two invocations of the same macro with the same first index in the
/// same module collide, as does an existing item with the emitted name.
#[proc_macro]
pub fn weighted_bilinear_kernel(input: TokenStream) -> TokenStream {
    let first = parse_macro_input!(input as LitInt);
    finish_expansion(weighted_bilinear::evaluate(first))
}

/// Generates a factored kernel for a group of gate constraints whose dynamic
/// bodies share one factor: `A · B_i` (or `B_i · A`) under one selector.
///
/// Takes a bracketed list of at least two integer-literal program indices,
/// strictly ascending and not necessarily consecutive. Each must fit `usize`
/// and lie in `0..sensei_shared::expressions::PROGRAM_COUNT`, indexing
/// [`sensei_shared::programs::expression_programs`]. Expansion requires each
/// selected tree to be a root product with exactly one fixed-only operand,
/// with the same structural fixed factor (selector) across the group. After
/// removing that factor, every body must be a product with a structurally
/// identical operand on the same side: all `A · B_i` or all `B_i · A`.
/// Mixing sides to expose `A` is rejected. Recognition does not reassociate
/// or commute products, even when the expressions are algebraically equal.
///
/// Emits one private `#[inline(always)]` function, with `<first>` replaced by
/// the first index in decimal:
///
/// ```text
/// fn weighted_factor_kernel_<first>(
///     q: &[Fp; GATE_QUERY_COUNT],
///     powers: &[Fp; GATE_CONSTRAINT_COUNT],
/// ) -> (Fp, Fp)
/// ```
///
/// Returns the shared factor `A` and the reduced weighted sum
/// `Σ powers[i] · B_i`, whose product is `Σ powers[i] · body_i` over the
/// selected indices. Weights use absolute program indices, including gaps;
/// the array must contain every selected index. Arbitrary weights are valid:
/// there is no consecutive-power precondition or runtime weight assertion.
/// The query array follows [`sensei_shared::queries::GATE_QUERY_DESCRIPTORS`],
/// and the caller applies the shared selector to the gate's sum.
///
/// See [`weighted_bilinear_kernel!`] for the required caller types, constants,
/// helpers, and a contextual accepted invocation. The generated name depends
/// only on the first index, so two factor groups with the same first index in
/// the same module collide even if their remaining indices differ. The
/// bilinear macro uses a different function-name prefix.
#[proc_macro]
pub fn weighted_factor_kernel(input: TokenStream) -> TokenStream {
    let programs = parse_macro_input!(input as weighted_factor::ProgramIndices);
    finish_expansion(weighted_factor::evaluate(programs))
}

fn finish_expansion(result: syn::Result<proc_macro2::TokenStream>) -> TokenStream {
    result
        .unwrap_or_else(|error| error.into_compile_error())
        .into()
}
