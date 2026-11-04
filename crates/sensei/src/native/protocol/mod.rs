//! Protocol dimensions shared by the fixed prover and verifier.
//!
//! # Transcript correspondence
//!
//! Transcript messages follow row order. Per-Action rows visit Actions in
//! request order, then columns, permutation sets, or lookups in ascending order;
//! query evaluations follow the arrays in [`sensei_shared::queries`]. In
//! particular, all instance evaluations precede all advice evaluations, and all
//! permutation products precede all lookup products. Challenges are squeezed
//! once in the listed order, except for the repeated IPA rounds; they emit no
//! proof bytes. Every proof point or scalar occupies 32 bytes.
//!
//! Paths below are relative to `native`: `ProverPrefix` is
//! `prover::ProverPrefix`, and `Equation` is `verifier::Equation`. The latter's
//! `point`/`points` helpers consume `transcript::Reader::point`; scalar reads
//! and challenges use `Reader::{scalar, scalars, challenge}` directly. Source
//! paths remain readable when either role is disabled; links to the enabled
//! roles' owning documentation follow the table.
//!
//! | Message, then challenge(s) | Multiplicity | Producing prover method | Consuming verifier read |
//! | --- | --- | --- | --- |
//! | Common verifying-key representative | 1 scalar, no proof bytes | `ProverPrefix::initialize_checked` | `Equation::proof`: `common_scalar` |
//! | Common instance commitments | 1 point / Action, no proof bytes | `ProverPrefix::initialize_checked` | `verifier::absorb_instances`: `common_point` |
//! | Advice commitments; `theta` | `ADVICE_COLUMNS` points / Action | `ProverPrefix::commit_advice` | `Equation::proof`: `a.advice`, then `challenge` |
//! | Permuted lookup input, table commitments; `beta`, `gamma` | `2 * LOOKUPS.len()` points / Action, input then table for each lookup | `ProverPrefix::commit_lookup_permutations` | `Equation::proof`: `a.lookup_pairs`, then two `challenge` calls |
//! | Permutation product commitments | `PERMUTATION_SETS` points / Action | `ProverPrefix::commit_product_arguments` | `Equation::proof`: `a.permutation` |
//! | Lookup product commitments | `LOOKUPS.len()` points / Action | `ProverPrefix::commit_product_arguments` | `Equation::proof`: `a.lookup_products` |
//! | Vanishing mask commitment; `y` | 1 point / proof | `ProverPrefix::commit_vanishing_random_polynomial` | `Equation::proof`: `vanishing`, then `challenge` |
//! | Quotient piece commitments; `x` | `QUOTIENT_PIECES` points / proof, piece order | `ProverPrefix::construct_quotient` | `Equation::proof`: `quotient`, then `challenge` |
//! | Instance evaluations | `INSTANCE_QUERIES.len()` = 1 scalar / Action | `ProverPrefix::write_evaluations` | `Equation::proof`: `a.instance_eval` |
//! | Advice evaluations | `ADVICE_QUERIES.len()` scalars / Action | `ProverPrefix::write_evaluations` | `Equation::proof`: `a.advice_evals` |
//! | Fixed evaluations | `FIXED_QUERIES.len()` scalars / proof | `ProverPrefix::write_evaluations` | `Equation::proof`: `fixed_evals` |
//! | Vanishing mask evaluation | 1 scalar / proof | `ProverPrefix::write_evaluations` | `Equation::proof`: `vanishing_eval` |
//! | Sigma evaluations | `PERMUTATION_COLUMN_COUNT` scalars / proof | `ProverPrefix::write_evaluations` | `Equation::proof`: `sigma_evals` |
//! | Permutation product evaluations | `3 * PERMUTATION_SETS - 1` scalars / Action | `ProverPrefix::write_evaluations` | `Equation::proof`: `a.permutation_evals`, two evaluations per set plus a third for each set but the last |
//! | Lookup evaluations; `x_1`, `x_2` | `5 * LOOKUPS.len()` scalars / Action | `ProverPrefix::write_evaluations` | `Equation::proof`: `a.lookup_evals`, then two `challenge` calls |
//! | Multi-opening quotient `Q′` commitment; `x_3` | 1 point / proof | `ProverPrefix::commit_multiopen_quotient` | `Equation::proof`: `q_prime`, then `challenge` |
//! | Collapsed evaluations `Q_i(x_3)`; `x_4` | `POINT_SETS` scalars / proof, opening-group order | `ProverPrefix::commit_ipa_mask` | `Equation::proof`: `u`, then `challenge` |
//! | IPA mask commitment; `xi`, `z` | 1 point / proof | `ProverPrefix::commit_ipa_mask` | `Equation::ipa`: `s`, then two `challenge` calls |
//! | IPA round `L`, `R`; `u_j` | 2 points per round, `K` rounds / proof | `ProverPrefix::finish_ipa` via `prover::ipa::run::Finish::finish` | `Equation::ipa`: each `round`, then `challenge` |
//! | Final IPA coefficient `c`, folded blind `f` | 2 scalars / proof | `ProverPrefix::finish_ipa` via `prover::ipa::run::Finish::finish` | `Equation::ipa`: `c`, then `f` |
//!
//! Common inputs are absorbed but never serialized into the proof. Each
//! instance commitment commits to the public-input prefix, zero-padded to the
//! domain size, with commitment blind one; the public statement's field bytes
//! are not absorbed separately. Proving uses [`crate::CircuitVersion::PostNu6_3`]
//! and this module's [`vk_representative`]. Verification selects its key scalar
//! with `CircuitVersion::vk_representative` and its populated prefix length with
//! `CircuitVersion::instance_len`: ten fields after NU6.3, including
//! `disable_cross_address`, versus nine for both earlier versions. The message
//! layout and counts above are shared by all three versions.
//!
//! Evaluation rotations and stage prerequisites remain with the prover methods'
//! transcript contracts; [`opening`] owns the opening groups. The encoding and
//! version-specific proof-length acceptance rules are described in
//! [`super::transcript`].

#![cfg_attr(
    feature = "prover",
    doc = "Prover stage contracts: [`prover::ProverPrefix`](super::prover::ProverPrefix)."
)]
#![cfg_attr(
    feature = "verifier",
    doc = "Verifier reads and version handling: [`verifier`](super::verifier)."
)]

pub(crate) mod opening;
pub(crate) const POINT_SETS: usize = 5;

/// The frozen post-NU6.3 verifying-key representative, absorbed before any
/// commitment by the prover and by verification of that version. Historical
/// verification selects its representative in `CircuitVersion::vk_representative`.
/// Pinned like the goldens rather than derived by the data pipeline.
pub(crate) fn vk_representative() -> udon::field::Fp {
    udon::fp_hex!("0x0522f7b7ed9fb95b2d017363ccd287622001e220169cbabb721fbf2954fab499")
}

/// Canonical proof extent, checked before allocation for arbitrary Action counts.
pub(crate) mod transcript_encoding {
    use crate::native::expression_layout::LOOKUPS;
    use sensei_shared::queries::{ADVICE_QUERIES, FIXED_QUERIES, INSTANCE_QUERIES};
    use sensei_shared::{
        ADVICE_COLUMNS, K, PERMUTATION_COLUMN_COUNT, PERMUTATION_SETS, QUOTIENT_PIECES,
    };
    pub(crate) const POINT_BYTES: usize = 32;
    pub(crate) const SCALAR_BYTES: usize = 32;
    // Vanishing mask + quotient pieces + multi-opening Q′ + IPA mask + L/R rounds.
    pub(crate) const FIXED_POINTS: usize = 1 + QUOTIENT_PIECES + 1 + 1 + 2 * K as usize;
    // Fixed evaluations + vanishing evaluation + sigma evaluations + Q_i(x_3) + c/f.
    pub(crate) const FIXED_SCALARS: usize =
        FIXED_QUERIES.len() + 1 + PERMUTATION_COLUMN_COUNT + super::POINT_SETS + 2;
    // Advice + lookup input/table/product commitments + permutation products.
    pub(crate) const ACTION_POINTS: usize = ADVICE_COLUMNS + 3 * LOOKUPS.len() + PERMUTATION_SETS;
    // Instance + advice queries + permutation evaluations (two for the last set,
    // three for the others) + five evaluations per lookup.
    pub(crate) const ACTION_SCALARS: usize =
        INSTANCE_QUERIES.len() + ADVICE_QUERIES.len() + 3 * PERMUTATION_SETS - 1
            + 5 * LOOKUPS.len();
    const BASE_BYTES: usize = FIXED_POINTS * POINT_BYTES + FIXED_SCALARS * SCALAR_BYTES;
    const ACTION_BYTES: usize = ACTION_POINTS * POINT_BYTES + ACTION_SCALARS * SCALAR_BYTES;
    /// Fixed messages plus the per-Action messages in the
    /// [transcript table](super#transcript-correspondence). Common inputs and
    /// challenges contribute no bytes; overflow at either step returns `None`.
    pub(crate) const fn proof_capacity(actions: usize) -> Option<usize> {
        match ACTION_BYTES.checked_mul(actions) {
            Some(bytes) => BASE_BYTES.checked_add(bytes),
            None => None,
        }
    }
    #[test]
    fn arbitrary_action_counts_and_overflow() {
        for n in [1, 2, 64, 65, 128, 1024, 1_000_000] {
            assert_eq!(proof_capacity(n), Some(2720 + 2272 * n));
        }
        let largest = (usize::MAX - BASE_BYTES) / ACTION_BYTES;
        assert!(proof_capacity(largest).is_some());
        assert_eq!(proof_capacity(largest + 1), None);
        assert_eq!(proof_capacity(usize::MAX), None);
    }
}
