//! Prepared multiplicative digit codebooks over $R_B = \mathbf{Z}[\omega]/2^c$.
//!
//! The unprepared orbit backend treats only the six units
//! $U_6 = \{\pm1, \pm\omega, \pm\omega^2\}$ as free actions on a stored
//! point, so a radix-$2^c$ window needs one bucket per *unit orbit* —
//! $(B^2 + 2)/6$ of them. With fixed bases, a whole subgroup
//! $G \subseteq R_B^\times$ can be made free instead: one transformed point
//! $\eta(P_i)$ is prepared per $U_6$-coset of $G$, and a window then needs
//! only one bucket per $G$-orbit of the nonzero residues.
//!
//! This module owns the scalar side of that construction. Everything here is
//! exact integer arithmetic over the Eisenstein integers; no curve points
//! appear. For a subgroup $G = \langle U_6, \alpha, \beta^k\rangle$ (with
//! $\alpha = 1 - \omega$ of norm 3, $\beta = 2 - \omega$ of norm 7, and the
//! $\beta$ part optional), the [`Codebook`] constructor re-derives from
//! first principles, and asserts:
//!
//! - the subgroup closure of $G$ in $R_B^\times$;
//! - its $U_6$-coset classes (the prepared **variants**) and the
//!   $G$-orbits of the nonzero residues (the coefficient **buckets**);
//! - a small exact lift $\eta_a \in \mathbf{Z}[\omega]$ for every variant
//!   class and $\delta_j$ for every bucket orbit (minimal max-norm, with a
//!   deterministic tie-break that prefers the integer and
//!   $n\alpha = (n, -n)$ shapes the fast table builder exploits);
//! - a factorization $r \equiv u\,\eta_a\,\delta_j \pmod{B}$ for **every**
//!   nonzero residue $r$, with the exact digit $d = u\eta_a\delta_j$
//!   computed in $\mathbf{Z}[\omega]$ (never a congruent substitute — the
//!   prepared point *is* $[\eta_a]P$, so the recoded value must subtract
//!   the exact product). Among the factorizations covering a residue the
//!   constructor keeps one minimizing the digit's max-norm, which is what
//!   bounds the recoding tail.
//!
//! Recoding is fixed-length: `main_windows` $= \lceil 127/c \rceil$ steps of
//! $z \mapsto (z - d)/B$ leave a residual $t$ with
//! $\lVert t\rVert_\infty \le$ [`Codebook::tail_bound`], by the contraction
//! $|a'| \le (|a| + D_{\max})/B$ iterated from the GLV component bound
//! (each step's bound is exact integer arithmetic, and the recoder asserts
//! the final bound on every scalar). The residual is *not* forced to zero —
//! the digit set is not a canonical number system — and is instead handed
//! back to the caller for a small tail MSM over the unprepared backend.
//!
//! The bucket coefficients are integrated by a static straight-line
//! [`CoeffOp`] program computing $\sum_j [\delta_j] Q_j$, generated here as
//! a joint signed-binary (NAF) multi-exponentiation over the fixed
//! coefficients: writing $\delta_j = a_j + b_j\omega$, the sum is
//! $\sum_j [a_j]Q_j + \phi(\sum_j [b_j]Q_j)$ folded into one accumulator
//! with $\phi$ applied per-operand as a free x-rotation.

use alloc::vec;
use alloc::vec::Vec;

#[cfg(feature = "multicore")]
use maybe_rayon::prelude::*;

use super::super::{SignedMagnitude, GLV_COMPONENT_BITS};

/// The narrowest supported prepared radix width ($B = 32$).
pub(crate) const MIN_WINDOW_BITS: usize = 5;
/// The widest supported prepared radix width ($B = 512$). Wider would need
/// a multi-megabyte residue table and more than 1024 variants or buckets,
/// past the packed-code fields below.
pub(crate) const MAX_WINDOW_BITS: usize = 9;

/// The most variants and buckets a codebook may have (10 packed bits each).
const MAX_CLASSES: usize = 1024;

/// A prepared codebook shape: the radix width $c$ (radix $B = 2^c$), and
/// which subgroup of $R_B^\times$ is made free by preparation.
///
/// `beta_power: None` selects $G = \langle U_6, \alpha \rangle$ — $B/2$
/// prepared point variants per base and $B/2$ coefficient buckets.
/// `beta_power: Some(k)` adjoins $\beta^k$, trading a larger variant table
/// for fewer buckets; `Some(1)` reaches the full unit group $R_B^\times$,
/// whose orbits are the $c$ 2-adic valuation classes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CodebookMode {
    /// The window width $c$; supported range 5..=9.
    pub window_bits: usize,
    /// Adjoin $\beta^k$ to $\langle U_6, \alpha \rangle$ (`None` = α-only).
    pub beta_power: Option<u32>,
}

impl CodebookMode {
    /// α-only mode at width `window_bits`.
    pub const fn alpha_only(window_bits: usize) -> Self {
        CodebookMode {
            window_bits,
            beta_power: None,
        }
    }
}

/// An exact Eisenstein integer $a + b\omega$ with `i64` coefficients. All
/// codebook lifts and digits fit comfortably: lifts are bounded by $B/2$
/// and digits by $6(B/2)^2 < 2^{20}$.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Eis {
    pub(crate) a: i64,
    pub(crate) b: i64,
}

impl Eis {
    pub(crate) const ZERO: Eis = Eis { a: 0, b: 0 };

    pub(crate) fn mul(self, other: Eis) -> Eis {
        // (a + bω)(c + dω) = (ac − bd) + (ad + bc − bd)ω, using ω² = −1 − ω.
        Eis {
            a: self.a * other.a - self.b * other.b,
            b: self.a * other.b + self.b * other.a - self.b * other.b,
        }
    }

    fn neg(self) -> Eis {
        Eis {
            a: -self.a,
            b: -self.b,
        }
    }

    /// Multiplication by ω: $(a + b\omega)\omega = -b + (a - b)\omega$.
    fn omega(self) -> Eis {
        Eis {
            a: -self.b,
            b: self.a - self.b,
        }
    }

    /// Multiplication by the unit with the shared code-order index
    /// `[+1, -1, +ω, -ω, +ω², -ω²]` (rotation `unit >> 1`, negation
    /// `unit & 1`), matching the parent modules' convention.
    pub(crate) fn unit(self, unit: usize) -> Eis {
        debug_assert!(unit < 6);
        let mut value = self;
        for _ in 0..(unit >> 1) {
            value = value.omega();
        }
        if unit & 1 == 1 {
            value = value.neg();
        }
        value
    }

    pub(crate) fn max_norm(self) -> i64 {
        self.a.abs().max(self.b.abs())
    }

    fn euclid_norm(self) -> i64 {
        self.a * self.a - self.a * self.b + self.b * self.b
    }

    /// The residue-table index of this value mod $B = 2^c$:
    /// `(a mod B) << c | (b mod B)`.
    fn residue_index(self, window_bits: usize) -> usize {
        let radix = 1i64 << window_bits;
        ((self.a.rem_euclid(radix) as usize) << window_bits) | (self.b.rem_euclid(radix) as usize)
    }
}

/// The digit assignment of one residue class: the packed online code and
/// the recoding carries.
///
/// `packed` is zero for the zero class; a nonzero digit sets bit 31 and
/// packs `bucket` (bits 0..10), `variant` (bits 10..20), and `unit`
/// (bits 20..23). The exact digit $d = u\eta\delta$ enters the recurrence
/// through the carries alone: $z' = (z - d)/B$ per coefficient is
/// `(a >> c) + carry_a`, where `carry_a` $= (r_a - d_a)/B$ is an exact
/// small integer because $d_a \equiv r_a \pmod B$.
#[derive(Clone, Copy, Debug)]
pub(crate) struct CodeEntry {
    packed: u32,
    carry_a: i16,
    carry_b: i16,
}

const CODE_FLAG: u32 = 1 << 31;

/// Unpacks a nonzero online code into `(bucket, variant, unit)`.
#[inline(always)]
pub(crate) fn unpack_code(packed: u32) -> (usize, usize, usize) {
    debug_assert!(packed & CODE_FLAG != 0);
    (
        (packed & 0x3ff) as usize,
        ((packed >> 10) & 0x3ff) as usize,
        ((packed >> 20) & 0x7) as usize,
    )
}

fn pack_code(bucket: usize, variant: usize, unit: usize) -> u32 {
    debug_assert!(bucket < MAX_CLASSES && variant < MAX_CLASSES && unit < 6);
    CODE_FLAG | (bucket as u32) | ((variant as u32) << 10) | ((unit as u32) << 20)
}

/// One instruction of the static coefficient-integration program.
#[derive(Clone, Copy, Debug)]
pub(crate) enum CoeffOp {
    /// `acc = 2·acc`.
    Double,
    /// `acc += [±ω^rotate] Q_bucket` (skipped when the bucket is empty).
    Add {
        /// Which bucket sum to add.
        bucket: u16,
        /// Apply φ (multiply the operand's x by ζ) before adding.
        rotate: bool,
        /// Negate the operand's y before adding.
        negate: bool,
    },
}

/// A fully derived codebook: the scalar side of one prepared zero-check
/// mode. Construction is pure integer computation (no curve points) and
/// asserts every structural claim it relies on; see the module docs.
#[derive(Debug)]
pub(crate) struct Codebook {
    mode: CodebookMode,
    /// Fixed number of main recoding windows, $\lceil 127/c \rceil$.
    main_windows: usize,
    /// Componentwise bound on every recoding residual.
    tail_bound: i64,
    /// Componentwise bound on every exact digit $u\eta\delta$ (retained
    /// for reporting; the recoding consumes it through `tail_bound`).
    #[allow(dead_code)]
    max_digit: i64,
    /// Exact variant lifts $\eta_a$, indexed by the packed `variant` field.
    variants: Vec<Eis>,
    /// Exact bucket coefficients $\delta_j$, indexed by `bucket`.
    coefficients: Vec<Eis>,
    /// The $B^2$-entry residue table, indexed by `(a mod B) << c | (b mod B)`.
    entries: Vec<CodeEntry>,
    /// The static coefficient-integration program.
    program: Vec<CoeffOp>,
    /// `program`'s operation counts `(additions, doublings)`, for planning
    /// and the benchmark harness's reporting.
    #[allow(dead_code)]
    program_cost: (usize, usize),
}

/// The six units as exact Eisenstein values, in shared code order.
fn exact_units() -> [Eis; 6] {
    let one = Eis { a: 1, b: 0 };
    [
        one,
        one.neg(),
        one.omega(),
        one.omega().neg(),
        one.omega().omega(),
        one.omega().omega().neg(),
    ]
}

impl Codebook {
    /// Derives the codebook for `mode`. Panics (via assertions) if any
    /// structural property fails — a wrong codebook cannot be constructed.
    pub(crate) fn new(mode: CodebookMode) -> Self {
        let c = mode.window_bits;
        assert!(
            (MIN_WINDOW_BITS..=MAX_WINDOW_BITS).contains(&c),
            "unsupported prepared window width {c}"
        );
        let radix = 1i64 << c;
        let table_len = 1usize << (2 * c);
        let residue = |value: Eis| value.residue_index(c);
        let reduce = |value: Eis| Eis {
            a: value.a.rem_euclid(radix),
            b: value.b.rem_euclid(radix),
        };

        // Subgroup closure of G = <U6, α, β^k> as residues mod B. α and β
        // have odd norm (3 and 7), so they are units mod 2^c and the
        // closure stays inside R_B^×.
        let mut generators = vec![
            Eis { a: 0, b: 1 },  // ω
            Eis { a: -1, b: 0 }, // −1
            Eis { a: 1, b: -1 }, // α = 1 − ω
        ];
        if let Some(k) = mode.beta_power {
            let beta = Eis { a: 2, b: -1 };
            let mut power = Eis { a: 1, b: 0 };
            for _ in 0..k {
                power = reduce(power.mul(beta));
            }
            generators.push(power);
        }
        let generators: Vec<Eis> = generators.iter().map(|&g| reduce(g)).collect();

        let mut in_group = vec![false; table_len];
        let identity = Eis { a: 1, b: 0 };
        in_group[residue(identity)] = true;
        let mut frontier = vec![identity];
        while let Some(element) = frontier.pop() {
            for &generator in &generators {
                let product = reduce(element.mul(generator));
                let index = residue(product);
                if !in_group[index] {
                    in_group[index] = true;
                    frontier.push(product);
                }
            }
        }
        let group_order = in_group.iter().filter(|&&m| m).count();
        assert_eq!(group_order % 6, 0, "U6 must act freely on G");

        // U6-coset classes of G (the variants), in ascending residue order.
        let mut coset_of = vec![u16::MAX; table_len];
        let mut coset_count: usize = 0;
        for index in 0..table_len {
            if !in_group[index] || coset_of[index] != u16::MAX {
                continue;
            }
            let element = Eis {
                a: (index >> c) as i64,
                b: (index & (radix as usize - 1)) as i64,
            };
            for unit in 0..6 {
                let rotated = residue(reduce(element.unit(unit)));
                debug_assert!(in_group[rotated]);
                coset_of[rotated] = u16::try_from(coset_count).expect("coset id fits u16");
            }
            coset_count += 1;
        }
        assert_eq!(coset_count * 6, group_order, "cosets must partition G");
        assert!(coset_count <= MAX_CLASSES, "variant count exceeds packing");

        // G-orbits of the nonzero residues (the buckets), ascending order.
        let mut orbit_of = vec![u16::MAX; table_len];
        let mut orbit_count: usize = 0;
        let mut orbit_frontier: Vec<Eis> = Vec::new();
        for index in 1..table_len {
            if orbit_of[index] != u16::MAX {
                continue;
            }
            let id = u16::try_from(orbit_count).expect("orbit id fits u16");
            orbit_count += 1;
            orbit_of[index] = id;
            orbit_frontier.clear();
            orbit_frontier.push(Eis {
                a: (index >> c) as i64,
                b: (index & (radix as usize - 1)) as i64,
            });
            while let Some(element) = orbit_frontier.pop() {
                for &generator in &generators {
                    let product = reduce(element.mul(generator));
                    let product_index = residue(product);
                    debug_assert_ne!(product_index, 0, "unit multiples of nonzero are nonzero");
                    if orbit_of[product_index] == u16::MAX {
                        orbit_of[product_index] = id;
                        orbit_frontier.push(product);
                    }
                }
            }
        }
        assert!(orbit_count <= MAX_CLASSES, "bucket count exceeds packing");

        // Small exact lifts. Candidates are every nonzero lattice point of
        // the box [−B/2, B/2]² (every residue class has a lift there), in a
        // deterministic best-first order: minimal max-norm first. Variant
        // lifts break ties toward the fast-to-prepare shapes — integers
        // (n, 0), then (n, −n) = nα — before Euclidean norm; coefficient
        // lifts break ties by Euclidean norm (smaller NAF programs).
        let mut candidates: Vec<Eis> = Vec::with_capacity(((radix + 1) * (radix + 1)) as usize);
        for a in -radix / 2..=radix / 2 {
            for b in -radix / 2..=radix / 2 {
                if (a, b) != (0, 0) {
                    candidates.push(Eis { a, b });
                }
            }
        }
        let shape_rank = |value: Eis| -> i64 {
            if value.b == 0 && value.a > 0 {
                0
            } else if value.a > 0 && value.b == -value.a {
                1
            } else {
                2
            }
        };
        let mut variant_order = candidates.clone();
        variant_order.sort_by_key(|&v| (v.max_norm(), shape_rank(v), v.euclid_norm(), v.a, v.b));
        let mut coefficient_order = candidates;
        coefficient_order.sort_by_key(|&v| (v.max_norm(), v.euclid_norm(), v.a, v.b));

        let mut variants = vec![Eis::ZERO; coset_count];
        let mut variants_found = 0usize;
        for &candidate in &variant_order {
            let coset = coset_of[residue(candidate)];
            if coset != u16::MAX && variants[usize::from(coset)] == Eis::ZERO {
                variants[usize::from(coset)] = candidate;
                variants_found += 1;
                if variants_found == coset_count {
                    break;
                }
            }
        }
        assert_eq!(variants_found, coset_count, "every variant class lifts");

        let mut coefficients = vec![Eis::ZERO; orbit_count];
        let mut coefficients_found = 0usize;
        for &candidate in &coefficient_order {
            let orbit = orbit_of[residue(candidate)];
            debug_assert_ne!(orbit, u16::MAX);
            if coefficients[usize::from(orbit)] == Eis::ZERO {
                coefficients[usize::from(orbit)] = candidate;
                coefficients_found += 1;
                if coefficients_found == orbit_count {
                    break;
                }
            }
        }
        assert_eq!(coefficients_found, orbit_count, "every orbit lifts");

        // Factorize every nonzero residue as u·η·δ, keeping the smallest
        // exact digit (max-norm; the enumeration order breaks ties
        // deterministically). Coverage is guaranteed: a residue in orbit j
        // is g·δ_j for some g ∈ G, and g = u·η_a for its coset's lift.
        let units = exact_units();
        let mut best = vec![i64::MAX; table_len];
        let mut entries = vec![
            CodeEntry {
                packed: 0,
                carry_a: 0,
                carry_b: 0,
            };
            table_len
        ];
        let mut max_digit = 0i64;
        for (variant, &eta) in variants.iter().enumerate() {
            for (unit, &exact_unit) in units.iter().enumerate() {
                let rotated = exact_unit.mul(eta);
                for (bucket, &delta) in coefficients.iter().enumerate() {
                    let digit = rotated.mul(delta);
                    let index = residue(digit);
                    debug_assert_ne!(index, 0, "digits are nonzero mod B");
                    // The factorization must respect the bucket structure:
                    // the digit's residue lies in orbit `bucket`.
                    debug_assert_eq!(usize::from(orbit_of[index]), bucket);
                    let norm = digit.max_norm();
                    if norm < best[index] {
                        best[index] = norm;
                        let carry_a = ((digit.a.rem_euclid(radix)) - digit.a) >> c;
                        let carry_b = ((digit.b.rem_euclid(radix)) - digit.b) >> c;
                        entries[index] = CodeEntry {
                            packed: pack_code(bucket, variant, unit),
                            carry_a: i16::try_from(carry_a).expect("carry fits i16"),
                            carry_b: i16::try_from(carry_b).expect("carry fits i16"),
                        };
                    }
                }
            }
        }
        for (index, entry) in entries.iter().enumerate() {
            assert_eq!(
                entry.packed == 0,
                index == 0,
                "exactly the nonzero residues must factor through U6·A·D"
            );
        }
        for &norm in &best[1..] {
            max_digit = max_digit.max(norm);
        }

        // Fixed recoding length and the residual bound: iterate the exact
        // contraction |a'| <= (|a| + D_max)/B from the GLV component bound.
        let main_windows = GLV_COMPONENT_BITS.div_ceil(c);
        let mut bound: u128 = (1u128 << GLV_COMPONENT_BITS) - 1;
        for _ in 0..main_windows {
            bound = (bound + max_digit as u128) >> c;
        }
        let tail_bound = i64::try_from(bound).expect("tail bound is small");

        let (program, program_cost) = coefficient_program(&coefficients);

        Codebook {
            mode,
            main_windows,
            tail_bound,
            max_digit,
            variants,
            coefficients,
            entries,
            program,
            program_cost,
        }
    }

    pub(crate) fn mode(&self) -> CodebookMode {
        self.mode
    }

    pub(crate) fn window_bits(&self) -> usize {
        self.mode.window_bits
    }

    pub(crate) fn main_windows(&self) -> usize {
        self.main_windows
    }

    pub(crate) fn tail_bound(&self) -> i64 {
        self.tail_bound
    }

    #[cfg(test)]
    pub(crate) fn max_digit(&self) -> i64 {
        self.max_digit
    }

    pub(crate) fn variants(&self) -> &[Eis] {
        &self.variants
    }

    #[cfg(test)]
    pub(crate) fn coefficients(&self) -> &[Eis] {
        &self.coefficients
    }

    pub(crate) fn bucket_count(&self) -> usize {
        self.coefficients.len()
    }

    pub(crate) fn program(&self) -> &[CoeffOp] {
        &self.program
    }

    /// `(additions, doublings)` of the coefficient program, for planning.
    #[cfg(test)]
    pub(crate) fn program_cost(&self) -> (usize, usize) {
        self.program_cost
    }

    /// The index of the trivial variant $\eta = 1$, whose prepared layer is
    /// the bases themselves (used by the tail MSM and identity checks).
    pub(crate) fn unit_variant(&self) -> usize {
        let index = self
            .variants
            .iter()
            .position(|&eta| eta == (Eis { a: 1, b: 0 }))
            .expect("the trivial coset lifts to 1");
        index
    }

    /// Bytes of the residue table plus lift vectors (planning/reporting).
    pub(crate) fn table_bytes(&self) -> usize {
        self.entries.len() * core::mem::size_of::<CodeEntry>()
            + (self.variants.len() + self.coefficients.len()) * core::mem::size_of::<Eis>()
    }

    /// Recodes one component pair into `row` (length `main_windows`, zeroed
    /// by the caller), returning one past the highest nonzero window and
    /// the residual `t` with `z = Σ B^j d_j + B^L t`. The residual is
    /// asserted against [`Self::tail_bound`].
    fn recode_pair(&self, mut a: i128, mut b: i128, row: &mut [u32]) -> (usize, (i64, i64)) {
        debug_assert_eq!(row.len(), self.main_windows);
        let c = self.mode.window_bits;
        let mask = (1i128 << c) - 1;
        let mut top = 0;
        for (window, slot) in row.iter_mut().enumerate() {
            if a == 0 && b == 0 {
                return (top, (0, 0));
            }
            let index = (((a & mask) as usize) << c) | ((b & mask) as usize);
            let entry = self.entries[index];
            *slot = entry.packed;
            if entry.packed != 0 {
                top = window + 1;
            }
            a = (a >> c) + i128::from(entry.carry_a);
            b = (b >> c) + i128::from(entry.carry_b);
        }
        assert!(
            a.unsigned_abs().max(b.unsigned_abs()) <= self.tail_bound as u128,
            "recoding residual exceeds the derived tail bound"
        );
        (top, (a as i64, b as i64))
    }
}

/// A recoded MSM input: the window-code matrix and the per-scalar
/// residuals for the tail MSM.
pub(crate) struct Recoded {
    /// Row-major codes, `main_windows` per scalar; zero means "no digit".
    pub(crate) codes: Vec<u32>,
    /// Residuals as signed-magnitude component pairs, ready for the
    /// unprepared tail backend. Rows recoded to zero (including all rows
    /// the caller zeroed) have zero residuals.
    pub(crate) residuals: Vec<(SignedMagnitude, SignedMagnitude)>,
    /// One past the highest window holding any nonzero code.
    pub(crate) active_windows: usize,
}

fn signed_magnitude(value: i64) -> SignedMagnitude {
    SignedMagnitude {
        negative: value < 0,
        magnitude: value.unsigned_abs() as u128,
    }
}

/// Recodes every component pair. Rows whose bases are dead (identity or
/// merged away) must arrive as zero components; they recode to all-zero
/// codes and zero residuals.
pub(crate) fn recode(
    codebook: &Codebook,
    components: &[(SignedMagnitude, SignedMagnitude)],
    num_threads: usize,
) -> Recoded {
    let width = codebook.main_windows();
    let signed = |component: SignedMagnitude| {
        debug_assert_eq!(component.magnitude >> GLV_COMPONENT_BITS, 0);
        if component.negative {
            -(component.magnitude as i128)
        } else {
            component.magnitude as i128
        }
    };
    let mut codes = vec![0u32; components.len() * width];

    #[cfg(not(feature = "multicore"))]
    let _ = num_threads;
    #[cfg(feature = "multicore")]
    if num_threads > 1 {
        let mut residuals = vec![(signed_magnitude(0), signed_magnitude(0)); components.len()];
        let active_windows = codes
            .par_chunks_mut(width)
            .zip(residuals.par_iter_mut().zip(components.par_iter()))
            .map(|(row, (residual, &(first, second)))| {
                let (top, (ta, tb)) = codebook.recode_pair(signed(first), signed(second), row);
                *residual = (signed_magnitude(ta), signed_magnitude(tb));
                top
            })
            .max()
            .unwrap_or(0);
        return Recoded {
            codes,
            residuals,
            active_windows,
        };
    }

    let mut residuals = Vec::with_capacity(components.len());
    let mut active_windows = 0;
    for (row, &(first, second)) in codes.chunks_exact_mut(width).zip(components) {
        let (top, (ta, tb)) = codebook.recode_pair(signed(first), signed(second), row);
        residuals.push((signed_magnitude(ta), signed_magnitude(tb)));
        active_windows = active_windows.max(top);
    }
    Recoded {
        codes,
        residuals,
        active_windows,
    }
}

/// Non-adjacent form of `value` as `(position, negate)` digits, ascending.
fn naf(mut value: i64) -> Vec<(u32, bool)> {
    let mut digits = Vec::new();
    let mut position = 0u32;
    while value != 0 {
        if value & 1 != 0 {
            // d ∈ {1, −1} with value ≡ d (mod 4), so (value − d)/2 is even.
            let digit = 2 - value.rem_euclid(4);
            digits.push((position, digit < 0));
            value -= digit;
        }
        value >>= 1;
        position += 1;
    }
    digits
}

/// Generates the static NAF program for $\sum_j [\delta_j] Q_j$ and its
/// `(additions, doublings)` cost. MSB-first double-and-add over both
/// coordinates of every coefficient jointly; leading doublings (before any
/// addition) are elided.
fn coefficient_program(coefficients: &[Eis]) -> (Vec<CoeffOp>, (usize, usize)) {
    let mut per_position: Vec<Vec<CoeffOp>> = Vec::new();
    let mut record = |position: u32, op: CoeffOp| {
        let position = position as usize;
        if per_position.len() <= position {
            per_position.resize_with(position + 1, Vec::new);
        }
        per_position[position].push(op);
    };
    for (bucket, &delta) in coefficients.iter().enumerate() {
        let bucket = u16::try_from(bucket).expect("bucket fits u16");
        for (position, negate) in naf(delta.a) {
            record(
                position,
                CoeffOp::Add {
                    bucket,
                    rotate: false,
                    negate,
                },
            );
        }
        for (position, negate) in naf(delta.b) {
            record(
                position,
                CoeffOp::Add {
                    bucket,
                    rotate: true,
                    negate,
                },
            );
        }
    }

    let mut program = Vec::new();
    let mut additions = 0usize;
    let mut doublings = 0usize;
    for (position, ops) in per_position.iter().enumerate().rev() {
        if !program.is_empty() {
            program.push(CoeffOp::Double);
            doublings += 1;
        } else if ops.is_empty() && position + 1 == per_position.len() {
            // Unreachable (the top position is always occupied), but keep
            // the elision logic obviously safe.
            continue;
        }
        additions += ops.len();
        program.extend_from_slice(ops);
    }
    (program, (additions, doublings))
}

#[cfg(test)]
mod tests {
    use super::super::super::{decompose, testutil, GlvParams};
    use super::*;
    use crate::{pallas, vesta};
    use ff::{Field, WithSmallOrderMulGroup};

    /// The §6.3 handoff table, re-derived: (c, β exponent) →
    /// (variants, buckets). Every supported α-only width plus the tabulated
    /// β rows for B = 32 and 64 and spot checks above.
    #[test]
    fn subgroup_table_matches_handoff() {
        let expect = [
            ((5, None), (16, 16)),
            ((5, Some(4)), (32, 12)),
            ((5, Some(2)), (64, 8)),
            ((5, Some(1)), (128, 5)),
            ((6, None), (32, 32)),
            ((6, Some(8)), (64, 24)),
            ((6, Some(4)), (128, 16)),
            ((6, Some(2)), (256, 10)),
            ((6, Some(1)), (512, 6)),
            ((7, None), (64, 64)),
            ((7, Some(16)), (128, 48)),
            ((7, Some(8)), (256, 32)),
            ((8, None), (128, 128)),
            ((8, Some(32)), (256, 96)),
            ((8, Some(16)), (512, 64)),
            ((9, None), (256, 256)),
            ((9, Some(64)), (512, 192)),
        ];
        for ((window_bits, beta_power), (variants, buckets)) in expect {
            let codebook = Codebook::new(CodebookMode {
                window_bits,
                beta_power,
            });
            assert_eq!(
                (codebook.variants().len(), codebook.bucket_count()),
                (variants, buckets),
                "counts diverge from the handoff table at c={window_bits}, β^{beta_power:?}"
            );
        }
    }

    /// Modes exercised by the structural tests below.
    fn test_modes() -> Vec<CodebookMode> {
        vec![
            CodebookMode::alpha_only(5),
            CodebookMode::alpha_only(6),
            CodebookMode::alpha_only(7),
            CodebookMode::alpha_only(8),
            CodebookMode::alpha_only(9),
            CodebookMode {
                window_bits: 6,
                beta_power: Some(1),
            },
            CodebookMode {
                window_bits: 6,
                beta_power: Some(4),
            },
            CodebookMode {
                window_bits: 7,
                beta_power: Some(8),
            },
        ]
    }

    /// Every nonzero residue's entry factors exactly: unpacking
    /// (bucket, variant, unit) and recomputing d = u·η·δ in Z[ω] must land
    /// back on the residue, with carries and bounds consistent.
    #[test]
    fn residue_factorizations_are_exact() {
        for mode in test_modes() {
            let codebook = Codebook::new(mode);
            let c = mode.window_bits;
            let radix = 1i64 << c;
            let mut max_digit = 0i64;
            for (index, entry) in codebook.entries.iter().enumerate() {
                if index == 0 {
                    assert_eq!(entry.packed, 0);
                    continue;
                }
                assert_ne!(entry.packed, 0, "residue {index} must have a digit");
                let (bucket, variant, unit) = unpack_code(entry.packed);
                let eta = codebook.variants()[variant];
                let delta = codebook.coefficients()[bucket];
                let digit = exact_units()[unit].mul(eta).mul(delta);
                assert_eq!(
                    digit.residue_index(c),
                    index,
                    "digit must be congruent to its residue"
                );
                assert_eq!(
                    i64::from(entry.carry_a),
                    (digit.a.rem_euclid(radix) - digit.a) >> c
                );
                assert_eq!(
                    i64::from(entry.carry_b),
                    (digit.b.rem_euclid(radix) - digit.b) >> c
                );
                max_digit = max_digit.max(digit.max_norm());
            }
            assert_eq!(max_digit, codebook.max_digit());
            // The α-only variant lifts have the fast-preparation shapes.
            if mode.beta_power.is_none() {
                for &eta in codebook.variants() {
                    assert!(
                        (eta.b == 0 && eta.a > 0 && eta.a % 2 == 1 && eta.a < radix / 2)
                            || (eta.a > 0
                                && eta.b == -eta.a
                                && eta.a % 2 == 1
                                && eta.a < radix / 2),
                        "α-only variant lift {eta:?} is not n or nα"
                    );
                }
            }
            assert_eq!(
                codebook.variants()[codebook.unit_variant()],
                Eis { a: 1, b: 0 }
            );
        }
    }

    /// The recoding identity in the scalar field: for random and edge-case
    /// scalars, Horner-folding the digits (ω → λ) plus the shifted residual
    /// reconstructs the scalar.
    fn recoding_reconstructs<C: GlvParams>() {
        for mode in test_modes() {
            let codebook = Codebook::new(mode);
            let radix = C::ScalarExt::from(1u64 << mode.window_bits);
            let signed = |v: i64| {
                let m = C::ScalarExt::from(v.unsigned_abs());
                if v < 0 {
                    -m
                } else {
                    m
                }
            };
            let check = |k: C::ScalarExt| {
                let (first, second) = decompose::<C>(&k);
                let a = if first.0 {
                    -(first.1 as i128)
                } else {
                    first.1 as i128
                };
                let b = if second.0 {
                    -(second.1 as i128)
                } else {
                    second.1 as i128
                };
                let mut row = vec![0u32; codebook.main_windows()];
                let (_, (ta, tb)) = codebook.recode_pair(a, b, &mut row);
                let mut acc = signed(ta) + signed(tb) * C::ScalarExt::ZETA;
                for &code in row.iter().rev() {
                    acc *= radix;
                    if code != 0 {
                        let (bucket, variant, unit) = unpack_code(code);
                        let digit = exact_units()[unit]
                            .mul(codebook.variants()[variant])
                            .mul(codebook.coefficients()[bucket]);
                        acc += signed(digit.a) + signed(digit.b) * C::ScalarExt::ZETA;
                    }
                }
                assert_eq!(acc, k, "digits + residual must reconstruct k ({mode:?})");
            };
            check(C::ScalarExt::ZERO);
            check(C::ScalarExt::ONE);
            check(-C::ScalarExt::ONE);
            check(C::ScalarExt::ZETA);
            check(-C::ScalarExt::ZETA);
            for k in testutil::scalars::<C::ScalarExt>(50) {
                check(k);
            }
        }
    }

    /// Extremal component pairs stay within the derived tail bound (the
    /// recoder asserts it; this drives the worst cases through).
    #[test]
    fn tail_bound_holds_at_extremes() {
        for mode in test_modes() {
            let codebook = Codebook::new(mode);
            let max = ((1u128 << GLV_COMPONENT_BITS) - 1) as i128;
            for (a, b) in [
                (max, max),
                (max, -max),
                (-max, max),
                (-max, -max),
                (max, 0),
                (0, -max),
                (max, 1),
                (max - 1, max),
            ] {
                let mut row = vec![0u32; codebook.main_windows()];
                let (_, (ta, tb)) = codebook.recode_pair(a, b, &mut row);
                assert!(ta.abs() <= codebook.tail_bound());
                assert!(tb.abs() <= codebook.tail_bound());
            }
        }
    }

    #[test]
    fn naf_is_nonadjacent_and_reconstructs() {
        for value in -1000i64..=1000 {
            let digits = naf(value);
            let mut acc = 0i64;
            let mut last: Option<u32> = None;
            for &(position, negate) in &digits {
                if let Some(last) = last {
                    assert!(position > last + 1, "adjacent NAF digits at {value}");
                }
                last = Some(position);
                acc += if negate { -1i64 } else { 1 } << position;
            }
            assert_eq!(acc, value);
        }
    }

    macro_rules! codebook_curve_tests {
        ($mod_name:ident, $curve:ty) => {
            mod $mod_name {
                use super::*;

                #[test]
                fn recoding() {
                    recoding_reconstructs::<$curve>();
                }
            }
        };
    }

    codebook_curve_tests!(pallas_codebook, pallas::Point);
    codebook_curve_tests!(vesta_codebook, vesta::Point);
}
