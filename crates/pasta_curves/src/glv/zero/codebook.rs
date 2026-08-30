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
//! The bucket coefficients are integrated by a static position-major
//! [`CoeffAdd`] program computing $\sum_j [\delta_j] Q_j$, generated as a
//! joint radix-2 multi-exponentiation whose digit set is $\{0\} \cup U_6$:
//! every Eisenstein integer has such a recoding (mod 2 a nonzero value
//! falls in one of three classes, each covered by a $\pm$ unit pair), and
//! a unit digit costs one accumulator addition of $[\pm\omega^e]Q_j$ —
//! an x-rotation and y-negation of the bucket sum, cheaper than the two
//! separate coordinate digits a per-coordinate NAF would spend. Each
//! coefficient's recoding is *minimal-weight*, from a 0-1 BFS over the
//! finite state graph of the recoding recurrence, and the orbit
//! representatives themselves are chosen to minimize that weight first
//! (this is the coefficient-circuit optimization of the handoff's §12,
//! scoped to the digit alphabet the free unit action provides).

use alloc::vec;
use alloc::vec::Vec;

#[cfg(feature = "multicore")]
use maybe_rayon::prelude::*;

use super::super::{GLV_COMPONENT_BITS, SignedMagnitude};

/// The narrowest supported prepared radix width ($B = 32$).
pub(crate) const MIN_WINDOW_BITS: usize = 5;
/// The widest supported prepared radix width ($B = 512$). Wider would need
/// a multi-megabyte residue table and more than 1024 variants or buckets,
/// past the packed-code fields below.
pub(crate) const MAX_WINDOW_BITS: usize = 9;

/// The most variants and buckets a codebook may have (10 packed bits each).
const MAX_CLASSES: usize = 1024;

/// A prepared codebook shape: the radix width $c$ (radix $B = 2^c$), and
/// which set of residues is made free by preparation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CodebookMode {
    /// The prepared variants are the $U_6$-cosets of a subgroup
    /// $G = \langle U_6, \alpha, \beta^k \rangle \subseteq R_B^\times$,
    /// and the coefficient buckets its orbits on the nonzero residues.
    ///
    /// `beta_power: None` selects $G = \langle U_6, \alpha \rangle$ —
    /// $B/2$ prepared point variants per base and $B/2$ coefficient
    /// buckets. `beta_power: Some(k)` adjoins $\beta^k$, trading a larger
    /// variant table for fewer buckets; `Some(1)` reaches the full unit
    /// group $R_B^\times$, whose orbits are the $c$ 2-adic valuation
    /// classes.
    Subgroup {
        /// The window width $c$; supported range 5..=9.
        window_bits: usize,
        /// Adjoin $\beta^k$ to $\langle U_6, \alpha \rangle$ (`None` =
        /// α-only).
        beta_power: Option<u32>,
    },
    /// A non-subgroup cover: the prepared variants are the rectangular
    /// exponent box $\{\alpha^i\beta^j : i < I,\, j < J\}$ in the unit
    /// quotient $R_B^\times / U_6$, and the coefficients tile the rest —
    /// $\{2^v \alpha^{sI} \beta^{tJ}\}$ box translates, one set per 2-adic
    /// valuation $v$ (every nonzero residue of the local ring
    /// $\mathbf{Z}[\omega]/2^c$ is $2^v \cdot \text{unit}$, and the box's
    /// projection modulo $2^{c-v}$ keeps covering as $v$ grows).
    ///
    /// A subgroup's variant/bucket tradeoff is quantized by the subgroup
    /// lattice; a box of the same cardinality can pair the same variant
    /// count with far fewer coefficient buckets (at $c = 8$, a
    /// $16 \times 16$ box needs 47 buckets where $\beta^{32}$ needs 96),
    /// trading coefficient-program size against bucket-fill additions.
    /// The box need not be (and is not) closed under multiplication; the
    /// constructor derives every structural claim by enumeration and
    /// asserts it.
    ///
    /// **Measured (2,048 fixed bases, 32-core x86-64, 2026-08-24):** no
    /// box beats the subgroup frontier. `x8_16x16` ties `β7^8` within
    /// run noise (±1–2% across sweeps, occasionally the single best
    /// parallel cell) at the same 48 MiB, slightly ahead of `β8^32` and
    /// behind `β8^16`; `x7_16x8` matches `β7^8`'s window/fill/program
    /// numbers in half the memory but runs ~5–6% behind it — the box's
    /// lean cover has little factorization redundancy, so its
    /// minimum-norm exact digits are several bits larger (tail bounds
    /// 53–151 against the subgroups' 15–63), and every scalar's residual
    /// then reaches one more tail window. The mode is kept as a
    /// searchable point of the design space (and would be the shape to
    /// revisit with a terminal-window recoding program that cancels
    /// residuals), not as a planner default.
    #[cfg(any(test, feature = "orbits"))]
    ExponentBox {
        /// The window width $c$; supported range 5..=9.
        window_bits: usize,
        /// Box extent $I$ along $\alpha$: $1 \le I \le$ ord($\bar\alpha$)
        /// (the constructor derives the order and asserts the range).
        alpha_extent: u32,
        /// Box extent $J$ along $\beta$: $1 \le J \le$ the index
        /// $[R_B^\times/U_6 : \langle\bar\alpha\rangle]$.
        beta_extent: u32,
    },
}

impl CodebookMode {
    /// α-only subgroup mode at width `window_bits`.
    pub const fn alpha_only(window_bits: usize) -> Self {
        CodebookMode::Subgroup {
            window_bits,
            beta_power: None,
        }
    }

    /// The radix width $c$ of this mode.
    pub const fn window_bits(&self) -> usize {
        match self {
            CodebookMode::Subgroup { window_bits, .. } => *window_bits,
            #[cfg(any(test, feature = "orbits"))]
            CodebookMode::ExponentBox { window_bits, .. } => *window_bits,
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

/// One addition operand of the static coefficient-integration program:
/// $[\pm\omega^{\text{rotation}}]\,Q_{\text{bucket}}$ contributes to the
/// binary position that owns it (skipped when the bucket is empty). The
/// program is stored position-major — `program()[t]` lists position $t$'s
/// operands — so the evaluator can reduce each position's operands through
/// the shared batched-affine tree and finish with one short Horner pass
/// $\sum_t 2^t S_t$, instead of paying a projective mixed addition per
/// operand.
#[derive(Clone, Copy, Debug)]
pub(crate) struct CoeffAdd {
    /// Which bucket sum the operand reads.
    pub(crate) bucket: u16,
    /// The φ power applied to the operand (0..=2): multiply the operand's
    /// x by ζ^rotation (ζ²x = −x − ζx).
    pub(crate) rotation: u8,
    /// Negate the operand's y.
    pub(crate) negate: bool,
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
    /// The static coefficient-integration program, position-major
    /// (ascending binary position).
    program: Vec<Vec<CoeffAdd>>,
    /// `program`'s operation counts `(additions, doublings)`, for planning
    /// and the benchmark harness's reporting.
    #[allow(dead_code)]
    program_cost: (usize, usize),
}

/// Derives a subgroup mode's class structure: `coset_of` (the $U_6$-coset
/// classes of $G = \langle U_6, \alpha, \beta^k\rangle$, ascending residue
/// order) and the coefficient classes (the $G$-orbits of every nonzero
/// residue). Returns `(coset_of, coset_count, coeff_class_of, coeff_count)`.
fn derive_subgroup_classes(
    c: usize,
    beta_power: Option<u32>,
    table_len: usize,
) -> (Vec<u16>, usize, Vec<u16>, usize) {
    let radix = 1i64 << c;
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
    if let Some(k) = beta_power {
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

    (coset_of, coset_count, orbit_of, orbit_count)
}

/// Derives an exponent-box mode's class structure. The prepared variants
/// are the box $A = \{\alpha^i\beta^j : i < I,\, j < J\}$ in the unit
/// quotient $R_B^\times / U_6$; the coefficient classes are the greedy
/// tiling $D \subseteq \{2^v\alpha^{sI}\beta^{tJ}\}$ that covers every
/// nonzero residue of the local ring as $u \cdot a \cdot \delta$
/// ($u \in U_6$, $a \in A$, $\delta \in D$). Everything structural —
/// that $\bar\alpha$ and $\bar\beta$ generate the quotient independently
/// (so the box's classes are distinct), and that the tiles cover — is
/// established by enumeration here, not assumed from a formula.
/// Returns `(coset_of, coset_count, coeff_class_of, coeff_count)`, with
/// `coeff_class_of` marking exactly the |D| tile residues.
#[cfg(any(test, feature = "orbits"))]
fn derive_box_classes(
    c: usize,
    alpha_extent: usize,
    beta_extent: usize,
    table_len: usize,
) -> (Vec<u16>, usize, Vec<u16>, usize) {
    let radix = 1i64 << c;
    let residue = |value: Eis| value.residue_index(c);
    let reduce = |value: Eis| Eis {
        a: value.a.rem_euclid(radix),
        b: value.b.rem_euclid(radix),
    };
    let alpha = Eis { a: 1, b: -1 };
    let beta = Eis { a: 2, b: -1 };

    // Canonical representative (smallest residue index over the six unit
    // rotations) of a value's U6-class, for quotient bookkeeping.
    let class_rep = |value: Eis| -> usize {
        (0..6)
            .map(|unit| residue(reduce(value.unit(unit))))
            .min()
            .expect("six units")
    };
    let identity_rep = class_rep(Eis { a: 1, b: 0 });

    // Order of ᾱ in the unit quotient, by iteration.
    let quotient_order = |generator: Eis| -> usize {
        let mut power = generator;
        let mut order = 1usize;
        while class_rep(power) != identity_rep {
            power = reduce(power.mul(generator));
            order += 1;
            assert!(order <= table_len, "generator order search must terminate");
        }
        order
    };
    let ord_alpha = quotient_order(alpha);

    // Exponent coordinates (i, j) with i < ord(ᾱ) and j < [Q : ⟨ᾱ⟩]: the
    // coset decomposition of the quotient along powers of β̄. This is
    // deliberately *not* ord(β̄) — measured here, ᾱ and β̄ both have
    // order 2^{c-1} and their cyclic subgroups share a C₂, so the naive
    // ⟨ᾱ⟩ × ⟨β̄⟩ coordinatization double-counts; the coset form is valid
    // for any two generators, and the bijectivity sweep below *proves*
    // the coordinates (and thereby that α and β generate the quotient)
    // rather than trusting a structure formula. Units of the local ring
    // Z[ω]/2^c are the residues odd somewhere (3/4 of all), so the
    // quotient has 4^c·(3/4)/6 = 2^{2c-3} classes.
    let unit_classes = table_len * 3 / 4 / 6;
    assert_eq!(
        unit_classes % ord_alpha,
        0,
        "⟨ᾱ⟩ must divide the unit quotient"
    );
    let beta_index = unit_classes / ord_alpha;
    let mut seen = vec![false; table_len];
    let mut distinct = 0usize;
    let mut alpha_power = Eis { a: 1, b: 0 };
    for _ in 0..ord_alpha {
        let mut element = alpha_power;
        for _ in 0..beta_index {
            let rep = class_rep(element);
            assert!(!seen[rep], "α^i β^j coordinates must be distinct");
            seen[rep] = true;
            distinct += 1;
            element = reduce(element.mul(beta));
        }
        alpha_power = reduce(alpha_power.mul(alpha));
    }
    assert_eq!(distinct, unit_classes, "the box coordinates must be onto");

    assert!(
        (1..=ord_alpha).contains(&alpha_extent) && (1..=beta_index).contains(&beta_extent),
        "box extents must fit the coordinate ranges ({ord_alpha} × {beta_index})"
    );
    let coset_count = alpha_extent * beta_extent;
    assert!(coset_count <= MAX_CLASSES, "variant count exceeds packing");

    // Variant classes: the box elements and their unit rotations.
    let mut coset_of = vec![u16::MAX; table_len];
    let mut box_elements = Vec::with_capacity(coset_count);
    let mut alpha_power = Eis { a: 1, b: 0 };
    for i in 0..alpha_extent {
        let mut element = alpha_power;
        for j in 0..beta_extent {
            let id = u16::try_from(i * beta_extent + j).expect("coset id fits u16");
            for unit in 0..6 {
                let rotated = residue(reduce(element.unit(unit)));
                // Distinctness was proved by the coordinate sweep.
                debug_assert_eq!(coset_of[rotated], u16::MAX);
                coset_of[rotated] = id;
            }
            box_elements.push(element);
            element = reduce(element.mul(beta));
        }
        alpha_power = reduce(alpha_power.mul(alpha));
    }

    // Coefficient tiles: greedy over the 2^v·α^{sI}β^{tJ} translates in
    // ascending (v, s, t) order. A translate joins D only if it covers a
    // yet-uncovered residue — as v grows, the residue's unit part is only
    // determined modulo 2^{c-v}, the box's projection widens relative to
    // the shrinking quotient, and later translates collapse onto earlier
    // ones and are dropped. The factorization pass re-derives coverage
    // from the exact lifts and asserts it again.
    let mut covered = vec![false; table_len];
    covered[0] = true;
    let mut coeff_class_of = vec![u16::MAX; table_len];
    let mut coeff_count = 0usize;
    for v in 0..c {
        let mut alpha_translate = Eis { a: 1i64 << v, b: 0 };
        let mut s = 0;
        while s < ord_alpha {
            let mut delta = alpha_translate;
            let mut t = 0;
            while t < beta_index {
                let mut newly_covered = false;
                for element in &box_elements {
                    let product = reduce(delta.mul(*element));
                    for unit in 0..6 {
                        let index = residue(reduce(product.unit(unit)));
                        if !covered[index] {
                            covered[index] = true;
                            newly_covered = true;
                        }
                    }
                }
                if newly_covered {
                    let id = u16::try_from(coeff_count).expect("bucket id fits u16");
                    let delta_index = residue(delta);
                    assert_eq!(
                        coeff_class_of[delta_index],
                        u16::MAX,
                        "tiles are distinct residues"
                    );
                    coeff_class_of[delta_index] = id;
                    coeff_count += 1;
                    assert!(coeff_count <= MAX_CLASSES, "bucket count exceeds packing");
                }
                for _ in 0..beta_extent {
                    delta = reduce(delta.mul(beta));
                }
                t += beta_extent;
            }
            for _ in 0..alpha_extent {
                alpha_translate = reduce(alpha_translate.mul(alpha));
            }
            s += alpha_extent;
        }
    }
    assert!(
        covered.iter().skip(1).all(|&covered| covered),
        "the box cover must reach every nonzero residue"
    );

    (coset_of, coset_count, coeff_class_of, coeff_count)
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
        let c = mode.window_bits();
        assert!(
            (MIN_WINDOW_BITS..=MAX_WINDOW_BITS).contains(&c),
            "unsupported prepared window width {c}"
        );
        let radix = 1i64 << c;
        let table_len = 1usize << (2 * c);
        let residue = |value: Eis| value.residue_index(c);

        // Class structure: `coset_of` marks each variant class's residues
        // (one prepared point layer per class), `coeff_class_of` the
        // coefficient classes (one bucket per class). A subgroup mode
        // marks every nonzero residue with its G-orbit — the coefficient
        // lift search may pick any orbit member — while an exponent box
        // marks exactly its |D| tile representatives (each coefficient
        // class is a single residue, so its lift is that residue's
        // best in-box representative).
        let (coset_of, coset_count, coeff_class_of, coeff_count) = match mode {
            CodebookMode::Subgroup { beta_power, .. } => {
                derive_subgroup_classes(c, beta_power, table_len)
            }
            #[cfg(any(test, feature = "orbits"))]
            CodebookMode::ExponentBox {
                alpha_extent,
                beta_extent,
                ..
            } => derive_box_classes(c, alpha_extent as usize, beta_extent as usize, table_len),
        };
        // Only subgroup modes have the orbit invariant "a digit's residue
        // lies in its bucket's orbit"; box factorizations may cover one
        // residue from several tiles.
        let orbit_invariant = matches!(mode, CodebookMode::Subgroup { .. });

        // Small exact lifts. Candidates are every nonzero lattice point of
        // the box [−B/2, B/2]² (every residue class has a lift there), in a
        // deterministic best-first order. Variant lifts take minimal
        // max-norm, breaking ties toward the fast-to-prepare shapes —
        // integers (n, 0), then (n, −n) = nα — before Euclidean norm.
        // Coefficient lifts minimize the integration program instead:
        // fewest unit digits first (each is one accumulator addition),
        // then max-norm (which bounds the digits and the recoding tail),
        // then Euclidean norm.
        let unit_weights = UnitDigitWeights::new(radix / 2);
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
        coefficient_order.sort_by_key(|&v| {
            (
                unit_weights.weight(v),
                v.max_norm(),
                v.euclid_norm(),
                v.a,
                v.b,
            )
        });

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

        let mut coefficients = vec![Eis::ZERO; coeff_count];
        let mut coefficients_found = 0usize;
        for &candidate in &coefficient_order {
            let class = coeff_class_of[residue(candidate)];
            if class != u16::MAX && coefficients[usize::from(class)] == Eis::ZERO {
                coefficients[usize::from(class)] = candidate;
                coefficients_found += 1;
                if coefficients_found == coeff_count {
                    break;
                }
            }
        }
        assert_eq!(
            coefficients_found, coeff_count,
            "every coefficient class lifts"
        );

        // Factorize every nonzero residue as u·η·δ, keeping the smallest
        // exact digit (max-norm; the enumeration order breaks ties
        // deterministically). Coverage is guaranteed: for a subgroup, a
        // residue in orbit j is g·δ_j for some g ∈ G with g = u·η_a for
        // its coset's lift; for an exponent box, the tile derivation
        // marked every nonzero residue as some u·a·δ product of the same
        // classes lifted here.
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
                    // A subgroup factorization must respect the bucket
                    // structure: the digit's residue lies in orbit
                    // `bucket`. (Box tiles may overlap, so a residue can
                    // legitimately factor through several buckets there.)
                    debug_assert!(!orbit_invariant || usize::from(coeff_class_of[index]) == bucket);
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

        let (program, program_cost) = coefficient_program(&coefficients, &unit_weights);

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
        self.mode.window_bits()
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

    pub(crate) fn program(&self) -> &[Vec<CoeffAdd>] {
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
        self.variants
            .iter()
            .position(|&eta| eta == (Eis { a: 1, b: 0 }))
            .expect("the trivial coset lifts to 1")
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
        let c = self.mode.window_bits();
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
    /// Window-major codes, `codes[window * terms + base]`; zero means "no
    /// digit". Window-major staging scans one contiguous run per window
    /// instead of striding the whole matrix.
    pub(crate) codes: Vec<u32>,
    /// Per-window bucket histograms of the nonzero codes,
    /// `counts[window * bucket_count + bucket]`, produced during recoding
    /// so staging skips its counting pass.
    pub(crate) counts: Vec<u32>,
    /// The number of recoded scalars (one code column per window).
    pub(crate) terms: usize,
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
#[cfg(test)]
pub(super) fn recode(
    codebook: &Codebook,
    components: &[(SignedMagnitude, SignedMagnitude)],
    num_threads: usize,
) -> Recoded {
    try_recode_with(codebook, components.len(), num_threads, |index| {
        Some(components[index])
    })
    .expect("component slices cannot decline recoding")
}

/// Recodes components produced on demand, so prepared evaluations can fuse
/// scalar decomposition into the row-major recoding pass.
pub(super) fn try_recode_with(
    codebook: &Codebook,
    terms: usize,
    num_threads: usize,
    component_at: impl Fn(usize) -> Option<(SignedMagnitude, SignedMagnitude)> + Sync,
) -> Option<Recoded> {
    let width = codebook.main_windows();
    let bucket_count = codebook.bucket_count();
    let signed = |component: SignedMagnitude| {
        debug_assert_eq!(component.magnitude >> GLV_COMPONENT_BITS, 0);
        if component.negative {
            -(component.magnitude as i128)
        } else {
            component.magnitude as i128
        }
    };
    let mut codes = vec![0u32; terms * width];
    let mut counts = vec![0u32; width * bucket_count];

    #[cfg(not(feature = "multicore"))]
    let _ = num_threads;
    #[cfg(feature = "multicore")]
    if num_threads > 1 {
        // Recode into a row-major scratch matrix (rows are the natural
        // parallel unit), then transpose per window; each transpose task
        // owns one code column and its histogram slice.
        let mut rows = vec![0u32; terms * width];
        let mut residuals = vec![(signed_magnitude(0), signed_magnitude(0)); terms];
        let active_windows = rows
            .par_chunks_mut(width)
            .zip(residuals.par_iter_mut())
            .enumerate()
            .map(|(index, (row, residual))| {
                let (first, second) = component_at(index)?;
                let (top, (ta, tb)) = codebook.recode_pair(signed(first), signed(second), row);
                *residual = (signed_magnitude(ta), signed_magnitude(tb));
                Some(top)
            })
            .try_reduce(|| 0, |left, right| Some(left.max(right)))?;
        codes
            .par_chunks_mut(terms)
            .zip(counts.par_chunks_mut(bucket_count))
            .enumerate()
            .for_each(|(window, (column, window_counts))| {
                if window >= active_windows {
                    return;
                }
                for (base, row) in rows.chunks_exact(width).enumerate() {
                    let code = row[window];
                    if code != 0 {
                        column[base] = code;
                        window_counts[unpack_code(code).0] += 1;
                    }
                }
            });
        return Some(Recoded {
            codes,
            counts,
            terms,
            residuals,
            active_windows,
        });
    }

    let mut residuals = Vec::with_capacity(terms);
    let mut active_windows = 0;
    // The scratch row is only read below its returned `top`, and
    // `recode_pair` writes every slot it passes before an early exit, so
    // stale contents above `top` are never observed.
    let mut row = vec![0u32; width];
    for base in 0..terms {
        let (first, second) = component_at(base)?;
        let (top, (ta, tb)) = codebook.recode_pair(signed(first), signed(second), &mut row);
        residuals.push((signed_magnitude(ta), signed_magnitude(tb)));
        active_windows = active_windows.max(top);
        for (window, &code) in row[..top].iter().enumerate() {
            if code != 0 {
                codes[window * terms + base] = code;
                counts[window * bucket_count + unpack_code(code).0] += 1;
            }
        }
    }
    Some(Recoded {
        codes,
        counts,
        terms,
        residuals,
        active_windows,
    })
}

/// Minimal-weight radix-2 unit-digit recodings over a bounded coefficient
/// box: for every $z$ with $\lVert z\rVert_\infty \le$ `radius`, the least
/// number of nonzero digits in $z = \sum_t 2^t d_t$, $d_t \in \{0\}\cup U_6$.
///
/// The recoding recurrence is a walk on a finite graph — an even state
/// must shift ($z \mapsto z/2$, no unit shares its parity class), an odd
/// state spends one digit on either unit of its parity class
/// ($z \mapsto (z - u)/2$) — and both moves stay inside the box
/// ($|z'| \le (|z| + 1)/2$), so the minimal weights are exact shortest
/// paths to zero, computed here by 0-1 BFS over the reversed edges.
struct UnitDigitWeights {
    radius: i64,
    /// `weights[(a + radius) * side + (b + radius)]`, `u16::MAX` sentinel
    /// for "unreached" (impossible inside the box once the BFS finishes).
    weights: Vec<u16>,
}

impl UnitDigitWeights {
    fn new(radius: i64) -> Self {
        let side = (2 * radius + 1) as usize;
        let mut weights = vec![u16::MAX; side * side];
        let index = |value: Eis| -> usize {
            debug_assert!(value.max_norm() <= radius);
            ((value.a + radius) as usize) * side + ((value.b + radius) as usize)
        };
        let units = exact_units();
        let mut queue: alloc::collections::VecDeque<Eis> = alloc::collections::VecDeque::new();
        weights[index(Eis::ZERO)] = 0;
        queue.push_back(Eis::ZERO);
        while let Some(state) = queue.pop_front() {
            let weight = weights[index(state)];
            // Zero-cost predecessor: 2·state (an even value that shifts to
            // `state`).
            let double = Eis {
                a: 2 * state.a,
                b: 2 * state.b,
            };
            if double.max_norm() <= radius && weights[index(double)] > weight {
                weights[index(double)] = weight;
                queue.push_front(double);
            }
            // Unit-cost predecessors: 2·state + u (odd values whose digit
            // step lands on `state`).
            for &unit in &units {
                let pred = Eis {
                    a: 2 * state.a + unit.a,
                    b: 2 * state.b + unit.b,
                };
                if pred.max_norm() <= radius && weights[index(pred)] > weight + 1 {
                    weights[index(pred)] = weight + 1;
                    queue.push_back(pred);
                }
            }
        }
        UnitDigitWeights { radius, weights }
    }

    fn weight(&self, value: Eis) -> u16 {
        let side = (2 * self.radius + 1) as usize;
        let weight = self.weights
            [((value.a + self.radius) as usize) * side + ((value.b + self.radius) as usize)];
        debug_assert_ne!(weight, u16::MAX, "every in-box value has a recoding");
        weight
    }

    /// One minimal-weight recoding of `value`, as ascending
    /// `(position, unit-code)` digits (shared `[+1,-1,+ω,-ω,+ω²,-ω²]`
    /// code order).
    fn recode(&self, mut value: Eis) -> Vec<(u32, usize)> {
        let units = exact_units();
        let mut digits = Vec::new();
        let mut position = 0u32;
        while value != Eis::ZERO {
            if value.a & 1 == 0 && value.b & 1 == 0 {
                value = Eis {
                    a: value.a >> 1,
                    b: value.b >> 1,
                };
            } else {
                let target = self.weight(value) - 1;
                let (unit_code, next) = units
                    .iter()
                    .enumerate()
                    .filter(|(_, unit)| (value.a - unit.a) & 1 == 0 && (value.b - unit.b) & 1 == 0)
                    .map(|(code, unit)| {
                        (
                            code,
                            Eis {
                                a: (value.a - unit.a) >> 1,
                                b: (value.b - unit.b) >> 1,
                            },
                        )
                    })
                    .find(|&(_, next)| self.weight(next) == target)
                    .expect("a digit on the shortest path exists");
                digits.push((position, unit_code));
                value = next;
            }
            position += 1;
        }
        digits
    }
}

/// Generates the static program for $\sum_j [\delta_j] Q_j$ and its
/// `(additions, doublings)` cost, position-major: `program[t]` holds the
/// unit digits of binary position $t$ across every coefficient's minimal
/// unit-digit recoding, so the evaluator computes each position sum $S_t$
/// batch-affine and Horner-folds $\sum_t 2^t S_t$ with one doubling per
/// position step.
fn coefficient_program(
    coefficients: &[Eis],
    weights: &UnitDigitWeights,
) -> (Vec<Vec<CoeffAdd>>, (usize, usize)) {
    let mut per_position: Vec<Vec<CoeffAdd>> = Vec::new();
    for (bucket, &delta) in coefficients.iter().enumerate() {
        let bucket = u16::try_from(bucket).expect("bucket fits u16");
        for (position, unit_code) in weights.recode(delta) {
            let position = position as usize;
            if per_position.len() <= position {
                per_position.resize_with(position + 1, Vec::new);
            }
            per_position[position].push(CoeffAdd {
                bucket,
                rotation: (unit_code >> 1) as u8,
                negate: unit_code & 1 == 1,
            });
        }
    }

    let additions = per_position.iter().map(Vec::len).sum();
    let doublings = per_position.len().saturating_sub(1);
    (per_position, (additions, doublings))
}

#[cfg(test)]
mod tests {
    use super::super::super::{GlvParams, decompose, testutil};
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
            let codebook = Codebook::new(CodebookMode::Subgroup {
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

    /// Exponent-box class counts, re-derived: (c, I, J) → (variants,
    /// buckets). The 16×16 box at c = 8 is the assessment's candidate:
    /// 256 variants against only 47 coefficient tiles (32 + 8 + 2 + 1×5
    /// across the eight 2-adic valuations), where the subgroup lattice
    /// pays ≥96 buckets for 256 variants (β^32). Aspect ratios of one
    /// cardinality tile differently; all are derived, never assumed.
    #[test]
    fn exponent_box_counts() {
        let expect = [
            ((8, 16, 16), (256, 47)),
            ((8, 32, 8), (256, 47)),
            ((8, 8, 32), (256, 47)),
            ((7, 16, 8), (128, 25)),
            ((6, 8, 8), (64, 14)),
        ];
        for ((window_bits, alpha_extent, beta_extent), (variants, buckets)) in expect {
            let codebook = Codebook::new(CodebookMode::ExponentBox {
                window_bits,
                alpha_extent,
                beta_extent,
            });
            assert_eq!(
                (codebook.variants().len(), codebook.bucket_count()),
                (variants, buckets),
                "box counts diverge at c={window_bits}, {alpha_extent}x{beta_extent}"
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
            CodebookMode::Subgroup {
                window_bits: 6,
                beta_power: Some(1),
            },
            CodebookMode::Subgroup {
                window_bits: 6,
                beta_power: Some(4),
            },
            CodebookMode::Subgroup {
                window_bits: 7,
                beta_power: Some(8),
            },
            CodebookMode::ExponentBox {
                window_bits: 6,
                alpha_extent: 8,
                beta_extent: 8,
            },
            CodebookMode::ExponentBox {
                window_bits: 8,
                alpha_extent: 16,
                beta_extent: 16,
            },
        ]
    }

    #[test]
    fn callback_recoding_handles_serial_rows_and_declines() {
        let codebook = Codebook::new(CodebookMode::alpha_only(7));
        let zero = SignedMagnitude {
            negative: false,
            magnitude: 0,
        };
        let recoded = try_recode_with(&codebook, 4, 1, |_| Some((zero, zero)))
            .expect("zero rows can be recoded");
        assert_eq!(recoded.terms, 4);
        assert_eq!(recoded.active_windows, 0);
        assert!(recoded.codes.iter().all(|&code| code == 0));
        assert!(recoded.counts.iter().all(|&count| count == 0));
        assert!(recoded.residuals.iter().all(|&pair| pair == (zero, zero)));

        for num_threads in [1, 2] {
            assert!(
                try_recode_with(&codebook, 4, num_threads, |index| {
                    (index != 2).then_some((zero, zero))
                })
                .is_none()
            );
        }
    }

    /// Every nonzero residue's entry factors exactly: unpacking
    /// (bucket, variant, unit) and recomputing d = u·η·δ in Z[ω] must land
    /// back on the residue, with carries and bounds consistent.
    #[test]
    fn residue_factorizations_are_exact() {
        for mode in test_modes() {
            let codebook = Codebook::new(mode);
            let c = mode.window_bits();
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
            if let CodebookMode::Subgroup {
                beta_power: None, ..
            } = mode
            {
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
            let radix = C::ScalarExt::from(1u64 << mode.window_bits());
            let signed = |v: i64| {
                let m = C::ScalarExt::from(v.unsigned_abs());
                if v < 0 { -m } else { m }
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

    /// Every in-box value's minimal unit-digit recoding reconstructs it
    /// exactly, matches the tabulated weight, and never beats the trivial
    /// lower bound; the weight also never exceeds the per-coordinate NAF
    /// weight (the recoding it replaced), since coordinate NAF digits
    /// embed into unit digits one-for-one when they don't share positions.
    #[test]
    fn unit_digit_recoding_is_minimal_and_exact() {
        let radius = 64;
        let weights = UnitDigitWeights::new(radius);
        let naf_weight = |mut v: i64| -> u16 {
            let mut weight = 0;
            while v != 0 {
                if v & 1 != 0 {
                    v -= 2 - v.rem_euclid(4);
                    weight += 1;
                }
                v >>= 1;
            }
            weight
        };
        for a in -radius..=radius {
            for b in -radius..=radius {
                let value = Eis { a, b };
                let digits = weights.recode(value);
                assert_eq!(digits.len(), usize::from(weights.weight(value)));
                let mut acc = Eis::ZERO;
                for &(position, unit_code) in &digits {
                    let unit = exact_units()[unit_code];
                    acc = Eis {
                        a: acc.a + (unit.a << position),
                        b: acc.b + (unit.b << position),
                    };
                }
                assert_eq!(acc, value, "digits must reconstruct {value:?}");
                if value != Eis::ZERO {
                    assert!(weights.weight(value) >= 1);
                }
                // At most one digit per position is spent, so two separate
                // coordinate NAFs are always matchable.
                assert!(
                    weights.weight(value) <= naf_weight(a) + naf_weight(b),
                    "unit digits must not lose to per-coordinate NAF at {value:?}"
                );
            }
        }
        // Spot checks: units are single digits; α = 1 − ω needs two.
        assert_eq!(weights.weight(Eis { a: 1, b: 1 }), 1); // −ω²
        assert_eq!(weights.weight(Eis { a: 1, b: -1 }), 2); // α
        assert_eq!(weights.weight(Eis { a: 8, b: 0 }), 1); // 2³
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
