//! Frozen constraint order and degree classes for the quotient Horner fold.
//!
//! Slot positions determine powers of the transcript challenge. Keep the family
//! inventory here aligned with the class kernels; it is part of proof parity.

use crate::native::generated_expressions::{GATE_PROGRAMS_2N, GATE_PROGRAMS_4N, LOOKUPS};
use crate::native::{generated_expressions::GATE_CONSTRAINT_COUNT, target::PERMUTATION_SETS};

/// The degree class a fold term is evaluated on: the fused 8N pass, or
/// one of the carved classes whose rows the class kernels handle.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum DegreeClass {
    /// Folded by the fused 8N row kernel.
    Extended,
    /// Carved out for the 4N class kernel.
    Class4N,
    /// Carved out for the 2N class kernel.
    Class2N,
    /// Carved out for the N class kernel.
    ClassN,
}

/// The named term families of one Action's fold, in the frozen order.
/// Each entry is (family, per-Action multiplicity); the lookup families
/// interleave per lookup (`LOOKUP_TERMS` terms for lookup 0, then lookup
/// 1, ...) and are described by [`LOOKUP_FAMILY_CLASSES`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Family {
    /// The gate constraints, one slot per program.
    Gates,
    /// The permutation argument's `l_0` boundary.
    PermutationL0,
    /// The permutation argument's `l_last` boundary.
    PermutationLLast,
    /// The set continuity terms (every set but the first).
    Continuity,
    /// The set product rules (one per set).
    Rules,
    /// The per-lookup terms, `LOOKUP_TERMS` per lookup.
    Lookups,
}

impl Family {
    /// The families in frozen order.
    pub(crate) const ORDER: [Self; 6] = [
        Self::Gates,
        Self::PermutationL0,
        Self::PermutationLLast,
        Self::Continuity,
        Self::Rules,
        Self::Lookups,
    ];

    /// Slots the family occupies per Action.
    pub(crate) const fn multiplicity(self) -> usize {
        match self {
            Self::Gates => GATES,
            Self::PermutationL0 | Self::PermutationLLast => 1,
            Self::Continuity => PERMUTATION_SET_COUNT - 1,
            Self::Rules => PERMUTATION_SET_COUNT,
            Self::Lookups => LOOKUP_TERMS * LOOKUP_COUNT,
        }
    }

    /// The family's first slot: the sum of the preceding multiplicities.
    pub(crate) const fn start(self) -> usize {
        let mut slot = 0;
        let mut index = 0;
        while index < Self::ORDER.len() {
            if Self::ORDER[index] as usize == self as usize {
                return slot;
            }
            slot += Self::ORDER[index].multiplicity();
            index += 1;
        }
        slot
    }
}

/// Gate constraint slots per Action.
pub(crate) const GATES: usize = GATE_CONSTRAINT_COUNT;

/// Permutation sets per Action (one rule each; continuity for all but the
/// first).
pub(crate) const PERMUTATION_SET_COUNT: usize = PERMUTATION_SETS;

/// Lookups per Action (five terms each).
pub(crate) const LOOKUP_COUNT: usize = LOOKUPS.len();

/// Terms per lookup, in order: `l_0`, `l_last`, rule, permuted `l_0`,
/// permuted continuity.
pub(crate) const LOOKUP_TERMS: usize = 5;

/// Lookup term offsets.
pub(crate) const LOOKUP_L_0: usize = 0;

pub(crate) const LOOKUP_L_LAST: usize = 1;

pub(crate) const LOOKUP_RULE: usize = 2;

pub(crate) const LOOKUP_PERMUTED_L_0: usize = 3;

pub(crate) const LOOKUP_PERMUTED_CONTINUITY: usize = 4;

/// The degree class of each lookup term, by offset: the `l_0` boundaries
/// fold on the N class, the `l_last` boundaries and the permuted
/// continuity on the 2N class, and the product rule on the fused pass.
pub(crate) const LOOKUP_FAMILY_CLASSES: [DegreeClass; LOOKUP_TERMS] = [
    DegreeClass::ClassN,
    DegreeClass::Class2N,
    DegreeClass::Extended,
    DegreeClass::ClassN,
    DegreeClass::Class2N,
];

/// Slots per Action: every family's multiplicity.
pub(crate) const TERMS_PER_ACTION: usize = Family::Lookups.start() + Family::Lookups.multiplicity();

/// The permutation argument's `l_0` slot.
pub(crate) const fn permutation_l_0() -> usize {
    Family::PermutationL0.start()
}

/// The permutation argument's `l_last` slot.
pub(crate) const fn permutation_l_last() -> usize {
    Family::PermutationLLast.start()
}

/// Continuity slot of permutation set `set` (`1..PERMUTATION_SET_COUNT`).
pub(crate) const fn continuity(set: usize) -> usize {
    Family::Continuity.start() + set - 1
}

/// Rule slot of permutation set `set`.
pub(crate) const fn rule(set: usize) -> usize {
    Family::Rules.start() + set
}

/// Slot of lookup `index`'s term `term` (one of the `LOOKUP_*` offsets).
pub(crate) const fn lookup(index: usize, term: usize) -> usize {
    Family::Lookups.start() + LOOKUP_TERMS * index + term
}

/// The continuity slots of sets `1..PERMUTATION_SET_COUNT`, set-ascending.
pub(crate) const fn continuity_slots() -> [usize; PERMUTATION_SET_COUNT - 1] {
    let mut slots = [0; PERMUTATION_SET_COUNT - 1];
    let mut set = 1;
    while set < PERMUTATION_SET_COUNT {
        slots[set - 1] = continuity(set);
        set += 1;
    }
    slots
}

/// The slot of term `term` for every lookup, lookup-ascending.
pub(crate) const fn lookup_slots(term: usize) -> [usize; LOOKUP_COUNT] {
    let mut slots = [0; LOOKUP_COUNT];
    let mut index = 0;
    while index < LOOKUP_COUNT {
        slots[index] = lookup(index, term);
        index += 1;
    }
    slots
}

/// The degree class of per-Action slot `slot`: gate programs by the
/// carved class lists, the boundaries and continuity terms on the N and
/// 2N classes, every set rule on the fused pass except the singleton
/// (last) set's degree-3 rule on the 2N class, and the lookup terms by
/// [`LOOKUP_FAMILY_CLASSES`].
pub(crate) const fn slot_class(slot: usize) -> DegreeClass {
    if slot < GATES {
        if contains(&GATE_PROGRAMS_2N, slot) {
            return DegreeClass::Class2N;
        }
        if contains(&GATE_PROGRAMS_4N, slot) {
            return DegreeClass::Class4N;
        }
        return DegreeClass::Extended;
    }
    if slot == permutation_l_0() {
        return DegreeClass::ClassN;
    }
    if slot == permutation_l_last() {
        return DegreeClass::Class2N;
    }
    if slot < Family::Rules.start() {
        return DegreeClass::ClassN;
    }
    if slot < Family::Lookups.start() {
        return if slot == rule(PERMUTATION_SET_COUNT - 1) {
            DegreeClass::Class2N
        } else {
            DegreeClass::Extended
        };
    }
    LOOKUP_FAMILY_CLASSES[(slot - Family::Lookups.start()) % LOOKUP_TERMS]
}

/// Extended rows per row of a class (`log2(8N / class size)`), the order
/// used to take the union of consumer classes.
const fn class_stride_log(class: DegreeClass) -> u32 {
    match class {
        DegreeClass::Extended => 0,
        DegreeClass::Class4N => 1,
        DegreeClass::Class2N => 2,
        DegreeClass::ClassN => 3,
    }
}

/// The larger (denser) of two classes.
const fn class_union(left: DegreeClass, right: DegreeClass) -> DegreeClass {
    if class_stride_log(left) <= class_stride_log(right) {
        left
    } else {
        right
    }
}

/// The largest degree class on which permutation set `set`'s grand product
/// is read anywhere in the fold — the union of its consumers' slot classes:
/// its own product rule, the `l_0` boundary (set 0), the `l_last` boundary
/// (the last set), and the continuity terms that read it directly (set ≥ 1)
/// or rotated (set + 1). The openings read only coefficients. A product's
/// coset need be produced only on this class: the full-width sets fold on
/// the fused 8N pass, and the singleton (last) set — whose degree-3 rule
/// folds on the 2N class — on the 2N class coset (the extended coset's
/// stride-4 rows), which every consumer reads at rows `≡ 0 (mod 4)` and
/// their `±8` rotations.
pub(crate) const fn permutation_product_class(set: usize) -> DegreeClass {
    let mut class = slot_class(rule(set));
    if set == 0 {
        class = class_union(class, slot_class(permutation_l_0()));
    }
    if set + 1 == PERMUTATION_SET_COUNT {
        class = class_union(class, slot_class(permutation_l_last()));
    }
    if set >= 1 {
        class = class_union(class, slot_class(continuity(set)));
    }
    if set + 1 < PERMUTATION_SET_COUNT {
        class = class_union(class, slot_class(continuity(set + 1)));
    }
    class
}

const _: () = {
    // The consumer census the product stage's form domains rely on: every
    // full-width set is read on the fused pass, and only the singleton set is
    // confined to the 2N class (its every consumer is a 2N or N term).
    let mut set = 0;
    while set + 1 < PERMUTATION_SET_COUNT {
        assert!(matches!(
            permutation_product_class(set),
            DegreeClass::Extended
        ));
        set += 1;
    }
    assert!(matches!(
        permutation_product_class(PERMUTATION_SET_COUNT - 1),
        DegreeClass::Class2N
    ));
    assert!(matches!(
        class_union(DegreeClass::ClassN, DegreeClass::Class2N),
        DegreeClass::Class2N
    ));
    assert!(matches!(
        class_union(DegreeClass::Extended, DegreeClass::Class4N),
        DegreeClass::Extended
    ));
};

const fn contains(programs: &[usize], program: usize) -> bool {
    let mut index = 0;
    while index < programs.len() {
        if programs[index] == program {
            return true;
        }
        index += 1;
    }
    false
}

const _: () = {
    // The frozen argument shape and the values the implementation has
    // always used.
    assert!(PERMUTATION_SET_COUNT == 3 && LOOKUP_COUNT == 3);
    assert!(TERMS_PER_ACTION == 215);
    assert!(permutation_l_0() == 193 && permutation_l_last() == 194);
    assert!(continuity(1) == 195 && continuity(2) == 196);
    assert!(rule(0) == 197 && rule(2) == 199);
    assert!(lookup(0, LOOKUP_L_0) == 200 && lookup(2, LOOKUP_PERMUTED_CONTINUITY) == 214);
    assert!(lookup(LOOKUP_COUNT - 1, LOOKUP_PERMUTED_CONTINUITY) + 1 == TERMS_PER_ACTION);
    // The classes the class-split kernels implement.
    assert!(matches!(slot_class(permutation_l_0()), DegreeClass::ClassN));
    assert!(matches!(
        slot_class(permutation_l_last()),
        DegreeClass::Class2N
    ));
    assert!(matches!(slot_class(continuity(1)), DegreeClass::ClassN));
    assert!(matches!(slot_class(rule(0)), DegreeClass::Extended));
    assert!(matches!(slot_class(rule(2)), DegreeClass::Class2N));
    assert!(matches!(
        slot_class(lookup(1, LOOKUP_RULE)),
        DegreeClass::Extended
    ));
    assert!(matches!(
        slot_class(lookup(1, LOOKUP_PERMUTED_L_0)),
        DegreeClass::ClassN
    ));
    assert!(matches!(
        slot_class(GATE_PROGRAMS_2N[0]),
        DegreeClass::Class2N
    ));
    assert!(matches!(
        slot_class(GATE_PROGRAMS_4N[0]),
        DegreeClass::Class4N
    ));
    assert!(matches!(slot_class(0), DegreeClass::Extended));
};
