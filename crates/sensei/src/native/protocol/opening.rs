//! The fixed multi-opening schedule, derived at compile time from the shared
//! circuit description.
//!
//! The multi-opening stage opens a fixed list of polynomials at a fixed list
//! of rotations of `x`, groups the polynomials by their point sets, and folds
//! each group with Horner weights in `x_1` before folding the groups in
//! `x_2`. Every part of that structure — which polynomials open at which
//! rotations, the first-appearance numbering of the points, the five point
//! sets and their order, and the order of the polynomials inside each set —
//! follows from the query tables and dimensions in `sensei-shared` alone. This
//! module derives it once, in `const` evaluation, from those tables; the
//! prover binds only the Action count, the polynomial buffers, and the
//! challenge values at proof time.
//!
//! The derivation replays the dynamic first-appearance grouping the prover
//! used to perform on every proof (kept as a `cfg(test)` oracle in
//! `prover::opening`): points are numbered in the order their rotations first
//! appear in the Action-major opening stream, polynomials keep their
//! first-appearance order, and point sets are numbered in the order the first
//! polynomial of each set appears. A polynomial's set is the same for every
//! Action, so the grouping of one Action followed by the fixed tail is the
//! grouping of any positive Action count: inside a set the members are Action
//! 0's, then Action 1's, …, then the fixed tail's, in the per-Action and fixed
//! orders recorded here. The prover's grouping compared points by field
//! equality, so the derived schedule stands for it exactly when the rotated
//! points are pairwise distinct (`x ≠ 0`); the stage checks that condition.

use sensei_shared::queries::{ADVICE_QUERIES, FIXED_QUERIES, INSTANCE_QUERIES};
use sensei_shared::{ADVICE_COLUMNS, BLINDING_FACTORS, PERMUTATION_COLUMN_COUNT, PERMUTATION_SETS};

use super::POINT_SETS;
use crate::native::expression_layout::LOOKUPS;

/// A polynomial opened once per Action; the Action index binds at proof time.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::native) enum ActionPolynomial {
    /// The Action's instance polynomial (column 0).
    Instance,
    /// The Action's advice column.
    Advice(u8),
    /// The Action's permutation grand product for one column set.
    Permutation(u8),
    /// The Action's lookup grand product.
    LookupProduct(u8),
    /// The Action's permuted lookup input.
    LookupInput(u8),
    /// The Action's permuted lookup table.
    LookupTable(u8),
}

/// A polynomial opened once per proof, after every Action's openings.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::native) enum FixedPolynomial {
    /// An embedded fixed column.
    Fixed(u8),
    /// An embedded permutation sigma column.
    Sigma(u8),
    /// The `x^N`-folded quotient pieces.
    Quotient,
    /// The linear vanishing mask.
    Vanishing,
}

/// The rotation of `x` the last-row permutation openings use.
const X_LAST_ROTATION: i32 = -(BLINDING_FACTORS as i32 + 1);

/// Openings in the per-Action stream: the instance and advice queries, each
/// permutation set at `x` and `x·ω` plus `x_last` for every set but the last,
/// and each lookup's five openings.
const ACTION_OPENINGS: usize =
    INSTANCE_QUERIES.len() + ADVICE_QUERIES.len() + (3 * PERMUTATION_SETS - 1) + 5 * LOOKUPS.len();
/// Openings in the fixed tail: the fixed queries, the sigma columns, the
/// quotient, and the vanishing mask.
const FIXED_OPENINGS: usize = FIXED_QUERIES.len() + PERMUTATION_COLUMN_COUNT + 2;
/// Upper bound on distinct rotations; the derived count is
/// [`OPENING_POINTS`].
const MAX_POINTS: usize = u8::BITS as usize;

#[derive(Clone, Copy)]
struct ActionOpening {
    polynomial: ActionPolynomial,
    rotation: i32,
}

#[derive(Clone, Copy)]
struct FixedOpening {
    polynomial: FixedPolynomial,
    rotation: i32,
}

const fn action_polynomial_eq(left: ActionPolynomial, right: ActionPolynomial) -> bool {
    match (left, right) {
        (ActionPolynomial::Instance, ActionPolynomial::Instance) => true,
        (ActionPolynomial::Advice(left), ActionPolynomial::Advice(right))
        | (ActionPolynomial::Permutation(left), ActionPolynomial::Permutation(right))
        | (ActionPolynomial::LookupProduct(left), ActionPolynomial::LookupProduct(right))
        | (ActionPolynomial::LookupInput(left), ActionPolynomial::LookupInput(right))
        | (ActionPolynomial::LookupTable(left), ActionPolynomial::LookupTable(right)) => {
            left == right
        }
        _ => false,
    }
}

const fn fixed_polynomial_eq(left: FixedPolynomial, right: FixedPolynomial) -> bool {
    match (left, right) {
        (FixedPolynomial::Quotient, FixedPolynomial::Quotient)
        | (FixedPolynomial::Vanishing, FixedPolynomial::Vanishing) => true,
        (FixedPolynomial::Fixed(left), FixedPolynomial::Fixed(right))
        | (FixedPolynomial::Sigma(left), FixedPolynomial::Sigma(right)) => left == right,
        _ => false,
    }
}

const fn small_index(index: usize) -> u8 {
    assert!(
        index < u8::MAX as usize,
        "schedule index exceeds the u8 table width"
    );
    index as u8
}

/// The per-Action opening stream in transcript order.
const fn action_openings() -> [ActionOpening; ACTION_OPENINGS] {
    let mut openings = [ActionOpening {
        polynomial: ActionPolynomial::Instance,
        rotation: 0,
    }; ACTION_OPENINGS];
    let mut count = 0;

    let mut index = 0;
    while index < INSTANCE_QUERIES.len() {
        assert!(
            INSTANCE_QUERIES[index].column == 0,
            "the instance queries read column 0 only"
        );
        openings[count] = ActionOpening {
            polynomial: ActionPolynomial::Instance,
            rotation: INSTANCE_QUERIES[index].rotation,
        };
        count += 1;
        index += 1;
    }
    index = 0;
    while index < ADVICE_QUERIES.len() {
        let query = ADVICE_QUERIES[index];
        assert!(
            query.column < ADVICE_COLUMNS,
            "advice query column out of range"
        );
        openings[count] = ActionOpening {
            polynomial: ActionPolynomial::Advice(small_index(query.column)),
            rotation: query.rotation,
        };
        count += 1;
        index += 1;
    }
    let mut set = 0;
    while set < PERMUTATION_SETS {
        let polynomial = ActionPolynomial::Permutation(small_index(set));
        openings[count] = ActionOpening {
            polynomial,
            rotation: 0,
        };
        openings[count + 1] = ActionOpening {
            polynomial,
            rotation: 1,
        };
        count += 2;
        set += 1;
    }
    // Every set but the last, descending.
    let mut set = PERMUTATION_SETS - 1;
    while set > 0 {
        set -= 1;
        openings[count] = ActionOpening {
            polynomial: ActionPolynomial::Permutation(small_index(set)),
            rotation: X_LAST_ROTATION,
        };
        count += 1;
    }
    let mut lookup = 0;
    while lookup < LOOKUPS.len() {
        let lookup_index = small_index(lookup);
        let lookup_openings = [
            (ActionPolynomial::LookupProduct(lookup_index), 0),
            (ActionPolynomial::LookupInput(lookup_index), 0),
            (ActionPolynomial::LookupTable(lookup_index), 0),
            (ActionPolynomial::LookupInput(lookup_index), -1),
            (ActionPolynomial::LookupProduct(lookup_index), 1),
        ];
        let mut opening = 0;
        while opening < lookup_openings.len() {
            openings[count] = ActionOpening {
                polynomial: lookup_openings[opening].0,
                rotation: lookup_openings[opening].1,
            };
            count += 1;
            opening += 1;
        }
        lookup += 1;
    }
    assert!(count == ACTION_OPENINGS);
    openings
}

/// The fixed tail of the opening stream in transcript order.
const fn fixed_openings() -> [FixedOpening; FIXED_OPENINGS] {
    let mut openings = [FixedOpening {
        polynomial: FixedPolynomial::Quotient,
        rotation: 0,
    }; FIXED_OPENINGS];
    let mut count = 0;

    let mut index = 0;
    while index < FIXED_QUERIES.len() {
        let query = FIXED_QUERIES[index];
        openings[count] = FixedOpening {
            polynomial: FixedPolynomial::Fixed(small_index(query.column)),
            rotation: query.rotation,
        };
        count += 1;
        index += 1;
    }
    let mut sigma = 0;
    while sigma < PERMUTATION_COLUMN_COUNT {
        openings[count] = FixedOpening {
            polynomial: FixedPolynomial::Sigma(small_index(sigma)),
            rotation: 0,
        };
        count += 1;
        sigma += 1;
    }
    openings[count] = FixedOpening {
        polynomial: FixedPolynomial::Quotient,
        rotation: 0,
    };
    openings[count + 1] = FixedOpening {
        polynomial: FixedPolynomial::Vanishing,
        rotation: 0,
    };
    count += 2;
    assert!(count == FIXED_OPENINGS);
    openings
}

const ACTION_OPENING_STREAM: [ActionOpening; ACTION_OPENINGS] = action_openings();
const FIXED_OPENING_STREAM: [FixedOpening; FIXED_OPENINGS] = fixed_openings();

struct PointTable {
    rotations: [i32; MAX_POINTS],
    count: usize,
}

impl PointTable {
    const fn id(&self, rotation: i32) -> usize {
        let mut id = 0;
        while id < self.count {
            if self.rotations[id] == rotation {
                return id;
            }
            id += 1;
        }
        panic!("rotation missing from the derived point table");
    }
}

/// Numbers the distinct rotations by first appearance in the stream.
const fn point_table() -> PointTable {
    let mut table = PointTable {
        rotations: [0; MAX_POINTS],
        count: 0,
    };
    let mut index = 0;
    while index < ACTION_OPENINGS + FIXED_OPENINGS {
        let rotation = if index < ACTION_OPENINGS {
            ACTION_OPENING_STREAM[index].rotation
        } else {
            FIXED_OPENING_STREAM[index - ACTION_OPENINGS].rotation
        };
        let mut known = false;
        let mut id = 0;
        while id < table.count {
            if table.rotations[id] == rotation {
                known = true;
            }
            id += 1;
        }
        if !known {
            assert!(
                table.count < MAX_POINTS,
                "too many distinct opening rotations"
            );
            table.rotations[table.count] = rotation;
            table.count += 1;
        }
        index += 1;
    }
    table
}

const POINT_TABLE: PointTable = point_table();

/// Distinct evaluation points of the schedule.
pub(in crate::native) const OPENING_POINTS: usize = POINT_TABLE.count;

/// The unrotated point `x`, shared by every opening group.
pub(in crate::native) const COMMON_OPENING_POINT: usize = POINT_TABLE.id(0);

/// The rotation of `x` behind each point id, in first-appearance order.
pub(in crate::native) const OPENING_ROTATIONS: [i32; OPENING_POINTS] = {
    let mut rotations = [0; OPENING_POINTS];
    let mut id = 0;
    while id < OPENING_POINTS {
        rotations[id] = POINT_TABLE.rotations[id];
        id += 1;
    }
    rotations
};

/// One committed polynomial with the set of point ids it opens at.
#[derive(Clone, Copy)]
struct Commitment<P: Copy> {
    polynomial: P,
    point_mask: u8,
}

struct Commitments {
    action: [Commitment<ActionPolynomial>; ACTION_OPENINGS],
    action_count: usize,
    fixed: [Commitment<FixedPolynomial>; FIXED_OPENINGS],
    fixed_count: usize,
}

/// Merges the stream's openings into commitments by first appearance,
/// rejecting a polynomial opened twice at one point.
const fn commitments() -> Commitments {
    let mut merged = Commitments {
        action: [Commitment {
            polynomial: ActionPolynomial::Instance,
            point_mask: 0,
        }; ACTION_OPENINGS],
        action_count: 0,
        fixed: [Commitment {
            polynomial: FixedPolynomial::Quotient,
            point_mask: 0,
        }; FIXED_OPENINGS],
        fixed_count: 0,
    };

    let mut index = 0;
    while index < ACTION_OPENINGS {
        let opening = ACTION_OPENING_STREAM[index];
        let bit = 1u8 << POINT_TABLE.id(opening.rotation);
        let mut slot = 0;
        while slot < merged.action_count {
            if action_polynomial_eq(merged.action[slot].polynomial, opening.polynomial) {
                break;
            }
            slot += 1;
        }
        if slot == merged.action_count {
            merged.action[slot].polynomial = opening.polynomial;
            merged.action_count += 1;
        }
        assert!(
            merged.action[slot].point_mask & bit == 0,
            "a polynomial is opened twice at one point"
        );
        merged.action[slot].point_mask |= bit;
        index += 1;
    }

    index = 0;
    while index < FIXED_OPENINGS {
        let opening = FIXED_OPENING_STREAM[index];
        let bit = 1u8 << POINT_TABLE.id(opening.rotation);
        let mut slot = 0;
        while slot < merged.fixed_count {
            if fixed_polynomial_eq(merged.fixed[slot].polynomial, opening.polynomial) {
                break;
            }
            slot += 1;
        }
        if slot == merged.fixed_count {
            merged.fixed[slot].polynomial = opening.polynomial;
            merged.fixed_count += 1;
        }
        assert!(
            merged.fixed[slot].point_mask & bit == 0,
            "a polynomial is opened twice at one point"
        );
        merged.fixed[slot].point_mask |= bit;
        index += 1;
    }
    merged
}

const COMMITMENTS: Commitments = commitments();

/// Polynomials committed per Action.
pub(in crate::native) const ACTION_COMMITMENTS: usize = COMMITMENTS.action_count;
/// Polynomials committed once per proof.
pub(in crate::native) const FIXED_COMMITMENTS: usize = COMMITMENTS.fixed_count;

/// One point set of the schedule with its members in fold order.
///
/// The members are the Action-major sequence: every Action's
/// [`per_action`](Self::per_action) polynomials in Action order, then the
/// [`fixed`](Self::fixed) tail. The last member carries Horner weight `1`.
pub(in crate::native) struct OpeningGroup {
    point_mask: u8,
    per_action: [ActionPolynomial; ACTION_COMMITMENTS],
    per_action_len: usize,
    fixed: [FixedPolynomial; FIXED_COMMITMENTS],
    fixed_len: usize,
}

impl OpeningGroup {
    const EMPTY: Self = Self {
        point_mask: 0,
        per_action: [ActionPolynomial::Instance; ACTION_COMMITMENTS],
        per_action_len: 0,
        fixed: [FixedPolynomial::Quotient; FIXED_COMMITMENTS],
        fixed_len: 0,
    };

    /// The group's polynomials opened by every Action, in fold order.
    pub(in crate::native) fn per_action(&self) -> &[ActionPolynomial] {
        &self.per_action[..self.per_action_len]
    }

    /// The group's once-per-proof polynomials, in fold order.
    pub(in crate::native) fn fixed(&self) -> &[FixedPolynomial] {
        &self.fixed[..self.fixed_len]
    }

    /// The group's point ids (indices into [`OPENING_ROTATIONS`]), ascending.
    pub(in crate::native) fn point_ids(&self) -> impl Iterator<Item = usize> + '_ {
        (0..OPENING_POINTS).filter(move |id| self.point_mask & (1u8 << id) != 0)
    }

    /// Members folded for `action_count` Actions.
    #[cfg(feature = "prover")]
    pub(in crate::native) const fn len(&self, action_count: usize) -> usize {
        self.fixed_len + action_count * self.per_action_len
    }

    /// Whether the folded quotient is one of the group's members.
    pub(in crate::native) const fn contains_quotient(&self) -> bool {
        let mut index = 0;
        while index < self.fixed_len {
            if matches!(self.fixed[index], FixedPolynomial::Quotient) {
                return true;
            }
            index += 1;
        }
        false
    }
}

/// Groups the commitments by point set in first-appearance order.
const fn opening_groups() -> [OpeningGroup; POINT_SETS] {
    let mut groups = [OpeningGroup::EMPTY; POINT_SETS];
    let mut group_count = 0;

    let mut index = 0;
    while index < ACTION_COMMITMENTS {
        let commitment = COMMITMENTS.action[index];
        let mut group = 0;
        while group < group_count {
            if groups[group].point_mask == commitment.point_mask {
                break;
            }
            group += 1;
        }
        if group == group_count {
            assert!(
                group_count < POINT_SETS,
                "more point sets than the inventory records"
            );
            groups[group].point_mask = commitment.point_mask;
            group_count += 1;
        }
        let slot = groups[group].per_action_len;
        groups[group].per_action[slot] = commitment.polynomial;
        groups[group].per_action_len += 1;
        index += 1;
    }

    index = 0;
    while index < FIXED_COMMITMENTS {
        let commitment = COMMITMENTS.fixed[index];
        let mut group = 0;
        while group < group_count {
            if groups[group].point_mask == commitment.point_mask {
                break;
            }
            group += 1;
        }
        if group == group_count {
            assert!(
                group_count < POINT_SETS,
                "more point sets than the inventory records"
            );
            groups[group].point_mask = commitment.point_mask;
            group_count += 1;
        }
        let slot = groups[group].fixed_len;
        groups[group].fixed[slot] = commitment.polynomial;
        groups[group].fixed_len += 1;
        index += 1;
    }
    assert!(
        group_count == POINT_SETS,
        "fewer point sets than the inventory records"
    );
    groups
}

const DERIVED_GROUPS: [OpeningGroup; POINT_SETS] = opening_groups();

/// The schedule's point sets in first-appearance order, each with its members
/// in fold order.
pub(in crate::native) static OPENING_GROUPS: [OpeningGroup; POINT_SETS] = DERIVED_GROUPS;

const _: () = {
    assert!(OPENING_POINTS == 4);
    assert!(OPENING_ROTATIONS[0] == 0);
    assert!(OPENING_ROTATIONS[1] == 1);
    assert!(OPENING_ROTATIONS[2] == -1);
    assert!(OPENING_ROTATIONS[3] == X_LAST_ROTATION);
    assert!(ACTION_COMMITMENTS == 23 && FIXED_COMMITMENTS == 46);
    // Every commitment lands in exactly one group.
    let mut per_action_total = 0;
    let mut fixed_total = 0;
    let mut group = 0;
    while group < POINT_SETS {
        // Quotient construction divides by this common factor after folding.
        assert!(DERIVED_GROUPS[group].point_mask & (1u8 << COMMON_OPENING_POINT) != 0);
        per_action_total += DERIVED_GROUPS[group].per_action_len;
        fixed_total += DERIVED_GROUPS[group].fixed_len;
        group += 1;
    }
    assert!(per_action_total == ACTION_COMMITMENTS && fixed_total == FIXED_COMMITMENTS);
    // The quotient's group is the one opened at `x` alone.
    assert!(DERIVED_GROUPS[0].point_mask == 1 && DERIVED_GROUPS[0].contains_quotient());
};
