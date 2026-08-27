# Derives the fixed seven-addition Eisenstein chain used by the
# effective-affine (omitted global-Z) table builder in `src/glv.rs`
# (`EFFECTIVE_CHAIN_UNITS` / `EFFECTIVE_CHAIN_RELATIONS`), and prints the
# constants in the exact shape of the Rust source so the two can be
# diffed.
#
# Run from this directory:
#
#     uv run sage effective_affine_chain.sage
#
# The chain builds the eight `Table` orbit representatives from one
# doubled point: starting at q0 = P, each step adds D = 2P with an
# incomplete affine formula and then applies an Eisenstein unit,
#
#     q_{i+1} = u_i * (q_i + 2),        u_i in U = {±1, ±ω, ±ω²},
#
# so every stored q_i lands in a distinct unit orbit U·Δ_j of the eight
# canonical representatives. The mixed additions never invert; the seven
# successive Z-ratios they emit let one backward pass bring all eight
# entries to a single omitted Jacobian denominator.
#
# This script re-derives the chain by exhaustive search over the 6^7
# unit sequences, proves the pinned chain minimal under the
# nontrivial-rotation cost model (each ±ω^e unit with e != 0 costs one
# x-coordinate multiplication in the builder), asserts every path
# relation exactly over Z[ω], and checks the group-level
# nonexceptionality of every chain addition for both Pasta curves.
# Everything is exact integer arithmetic on Eisenstein coefficient
# pairs, so the output does not depend on the SageMath version.

# The Pasta base/scalar field moduli. Fp is the Pallas base field and the
# Vesta scalar field; Fq is the Pallas scalar field and the Vesta base field.
p = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
q = 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001


# --- Z[ω] on coefficient pairs -----------------------------------------------
#
# An Eisenstein integer a + bω (ω² + ω + 1 = 0) is the pair (a, b).

def emul(x, y):
    # (a + bω)(c + dω) = (ac - bd) + (ad + bc - bd)ω.
    (a, b), (c, d) = x, y
    return (a * c - b * d, a * d + b * c - b * d)


def eadd(x, y):
    return (x[0] + y[0], x[1] + y[1])


def eneg(x):
    return (-x[0], -x[1])


def enorm(x):
    # N(a + bω) = a² - ab + b², multiplicative and zero only at zero.
    a, b = x
    return a * a - a * b + b * b


# The six units in the crate's digit code order [+1, -1, +ω, -ω, +ω², -ω²]
# (see `JOINT_DIGITS` in `src/glv.rs`: `unit >> 1` is the rotation
# exponent, `unit & 1` the negation).
UNITS = [(1, 0), (-1, 0), (0, 1), (0, -1), (-1, -1), (1, 1)]
UNIT_NAMES = ["+1", "-1", "+ω", "-ω", "+ω²", "-ω²"]
for code, u in enumerate(UNITS):
    rotation, negate = code >> 1, code & 1
    expected = (1, 0)
    for _ in range(rotation):
        expected = emul(expected, (0, 1))
    if negate:
        expected = eneg(expected)
    assert u == expected, "unit code order must match JOINT_DIGITS"

# The eight orbit representatives Δ from `DELTA` in `src/glv.rs`
# (norms 1, 3, 7, 7, 9, 13, 13, 19).
DELTA = [(1, 0), (1, -1), (2, -1), (1, -2), (3, 0), (3, -1), (1, -3), (2, -3)]
assert [enorm(d) for d in DELTA] == [1, 3, 7, 7, 9, 13, 13, 19]

# Every unit multiple of every representative, keyed by value:
# relation (slot, rotation, negate) means value = ±ω^rotation · Δ_slot.
# The 48 products are distinct (they tile the odd classes mod 2Z[ω],
# re-derived by `joint_digit_table_matches_first_principles` in Rust).
orbit_relation = {}
for slot, delta in enumerate(DELTA):
    for code, unit in enumerate(UNITS):
        value = emul(unit, delta)
        assert value not in orbit_relation, "unit orbits must be disjoint"
        orbit_relation[value] = (slot, code >> 1, code & 1 == 1)

TWO = (2, 0)


# --- Exhaustive chain search -------------------------------------------------
#
# A chain is valid when every stored point (q0 = P included) lies in a
# target unit orbit, all eight orbits are visited exactly once, and no
# pre-addition state is ±2 — the incomplete mixed addition q + D is
# exceptional exactly when x(q·P) = x(2P), i.e. q = ±2 (checked at the
# group level below).

import itertools


def walk(units):
    q = (1, 0)
    stored = [q]
    for code in units:
        if q == TWO or q == eneg(TWO):
            return None  # exceptional mixed addition
        q = emul(UNITS[code], eadd(q, TWO))
        stored.append(q)
    return stored


valid = []
for units in itertools.product(range(6), repeat=7):
    stored = walk(units)
    if stored is None:
        continue
    relations = [orbit_relation.get(value) for value in stored]
    if None in relations:
        continue
    if sorted(relation[0] for relation in relations) != list(range(8)):
        continue
    rotations = sum(1 for code in units if code >> 1 != 0)
    valid.append((units, stored, relations, rotations))

assert len(valid) == 54, "expected 54 valid seven-step chains"
minimum = min(chain[3] for chain in valid)
assert minimum == 4, "expected a four-rotation minimum"
minimal = sorted(chain for chain in valid if chain[3] == minimum)
assert len(minimal) == 4, "expected 4 chains at the minimum"

# Selection rule: the lexicographically least unit-code sequence (in the
# crate's unit code order) among the minimal-rotation chains.
units, stored, relations, _ = minimal[0]

EXPECTED_UNITS = (2, 0, 5, 2, 4, 0, 0)  # [+ω, +1, -ω², +ω, +ω², +1, +1]
EXPECTED_RELATIONS = [
    (0, 0, False),
    (4, 1, False),
    (3, 1, False),
    (5, 1, False),
    (6, 2, False),
    (1, 1, False),
    (2, 2, True),
    (7, 2, True),
]
assert units == EXPECTED_UNITS, "selected chain must match the pinned one"
assert relations == EXPECTED_RELATIONS


# --- Exact relation and nonexceptionality checks -----------------------------

for value, (slot, rotation, negate) in zip(stored, relations):
    canonical = DELTA[slot]
    for _ in range(rotation):
        canonical = emul(canonical, (0, 1))
    if negate:
        canonical = eneg(canonical)
    assert value == canonical, "path relation must be exact over Z[ω]"

# Group-level nonexceptionality for both Pasta curves: with λ a root of
# x² + x + 1 in the scalar field, the multiplier a + bω acts as
# a + bλ (mod n). A chain addition q + 2 is exceptional only if
# x([q]P) = x([2]P), i.e. (q ∓ 2) · P = O, i.e. a + bλ ≡ ±2 (mod n) —
# impossible here because N(q ∓ 2) = (a + bλ)(a + bλ̄) mod n is a small
# nonzero integer. The same argument keeps every pre-addition state
# nonidentity (q itself has small nonzero norm).
for curve, n in [("Pallas", q), ("Vesta", p)]:
    Fn = GF(n)
    lambdas = sorted(
        root for root, _ in (polygen(Fn) ^ 2 + polygen(Fn) + 1).roots()
    )
    assert len(lambdas) == 2, "n = 1 (mod 3) gives two cube roots"
    for lam in lambdas:
        image = lambda value: Fn(value[0]) + Fn(value[1]) * lam
        # ω ↔ λ is a ring homomorphism Z[ω] -> F_n; spot-check it.
        assert image(emul((2, -3), (1, 4))) == image((2, -3)) * image((1, 4))
        for value in stored[:-1]:  # pre-addition states
            for offset in [TWO, eneg(TWO), (0, 0)]:
                difference = eadd(value, eneg(offset))
                norm = enorm(difference)
                assert 0 < norm < n, "|q ∓ 2| and |q| have small nonzero norm"
                assert image(difference) != 0, f"{curve}: exceptional chain state"
        # The stored relations under λ: value ≡ ±λ^rotation · Δ_slot (mod n).
        for value, (slot, rotation, negate) in zip(stored, relations):
            expected = image(DELTA[slot]) * lam ^ rotation
            if negate:
                expected = -expected
            assert image(value) == expected, f"{curve}: relation image mismatch"


# --- Rust-diffable output ----------------------------------------------------

print("// Chain: q0 = P; q_{i+1} = u_i * (q_i + 2P). Units in digit code")
print("// order [+1, -1, +ω, -ω, +ω², -ω²]; four have nontrivial rotation")
print("// (the exhaustive-search minimum; this is the lexicographically")
print("// least of the four minimal chains).")
print("const EFFECTIVE_CHAIN_UNITS: [u8; 7] = [%s];" % ", ".join(map(str, units)))
print("")
print("// path i = ±ω^rotation · Δ_slot as (slot, rotation, negate):")
for value, (slot, rotation, negate) in zip(stored, relations):
    sign = "-" if negate else "+"
    print(
        "//   q%d = %+d %+dω = %sω^%d · Δ%d (norm %d)"
        % (stored.index(value), value[0], value[1], sign, rotation, slot, enorm(value))
    )
print("const EFFECTIVE_CHAIN_RELATIONS: [(u8, u8, bool); 8] = [")
for slot, rotation, negate in relations:
    print("    (%d, %d, %s)," % (slot, rotation, "true" if negate else "false"))
print("];")
