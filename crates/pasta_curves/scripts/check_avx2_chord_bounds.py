#!/usr/bin/env python3
"""Independent exact-integer audit of PR 701's AVX2 arithmetic.

This checks the generated Rust columns structurally, proves conservative
interval bounds with exact rationals, and exercises a single-lane execution
model against Python's arbitrary-precision modular arithmetic. It does not
constitute a machine-checked proof of the Rust implementation or compiler.

Usage: python3 scripts/check_avx2_chord_bounds.py [repository-root]
"""

import ast
from fractions import Fraction as F
from pathlib import Path
import random
import re
import sys

ROOT = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parents[3]
RADIX = 1 << 29
MASK = RADIX - 1
WORD = (1 << 64) - 1
R = 1 << 261
MODULI = {
    "Fp": 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001,
    "Fq": 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001,
}
src = (ROOT / "crates/pasta_curves/src/arithmetic/avx2_sqrt.rs").read_text()
assert "const L: usize = 9;" in src
assert "const BITS: i32 = 29;" in src
for name, modulus in MODULI.items():
    field_src = (ROOT / f"crates/pasta_curves/src/fields/{name.lower()}.rs").read_text()
    raw = re.search(rf"const MODULUS: {name} = {name}\(\[(.*?)\]\);", field_src, re.S)
    words = [int(word.strip().replace("_", ""), 0) for word in raw[1].split(",") if word.strip()]
    assert sum(word << (64 * i) for i, word in enumerate(words)) == modulus
body = src.split("pub(super) fn mul<", 1)[1].split("/// Lane-wise Montgomery square.", 1)[0]
body = body.split("let mut carry = zero;", 1)[1]
statements = re.findall(
    r"(let col|q\[\d+\]|carry|out\[\d+\]) = (.*?);", body, re.S
)


def expr(s):
    s = re.sub(r"::<(BITS|22)>", lambda m: "29" if m[1] == "BITS" else "22", s)
    return ast.parse(s.strip(), mode="eval").body


statements = [(lhs, expr(rhs)) for lhs, rhs in statements]
assert len(statements) == 17 * 3 + 1
for column in range(17):
    group = statements[3 * column:3 * column + 3]
    assert group[0][0] == "let col"
    if column < 9:
        expected = [(f"q[{column}]", f"_mm256_and_si256(_mm256_sub_epi64(zero, col), mask)"),
                    ("carry", f"_mm256_srli_epi64::<BITS>(_mm256_add_epi64(col, q[{column}]))")]
    else:
        expected = [(f"out[{column - 9}]", "_mm256_and_si256(col, mask)"),
                    ("carry", "_mm256_srli_epi64::<BITS>(col)")]
    for (actual_lhs, actual_rhs), (lhs, rhs) in zip(group[1:], expected):
        assert actual_lhs == lhs and ast.dump(actual_rhs) == ast.dump(expr(rhs))
assert statements[-1][0] == "out[8]" and ast.dump(statements[-1][1]) == ast.dump(expr("carry"))


def evaluate(node, env, ops):
    if isinstance(node, ast.Name):
        return env[node.id]
    if isinstance(node, ast.Constant):
        return node.value
    if isinstance(node, ast.Subscript):
        return env[node.value.id][node.slice.value]
    if isinstance(node, ast.Call):
        return ops[node.func.id](*(evaluate(a, env, ops) for a in node.args))
    raise AssertionError(ast.dump(node))


def add(a, b):
    assert 0 <= a + b <= WORD, ("64-bit addition", a, b)
    return a + b


def mul(a, b):
    assert 0 <= a < 1 << 32 and 0 <= b < 1 << 32
    return a * b


OPS = {
    "_mm256_add_epi64": add,
    "_mm256_mul_epu32": mul,
    # Negation of a column is intentionally modulo 2^64 before masking.
    "_mm256_sub_epi64": lambda a, b: (a - b) & WORD,
    "_mm256_and_si256": lambda a, b: a & b,
    "_mm256_slli_epi6422": lambda a: a << 22,
    "_mm256_srli_epi6429": lambda a: a >> 29,
}


def limbs(x):
    return [(x >> (29 * i)) & MASK for i in range(9)]


def integer(x):
    return sum(v << (29 * i) for i, v in enumerate(x))


def environment(p, a, b):
    pl = limbs(p)
    return dict(a=a, b=b, q=[0] * 9, out=[0] * 9, carry=0, zero=0,
                mask=MASK, **{f"p{i}": pl[i] for i in range(1, 5)})


def run_mul(p, a, b):
    env = environment(p, limbs(a), limbs(b))
    for lhs, rhs in statements:
        val = evaluate(rhs, env, OPS)
        if lhs == "let col":
            env["col"] = val
        elif lhs == "carry":
            env["carry"] = val
        else:
            name, index = lhs[0:lhs.index("[")], int(lhs[lhs.index("[") + 1:-1])
            env[name][index] = val
    out, q = integer(env["out"]), integer(env["q"])
    assert out * R == a * b + q * p
    assert out < F(a * b, R) + p
    assert out % p == (a * b * pow(R, -1, p)) % p
    assert all(x <= MASK for x in env["out"][:8])
    return out


# Polynomial normal forms of the actual Rust columns, independently compared
# with the full schoolbook A*B + Q*p convolution.
def polyadd(a, b):
    result = a.copy()
    for k, v in b.items():
        result[k] = result.get(k, 0) + v
    return {k: v for k, v in result.items() if v}


def polymul(a, b):
    result = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            k = tuple(sorted(ka + kb))
            result[k] = result.get(k, 0) + va * vb
    return result


def variable(name):
    return {(name,): 1}


def check_columns(p):
    pl = limbs(p)
    assert pl[0] == 1 and pl[5:8] == [0, 0, 0] and pl[8] == 1 << 22
    env = {name: [variable(f"{name}{i}") for i in range(9)] for name in ["a", "b", "q"]}
    env.update(carry=variable("carry"), **{f"p{i}": {(): pl[i]} for i in range(1, 5)})
    ops = {"_mm256_add_epi64": polyadd, "_mm256_mul_epu32": polymul,
           "_mm256_slli_epi6422": lambda a: polymul(a, {(): 1 << 22})}
    columns = [rhs for lhs, rhs in statements if lhs == "let col"]
    for k, rhs in enumerate(columns):
        expected = variable("carry")
        for i in range(9):
            j = k - i
            if 0 <= j < 9:
                expected = polyadd(expected, polymul(env["a"][i], env["b"][j]))
        for i in range(min(k, 9)):
            j = k - i
            if 0 <= j < 9 and pl[j]:
                expected = polyadd(expected, polymul(env["q"][i], {(): pl[j]}))
        assert evaluate(rhs, env, ops) == expected, ("column", k)

    # A bounding box for *all* normalized operands below 2^261. For q, the
    # bit mask proves 0 <= q_i <= MASK independently of preceding columns.
    env = environment(p, [MASK] * 9, [MASK] * 9)
    peak = 0
    def bound_add(a, b):
        nonlocal peak
        result = add(a, b)
        peak = max(peak, result)
        return result
    bound_ops = dict(OPS, _mm256_add_epi64=bound_add)
    for lhs, rhs in statements:
        if lhs.startswith("q["):
            env["q"][int(lhs[2:-1])] = MASK
            continue
        val = evaluate(rhs, env, bound_ops)
        peak = max(peak, val)
        if lhs == "let col":
            env["col"] = val
        elif lhs == "carry":
            env["carry"] = val
    assert peak < 1 << 64
    return peak


def normalize(v):
    v = v.copy()
    for i in range(8):
        assert 0 <= v[i] <= WORD
        v[i + 1] += v[i] >> 29
        v[i] &= MASK
    assert -(1 << 63) < v[8] < (1 << 63)
    return v


def kp(pl, c):
    return [c * x + ((1 << 30) if i < 8 else 0) - (2 if i else 0)
            for i, x in enumerate(pl)]


def canonical(p, x):
    assert 0 <= x < 8 * p
    v, pl = limbs(x), limbs(p)
    q = v[8] >> 22
    t = [v[i] + ((1 << 32) if i == 0 else -8 if i == 8 else (1 << 32) - 8)
         - q * pl[i] for i in range(9)]
    assert all(x >= 0 for x in t[:8])
    t = normalize(t)
    if t[8] < 0:
        t = [a + b for a, b in zip(t, pl)]
    t = normalize(t)
    assert integer(t) == x % p
    return integer(t)


def reduce_wide(p, x):
    assert 0 <= x < 1 << 260
    # Model the source's word-wise arithmetic and final sign/correction.
    words = [(x >> (64 * i)) & WORD for i in range(5)]
    pw = [(p >> (64 * i)) & WORD for i in range(4)]
    q = (words[4] << 2) | (words[3] >> 62)
    qpw, carry = [], 0
    for word in pw:
        t = q * word + carry
        assert 0 <= t < 1 << 128
        qpw.append(t & WORD)
        carry = t >> 64
    qpw.append(carry)
    out, borrow = [], 0
    for a, b in zip(words, qpw):
        t = a - b + borrow
        assert -(1 << 127) <= t < 1 << 127
        out.append(t & WORD)
        borrow = t >> 64
    result = sum(w << (64 * i) for i, w in enumerate(out[:4]))
    if t < 0:
        result = (result + p) % (1 << 256)
    assert result == x % p
    return result


def prove_bounds(p):
    d, h, H = p - (1 << 254), F(p, R), F(401, 100)
    assert 0 < d < 1 << 126
    assert 96 * p < R
    assert 96 * h < 1
    assert 96 * H * h + 1 < H
    fixed = 1 / (1 - 96 * h)
    assert 4 < fixed < 4 + F(1, 1 << 120)
    slope = H * H * h + 1
    assert slope < F(1126, 1000)
    x3 = 32 * slope * slope * h + 4
    y3 = 32 * slope * 6 * h + 3
    assert x3 < F(432, 100) and y3 < F(469, 100)
    assert 32 * slope < 96
    assert x3 < 5 and y3 < 8
    assert H * p < 1 << 260
    # For normalized subtrahends, bounding the integer also bounds limb 8.
    pl = limbs(p)
    for c, subtrahend_bound in [(2, F(1)), (3, F(2)), (5, x3)]:
        k = kp(pl, c)
        max_top = (subtrahend_bound * p).__ceil__() - 1
        max_top >>= 232
        assert all(ki >= MASK for ki in k[:8])
        assert k[8] >= max_top
        assert integer(k) == c * p
        assert max(k) + MASK + 16 < 1 << 64
    # Canonical's q is <= 8, lower offsets dominate q*p_i, and the signed
    # residual needs no more than one p correction. The wider reducer has
    # q <= 63, with the same one-correction property.
    assert (8 * p - 1) >> 254 == 8
    assert all(8 * pi <= (1 << 32) - 8 for pi in pl[1:8])
    assert 64 * d < p and 8 * d < p
    assert F(469, 100) * p < 8 * p
    # Remaining carry and sign-width obligations in normalize, shl5 and
    # canonical. Their integer transformations preserve the bounds above.
    assert 32 * MASK + 32 < 1 << 64
    assert MASK + (1 << 32) + 16 < 1 << 64
    assert (1 << 22) + 16 < 1 << 63
    assert 63 * ((1 << 64) - 1) + 63 < 1 << 128
    return dict(prefix_bound=float(H), prefix_step=float(96 * H * h + 1),
                slope=float(slope), x3=float(x3), y3=float(y3))


def sample_tests(p):
    rng = random.Random(p)
    # Endpoints around both radix and field boundaries, plus every quotient
    # transition of the two canonicalization functions.
    canonical_values = {0, 1, 2, 8 * p - 1}
    for center in [k * p for k in range(9)] + [k << 254 for k in range(9)]:
        canonical_values.update(x for x in range(center - 3, center + 4) if 0 <= x < 8 * p)
    canonical_values.update(rng.randrange(8 * p) for _ in range(10000))
    for x in canonical_values:
        canonical(p, x)
    wide_values = {0, 1, (1 << 260) - 1}
    for center in [k * p for k in range(64)] + [k << 254 for k in range(65)]:
        wide_values.update(x for x in range(center - 3, center + 4) if 0 <= x < 1 << 260)
    wide_values.update(rng.randrange(1 << 260) for _ in range(10000))
    for x in wide_values:
        reduce_wide(p, x)

    edge_values = {0, 1, 2, R - 1, R - 2}
    for center in [p, 2 * p, 4 * p, 5 * p, 36 * p, 96 * p]:
        edge_values.update(x for x in range(center - 2, center + 3) if 0 <= x < R)
    # Single maximal/minimal limbs catch off-diagonal terms and carries.
    edge_values.update(MASK << (29 * i) for i in range(9))
    edge_values.update(R - 1 - (MASK << (29 * i)) for i in range(9))
    count = 0
    for a in edge_values:
        for b in edge_values:
            run_mul(p, a, b)
            count += 1
    for _ in range(10000):
        run_mul(p, rng.randrange(R), rng.randrange(R))
        count += 1
    return dict(mul=count, canonical=len(canonical_values), wide=len(wide_values))


for name, p in MODULI.items():
    peak = check_columns(p)
    bounds = prove_bounds(p)
    checks = sample_tests(p)
    print(name, "bounds:", bounds)
    print(name, "max multiply accumulation:", peak, f"({peak.bit_length()} bits)")
    print(name, "integer-model checks:", checks)
print("All exact interval, source-column, and integer-model checks passed.")
