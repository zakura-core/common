# Derives the quadratic CM/AMNS constants declared in `src/fields/cm.rs`
# (the `CmParams` implementations for `FpParams` and `FqParams`) from the
# curve definitions alone, and prints them in the exact shape of the Rust
# source so the two can be diffed. Also prints the Babai tie-scalar test
# vectors used by the conversion tests.
#
# Run from this directory:
#
#     uv run sage cm_constants.sage
#
# Everything below is exact integer/rational arithmetic and hand-rolled
# two-dimensional lattice reduction, so the output does not depend on
# the SageMath version.
#
# The representation: work in R = Z[sigma]/(sigma^2 - 3*sigma + 3). For each
# Pasta modulus r there is a generator g = t + m*sigma with
# Norm(g) = t^2 + 3*t*m + 3*m^2 = r, and a stored pair (a, b) represents the
# field element x when a + b*sigma == beta*x (mod g), beta = 2^131. The
# reducer's 3-bit lift requires the unique unit associate of g with
# t == 1 (mod 8) and m == 0 (mod 8).

p = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
q = 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001

Fp = GF(p)
Fq = GF(q)

BETA = 2 ^ 131
A_BOUND = 31 * 2 ^ 122
B_BOUND = 3 * 2 ^ 124


def iround(a, b):
    # round(a / b), half away from zero, exact integers; b > 0.
    if a >= 0:
        return (2 * a + b) // (2 * b)
    return -((-2 * a + b) // (2 * b))


# --- The cube roots of unity (pinned exactly as in glv_constants.sage) ------

zeta_q = Fq(5) ^ ((q - 1) // 3)
assert zeta_q != 1 and zeta_q ^ 3 == 1

Pallas = EllipticCurve(Fp, [0, 5])
Gp = Pallas(-1, 2)
endo_image = int(zeta_q) * Gp
zeta_p = Fp(endo_image[0]) / Fp(Gp[0])
assert zeta_p != 1 and zeta_p ^ 3 == 1


# --- CM lattice machinery ----------------------------------------------------
#
# For a canonical root s of x^2 - 3x + 3 over GF(r), the lattice
# L = {(x, y) : x + y*s == 0 (mod r)} has covolume r under the norm form
# N(x, y) = x^2 + 3xy + 3y^2 (the ring norm of x + y*sigma). Lagrange-Gauss
# reduction under that form yields a generator of norm exactly r.

def cm_norm(v):
    return v[0] ^ 2 + 3 * v[0] * v[1] + 3 * v[1] ^ 2


def cm_dot2(u, v):
    # Twice the polar bilinear form of cm_norm (kept integral).
    return 2 * u[0] * v[0] + 3 * (u[0] * v[1] + u[1] * v[0]) + 6 * u[1] * v[1]


def lagrange_gauss_cm(u, v):
    while True:
        if cm_norm(u) > cm_norm(v):
            u, v = v, u
        m = iround(cm_dot2(u, v), 2 * cm_norm(u))
        if m == 0:
            return u, v
        v = (v[0] - m * u[0], v[1] - m * u[1])


def associates(g):
    # The unit group of R is {±1, ±(sigma-2), ±(sigma-2)^2}: multiplication
    # by the unit zeta = sigma - 2 maps (t, m) -> (-2t - 3m, t + m).
    out = []
    t, m = g
    for _ in range(3):
        out.append((t, m))
        out.append((-t, -m))
        t, m = (-2 * t - 3 * m, t + m)
    return out


def derive(field_name, r, Fr, zeta):
    # Select the root (zeta+2 or zeta^2+2) and unit associate for which the
    # reduced generator satisfies t == 1 (mod 8), m == 0 (mod 8), m > 0,
    # and the multiplication-closure inequalities. Exactly one qualifies.
    winners = []
    for root_name, s in [("zeta+2", zeta + 2), ("zeta^2+2", zeta ^ 2 + 2)]:
        assert s ^ 2 - 3 * s + 3 == 0
        u, v = lagrange_gauss_cm((r, 0), ((-int(s)) % r, 1))
        g = u if cm_norm(u) <= cm_norm(v) else v
        assert cm_norm(g) == r
        for t, m in associates(g):
            if t % 8 == 1 and m % 8 == 0 and m > 0:
                winners.append((root_name, int(s), t, m))
    assert len(winners) == 1, winners
    root_name, sigma, t, m = winners[0]
    m0 = t + m
    assert (t + m * sigma) % r == 0 or True  # g generates the ideal below
    assert Fr(t) + Fr(m) * Fr(sigma) == 0

    # Multiplication-closure inequalities (spec section 8): with
    # A = 31*2^122, B = 3*2^124, U = 2^127, the reduced product satisfies
    # |Z0| <= (A^2 + 3B^2 + 2^130*(|t| + 3*m0)) / 2^131 < A and
    # |Z1| <= (2AB + 3B^2 + 2^130*(m + |t|)) / 2^131 < B.
    z0_bound = (A_BOUND ^ 2 + 3 * B_BOUND ^ 2 + 2 ^ 130 * (abs(t) + 3 * m0))
    z1_bound = (2 * A_BOUND * B_BOUND + 3 * B_BOUND ^ 2 + 2 ^ 130 * (m + abs(t)))
    assert z0_bound < A_BOUND * 2 ^ 131
    assert z1_bound < B_BOUND * 2 ^ 131

    # g^{-1} mod 2^128 via the conjugate: gbar = (t + 3m) - m*sigma and
    # g * gbar = Norm(g) = r, so I = gbar * r^{-1} (mod 2^128).
    M128 = 2 ^ 128
    rinv = int(inverse_mod(r, M128))
    i0 = ((t + 3 * m) * rinv) % M128
    i1 = ((-m) * rinv) % M128
    # Self-check: (t + m*sigma)(i0 + i1*sigma) == 1 in R/2^128.
    c0 = (t * i0 - 3 * m * i1) % M128
    c1 = (t * i1 + m * i0 + 3 * m * i1) % M128
    assert (c0, c1) == (1, 0)

    # ONE: exact-rational Babai reduction of (beta, 0) by the lattice basis
    # w1 = (t, m), w2 = (-3*m0, t). The basis-inverse coordinates of (k, 0)
    # are (k*t/r, -k*m/r).
    def babai(k):
        c1_ = iround(k * t, r)
        c2_ = iround(-k * m, r)
        a = k - c1_ * t - c2_ * (-3 * m0)
        b = -c1_ * m - c2_ * t
        return a, b

    one_a, one_b = babai(BETA)
    assert Fr(one_a) + Fr(one_b) * Fr(sigma) == Fr(BETA)
    assert abs(one_a) < A_BOUND and abs(one_b) < B_BOUND

    # The deferred-finalize scale correction: a reduced representative of
    # 2^259 = 2^128 * beta (mod g).
    tp259_a, tp259_b = babai(2 ^ 259 % r)
    assert Fr(tp259_a) + Fr(tp259_b) * Fr(sigma) == Fr(2 ^ 259)
    assert abs(tp259_a) < A_BOUND and abs(tp259_b) < B_BOUND

    # Conversion constants.
    beta_inv = int(Fr(BETA) ^ -1)
    sigma_beta_inv = int(Fr(sigma) * Fr(BETA) ^ -1)
    solinas_c = r - 2 ^ 254
    assert 0 < solinas_c < 2 ^ 126

    # Babai rounding constants at 512 fractional bits. 384 bits (the GLV
    # scale) admits ±1 rounding slips that the CM bounds cannot absorb; at
    # 2^512 the perturbation is below 1/(2r) and r is odd, so the fixed-point
    # rounding equals exact rounding for every k in [0, r).
    g_t = iround(2 ^ 512 * abs(t), r)
    g_m = iround(2 ^ 512 * m, r)
    assert max(g_t, g_m) < 2 ^ 448  # each fits seven u64 limbs

    # Sanity: the exact Babai output box stays inside the storage invariant
    # for every canonical input (residual bounds (|t| + 3*m0)/2, (m + |t|)/2).
    assert (abs(t) + 3 * m0) < 2 * A_BOUND
    assert (m + abs(t)) < 2 * B_BOUND

    return {
        "root_name": root_name,
        "sigma": sigma,
        "t": t,
        "m": m,
        "m0": m0,
        "i0": i0,
        "i1": i1,
        "one": (one_a, one_b),
        "two_pow_259": (tp259_a, tp259_b),
        "modulus": r,
        "solinas_c": solinas_c,
        "beta_inv": beta_inv,
        "sigma_beta_inv": sigma_beta_inv,
        "g_t": g_t,
        "g_m": g_m,
    }


def rust_limbs(x, count, indent):
    limbs = [(x >> (64 * i)) & (2 ^ 64 - 1) for i in range(count)]
    assert x == sum(l << (64 * i) for i, l in enumerate(limbs))
    return "\n".join("%s0x%016x," % (" " * indent, l) for l in limbs)


def rust_i128(x):
    return ("-%#x" % -x) if x < 0 else ("%#x" % x)


def print_impl(struct, d):
    print("impl CmParams for %s {" % struct)
    print("    const T: i128 = %s;" % rust_i128(d["t"]))
    print("    const M: i128 = %s;" % rust_i128(d["m"]))
    print("    const M0: i128 = %s;" % rust_i128(d["m0"]))
    print("    const I0: u128 = %#x;" % d["i0"])
    print("    const I1: u128 = %#x;" % d["i1"])
    print("    const ONE: (i128, i128) = (")
    print("        %s," % rust_i128(d["one"][0]))
    print("        %s," % rust_i128(d["one"][1]))
    print("    );")
    print("    const TWO_POW_259: (i128, i128) = (")
    print("        %s," % rust_i128(d["two_pow_259"][0]))
    print("        %s," % rust_i128(d["two_pow_259"][1]))
    print("    );")
    for name, value, count in [
        ("MODULUS_LIMBS", d["modulus"], 4),
        ("SIGMA", d["sigma"], 4),
        ("BETA_INV", d["beta_inv"], 4),
        ("SIGMA_BETA_INV", d["sigma_beta_inv"], 4),
    ]:
        print("    const %s: [u64; %d] = [" % (name, count))
        print(rust_limbs(value, count, 8))
        print("    ];")
    print("    const SOLINAS_C: u128 = %#x;" % d["solinas_c"])
    for name, value in [("G_T", d["g_t"]), ("G_M", d["g_m"])]:
        print("    const %s: [u64; 7] = [" % name)
        print(rust_limbs(value, 7, 8))
        print("    ];")
    print("}")


def print_tie_scalars(prefix, d):
    # Canonical scalars for which k*|t| or k*m is as close as possible to a
    # half-integer multiple of r — the worst cases for the fixed-point Babai
    # rounding in `encode` — plus their +/-1 neighbors.
    r = d["modulus"]
    out = []
    for coeff in [abs(d["t"]), d["m"]]:
        cinv = int(inverse_mod(coeff, r))
        for target in [(r - 1) // 2, (r + 1) // 2]:
            k = (target * cinv) % r
            for dk in [-1, 0, 1]:
                out.append((k + dk) % r)
    print("const %s_BABAI_TIE_SCALARS: [[u64; 4]; %d] = [" % (prefix, len(out)))
    for k in out:
        print("    [")
        print(rust_limbs(k, 4, 8))
        print("    ],")
    print("];")


dp = derive("Fp", p, Fp, zeta_p)
dq = derive("Fq", q, Fq, zeta_q)

print("// Fp: sigma = %s = %#x" % (dp["root_name"], dp["sigma"]))
print_impl("FpParams", dp)
print()
print("// Fq: sigma = %s = %#x" % (dq["root_name"], dq["sigma"]))
print_impl("FqParams", dq)
print()
print_tie_scalars("FP", dp)
print()
print_tie_scalars("FQ", dq)
