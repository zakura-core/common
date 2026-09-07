// Metal compute kernels for Pasta multiscalar multiplication.
//
// This file is a transliteration of the portable Rust in `src/field.rs`,
// `src/curve.rs`, and `src/pipeline.rs` (functions `accumulate_bucket` and
// `reduce_chunk`), which are the reference implementation and the tests'
// oracle. Buffer layouts, limb order, arithmetic schedules, and index
// conventions are identical; change the Rust and this file together.
//
// Representation: field elements are twenty little-endian 13-bit limbs,
// each in a uint, in Montgomery form with R = 2^260 (see `src/field.rs`
// for why: a 26-bit limb product lets a whole Montgomery column — up to
// forty products plus a carry — accumulate in a uint, so multiplication
// needs neither 64-bit emulation nor multiply-high). Both Pasta primes are
// 1 mod 2^13, so the per-column Montgomery factor -p^{-1} mod 2^13 is
// 2^13 - 1 for both. Every value is canonical: limbs below 2^13 and the
// integer below p.
// Points: affine (x, y) with (0, 0) the identity; Jacobian (X, Y, Z) with
// Z = 0 the identity. The curves have a = 0, b = 5.
//
// Everything is variable-time; inputs are public.

#include <metal_stdlib>
using namespace metal;

constant uint LIMB_BITS = 13u;
constant uint LIMBS = 20u;
constant uint LIMB_MASK = 0x1fffu;
constant uint MU = 0x1fffu;
constant uint TERM_NEGATE = 0x80000000u;

struct Fe {
    uint v[20];
};

struct Affine {
    Fe x;
    Fe y;
};

struct Jacobian {
    Fe x;
    Fe y;
    Fe z;
};

struct FieldParams {
    uint modulus[20];
    uint one[20];  // R mod p: the Montgomery form of 1
};

struct AccumulateParams {
    uint total_buckets;
};

struct ReduceParams {
    uint windows;
    uint input_len;  // entries per window in the input arrays
    uint chunks;     // chunks (threads, outputs) per window
    uint chunk_log2;
    uint has_plain;  // whether the plain input array is meaningful
};

// ---------------------------------------------------------------- field

static inline Fe fe_zero() {
    Fe out;
    for (uint i = 0; i < LIMBS; i++) out.v[i] = 0u;
    return out;
}

static inline Fe fe_from_params(constant uint* limbs) {
    Fe out;
    for (uint i = 0; i < LIMBS; i++) out.v[i] = limbs[i];
    return out;
}

static inline bool fe_is_zero(Fe a) {
    uint acc = 0u;
    for (uint i = 0; i < LIMBS; i++) acc |= a.v[i];
    return acc == 0u;
}

// a - modulus over 13-bit limbs, with the final borrow (true when a < p).
static inline Fe fe_sub_modulus(Fe a, constant FieldParams& f, thread bool& borrow_out) {
    Fe out;
    uint borrow = 0u;
    for (uint i = 0; i < LIMBS; i++) {
        uint d = a.v[i] - f.modulus[i] - borrow;
        out.v[i] = d & LIMB_MASK;
        borrow = d >> 31;  // limbs are 13 bits: a negative difference sets bit 31
    }
    borrow_out = borrow == 1u;
    return out;
}

// Reduces a carried value below 2p into [0, p).
static inline Fe fe_reduce_once(Fe a, constant FieldParams& f) {
    bool borrow;
    Fe reduced = fe_sub_modulus(a, f, borrow);
    return borrow ? a : reduced;
}

static inline Fe fe_add(Fe a, Fe b, constant FieldParams& f) {
    Fe sum;
    uint carry = 0u;
    for (uint i = 0; i < LIMBS; i++) {
        uint s = a.v[i] + b.v[i] + carry;
        sum.v[i] = s & LIMB_MASK;
        carry = s >> LIMB_BITS;
    }
    return fe_reduce_once(sum, f);
}

static inline Fe fe_double(Fe a, constant FieldParams& f) {
    return fe_add(a, a, f);
}

static inline Fe fe_sub(Fe a, Fe b, constant FieldParams& f) {
    Fe diff;
    uint borrow = 0u;
    for (uint i = 0; i < LIMBS; i++) {
        uint d = a.v[i] - b.v[i] - borrow;
        diff.v[i] = d & LIMB_MASK;
        borrow = d >> 31;
    }
    if (borrow == 1u) {
        uint carry = 0u;
        for (uint i = 0; i < LIMBS; i++) {
            uint s = diff.v[i] + f.modulus[i] + carry;
            diff.v[i] = s & LIMB_MASK;
            carry = s >> LIMB_BITS;
        }
    }
    return diff;
}

static inline Fe fe_neg(Fe a, constant FieldParams& f) {
    if (fe_is_zero(a)) return fe_zero();
    return fe_sub(fe_from_params(f.modulus), a, f);
}

// Montgomery product a * b * R^-1 mod p: the carry-free schoolbook
// schedule of `Field::mul`. Column t[k] accumulates at most 2 * LIMBS
// 26-bit products plus one 19-bit carry before its own carry is taken,
// which fits a uint.
static inline Fe fe_mul(Fe a, Fe b, constant FieldParams& f) {
    uint t[40];
    for (uint i = 0; i < 2u * LIMBS; i++) t[i] = 0u;
    for (uint i = 0; i < LIMBS; i++) {
        uint bi = b.v[i];
        for (uint j = 0; j < LIMBS; j++) t[i + j] += a.v[j] * bi;
        uint m = ((t[i] & LIMB_MASK) * MU) & LIMB_MASK;
        for (uint j = 0; j < LIMBS; j++) t[i + j] += m * f.modulus[j];
        t[i + 1] += t[i] >> LIMB_BITS;
    }
    for (uint k = LIMBS; k < 2u * LIMBS - 1u; k++) {
        t[k + 1] += t[k] >> LIMB_BITS;
        t[k] &= LIMB_MASK;
    }
    Fe out;
    for (uint i = 0; i < LIMBS; i++) out.v[i] = t[LIMBS + i];
    return fe_reduce_once(out, f);
}

static inline Fe fe_square(Fe a, constant FieldParams& f) {
    return fe_mul(a, a, f);
}

// ---------------------------------------------------------------- curve

static inline bool affine_is_identity(Affine p) {
    return fe_is_zero(p.x) && fe_is_zero(p.y);
}

static inline bool jac_is_identity(Jacobian p) {
    return fe_is_zero(p.z);
}

static inline Jacobian jac_identity() {
    Jacobian out;
    out.x = fe_zero();
    out.y = fe_zero();
    out.z = fe_zero();
    return out;
}

static inline Jacobian affine_to_jacobian(Affine p, constant FieldParams& f) {
    if (affine_is_identity(p)) return jac_identity();
    Jacobian out;
    out.x = p.x;
    out.y = p.y;
    out.z = fe_from_params(f.one);
    return out;
}

// dbl-2009-l, a = 0.
static inline Jacobian jac_double(Jacobian p, constant FieldParams& f) {
    if (jac_is_identity(p)) return jac_identity();
    Fe a = fe_square(p.x, f);
    Fe b = fe_square(p.y, f);
    Fe c = fe_square(b, f);
    Fe xb = fe_add(p.x, b, f);
    Fe d = fe_double(fe_sub(fe_sub(fe_square(xb, f), a, f), c, f), f);
    Fe e = fe_add(fe_double(a, f), a, f);
    Fe ff = fe_square(e, f);
    Jacobian out;
    out.x = fe_sub(ff, fe_double(d, f), f);
    Fe c8 = fe_double(fe_double(fe_double(c, f), f), f);
    out.y = fe_sub(fe_mul(e, fe_sub(d, out.x, f), f), c8, f);
    out.z = fe_double(fe_mul(p.y, p.z, f), f);
    return out;
}

// madd-2007-bl with exact exceptional cases.
static inline Jacobian jac_add_mixed(Jacobian p, Affine q, constant FieldParams& f) {
    if (affine_is_identity(q)) return p;
    if (jac_is_identity(p)) return affine_to_jacobian(q, f);
    Fe z1z1 = fe_square(p.z, f);
    Fe u2 = fe_mul(q.x, z1z1, f);
    Fe s2 = fe_mul(q.y, fe_mul(p.z, z1z1, f), f);
    Fe h = fe_sub(u2, p.x, f);
    Fe r = fe_double(fe_sub(s2, p.y, f), f);
    if (fe_is_zero(h)) {
        return fe_is_zero(r) ? jac_double(p, f) : jac_identity();
    }
    Fe hh = fe_square(h, f);
    Fe i = fe_double(fe_double(hh, f), f);
    Fe j = fe_mul(h, i, f);
    Fe v = fe_mul(p.x, i, f);
    Jacobian out;
    out.x = fe_sub(fe_sub(fe_square(r, f), j, f), fe_double(v, f), f);
    out.y = fe_sub(fe_mul(r, fe_sub(v, out.x, f), f), fe_double(fe_mul(p.y, j, f), f), f);
    out.z = fe_sub(fe_sub(fe_square(fe_add(p.z, h, f), f), z1z1, f), hh, f);
    return out;
}

// add-2007-bl with exact exceptional cases.
static inline Jacobian jac_add(Jacobian p, Jacobian q, constant FieldParams& f) {
    if (jac_is_identity(q)) return p;
    if (jac_is_identity(p)) return q;
    Fe z1z1 = fe_square(p.z, f);
    Fe z2z2 = fe_square(q.z, f);
    Fe u1 = fe_mul(p.x, z2z2, f);
    Fe u2 = fe_mul(q.x, z1z1, f);
    Fe s1 = fe_mul(p.y, fe_mul(q.z, z2z2, f), f);
    Fe s2 = fe_mul(q.y, fe_mul(p.z, z1z1, f), f);
    Fe h = fe_sub(u2, u1, f);
    Fe r = fe_double(fe_sub(s2, s1, f), f);
    if (fe_is_zero(h)) {
        return fe_is_zero(r) ? jac_double(p, f) : jac_identity();
    }
    Fe i = fe_square(fe_double(h, f), f);
    Fe j = fe_mul(h, i, f);
    Fe v = fe_mul(u1, i, f);
    Jacobian out;
    out.x = fe_sub(fe_sub(fe_square(r, f), j, f), fe_double(v, f), f);
    out.y = fe_sub(fe_mul(r, fe_sub(v, out.x, f), f), fe_double(fe_mul(s1, j, f), f), f);
    out.z = fe_mul(fe_sub(fe_sub(fe_square(fe_add(p.z, q.z, f), f), z1z1, f), z2z2, f), h, f);
    return out;
}

static inline Jacobian jac_double_n(Jacobian p, uint k, constant FieldParams& f) {
    for (uint i = 0; i < k; i++) p = jac_double(p, f);
    return p;
}

// -------------------------------------------------------------- kernels

// Kernel 1 (`pipeline::accumulate_bucket`): one thread per bucket sums
// the bases it references with mixed additions.
kernel void accumulate_buckets(
    device const Affine* bases [[buffer(0)]],
    device const uint* terms [[buffer(1)]],
    device const uint* offsets [[buffer(2)]],
    device Jacobian* buckets [[buffer(3)]],
    constant FieldParams& field [[buffer(4)]],
    constant AccumulateParams& params [[buffer(5)]],
    uint gid [[thread_position_in_grid]])
{
    if (gid >= params.total_buckets) return;
    uint start = offsets[gid];
    uint end = offsets[gid + 1];
    Jacobian acc = jac_identity();
    for (uint t = start; t < end; t++) {
        uint reference = terms[t];
        Affine base = bases[reference & ~TERM_NEGATE];
        if ((reference & TERM_NEGATE) != 0u) base.y = fe_neg(base.y, field);
        acc = jac_add_mixed(acc, base, field);
    }
    buckets[gid] = acc;
}

// Kernel 2 (`pipeline::reduce_chunk`): one thread per (window, chunk)
// folds a chunk of `2^chunk_log2` entries of the level's plain and
// weighted arrays into the next level's entries.
kernel void reduce_level(
    device const Jacobian* weighted [[buffer(0)]],
    device const Jacobian* plain [[buffer(1)]],
    device Jacobian* out_plain [[buffer(2)]],
    device Jacobian* out_weighted [[buffer(3)]],
    constant FieldParams& field [[buffer(4)]],
    constant ReduceParams& params [[buffer(5)]],
    uint gid [[thread_position_in_grid]])
{
    if (gid >= params.windows * params.chunks) return;
    uint window = gid / params.chunks;
    uint chunk = gid % params.chunks;
    uint size = 1u << params.chunk_log2;
    uint base = window * params.input_len;
    uint start = chunk * size;
    uint end = min(start + size, params.input_len);
    uint count = end - start;

    Jacobian running = jac_identity();
    Jacobian acc = jac_identity();
    for (uint i = count; i-- > 1;) {
        running = jac_add(running, weighted[base + start + i], field);
        acc = jac_add(acc, running, field);
    }
    Jacobian total = jac_add(running, weighted[base + start], field);
    if (params.has_plain != 0u) {
        for (uint i = start; i < end; i++) acc = jac_add(acc, plain[base + i], field);
    }
    out_plain[gid] = acc;
    out_weighted[gid] = jac_double_n(total, params.chunk_log2, field);
}
