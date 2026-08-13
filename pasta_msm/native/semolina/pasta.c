/*
 * Copyright Supranational LLC
 * Licensed under the Apache License, Version 2.0, see LICENSE for details.
 * SPDX-License-Identifier: Apache-2.0
 * Modified by Zakura for the self-contained Pasta MSM backend.
 */

#include "consts.c"
#include "bytes.h"

void pasta_from_scalar(vec256 ret, const pow256 a, const vec256 p, limb_t n0)
{
    const union {
        long one;
        char little;
    } is_endian = { 1 };

    if ((uptr_t)ret == (uptr_t)a && is_endian.little) {
        mul_mont_pasta(ret, (byte)p[1] == (byte)Pallas_P[1] ? Pallas_RR
                                                            : Vesta_RR,
                            (const limb_t *)a, p, n0);
    } else {
        vec256 out;
        limbs_from_le_bytes(out, a, 32);
        mul_mont_pasta(ret, (byte)p[1] == (byte)Pallas_P[1] ? Pallas_RR
                                                            : Vesta_RR,
                            out, p, n0);
        vec_zero(out, sizeof(out));
    }
}

void pasta_to_scalar(pow256 ret, const vec256 a, const vec256 p, limb_t n0)
{
    const union {
        long one;
        char little;
    } is_endian = { 1 };

    if ((size_t)ret % sizeof(limb_t) == 0 && is_endian.little) {
        from_mont_pasta((limb_t *)ret, a, p, n0);
    } else {
        vec256 out;
        from_mont_pasta(out, a, p, n0);
        le_bytes_from_limbs(ret, out, 32);
        vec_zero(out, sizeof(out));
    }
}

void pasta_mul(vec256 out, const vec256 a, const vec256 b,
                           const vec256 p, limb_t n0)
{   mul_mont_pasta(out, a, b, p, n0);   }

void pasta_sqr(vec256 out, const vec256 a, const vec256 p, limb_t n0)
{   sqr_mont_pasta(out, a, p, n0);   }

void pasta_from(vec256 out, const vec256 a, const vec256 p, limb_t n0)
{   from_mont_pasta(out, a, p, n0);   }

#include "recip.c"
