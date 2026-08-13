/*
 * Copyright Supranational LLC
 * Licensed under the Apache License, Version 2.0, see LICENSE for details.
 * SPDX-License-Identifier: Apache-2.0
 * Modified by Zakura for the self-contained Pasta MSM backend.
 */

#include "vect.h"

void pasta_reciprocal(vec256 out, const vec256 inp, const vec256 mod, limb_t m0)
{
    static const vec256 Pallasx2 = { /* left-aligned value of the modulus */
        TO_LIMB_T(0x325a61da00000002), TO_LIMB_T(0x448d31f81299f237),
        TO_LIMB_T(0x0000000000000000), TO_LIMB_T(0x8000000000000000)
    };
    static const vec256 Vestax2 = { /* left-aligned value of the modulus */
        TO_LIMB_T(0x188dd64200000002), TO_LIMB_T(0x448d31f8132951bb),
        TO_LIMB_T(0x0000000000000000), TO_LIMB_T(0x8000000000000000)
    };
    vec512 temp;

    if ((byte)mod[1] == (byte)Pallas_P[1]) {
        ct_inverse_pasta(temp, inp, mod, Pallasx2);
        redc_mont_pasta(out, temp, mod, m0);
        mul_mont_pasta(out, Pallas_RR, out, mod, m0);
    } else {
        ct_inverse_pasta(temp, inp, mod, Vestax2);
        redc_mont_pasta(out, temp, mod, m0);
        mul_mont_pasta(out, Vesta_RR, out, mod, m0);
    }
}
