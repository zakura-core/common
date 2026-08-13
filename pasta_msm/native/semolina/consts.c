/*
 * Copyright Supranational LLC
 * Licensed under the Apache License, Version 2.0, see LICENSE for details.
 * SPDX-License-Identifier: Apache-2.0
 * Modified by Zakura for the self-contained Pasta MSM backend.
 */

#include "vect.h"

/* 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001 */
static const vec256 Pallas_P = {
    TO_LIMB_T(0x992d30ed00000001), TO_LIMB_T(0x224698fc094cf91b),
    TO_LIMB_T(0x0000000000000000), TO_LIMB_T(0x4000000000000000)
};
static const limb_t Pallas_p0 = 0x992d30ecffffffff;
static const vec256 Pallas_RR = { /* (1<<512)%P */
    TO_LIMB_T(0x8c78ecb30000000f), TO_LIMB_T(0xd7d30dbd8b0de0e7),
    TO_LIMB_T(0x7797a99bc3c95d18), TO_LIMB_T(0x096d41af7b9cb714)
};
static const vec256 Pallas_one = { /* (1<<256)%P */
    TO_LIMB_T(0x34786d38fffffffd), TO_LIMB_T(0x992c350be41914ad),
    TO_LIMB_T(0xffffffffffffffff), TO_LIMB_T(0x3fffffffffffffff)
};

/* 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001 */
static const vec256 Vesta_P = {
    TO_LIMB_T(0x8c46eb2100000001), TO_LIMB_T(0x224698fc0994a8dd),
    TO_LIMB_T(0x0000000000000000), TO_LIMB_T(0x4000000000000000)
};
static const limb_t Vesta_p0 = 0x8c46eb20ffffffff;
static const vec256 Vesta_RR = { /* (1<<512)%P */
    TO_LIMB_T(0xfc9678ff0000000f), TO_LIMB_T(0x67bb433d891a16e3),
    TO_LIMB_T(0x7fae231004ccf590), TO_LIMB_T(0x096d41af7ccfdaa9)
};
static const vec256 Vesta_one = { /* (1<<256)%P */
    TO_LIMB_T(0x5b2b3e9cfffffffd), TO_LIMB_T(0x992c350be3420567),
    TO_LIMB_T(0xffffffffffffffff), TO_LIMB_T(0x3fffffffffffffff)
};
