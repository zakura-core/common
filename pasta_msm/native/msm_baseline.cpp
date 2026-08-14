// Copyright Supranational LLC
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Modified by Zakura to build a private baseline MSM backend.

#define ZAKURA_PASTA_MSM_BASELINE_BACKEND
#define ZAKURA_PASTA_MSM_PRIVATE_BACKEND
#define pasta_t zakura_pasta_msm_baseline_field_t
#define ZAKURA_PASTA_MSM_PALLAS_ENTRY \
    zakura_pasta_msm_pallas_vartime_baseline
#define ZAKURA_PASTA_MSM_VESTA_ENTRY \
    zakura_pasta_msm_vesta_vartime_baseline
#include "msm.cpp"
