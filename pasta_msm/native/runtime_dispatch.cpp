// Copyright Supranational LLC
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Modified by Zakura to select the x86_64 field backend at runtime.

#include <cstddef>
#include <cstdint>

#if defined(_MSC_VER)
# include <intrin.h>
#else
# include <cpuid.h>
#endif

using msm_fn = int (*)(void*, const void*, const void*, size_t);

int zakura_pasta_msm_pallas_vartime_baseline(
    void* output, const void* points, const void* scalars, size_t len) noexcept;
int zakura_pasta_msm_vesta_vartime_baseline(
    void* output, const void* points, const void* scalars, size_t len) noexcept;
int zakura_pasta_msm_pallas_vartime_adx(
    void* output, const void* points, const void* scalars, size_t len) noexcept;
int zakura_pasta_msm_vesta_vartime_adx(
    void* output, const void* points, const void* scalars, size_t len) noexcept;

namespace {

// CPUID leaf 7 EBX feature bits required by the generated mulx backend.
constexpr uint32_t CPUID_BMI2 = uint32_t{1} << 8;
constexpr uint32_t CPUID_ADX = uint32_t{1} << 19;

struct backend_t {
    msm_fn pallas;
    msm_fn vesta;
};

bool supports_adx_backend() noexcept
{
    uint32_t ebx;
#if defined(_MSC_VER)
    int registers[4];
    __cpuid(registers, 0);
    if (registers[0] < 7)
        return false;
    __cpuidex(registers, 7, 0);
    ebx = static_cast<uint32_t>(registers[1]);
#else
    unsigned int eax, ecx, edx;
    if (__get_cpuid_max(0, nullptr) < 7)
        return false;
    __cpuid_count(7, 0, eax, ebx, ecx, edx);
#endif
    return (ebx & (CPUID_BMI2 | CPUID_ADX)) == (CPUID_BMI2 | CPUID_ADX);
}

backend_t select_backend() noexcept
{
    if (supports_adx_backend()) {
        return {zakura_pasta_msm_pallas_vartime_adx,
                zakura_pasta_msm_vesta_vartime_adx};
    }
    return {zakura_pasta_msm_pallas_vartime_baseline,
            zakura_pasta_msm_vesta_vartime_baseline};
}

const backend_t& backend() noexcept
{
    // C++11 makes function-local static initialization thread-safe.
    static const backend_t selected = select_backend();
    return selected;
}

} // namespace

extern "C" int zakura_pasta_msm_pallas_vartime(
    void* output, const void* points, const void* scalars, size_t len) noexcept
{
    return backend().pallas(output, points, scalars, len);
}

extern "C" int zakura_pasta_msm_vesta_vartime(
    void* output, const void* points, const void* scalars, size_t len) noexcept
{
    return backend().vesta(output, points, scalars, len);
}
