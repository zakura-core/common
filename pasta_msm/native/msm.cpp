// Copyright Supranational LLC
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Modified by Zakura for a status-returning, caller-thread-only CPU bridge.

#include <cstddef>
#include <cstdint>
#include <new>
#include <type_traits>

#include <glv.hpp>
#include <sppark/curve.hpp>
#include <sppark/pasta.hpp>

namespace {

constexpr int STATUS_OK = 0;
constexpr int STATUS_INVALID_ARGUMENT = 1;
constexpr int STATUS_ALLOCATION_FAILURE = 2;
constexpr int STATUS_NATIVE_FAILURE = 3;

template<class field_t>
struct projective_output_t {
    field_t X, Y, Z;
};

static_assert(sizeof(pallas_t) == 4 * sizeof(uint64_t),
              "Pallas fields must contain four 64-bit limbs");
static_assert(alignof(pallas_t) == alignof(uint64_t),
              "Pallas fields must use 64-bit alignment");
static_assert(sizeof(vesta_t) == 4 * sizeof(uint64_t),
              "Vesta fields must contain four 64-bit limbs");
static_assert(alignof(vesta_t) == alignof(uint64_t),
              "Vesta fields must use 64-bit alignment");
static_assert(sizeof(affine_t<pallas_t>) == 8 * sizeof(uint64_t),
              "Pallas affine points must contain two fields");
static_assert(alignof(affine_t<pallas_t>) == alignof(uint64_t),
              "Pallas affine points must use 64-bit alignment");
static_assert(sizeof(affine_t<vesta_t>) == 8 * sizeof(uint64_t),
              "Vesta affine points must contain two fields");
static_assert(alignof(affine_t<vesta_t>) == alignof(uint64_t),
              "Vesta affine points must use 64-bit alignment");
static_assert(sizeof(projective_output_t<pallas_t>) == 12 * sizeof(uint64_t),
              "Pallas projective points must contain three fields");
static_assert(alignof(projective_output_t<pallas_t>) == alignof(uint64_t),
              "Pallas projective points must use 64-bit alignment");
static_assert(sizeof(projective_output_t<vesta_t>) == 12 * sizeof(uint64_t),
              "Vesta projective points must contain three fields");
static_assert(alignof(projective_output_t<vesta_t>) == alignof(uint64_t),
              "Vesta projective points must use 64-bit alignment");
static_assert(std::is_standard_layout<affine_t<pallas_t>>::value,
              "Pallas affine points must be standard-layout");
static_assert(std::is_trivially_copyable<affine_t<pallas_t>>::value,
              "Pallas affine points must be trivially copyable");
static_assert(std::is_standard_layout<affine_t<vesta_t>>::value,
              "Vesta affine points must be standard-layout");
static_assert(std::is_trivially_copyable<affine_t<vesta_t>>::value,
              "Vesta affine points must be trivially copyable");
static_assert(std::is_standard_layout<projective_output_t<pallas_t>>::value,
              "Pallas projective points must be standard-layout");
static_assert(
    std::is_trivially_copyable<projective_output_t<pallas_t>>::value,
    "Pallas projective points must be trivially copyable");
static_assert(std::is_standard_layout<projective_output_t<vesta_t>>::value,
              "Vesta projective points must be standard-layout");
static_assert(
    std::is_trivially_copyable<projective_output_t<vesta_t>>::value,
    "Vesta projective points must be trivially copyable");

template<class base_t, class scalar_t>
int multiscalar(void* output, const void* points, const void* scalars,
                size_t len, const zakura_pasta_msm::glv_params_t& params,
                const base_t& zeta) noexcept
{
    if (output == nullptr ||
        (len != 0 && (points == nullptr || scalars == nullptr))) {
        return STATUS_INVALID_ARGUMENT;
    }

    try {
        using point_t = xyzz_t<base_t>;
        using affine_type = typename point_t::affine_type;
        point_t result;
        zakura_pasta_msm::mult_pippenger_glv_signed_serial(
            result, static_cast<const affine_type*>(points), len,
            static_cast<const scalar_t*>(scalars), params, zeta);

        affine_type affine = result.to_affine();
        auto* rust_output =
            static_cast<projective_output_t<base_t>*>(output);
        rust_output->X = affine.X;
        rust_output->Y = affine.Y;
        if (affine.is_inf()) {
            rust_output->Z.zero();
        } else {
            rust_output->Z = base_t::one();
        }
        return STATUS_OK;
    } catch (const std::bad_alloc&) {
        return STATUS_ALLOCATION_FAILURE;
    } catch (...) {
        return STATUS_NATIVE_FAILURE;
    }
}

} // namespace

#ifndef ZAKURA_PASTA_MSM_PALLAS_ENTRY
# define ZAKURA_PASTA_MSM_PALLAS_ENTRY zakura_pasta_msm_pallas_vartime
# define ZAKURA_PASTA_MSM_VESTA_ENTRY zakura_pasta_msm_vesta_vartime
#endif

#if defined(ZAKURA_PASTA_MSM_PRIVATE_BACKEND) && \
    (defined(__GNUC__) || defined(__clang__))
# define ZAKURA_PASTA_MSM_VISIBILITY __attribute__((visibility("hidden")))
#else
# define ZAKURA_PASTA_MSM_VISIBILITY
#endif

#if defined(ZAKURA_PASTA_MSM_PRIVATE_BACKEND)
# define ZAKURA_PASTA_MSM_LINKAGE ZAKURA_PASTA_MSM_VISIBILITY
#else
# define ZAKURA_PASTA_MSM_LINKAGE extern "C"
#endif

ZAKURA_PASTA_MSM_LINKAGE int ZAKURA_PASTA_MSM_PALLAS_ENTRY(
    void* output, const void* points, const void* scalars, size_t len) noexcept
{
    return multiscalar<pallas_t, vesta_t>(
        output, points, scalars, len, zakura_pasta_msm::PALLAS_GLV,
        zakura_pasta_msm::pallas_zeta());
}

ZAKURA_PASTA_MSM_LINKAGE int ZAKURA_PASTA_MSM_VESTA_ENTRY(
    void* output, const void* points, const void* scalars, size_t len) noexcept
{
    return multiscalar<vesta_t, pallas_t>(
        output, points, scalars, len, zakura_pasta_msm::VESTA_GLV,
        zakura_pasta_msm::vesta_zeta());
}
