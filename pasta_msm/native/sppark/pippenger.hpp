// Copyright Supranational LLC
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Modified by Zakura for serial signed-Booth CPU execution only.

#ifndef ZAKURA_PASTA_MSM_SPPARK_PIPPENGER_HPP
#define ZAKURA_PASTA_MSM_SPPARK_PIPPENGER_HPP

#include <algorithm>
#include <cstddef>
#include <memory>
#include <vector>

static size_t get_wval(const unsigned char* data, size_t offset, size_t bits)
{
    size_t top = (offset + bits - 1) / 8;
    size_t mask = static_cast<size_t>(0) - 1;

    data += offset / 8;
    top -= offset / 8 - 1;

    size_t value = 0;
    for (size_t i = 0; i < 4;) {
        value |= (*data & mask) << (8 * i);
        mask = static_cast<size_t>(0) -
               ((++i - top) >> (8 * sizeof(top) - 1));
        data += 1 & mask;
    }
    return value >> (offset % 8);
}

static size_t get_wval_bounded(const unsigned char* data, size_t offset,
                               size_t bits, size_t nbits)
{
    if (offset >= nbits)
        return 0;

    bits = std::min(bits, nbits - offset);
    return get_wval(data, offset, bits) &
           ((static_cast<size_t>(1) << bits) - 1);
}

static size_t window_size(size_t npoints)
{
    size_t bits = 0;
    while (npoints >>= 1)
        bits++;

    return bits > 12 ? bits - 3 : (bits > 4 ? bits - 2 : (bits ? 2 : 1));
}

template<class point_t>
static void integrate_buckets(point_t& output, point_t buckets[],
                              size_t bucket_bits)
{
    size_t count = static_cast<size_t>(1) << bucket_bits;
    point_t accumulator = buckets[--count];
    point_t result = buckets[count];
    buckets[count].inf();
    while (count--) {
        accumulator.add(buckets[count]);
        result.add(accumulator);
        buckets[count].inf();
    }
    output = result;
}

template<class point_t, class affine_t, typename scalar_t>
static void mult(point_t& output, const affine_t& point,
                 const scalar_t scalar, size_t top)
{
    output.inf();
    if (point.is_inf())
        return;

    while (--top && ((scalar[top / 8] >> (top % 8)) & 1) == 0) {}
    if ((scalar[top / 8] >> (top % 8)) & 1) {
        output = point;
        while (top--) {
            output.dbl();
            if ((scalar[top / 8] >> (top % 8)) & 1)
                output.add(point);
        }
    }
}

static size_t booth_digit(const unsigned char* scalar, size_t bit0,
                          size_t window, size_t nbits, bool& negative)
{
    size_t encoded;
    if (bit0 == 0) {
        encoded = get_wval_bounded(scalar, 0, window, nbits) << 1;
    } else {
        encoded = get_wval_bounded(scalar, bit0 - 1, window + 1, nbits);
    }

    negative = ((encoded >> window) & 1) != 0;
    size_t rounded = (encoded + 1) >> 1;
    return negative ? (static_cast<size_t>(1) << window) - rounded : rounded;
}

template<class point_t, class affine_t>
static void tile_signed(point_t& output, const affine_t points[],
                        size_t npoints, const unsigned char* scalars,
                        size_t nbits, point_t buckets[], size_t bit0,
                        size_t window)
{
    size_t scalar_bytes = (nbits + 7) / 8;
    for (size_t i = 0; i < npoints; i++, scalars += scalar_bytes) {
        bool negative;
        size_t digit = booth_digit(scalars, bit0, window, nbits, negative);
        if (digit != 0)
            buckets[digit - 1].add(points[i], negative);
    }
    integrate_buckets(output, buckets, window - 1);
}

template<class point_t, class scalar_t,
         class affine_t = typename point_t::affine_type>
static void mult_pippenger_signed_serial(point_t& output,
                                         const affine_t points[],
                                         size_t npoints,
                                         const scalar_t mont_scalars[])
{
    using canonical_scalar = typename scalar_t::pow_t;
    const size_t nbits = scalar_t::nbits;

    if (npoints == 0) {
        output.inf();
        return;
    }

    std::unique_ptr<canonical_scalar[]> scalars(
        new canonical_scalar[npoints]);
    for (size_t i = 0; i < npoints; i++)
        mont_scalars[i].to_scalar(scalars[i]);

    if (npoints == 1) {
        mult(output, points[0], scalars[0], nbits);
        return;
    }

    size_t window = window_size(npoints);
    size_t windows = nbits / window + 1;
    std::vector<point_t> buckets(
        static_cast<size_t>(1) << (window - 1));

    point_t partial;
    output.inf();
    for (size_t index = windows; index-- > 0;) {
        tile_signed(partial, points, npoints, scalars[0], nbits,
                    buckets.data(), index * window, window);
        output.add(partial);
        if (index != 0) {
            for (size_t i = 0; i < window; i++)
                output.dbl();
        }
    }
}

#endif
