/*
 * Copyright Supranational LLC
 * Licensed under the Apache License, Version 2.0, see LICENSE for details.
 * SPDX-License-Identifier: Apache-2.0
 * Modified by Zakura for the self-contained Pasta MSM backend.
 */
#ifndef __PASTA_ASM_VECT_H__
#define __PASTA_ASM_VECT_H__

#include <stddef.h>

#if defined(__x86_64__) || defined(__aarch64__)
/* These are available even in ILP32 flavours, but even then they are
 * capable of performing 64-bit operations as efficiently as in *P64. */
typedef unsigned long long limb_t;
# define LIMB_T_BITS    64

#elif defined(_WIN64)   /* Win64 is P64 */
typedef unsigned __int64 limb_t;
# define LIMB_T_BITS    64

#else
# error "unsupported platform"
#endif

/*
 * Why isn't LIMB_T_BITS defined as 8*sizeof(limb_t)? Because pre-processor
 * knows nothing about sizeof(anything)...
 */
#if LIMB_T_BITS == 64
# define TO_LIMB_T(limb64)     limb64
#else
# define TO_LIMB_T(limb64)     (limb_t)limb64,(limb_t)(limb64>>32)
#endif

#define NLIMBS(bits)   (bits/LIMB_T_BITS)

typedef limb_t vec256[NLIMBS(256)];
typedef limb_t vec512[NLIMBS(512)];

typedef unsigned char byte;
#define TO_BYTES(limb64)    (byte)limb64,(byte)(limb64>>8),\
                            (byte)(limb64>>16),(byte)(limb64>>24),\
                            (byte)(limb64>>32),(byte)(limb64>>40),\
                            (byte)(limb64>>48),(byte)(limb64>>56)
typedef byte pow256[256/8];

/*
 * Internal Boolean type, Bolean by value, hence safe to cast to or
 * reinterpret as 'bool'.
 */
typedef limb_t bool_t;

/*
 * Assembly subroutines...
 */
#if defined(__ADX__) /* e.g. -march=broadwell */ && !defined(__PASTA_PORTABLE__)
# define mul_mont_pasta mulx_mont_pasta
# define sqr_mont_pasta sqrx_mont_pasta
# define from_mont_pasta fromx_mont_pasta
# define redc_mont_pasta redcx_mont_pasta
#endif

void mul_mont_pasta(vec256 ret, const vec256 a, const vec256 b,
                                const vec256 p, limb_t n0);
void sqr_mont_pasta(vec256 ret, const vec256 a, const vec256 p, limb_t n0);
void redc_mont_pasta(vec256 ret, const vec512 a, const vec256 p, limb_t n0);
void from_mont_pasta(vec256 ret, const vec256 a, const vec256 p, limb_t n0);

void pasta_add(vec256 ret, const vec256 a, const vec256 b, const vec256 p);
void pasta_sub(vec256 ret, const vec256 a, const vec256 b, const vec256 p);
void pasta_cneg(vec256 ret, const vec256 a, bool_t flag, const vec256 p);
void pasta_lshift(vec256 ret, const vec256 a, size_t count, const vec256 p);
void pasta_rshift(vec256 ret, const vec256 a, size_t count, const vec256 p);

void ct_inverse_pasta(vec512 ret, const vec256 inp, const vec256 mod,
                                                    const vec256 modx);

/*
 * C subroutines
 */
#if defined(ZAKURA_PASTA_MSM_BASELINE_BACKEND)
# define pasta_from_scalar pasta_from_scalar_baseline
# define pasta_to_scalar pasta_to_scalar_baseline
# define pasta_mul pasta_mul_baseline
# define pasta_sqr pasta_sqr_baseline
# define pasta_from pasta_from_baseline
# define pasta_reciprocal pasta_reciprocal_baseline
#elif defined(ZAKURA_PASTA_MSM_ADX_BACKEND)
# define pasta_from_scalar pasta_from_scalar_adx
# define pasta_to_scalar pasta_to_scalar_adx
# define pasta_mul pasta_mul_adx
# define pasta_sqr pasta_sqr_adx
# define pasta_from pasta_from_adx
# define pasta_reciprocal pasta_reciprocal_adx
#endif

void pasta_reciprocal(vec256 ret, const vec256 a, const vec256 p, limb_t n0);
void pasta_mul(vec256 out, const vec256 a, const vec256 b,
                           const vec256 p, limb_t n0);
void pasta_sqr(vec256 out, const vec256 a, const vec256 p, limb_t n0);
void pasta_from(vec256 out, const vec256 a, const vec256 p, limb_t n0);
void pasta_to_scalar(pow256 ret, const vec256 a, const vec256 p, limb_t n0);

#ifdef __UINTPTR_TYPE__
typedef __UINTPTR_TYPE__ uptr_t;
#else
typedef const void *uptr_t;
#endif

#if !defined(restrict)
# if !defined(__STDC_VERSION__) || __STDC_VERSION__<199901
#  if defined(__GNUC__) && __GNUC__>=2
#   define restrict __restrict__
#  elif defined(_MSC_VER)
#   define restrict __restrict
#  else
#   define restrict
#  endif
# endif
#endif

#if !defined(inline) && !defined(__cplusplus)
# if !defined(__STDC_VERSION__) || __STDC_VERSION__<199901
#  if defined(__GNUC__) && __GNUC__>=2
#   define inline __inline__
#  elif defined(_MSC_VER)
#   define inline __inline
#  else
#   define inline
#  endif
# endif
#endif

#if defined(__GNUC__) || defined(__clang__)
# define launder(var) asm volatile("" : "+r"(var))
#else
# define launder(var)
#endif

static inline bool_t is_bit_set(const byte *v, size_t i)
{
    bool_t ret = (v[i/8] >> (i%8)) & 1;
    launder(ret);
    return ret;
}

static inline bool_t byte_is_zero(unsigned char c)
{
    limb_t ret = ((limb_t)(c) - 1) >> (LIMB_T_BITS - 1);
    launder(ret);
    return ret;
}

static inline bool_t bytes_are_zero(const unsigned char *a, size_t num)
{
    unsigned char acc;
    size_t i;

    for (acc = 0, i = 0; i < num; i++)
        acc |= a[i];

    return byte_is_zero(acc);
}

static inline void vec_cswap(void *restrict a, void *restrict b, size_t num,
                             bool_t cbit)
{
    limb_t ai, *ap = (limb_t *)a;
    limb_t bi, *bp = (limb_t *)b;
    limb_t xorm, mask = (limb_t)0 - cbit;
    size_t i;

    num /= sizeof(limb_t);

    for (i = 0; i < num; i++) {
        xorm = ((ai = ap[i]) ^ (bi = bp[i])) & mask;
        ap[i] = ai ^ xorm;
        bp[i] = bi ^ xorm;
    }
}

/* ret = bit ? a : b */
void vec_select_32(void *ret, const void *a, const void *b, bool_t sel_a);
void vec_select_64(void *ret, const void *a, const void *b, bool_t sel_a);
void vec_select_96(void *ret, const void *a, const void *b, bool_t sel_a);
void vec_select_128(void *ret, const void *a, const void *b, bool_t sel_a);
static inline void vec_select(void *ret, const void *a, const void *b,
                              size_t num, bool_t sel_a)
{
    launder(sel_a);
#if 0
    if (num == 32)          vec_select_32(ret, a, b, sel_a);
    else if (num == 64)     vec_select_64(ret, a, b, sel_a);
    else if (num == 97)     vec_select_964(ret, a, b, sel_a);
    else if (num == 128)    vec_select_128(ret, a, b, sel_a);
#else
    if (0) ;
#endif
    else {
        limb_t bi, *rp = (limb_t *)ret;
        const limb_t *ap = (const limb_t *)a;
        const limb_t *bp = (const limb_t *)b;
        limb_t xorm, mask = (limb_t)0 - sel_a;
        size_t i;

        num /= sizeof(limb_t);

        for (i = 0; i < num; i++) {
            xorm = (ap[i] ^ (bi = bp[i])) & mask;
            rp[i] = bi ^ xorm;
        }
    }
}

static inline bool_t is_zero(limb_t l)
{
    limb_t ret = (~l & (l - 1)) >> (LIMB_T_BITS - 1);
    launder(ret);
    return ret;
}

static inline bool_t vec_is_zero(const void *a, size_t num)
{
    const limb_t *ap = (const limb_t *)a;
    limb_t acc;
    size_t i;

    num /= sizeof(limb_t);

    for (acc = 0, i = 0; i < num; i++)
        acc |= ap[i];

    return is_zero(acc);
}

static inline bool_t vec_is_equal(const void *a, const void *b, size_t num)
{
    const limb_t *ap = (const limb_t *)a;
    const limb_t *bp = (const limb_t *)b;
    limb_t acc;
    size_t i;

    num /= sizeof(limb_t);

    for (acc = 0, i = 0; i < num; i++)
        acc |= ap[i] ^ bp[i];

    return is_zero(acc);
}

static inline void vec_copy(void *restrict ret, const void *a, size_t num)
{
    limb_t *rp = (limb_t *)ret;
    const limb_t *ap = (const limb_t *)a;
    size_t i;

    num /= sizeof(limb_t);

    for (i = 0; i < num; i++)
        rp[i] = ap[i];
}

static inline void vec_zero(void *ret, size_t num)
{
    volatile limb_t *rp = (volatile limb_t *)ret;
    size_t i;

    num /= sizeof(limb_t);

    for (i = 0; i < num; i++)
        rp[i] = 0;

#if defined(__GNUC__)
    asm volatile("" : : "r"(ret) : "memory");
#endif
}

#if defined(__GNUC__)
# ifndef alloca
#  define alloca(s) __builtin_alloca(s)
# endif
#elif defined(__sun)
# include <alloca.h>
#elif defined(_WIN32)
# include <malloc.h>
# ifndef alloca
#  define alloca(s) _alloca(s)
# endif
#endif

#endif /* __PASTA_ASM_VECT_H__ */
