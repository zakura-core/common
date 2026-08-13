// Copyright Supranational LLC
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Modified by Zakura to retain only caller-thread affine and XYZZ formulas.

#ifndef ZAKURA_PASTA_MSM_SPPARK_CURVE_HPP
#define ZAKURA_PASTA_MSM_SPPARK_CURVE_HPP

template<class field_t>
class affine_t {
public:
    field_t X, Y;

    affine_t() = default;
    affine_t(const field_t& x, const field_t& y) : X(x), Y(y) {}

    bool is_inf() const
    {   return static_cast<bool>(static_cast<int>(X.is_zero()) &
                                static_cast<int>(Y.is_zero()));   }

    void cneg(bool negative) { Y.cneg(negative); }
};

template<class field_t>
class xyzz_t {
    field_t X, Y, ZZZ, ZZ;

public:
    using affine_type = affine_t<field_t>;

    xyzz_t() = default;
    xyzz_t(const field_t& x, const field_t& y, bool is_inf) :
        X(x), Y(y), ZZZ(field_t::one(is_inf)), ZZ(ZZZ) {}

    xyzz_t& operator=(const affine_type& point)
    {
        X = point.X;
        Y = point.Y;
        ZZZ = ZZ = field_t::one(point.is_inf());
        return *this;
    }

    bool is_inf() const
    {   return static_cast<bool>(static_cast<int>(ZZZ.is_zero()) &
                                static_cast<int>(ZZ.is_zero()));   }

    void inf() { ZZZ.zero(); ZZ.zero(); }

    affine_type to_affine() const
    {
        if (is_inf()) {
            field_t zero;
            zero.zero();
            return affine_type{zero, zero};
        }

        field_t y = 1 / ZZZ;
        field_t x = y * ZZ;
        x = x ^ 2;
        x *= X;
        y *= Y;
        return affine_type{x, y};
    }

    void add(const xyzz_t& other)
    {
        if (other.is_inf()) {
            return;
        }
        if (is_inf()) {
            *this = other;
            return;
        }

        field_t U = X * other.ZZ;
        field_t S = Y * other.ZZZ;
        field_t P = other.X * ZZ;
        field_t R = other.Y * ZZZ;
        P -= U;
        R -= S;

        if (!P.is_zero()) {
            field_t PP = P ^ 2;
            P = P * PP;
            ZZ *= PP;
            ZZZ *= P;
            PP = U * PP;
            X = R ^ 2;
            X -= P;
            X -= PP;
            X -= PP;
            PP -= X;
            PP *= R;
            Y = S * P;
            Y = PP - Y;
            ZZ *= other.ZZ;
            ZZZ *= other.ZZZ;
        } else if (R.is_zero()) {
            field_t U2 = Y + Y;
            P = U2 ^ 2;
            R = U2 * P;
            S = X * P;
            field_t M = X ^ 2;
            M = M + M + M;
            X = M ^ 2;
            X -= S;
            X -= S;
            Y *= R;
            S -= X;
            S *= M;
            Y = S - Y;
            ZZ *= P;
            ZZZ *= R;
        } else {
            inf();
        }
    }

    void dbl()
    {
        xyzz_t copy = *this;
        add(copy);
    }

    void add(const affine_type& point, bool subtract = false)
    {
        if (point.is_inf()) {
            return;
        }
        if (is_inf()) {
            *this = point;
            ZZZ.cneg(subtract);
            return;
        }

        field_t R = point.Y * ZZZ;
        R.cneg(subtract);
        R -= Y;
        field_t P = point.X * ZZ;
        P -= X;

        if (!P.is_zero()) {
            field_t PP = P ^ 2;
            P = P * PP;
            ZZ *= PP;
            ZZZ *= P;
            PP *= X;
            X = R ^ 2;
            X -= P;
            X -= PP;
            X -= PP;
            PP -= X;
            PP *= R;
            Y *= P;
            Y = PP - Y;
        } else if (R.is_zero()) {
            P = point.Y + point.Y;
            ZZ = P ^ 2;
            ZZZ = ZZ * P;
            R = point.X * ZZ;
            field_t M = point.X ^ 2;
            M = M + M + M;
            X = M ^ 2;
            X -= R;
            X -= R;
            Y = ZZZ * point.Y;
            R -= X;
            R *= M;
            Y = R - Y;
            ZZZ.cneg(subtract);
        } else {
            inf();
        }
    }
};

#endif
