#!/usr/bin/env python3
"""Arb certificate for a small-residual frozen Abel coordinate.

On the marked rectangle 0 <= Im(theta) <= 0.00166823 we prove
|A/(20D)-i| < .09 and |P_Y| < .01.  On the wider box
|Im(theta)| <= .01 we prove |A/(20D)-i| < .18 and |P_Y| < .004,
as well as an explicit frozen vertical slope > .98 and a residual
bounded by .001 sech^2(Y/20).  With the periodic Beurling bound
< 6, the paper obtains Im(h_Y) > .93 on the whole wide box.

Validated with python-flint 0.9.0 and FLINT 3.6.0.
"""

from math import factorial

from flint import acb, arb, ctx, fmpq

from certify_exterior_flat_cylinder import (
    SERIES_STOP,
    ball_power,
    interpolation_h,
)


ctx.dps = 80
I = acb(0, 1)
P_CENTER = fmpq(1000435842, 10_000_000_000)
P_RADIUS = fmpq(1, 100_000_000)
Q_MARKED = fmpq(166823, 100_000_000)
Q_WIDE = fmpq(1, 100)


def interval(lo, hi):
    return arb((lo + hi) / 2, arb((hi - lo) / 2))


def t_ball(j, n):
    return interval(fmpq(-1) + fmpq(2 * j, n), fmpq(-1) + fmpq(2 * (j + 1), n))


def x_ball(j, n):
    return interval(fmpq(j, n), fmpq(j + 1, n))


def q_ball_marked(j, n):
    return interval(Q_MARKED * fmpq(j, n), Q_MARKED * fmpq(j + 1, n))


def q_ball_wide(j, n):
    return interval(-Q_WIDE + 2 * Q_WIDE * fmpq(j, n),
                    -Q_WIDE + 2 * Q_WIDE * fmpq(j + 1, n))


def exp_divided_difference(log_b):
    """Enclose (exp(L)-1)/L without division by a ball containing 0."""
    value = acb(0)
    power = acb(1)
    for n in range(9):
        value += power / factorial(n + 1)
        power *= log_b
    radius = arb(fmpq(12, 100))
    assert abs(log_b) < radius
    tail = radius ** 9 / (factorial(10) * (1 - radius / 11))
    return value + acb(arb(0, tail), arb(0, tail))


def interpolation_h_t(theta, t):
    """Derivative in t of the factored interpolation remainder H.

    The tail bound uses |P_n'(t)| <= n^2/4 on -1 <= t <= 1,
    where P_n is the polynomial in interpolation_h.  Consecutive
    majorants from n=12 have ratio at most R/10.
    """
    value = acb(0)
    for n in range(2, SERIES_STOP):
        half = n // 2
        if n % 2:
            derivative = sum(
                ((2 * j + 1) * ball_power(t, 2 * j)
                 for j in range(half)), arb(0)
            )
        else:
            derivative = sum(
                ((2 * j) * ball_power(t, 2 * j - 1)
                 for j in range(1, half)), arb(0)
            )
        value -= (I ** n) * (theta ** (n - 2)) * derivative / factorial(n)
    radius = arb(fmpq(102, 1000))
    tail = 36 * radius ** 10 / (
        factorial(12) * (1 - radius / 10)
    )
    return value + acb(arb(0, tail), arb(0, tail))


def main():
    p = arb(P_CENTER, arb(P_RADIUS))

    # P=A/(20D) in the exact equation h_Y=P h_x.
    p_distance_upper = 0.0
    p_y_upper = 0.0
    for j in range(20):
        theta = acb(p, q_ball_marked(j, 20))
        sine = theta.sin()
        for k in range(32):
            t = t_ball(k, 32)
            h, _ = interpolation_h(theta, t)
            h_t = interpolation_h_t(theta, t)
            d = theta * theta * h / (I * sine)
            d_t = theta * theta * h_t / (I * sine)
            b = theta * (I * theta * t).exp() / sine
            for m in range(8):
                x = x_ball(m, 8)
                a = 1 + x * (b - 1)
                p_coefficient = a / (20 * d)
                assert abs(p_coefficient - I) < arb(fmpq(9, 100))
                p_distance_upper = max(p_distance_upper,
                                       float(abs(p_coefficient - I).upper()))
                a_t = x * I * theta * b
                p_t = (a_t * d - a * d_t) / (20 * d * d)
                p_y = (1 - t * t) * p_t / 20
                assert abs(p_y) < arb(fmpq(1, 100))
                p_y_upper = max(p_y_upper, float(abs(p_y).upper()))

    # The sharper periodic Beurling estimate permits a wider parameter
    # box despite its larger deviation from the flat coefficient i.
    p_wide_upper = 0.0
    p_y_wide_upper = 0.0
    for j in range(80):
        theta = acb(p, q_ball_wide(j, 80))
        sine = theta.sin()
        for k in range(64):
            t = t_ball(k, 64)
            h, _ = interpolation_h(theta, t)
            h_t = interpolation_h_t(theta, t)
            d = theta * theta * h / (I * sine)
            d_t = theta * theta * h_t / (I * sine)
            b = theta * (I * theta * t).exp() / sine
            for m in range(8):
                x = x_ball(m, 8)
                a = 1 + x * (b - 1)
                p_coefficient = a / (20 * d)
                assert abs(p_coefficient - I) < arb(fmpq(18, 100))
                p_wide_upper = max(p_wide_upper,
                                   float(abs(p_coefficient - I).upper()))
                a_t = x * I * theta * b
                p_t = (a_t * d - a * d_t) / (20 * d * d)
                p_y = (1 - t * t) * p_t / 20
                assert abs(p_y) < arb(fmpq(4, 1000))
                p_y_wide_upper = max(p_y_wide_upper,
                                     float(abs(p_y).upper()))

    # L=Log(s') is small.  The frozen vertical slope is
    # c=(exp(L)-1)/(20 D L).  Its imaginary part is strictly positive.
    frozen_slope_lower = 1.0
    for j in range(40):
        theta = acb(p, q_ball_wide(j, 40))
        sine = theta.sin()
        log_prefactor = (theta / sine).log()
        for k in range(32):
            t = t_ball(k, 32)
            log_b = log_prefactor + I * theta * t
            ratio = exp_divided_difference(log_b)
            h, _ = interpolation_h(theta, t)
            d = theta * theta * h / (I * sine)
            slope = ratio / (20 * d)
            assert slope.imag > arb(fmpq(98, 100))
            frozen_slope_lower = min(frozen_slope_lower,
                                     float(slope.imag.lower()))

    # For F(L,x)=Log(1+x(exp(L)-1))/L, the exact integral formula gives
    # |F_L| <= exp(.12) / (8(2-exp(.12))^2).  Since
    # |L_Y| <= .102 sech^2(Y/20)/20, the residual |F_Y| has the
    # following fully explicit envelope.  Its L2 norm on C/Z is
    # bounded using integral sech^4(u) du over R = 4/3.
    radius = arb(fmpq(12, 100))
    exp_radius = radius.exp()
    assert exp_radius < arb(2)
    residual_coefficient = exp_radius * arb(fmpq(102, 1000)) / (
        160 * (2 - exp_radius) ** 2
    )
    assert residual_coefficient < arb(fmpq(1, 1000))
    residual_l2 = residual_coefficient * (arb(fmpq(80, 3))).sqrt()
    assert residual_l2 < arb(fmpq(5, 1000))
    sech8_l4 = (arb(fmpq(640, 35)).sqrt()).sqrt()
    assert residual_coefficient * sech8_l4 < arb(fmpq(2, 1000))

    # The Y derivative of the residual is
    # F_YY = F_LL L_Y^2 + F_L L_YY.  The integral formulas for F_L
    # and F_LL give the following bounds when |L| <= .12:
    # |F_L| <= E/(8 a^2),
    # |F_LL| <= E/(12 a^2) + E^2/(6 a^3),
    # where E=exp(.12), a=2-E.  Both |L_Y| <= .102/20 sech^2
    # and |L_YY| <= .102/200 sech^2.
    a = 2 - exp_radius
    f_l = exp_radius / (8 * a * a)
    f_ll = exp_radius / (12 * a * a) + exp_radius ** 2 / (6 * a ** 3)
    f_yy_coefficient = (
        f_ll * (arb(fmpq(102, 1000)) / 20) ** 2
        + f_l * arb(fmpq(102, 1000)) / 200
    )
    assert f_yy_coefficient < arb(fmpq(12, 100_000))
    assert f_yy_coefficient * sech8_l4 < arb(fmpq(25, 100_000))

    # Rational contraction and local Morrey budgets used in the paper.
    t_norm = fmpq(13, 2)
    p_distance = fmpq(9, 100)
    denominator = 1 - t_norm * p_distance
    assert t_norm * fmpq(2, 1000) / denominator < fmpq(32, 1000)
    assert p_distance * fmpq(32, 1000) + fmpq(2, 1000) < fmpq(5, 1000)
    assert fmpq(32, 1000) + fmpq(5, 1000) == fmpq(37, 1000)
    source = fmpq(1, 100) * fmpq(32, 1000) + fmpq(25, 100_000)
    assert source == fmpq(57, 100_000)
    assert t_norm * source / denominator < fmpq(9, 1000)
    assert fmpq(109, 100) * fmpq(9, 1000) + source < fmpq(11, 1000)
    # At disk radius 1/4, the mean coefficient is (16/pi)^1/4
    # and the gradient coefficient has fourth power 27/(256 pi).
    # Use the elementary rational lower bound pi > 3.14.
    pi_low = fmpq(314, 100)
    assert fmpq(16) / pi_low < fmpq(151, 100) ** 4
    assert fmpq(27) / (256 * pi_low) < fmpq(43, 100) ** 4
    assert (fmpq(151, 100) * fmpq(37, 1000)
            + fmpq(43, 100) * fmpq(20, 1000)) < fmpq(65, 1000)

    # Wide-box contraction and pointwise seam budget.  The planar
    # Beurling bound < 4.725 transfers to the periodic cylinder, so
    # ||T||_4 < (1+6)/2 = 3.5.  All following inequalities are rational.
    t_wide = fmpq(7, 2)
    p_wide = fmpq(18, 100)
    den_wide = 1 - t_wide * p_wide
    assert t_wide * fmpq(2, 1000) / den_wide < fmpq(19, 1000)
    assert p_wide * fmpq(19, 1000) + fmpq(2, 1000) < fmpq(55, 10000)
    assert fmpq(19, 1000) + fmpq(55, 10000) < fmpq(25, 1000)
    source_wide = fmpq(4, 1000) * fmpq(19, 1000) + fmpq(25, 100_000)
    assert source_wide < fmpq(33, 100_000)
    assert t_wide * fmpq(33, 100_000) / den_wide < fmpq(32, 10_000)
    assert (1 + p_wide) * fmpq(32, 10_000) + fmpq(33, 100_000) < fmpq(42, 10_000)
    assert (fmpq(151, 100) * fmpq(25, 1000)
            + fmpq(43, 100) * fmpq(74, 10_000)) < fmpq(41, 1000)
    assert fmpq(98, 100) - fmpq(41, 1000) > fmpq(93, 100)

    print("CERTIFIED marked path |A/(20D)-i| < 0.09")
    print("CERTIFIED marked path |P_Y| < 0.01")
    print("CERTIFIED wide box |A/(20D)-i| < 0.18")
    print("CERTIFIED wide box |P_Y| < 0.004")
    print("CERTIFIED wide box Im(frozen vertical slope) > 0.98")
    print("CERTIFIED frozen-coordinate residual |F_Y| < .001 sech^2(Y/20)")
    print("CERTIFIED residual L2(C/Z) < .005")
    print("CERTIFIED residual derivative |F_YY| < .00012 sech^2(Y/20)")
    print("CERTIFIED residual derivative L4(C/Z) < .00025")
    print("CERTIFIED exact seam derivative Im(h_Y) > 0.9")
    print("CERTIFIED wide-box exact seam derivative Im(h_Y) > 0.93")
    print("display-only upper |P-i|:", p_distance_upper)
    print("display-only upper |P_Y|:", p_y_upper)
    print("display-only wide upper |P-i|:", p_wide_upper)
    print("display-only wide upper |P_Y|:", p_y_wide_upper)
    print("display-only lower frozen slope:", frozen_slope_lower)
    print("display-only residual envelope coefficient:",
          float(residual_coefficient.upper()))
    print("display-only residual derivative coefficient:",
          float(f_yy_coefficient.upper()))


if __name__ == "__main__":
    main()
