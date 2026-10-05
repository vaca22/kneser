#!/usr/bin/env python3
"""Interval certificate for an unmarked exterior crescent on a full cone.

Parameter: theta = p(1+i*u), 0 < p <= 0.100044, 0 <= u <= 0.1.
For the chord gamma_theta(t) and its exponential image, this checks:

* Re(s_theta'(t)) > 0.98, so the image arc is a graph;
* Im((s_theta(t)-t)/(p(1-t*t))) < -0.4, so it lies below the chord;
* the straight interpolation, with flat height (2/p)*atanh(t), has
  Beltrami coefficient of modulus < 0.1 on the whole cylinder.
* b(theta)=B(theta^2) with Re(B')>1/4 on |theta^2|<=0.0104;
  hence the complex-base parameter is injective on the cone.

All interval inputs are exact rationals. FLINT/Arb operations are outward
rounded. The final assertions, not the printed floats, are the certificate.
The certificate concerns the unmarked quotient; it does not locate the
orbit of 1 or identify a height germ.
"""

from math import factorial

from flint import acb, arb, ctx, fmpq


ctx.dps = 60
I = acb(0, 1)
P_MAX = fmpq(100044, 1000000)
R = arb(fmpq(102, 1000))
SERIES_STOP = 12


def ball(lo, hi):
    """Outward enclosure of the rational interval [lo, hi]."""
    return arb((lo + hi) / 2, (hi - lo) / 2)


def ball_power(x, n):
    """Repeated multiplication avoids a python-flint 0.9.0 power edge case."""
    result = arb(1)
    for _ in range(n):
        result *= x
    return result


def interpolation_h(theta, t):
    """(exp(i theta t)-cos(theta)-i t sin(theta))/((1-t*t)theta^2).

    The polynomial quotient at order n is bounded by n/2 on [-1,1].
    This is the same expansion and tail estimate used in the existing
    certify_exterior_flat_cylinder.py, now applied to the whole cone.
    """
    result = acb(0)
    for n in range(2, SERIES_STOP):
        polynomial = sum(
            (ball_power(t, 2 * j) for j in range(n // 2)), arb(0)
        )
        if n % 2:
            polynomial *= t
        result -= I**n * theta ** (n - 2) * polynomial / factorial(n)
    n = SERIES_STOP
    tail = R ** (n - 2) / (2 * factorial(n - 1) * (1 - R / n))
    return result + acb(arb(0, tail), arb(0, tail))


def theta_over_sin(theta):
    """Enclose theta/sin(theta) via the regular Taylor series at zero."""
    denominator = acb(0)
    for k in range(6):
        denominator += (-1) ** k * theta ** (2 * k) / factorial(2 * k + 1)
    # First omitted term has order theta^12/13!; later ratios are <= R^2/(14*15).
    tail = R**12 / factorial(13) / (1 - R**2 / (14 * 15))
    denominator += acb(arb(0, tail), arb(0, tail))
    return 1 / denominator


def base_derivative_on_squared_disk():
    """Enclose B'(v), B(v)=exp((sin(sqrt(v))/sqrt(v))^-1
    * exp(-cos(sqrt(v))/(sin(sqrt(v))/sqrt(v)))) on |v|<=0.0104.
    """
    radius = arb(fmpq(104, 10000))
    v = acb(arb(0, radius), arb(0, radius))
    sine_ratio = acb(0)
    sine_ratio_derivative = acb(0)
    cosine = acb(0)
    cosine_derivative = acb(0)
    for k in range(7):
        sine_ratio += (-1) ** k * v**k / factorial(2 * k + 1)
        cosine += (-1) ** k * v**k / factorial(2 * k)
        if k:
            sine_ratio_derivative += (
                (-1) ** k * k * v ** (k - 1) / factorial(2 * k + 1)
            )
            cosine_derivative += (
                (-1) ** k * k * v ** (k - 1) / factorial(2 * k)
            )
    sine_tail = radius**7 / factorial(15) / (1 - radius / (16 * 17))
    cosine_tail = radius**7 / factorial(14) / (1 - radius / (15 * 16))
    sine_derivative_tail = (
        7 * radius**6 / factorial(15) / (1 - 2 * radius / (16 * 17))
    )
    cosine_derivative_tail = (
        7 * radius**6 / factorial(14) / (1 - 2 * radius / (15 * 16))
    )
    sine_ratio += acb(arb(0, sine_tail), arb(0, sine_tail))
    cosine += acb(arb(0, cosine_tail), arb(0, cosine_tail))
    sine_ratio_derivative += acb(
        arb(0, sine_derivative_tail), arb(0, sine_derivative_tail)
    )
    cosine_derivative += acb(
        arb(0, cosine_derivative_tail), arb(0, cosine_derivative_tail)
    )

    ratio = 1 / sine_ratio
    ratio_derivative = -sine_ratio_derivative / sine_ratio**2
    a = ratio * (-cosine * ratio).exp()
    a_derivative = (-cosine * ratio).exp() * (
        ratio_derivative
        - ratio * (cosine_derivative * ratio + cosine * ratio_derivative)
    )
    return a.exp() * a_derivative


def main():
    # |theta|^2 = p^2(1+u^2) < R^2 throughout the closed parameter cone.
    assert arb(P_MAX * P_MAX * fmpq(101, 100)) < R * R
    assert arb(P_MAX * P_MAX * fmpq(101, 100)) < arb(fmpq(104, 10000))
    base_derivative = base_derivative_on_squared_disk()
    assert base_derivative.real > arb(fmpq(1, 4))

    min_arc_slope = float("inf")
    max_arc_height_factor = float("-inf")
    max_mu = 0.0

    for jp in range(48):
        p = ball(P_MAX * jp / 48, P_MAX * (jp + 1) / 48)
        for ju in range(8):
            u = ball(fmpq(ju, 80), fmpq(ju + 1, 80))
            theta = acb(p, p * u)
            ratio = theta_over_sin(theta)
            for jt in range(16):
                t = ball(-1 + fmpq(jt, 8), -1 + fmpq(jt + 1, 8))
                h = interpolation_h(theta, t)
                # D = (s_theta(t)-t)/(p(1-t^2)), with analytic continuation
                # at p=0 and t=+/-1. s_theta'(t)=ratio*exp(i theta t).
                d = (1 + I * u) * ratio * h / I
                s_prime = ratio * (I * theta * t).exp()
                assert d.imag < arb(fmpq(-2, 5))
                assert s_prime.real > arb(fmpq(49, 50))
                min_arc_slope = min(min_arc_slope, float(s_prime.real.lower()))
                max_arc_height_factor = max(
                    max_arc_height_factor, float(d.imag.upper())
                )

                for jx in range(4):
                    x = ball(fmpq(jx, 4), fmpq(jx + 1, 4))
                    a = 1 + x * (s_prime - 1)
                    # Z(x+i y)=t+x(s_theta(t)-t), y=(2/p)atanh(t).
                    # The factor p(1-t^2) cancels from Z_x and Z_y.
                    mu = (d + I * a / 2) / (d - I * a / 2)
                    assert abs(mu) < arb(fmpq(1, 10))
                    max_mu = max(max_mu, float(abs(mu).upper()))

    print("PASS unmarked Jordan crescent and K<11/9 quotient cylinder")
    print("0<p<=0.100044, 0<=Im(theta)/Re(theta)<=0.1")
    print("display-only min Re s_prime:", min_arc_slope)
    print("display-only max Im normalized arc displacement:", max_arc_height_factor)
    print("display-only max |mu|:", max_mu)
    print("display-only min Re B_prime:", float(base_derivative.real.lower()))


if __name__ == "__main__":
    main()
