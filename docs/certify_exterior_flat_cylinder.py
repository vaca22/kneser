#!/usr/bin/env python3
"""Arb certificate for a global near-flat cylinder coordinate on H_theta.

The certificate covers the prescribed Brjuno vertical path from
certify_brjuno_exterior_mark.py, including its boundary endpoint.  In
the chord coordinate, write the initial region as the interpolation
between t and s_theta(t), with -1<t<1 and 0<x<1.  Set

    z = x + 20 i atanh(t),
    Z_theta(z) = t + x (s_theta(t)-t).

The bounds below prove |mu_{Z_theta}| < 1/10 uniformly.  Decimal
constants are exact rationals.  Validated with python-flint 0.9.0 and
FLINT 3.6.0.  Printed floats are only diagnostics, not certificate
inputs.
"""

from math import factorial

from flint import acb, arb, ctx, fmpq


ctx.dps = 80
I = acb(0, 1)
P_CENTER = fmpq(1000435842, 10_000_000_000)
P_RADIUS = fmpq(1, 100_000_000)
Q_MAX = fmpq(166823, 100_000_000)
R = fmpq(102, 1000)
SERIES_STOP = 12


def ball_power(x, n):
    """Repeated multiplication avoids a python-flint 0.9.0 power edge case.

    In this version, ``arb(0, 1) ** n`` can return NaN for n > 0 even
    though direct ball multiplication is well-defined.
    """
    value = arb(1)
    for _ in range(n):
        value *= x
    return value


def interpolation_h(theta, t):
    """Enclose H in exp(i theta t)-cos(theta)-i t sin(theta)
    = (1-t^2) theta^2 H, including t = +/-1 by continuation.
    """
    result = acb(0)
    for n in range(2, SERIES_STOP):
        half = n // 2
        polynomial = sum(
            (ball_power(t, 2 * j) for j in range(half)), arb(0)
        )
        if n % 2:
            polynomial *= t
        result -= (I ** n) * (theta ** (n - 2)) * polynomial / factorial(n)

    radius = arb(R)
    assert (
        arb(P_CENTER + P_RADIUS) ** 2 + arb(Q_MAX) ** 2
        < radius * radius
    )
    n = SERIES_STOP
    tail = radius ** (n - 2) / (
        2 * factorial(n - 1) * (1 - radius / n)
    )
    # The tail is bounded in modulus; its real and imaginary parts are
    # each therefore in [-tail, tail].
    return result + acb(arb(0, tail), arb(0, tail)), tail


def main():
    p = arb(P_CENTER, arb(P_RADIUS))
    q = arb(Q_MAX / 2, arb(Q_MAX / 2))
    theta = acb(p, q)
    t = arb(0, 1)
    x = arb(fmpq(1, 2), arb(fmpq(1, 2)))

    h, tail = interpolation_h(theta, t)
    d = theta * theta * h / (I * theta.sin())
    a = 1 + x * (theta * (I * theta * t).exp() / theta.sin() - 1)

    # The chord-coordinate interpolation has derivatives
    # Z_x=(1-t^2) D and Z_y=(1-t^2) A for t=tanh(y).  The common
    # factor cancels from its Beltrami coefficient in z=x+20 i y.
    mu = (d + I * a / 20) / (d - I * a / 20)
    assert abs(mu) < arb(fmpq(1, 10))

    print("CERTIFIED |mu| < 1/10 on the full marked Brjuno path")
    print("flat cylinder z=x+20i atanh(t), 0<=x<=1, -1<t<1")
    print("quasiconformal dilatation K < 11/9")
    print("H series tail modulus bound (display float only):", float(tail.upper()))
    print("mu enclosure (display float only):", str(mu))


if __name__ == "__main__":
    main()
