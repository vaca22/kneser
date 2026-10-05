#!/usr/bin/env python3
"""Rigorous Arb enclosure of a = Phi_att(1/e-1) for f(u)=exp(u)-1.

The formal Abel coefficients are computed with exact rational power series.
The residual of the truncated Abel function vanishes to order N+2.  An Arb
bound on the circle |u|=1/2 and the maximum-modulus principle bound the
residual on the attracting orbit.  No floating-point orbit data enter the
certificate.
"""

from fractions import Fraction
from math import factorial

from flint import acb, arb, ctx, fmpq

ctx.dps = 80
N = 10
DEG = N + 2
SIZE = DEG + 2
I = acb(0, 1)


def mul(a, b):
    out = [Fraction(0)] * SIZE
    for i, x in enumerate(a):
        if not x:
            continue
        for j, y in enumerate(b):
            if i + j >= SIZE:
                break
            out[i + j] += x * y
    return out


def formal_coefficients():
    """Solve alpha(f)-alpha=1 to order u^(N+1), exactly."""
    q = [Fraction(1, factorial(k + 1)) for k in range(SIZE)]  # f(u)/u
    inv = [Fraction(0)] * SIZE
    inv[0] = 1
    for n in range(1, SIZE):
        inv[n] = -sum(q[j] * inv[n-j] for j in range(1, n+1))
    v = q[:]
    v[0] = 0
    logq = [Fraction(0)] * SIZE
    power = [Fraction(1)] + [Fraction(0)] * (SIZE-1)
    for k in range(1, SIZE):
        power = mul(power, v)
        for j in range(1, SIZE):
            logq[j] += Fraction((-1)**(k+1), k) * power[j]
    # 1 - (-2/f+2/u) - log(f/u)/3.
    remainder = [
        (Fraction(1) if k == 0 else Fraction(0))
        + 2*inv[k+1] - logq[k]/3
        for k in range(DEG+1)
    ] + [Fraction(0)]
    f = [Fraction(0)] + q[:SIZE-1]
    power = [Fraction(1)] + [Fraction(0)] * (SIZE-1)
    coeffs = []
    for k in range(1, N+1):
        power = mul(power, f)
        delta = power[:]
        delta[k] -= 1
        assert delta[k+1] == Fraction(k, 2)
        c = remainder[k+1] / delta[k+1]
        coeffs.append(c)
        for j in range(DEG+1):
            remainder[j] -= c*delta[j]
    assert all(remainder[j] == 0 for j in range(N+2))
    return coeffs


def arb_fraction(q):
    return arb(q.numerator) / q.denominator


def residual(u, coeffs):
    f = u.exp() - 1
    q = f/u
    result = -2/f + 2/u - 1 + q.log()/3
    for k, c in enumerate(coeffs, 1):
        result += arb_fraction(c) * (f**k-u**k)
    return result


def circle_bound(coeffs):
    """Bound the residual on |u|=1/2 by 128 outward-rounded arcs."""
    radius = arb(fmpq(1, 2))
    bound = arb(0)
    for j in range(128):
        angle = arb.pi() * arb(fmpq(2*j+1, 128), fmpq(1, 128))
        u = radius*(I*angle).exp()
        assert abs((u.exp()-1)/u-1) < arb(fmpq(1, 2))
        value = abs(residual(u, coeffs))
        if value.upper() > bound.upper():
            bound = value
    assert bound < arb(fmpq(1, 2))
    return bound.upper()


def certify():
    coeffs = formal_coefficients()
    circle = circle_bound(coeffs)
    u = 1/arb(1).exp()-1
    for _ in range(1000):
        u = u.exp()-1
    x = -u
    assert 0 < x and x < arb(fmpq(1, 2))
    estimate = -2/u + (-u).log()/3 - 1000
    for k, c in enumerate(coeffs, 1):
        estimate += arb_fraction(c)*u**k
    # If x_0=x, then x_{k+1}=1-exp(-x_k)<=x_k-x_k^2/3 for x_k<=1.
    # Hence x_k <= (1/x+k/3)^-1 and
    # sum_{k>=0} x_k^(N+2) <= x^(N+2)+3*x^(N+1)/(N+1).
    error = circle / arb(fmpq(1, 2))**(N+2) * (
        x**(N+2)+3*x**(N+1)/(N+1)
    )
    enclosure = arb(estimate.mid(), estimate.rad()+error.upper())
    lo = arb('3.0292972144180360989249938')
    hi = arb('3.0292972144180360989249940')
    assert enclosure.lower() > lo and enclosure.upper() < hi
    print('PASS exact Abel coefficients:', coeffs)
    print('PASS residual bound on |u|=1/2:', circle)
    print('PASS tail error:', error)
    print('PASS a in (3.0292972144180360989249938, '
          '3.0292972144180360989249940)')
    print('Arb enclosure:', enclosure)


if __name__ == '__main__':
    certify()
