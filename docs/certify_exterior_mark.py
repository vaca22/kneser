#!/usr/bin/env python3
"""Ball-arithmetic certificate for one exterior marked-curve corridor.

Validated with python-flint 0.9.0 / FLINT 3.6.0.  All inputs are exact
rationals; arb/acb operations enclose their true values with outward
rounding.  The mathematical reduction
from the checked inequalities to membership in the initial region is stated
in Proposition `exterior-marked-path` of paper-submission/main.tex.
"""

from flint import acb, arb, ctx, fmpq


ctx.dps = 80
P = fmpq(1, 10)
Q = fmpq(1667, 1_000_000)
STEPS = 28
SLABS = 1000
I = acb(0, 1)


def theta(q):
    return acb(arb(P), q)


def lam_plus(th):
    return th * th.cos() / th.sin() + I * th


def squared_modulus(z):
    return z.real * z.real + z.imag * z.imag


def arc_s(th, t):
    return ((I * th * t).exp() - th.cos()) / (I * th.sin())


def rational_ball(j):
    """An enclosing ball for [j Q/N, (j+1) Q/N]."""
    mid = Q * fmpq(2 * j + 1, 2 * SLABS)
    rad = Q * fmpq(1, 2 * SLABS)
    return arb(mid, rad)


def main():
    # For all t in [-1,1], the interpolation remainder is
    # e^(i theta t)-cos(theta)-i t sin(theta)
    #   = (1-t^2) theta^2 H(theta,t),
    # where |H-1/2| <= (e^R-1-R)/(2R) if |theta|<=R.
    # The bound follows termwise: the nth divided polynomial is <= n/2.
    R = arb(fmpq(101, 1000))
    assert arb(P * P + Q * Q) < R * R
    h_error = (R.exp() - 1 - R) / (2 * R)
    sin_error = R.sinh() / R - 1
    assert h_error < arb("0.027")
    assert sin_error < arb("0.002")
    a_error = h_error / (1 - sin_error) + sin_error / (2 * (1 - sin_error))
    assert arb(P) / 2 - R * a_error > arb("0.04")
    # Thus Im s_theta(t) < -0.04 (1-t^2) for -1<t<1.

    q_all = arb(Q / 2, Q / 2)
    th_all = theta(q_all)
    t_all = arb(0, 1)
    s_prime = th_all * (I * th_all * t_all).exp() / th_all.sin()
    assert s_prime.real > arb("0.98")
    assert arc_s(th_all, arb(fmpq(-1, 10))).real < arb("-0.08")
    assert arc_s(th_all, arb(fmpq(1, 10))).real > arb("0.08")
    # The arc is a graph over the chord, and at horizontal coordinates
    # between -0.01 and 0.04 its height is below -0.0396.

    lp_zero = lam_plus(theta(arb(0)))
    lp_max = lam_plus(theta(arb(Q)))
    assert squared_modulus(lp_zero) > arb(1)
    assert squared_modulus(lp_max) < arb(1)
    dlam_dq = I * (
        th_all.cos() / th_all.sin()
        - th_all / (th_all.sin() * th_all.sin())
        + I
    )
    dG_dq = 2 * (lam_plus(th_all).conjugate() * dlam_dq).real
    assert dG_dq < arb(-1)
    # There is exactly one q_c in (0,Q) with |lambda_+|=1.

    bounds = [float("inf"), float("-inf"), float("inf"), float("-inf")]
    for j in range(SLABS):
        q = rational_ball(j)
        th = theta(q)
        sine, cosine = th.sin(), th.cos()
        cot = cosine / sine
        r = (th * cot).exp()
        a = th * (-th * cot).exp() / sine
        lp = th * cot + I * th
        lm = th * cot - I * th
        assert squared_modulus(lm) > arb("1.003")

        # The image b(theta(q)) is an embedded arc: Im db/dq > 0.05.
        dlam_dtheta = cot - th / (sine * sine) + I
        b = a.exp()
        db_dq = I * b * (-lp).exp() * (1 - lp) * dlam_dtheta
        assert db_dq.imag > arb("0.05")

        w = acb(1)
        for _ in range(STEPS):
            w = (a * w).exp()
        zeta = (w / r - cosine) / (I * sine)
        assert zeta.real > arb("-0.01")
        assert zeta.real < arb("0.04")
        assert zeta.imag > arb("-0.03")
        assert zeta.imag < arb("-0.01")
        bounds[0] = min(bounds[0], float(zeta.real.lower()))
        bounds[1] = max(bounds[1], float(zeta.real.upper()))
        bounds[2] = min(bounds[2], float(zeta.imag.lower()))
        bounds[3] = max(bounds[3], float(zeta.imag.upper()))

    print("CERTIFIED p=1/10, 0<=q<=1667/1000000, 28 iterates, 1000 slabs")
    print("unique q_c in (0,1667/1000000); both ends repelling for q<q_c")
    print("initial curve is Jordan; the parameter path has Im(db/dq)>0.05")
    print("w_28=E_b^28(1) lies strictly inside H_theta throughout the path")
    print("enclosed zeta bounds (display floats only):", bounds)


if __name__ == "__main__":
    main()
