#!/usr/bin/env python3
"""Arb certificate for a wide analytic exterior germ corridor.

The closed parameter box is |Re(theta)-0.1000435842| <= 1e-8 and
|Im(theta)| <= 0.01.  It contains the short non-cusp neutral arc and
extends well to both sides.  Every decimal bound is an exact rational;
all inequalities are checked with outward-rounded Arb/Acb balls.

Validated with python-flint 0.9.0 and FLINT 3.6.0.  This certifies the
geometric quotient and the marked local germ, not a common height
domain containing [0,1].
"""

from flint import acb, arb, ctx, fmpq

from certify_exterior_flat_cylinder import interpolation_h


ctx.dps = 80
I = acb(0, 1)
P_CENTER = fmpq(1000435842, 10_000_000_000)
P_RADIUS = fmpq(1, 100_000_000)
Q = fmpq(1, 100)
R = arb(fmpq(102, 1000))


def q_ball(j, n):
    return arb(-Q + Q * fmpq(2 * j + 1, n), arb(Q / n))


def t_ball(j, n):
    return arb(-1 + fmpq(2 * j + 1, n), arb(fmpq(1, n)))


def x_ball(j, n):
    return arb(fmpq(2 * j + 1, 2 * n), arb(fmpq(1, 2 * n)))


def arc_s(theta, t):
    return ((I * theta * t).exp() - theta.cos()) / (I * theta.sin())


def main():
    p = arb(P_CENTER, arb(P_RADIUS))
    assert arb(P_CENTER + P_RADIUS) ** 2 + arb(Q) ** 2 < R * R

    # Whole-arc graph bound, with the endpoint factor (1-t^2) removed.
    h_error = (R.exp() - 1 - R) / (2 * R)
    sin_error = R.sinh() / R - 1
    a_error = h_error / (1 - sin_error) + sin_error / (2 * (1 - sin_error))
    assert arb(P_CENTER - P_RADIUS) / 2 - R * a_error > arb(fmpq(4, 100))

    # The image arc is an increasing graph.  The horizontal mark range
    # [-.25,.25] corresponds to an arc parameter inside [-.27,.27].
    for j in range(40):
        theta = acb(p, q_ball(j, 40))
        assert arc_s(theta, arb(fmpq(-27, 100))).real < arb(fmpq(-25, 100))
        assert arc_s(theta, arb(fmpq(27, 100))).real > arb(fmpq(25, 100))
        for k in range(32):
            t = t_ball(k, 32)
            s_prime = theta * (I * theta * t).exp() / theta.sin()
            assert s_prime.real > arb(fmpq(98, 100))

    # Full-cylinder Beltrami estimate on the larger box.  Subdivision
    # controls dependency in q, t, and x while retaining exact coverage.
    mu_upper = 0.0
    for j in range(40):
        theta = acb(p, q_ball(j, 40))
        sine = theta.sin()
        for k in range(16):
            t = t_ball(k, 16)
            h, _ = interpolation_h(theta, t)
            d = theta * theta * h / (I * sine)
            s_prime = theta * (I * theta * t).exp() / sine
            for m in range(8):
                x = x_ball(m, 8)
                a = 1 + x * (s_prime - 1)
                mu = (d + I * a / 20) / (d - I * a / 20)
                assert abs(mu) < arb(fmpq(1, 10))
                mu_upper = max(mu_upper, float(abs(mu).upper()))

    # The marked iterate stays in the lens, and every singular value
    # of E_b^28 stays strictly above its chord.  The 5000 slabs keep
    # interval growth under 28 exponential iterates under control.
    singular_lower = 1.0
    bprime_lower = 1.0
    for j in range(5000):
        theta = acb(p, q_ball(j, 5000))
        sine, cosine = theta.sin(), theta.cos()
        cot = cosine / sine
        r = (theta * cot).exp()
        a = theta * (-theta * cot).exp() / sine
        lam_plus = theta * cot + I * theta
        lam_minus = theta * cot - I * theta
        assert lam_plus.real > arb(fmpq(9, 10))
        assert lam_minus.real > arb(fmpq(9, 10))
        assert lam_plus.imag > arb(fmpq(9, 100))
        assert lam_minus.imag < arb(fmpq(-9, 100))
        assert (-1 / (10 * lam_plus.log())).imag > arb(fmpq(98, 100))
        assert (1 / (10 * lam_minus.log())).imag > arb(fmpq(98, 100))
        dlam_dtheta = cot - theta / (sine * sine) + I
        b = a.exp()
        db_dq = I * b * (-lam_plus).exp() * (1 - lam_plus) * dlam_dtheta
        assert db_dq.imag > arb(fmpq(5, 100))
        bprime_lower = min(bprime_lower, float(db_dq.imag.lower()))

        orbit = acb(0)
        for _ in range(29):
            zeta = (orbit / r - cosine) / (I * sine)
            assert zeta.imag > arb(fmpq(5, 1000))
            singular_lower = min(singular_lower, float(zeta.imag.lower()))
            orbit = (a * orbit).exp()

        mark = acb(1)
        for _ in range(28):
            mark = (a * mark).exp()
        zeta = (mark / r - cosine) / (I * sine)
        assert zeta.real > arb(fmpq(-25, 100))
        assert zeta.real < arb(fmpq(25, 100))
        assert zeta.imag > arb(fmpq(-35, 1000))
        assert zeta.imag < arb(fmpq(-5, 1000))
        # The image arc at this real coordinate lies below
        # -.04*(1-.27^2) < -.037, while the mark is above -.035.

    print("CERTIFIED wide exterior germ corridor |Re(theta)-.1000435842| <= 1e-8, |Im(theta)| <= .01")
    print("Jordan initial cell, E_b^28(1) interior, inverse branch through depth 28")
    print("full cylinder |mu| < 1/10, Re b'(theta) > 0.05")
    print("both limiting seam-height slopes > 0.98")
    print("display-only upper mu enclosure:", mu_upper)
    print("display-only lower singular clearance:", singular_lower)
    print("display-only lower Re b' enclosure:", bprime_lower)


if __name__ == "__main__":
    main()
