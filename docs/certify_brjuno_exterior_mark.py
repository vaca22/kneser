#!/usr/bin/env python3
"""Rigorous marked exterior path to a prescribed Brjuno multiplier.

Target rotation number: alpha = (sqrt(2)-1)/26.  Validated with
python-flint 0.9.0 / FLINT 3.6.0.  All decimal-looking constants below
are represented as exact rationals.  Arb/Acb operations round outward.
"""

from flint import acb, arb, ctx, fmpq


ctx.dps = 80
I = acb(0, 1)
P_CENTER = fmpq(1000435842, 10_000_000_000)
Q_CENTER = fmpq(16682119, 10_000_000_000)
BOX_RADIUS = fmpq(1, 100_000_000)
Q_MAX = fmpq(166823, 100_000_000)
STEPS = 28
SLABS = 1000


def squared_modulus(z):
    return z.real * z.real + z.imag * z.imag


def lambda_plus(th):
    return th * th.cos() / th.sin() + I * th


def arc_s(th, t):
    return ((I * th * t).exp() - th.cos()) / (I * th.sin())


def q_slab(j):
    mid = Q_MAX * fmpq(2 * j + 1, 2 * SLABS)
    rad = Q_MAX * fmpq(1, 2 * SLABS)
    return arb(mid, rad)


def main():
    alpha = (arb(2).sqrt() - 1) / 26
    lambda_target = (I * (2 * arb.pi() * alpha)).exp()
    center = acb(arb(P_CENTER), arb(Q_CENTER))
    radius = arb(BOX_RADIUS)
    square = acb(arb(P_CENTER, radius), arb(Q_CENTER, radius))

    # T(theta) = theta + i (lambda_+(theta)-lambda_target).
    # Its derivative is i(cot(theta)-theta*csc(theta)^2).
    residual = lambda_plus(center) - lambda_target
    derivative = I * (
        square.cos() / square.sin()
        - square / (square.sin() * square.sin())
    )
    assert abs(residual) < arb(fmpq(3, 100_000_000_000))
    assert abs(derivative) < arb(fmpq(7, 100))
    assert (
        arb(fmpq(3, 100_000_000_000))
        + arb(fmpq(7, 100)) * arb(2).sqrt() * radius
        < radius
    )
    # Banach's theorem gives a unique theta_c in this closed square.
    assert arb(Q_CENTER - BOX_RADIUS) > 0
    assert arb(Q_CENTER + BOX_RADIUS) < arb(Q_MAX)

    p_ball = arb(P_CENTER, radius)
    q_all = arb(Q_MAX / 2, Q_MAX / 2)
    th_all = acb(p_ball, q_all)

    # Whole-arc interpolation bound.  For |theta|<=R and real |t|<=1,
    # Im s_theta(t) = -(1-t^2) Re[theta^2 H(theta,t)/sin(theta)].
    R = arb(fmpq(102, 1000))
    assert (arb(P_CENTER + BOX_RADIUS) ** 2 + arb(Q_MAX) ** 2) < R * R
    h_error = (R.exp() - 1 - R) / (2 * R)
    sin_error = R.sinh() / R - 1
    a_error = h_error / (1 - sin_error) + sin_error / (2 * (1 - sin_error))
    assert arb(P_CENTER - BOX_RADIUS) / 2 - R * a_error > arb("0.04")
    # Hence the image arc is below -0.04(1-t^2) for interior t.
    t_all = arb(0, 1)
    s_prime = th_all * (I * th_all * t_all).exp() / th_all.sin()
    assert s_prime.real > arb("0.98")
    assert arc_s(th_all, arb(fmpq(-1, 10))).real < arb("-0.08")
    assert arc_s(th_all, arb(fmpq(1, 10))).real > arb("0.08")

    # The target has |lambda_+|=1.  Strictly decreasing G(q) implies
    # |lambda_+|>1 on the vertical approach q<Im(theta_c).
    th_zero = acb(p_ball, arb(0))
    assert squared_modulus(lambda_plus(th_zero)) > arb(1)
    # The q=Q_MAX gap is narrower than the full p-ball's natural
    # interval overestimate; subdivide that one endpoint check.
    for j in range(100):
        p_mid = P_CENTER - BOX_RADIUS + BOX_RADIUS * fmpq(2 * j + 1, 100)
        p_piece = arb(p_mid, arb(BOX_RADIUS / 100))
        th_qmax = acb(p_piece, arb(Q_MAX))
        assert squared_modulus(lambda_plus(th_qmax)) < arb(1)
    dlam_dq = I * (
        th_all.cos() / th_all.sin()
        - th_all / (th_all.sin() * th_all.sin())
        + I
    )
    dG_dq = 2 * (lambda_plus(th_all).conjugate() * dlam_dq).real
    assert dG_dq < arb(-1)

    bounds = [float("inf"), float("-inf"), float("inf"), float("-inf")]
    singular_clearance = float("inf")
    for j in range(SLABS):
        q = q_slab(j)
        th = acb(p_ball, q)
        sine, cosine = th.sin(), th.cos()
        cot = cosine / sine
        r = (th * cot).exp()
        a = th * (-th * cot).exp() / sine
        lp = th * cot + I * th
        lm = th * cot - I * th
        assert squared_modulus(lm) > arb("1.003")

        dlam_dtheta = cot - th / (sine * sine) + I
        b = a.exp()
        db_dq = I * b * (-lp).exp() * (1 - lp) * dlam_dtheta
        assert db_dq.imag > arb("0.05")

        # S(E_b^28) is contained in {E_b^k(0): 0 <= k < 28}.
        # Certify an additional iterate for a uniform margin.  In the
        # chord coordinate H lies below Im(zeta)=0; all these values stay
        # above it, with their real coordinates in the chord span.
        singular_orbit = acb(0)
        for _ in range(STEPS + 1):
            orbit_zeta = (singular_orbit / r - cosine) / (I * sine)
            assert orbit_zeta.real > arb("-0.1")
            assert orbit_zeta.real < arb("0.2")
            assert orbit_zeta.imag > arb("0.02")
            singular_clearance = min(
                singular_clearance, float(orbit_zeta.imag.lower())
            )
            singular_orbit = (a * singular_orbit).exp()

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

    print("CERTIFIED alpha=(sqrt(2)-1)/26, a quadratic irrational Brjuno number")
    print("unique theta_c in center +/- 1e-8 per coordinate:", P_CENTER, Q_CENTER)
    print("both ends repelling for q<Im(theta_c); path embedded in the base plane")
    print("for every p in the enclosing box, one boundary height q_c(p) lies in (0,Q_MAX)")
    print("E_b^28(1) lies in the initial region through the boundary endpoint")
    print("singular values of E_b^28 stay above the chord; certified minimum Im(zeta) > 0.02")
    print("enclosed zeta bounds (display floats only):", bounds)
    print("observed lower enclosure for singular-orbit Im(zeta) (display float only):", singular_clearance)


if __name__ == "__main__":
    main()
