#!/usr/bin/env python3
"""Arb checks for the analytic first-crossing proof in paulsen-far-entry-audit-zh.md.

The line is theta=p*(1+i*c), c=0.01/0.1000435842, 0<p<=p0.
This certifies the initial cross-ratio bounds and the elementary constants
used in the step estimate.  The step estimate itself is a proved analytic
inequality, not a finite sampling of iterates.  All inputs are rational and
all strict comparisons use outward-rounded Arb balls.
"""

from math import factorial
from flint import acb, arb, ctx, fmpq
from certify_exterior_cone_cylinder import interpolation_h, theta_over_sin

ctx.dps = 80
I = acb(0, 1)
P0 = fmpq(1000435842, 10_000_000_000)
C0 = fmpq(1, 100) / P0
R = arb(fmpq(102, 1000))


def interval(lo, hi):
    return arb((lo + hi) / 2, (hi - lo) / 2)


def series_s_c(v):
    """S=sin(sqrt(v))/sqrt(v), C=cos(sqrt(v))."""
    s = sum(((-1) ** k * v**k / factorial(2 * k + 1)
             for k in range(7)), acb(0))
    c = sum(((-1) ** k * v**k / factorial(2 * k)
             for k in range(7)), acb(0))
    st = R**7 / factorial(15) / (1 - R / (16 * 17))
    ct = R**7 / factorial(14) / (1 - R / (15 * 16))
    return (s + acb(arb(0, st), arb(0, st)),
            c + acb(arb(0, ct), arb(0, ct)))


def main():
    assert arb(0) < arb(C0) < arb(fmpq(1, 10))
    assert arb(P0*P0*(1+C0*C0)) < R*R

    # A rectangle enclosing v=theta^2 for every point of the line,
    # including its limit at p=0.
    v = acb(interval(0, P0*P0), interval(0, P0*P0/5))
    s, co = series_s_c(v)
    rr = (co/s).exp()
    d = rr*s/(1-rr*co)
    t = -v*d*d
    assert abs(t) < arb(fmpq(3, 100))
    atanh_ratio = sum((t**k / (2*k+1) for k in range(8)), acb(0))
    tail = arb(fmpq(3, 100))**8 / (17*(1-arb(fmpq(3, 100))))
    atanh_ratio += acb(arb(0, tail), arb(0, tail))
    chi0_over_p = (1+I*arb(C0))*(-2*I*d*atanh_ratio)
    assert chi0_over_p.real > arb(fmpq(-2, 5))
    assert chi0_over_p.real < arb(0)
    assert chi0_over_p.imag > arb(3)
    assert chi0_over_p.imag < arb(fmpq(33, 10))

    # (theta*cot(theta)-1)/theta^2 is analytic at zero.
    diff_over_v = sum(((-1)**k *
        (fmpq(1, factorial(2*k)) - fmpq(1, factorial(2*k+1))) *
        v**(k-1) for k in range(1, 7)), acb(0))
    tail_d = (R**6/factorial(14) + R**6/factorial(15)) / (1-R/(15*16))
    diff_over_v += acb(arb(0, tail_d), arb(0, tail_d))
    delta_over_p2 = (1+I*arb(C0))**2 * diff_over_v/s
    assert delta_over_p2.real < arb(fmpq(-31, 100))
    assert delta_over_p2.imag > arb(fmpq(-8, 100))
    assert delta_over_p2.imag < arb(fmpq(8, 100))
    assert abs(delta_over_p2) < arb(fmpq(36, 100))
    st_quadratic = (arb(fmpq(101, 100)) - arb(fmpq(62, 100))
                    + arb(fmpq(62, 1000))*arb(P0)
                    + arb(fmpq(16, 100))*arb(P0)
                    + arb(fmpq(1296, 10000))*arb(P0)**2)
    assert st_quadratic < arb(fmpq(414, 1000))
    assert 2*arb(C0) > arb(fmpq(414, 1000))*arb(P0)
    assert arb(fmpq(8, 100))*arb(P0) < 1

    # For y in [3p,pi+1.14p], |1-exp(x+iy)| is at least sin(3p)
    # when y<=pi/2, and at least 1 otherwise.  The following are the
    # exact numerical constants in the analytic bound.
    theta_factor = arb(fmpq(101, 100)).sqrt()
    denom_factor = 3 - arb(fmpq(9, 2))*arb(P0)**2
    v_bound = theta_factor/denom_factor
    assert arb(fmpq(1174, 1000))*v_bound < arb(fmpq(2, 5))
    rho = arb(fmpq(2, 5))
    sinhc = rho.sinh()/rho
    deriv = (rho*rho.cosh()-rho.sinh())/(rho*rho)
    assert deriv/(2-sinhc)*theta_factor < arb(fmpq(14, 100))

    # The crude invariant rectangle [-1,.16] for Re chi remains invariant
    # until the first Im chi >= pi.  Strict rational inequalities include
    # the last step.  We use pi<22/7 and p<=.101.
    n_p_bound = arb(fmpq(22, 7))/arb(fmpq(86, 100)) + arb(P0)
    assert -arb(fmpq(4, 100))-arb(fmpq(24, 100))*n_p_bound > -1
    assert arb(fmpq(4, 100))*n_p_bound < arb(fmpq(16, 100))

    # The crossing orbit sits in a central chord rectangle; the same
    # enclosure covers the orbit point immediately before the crossing.
    pi = arb.pi()
    for j in range(64):
        x = interval(-1+fmpq(29*j, 1600), -1+fmpq(29*(j+1), 1600))
        for k in range(32):
            yy = interval(-fmpq(114, 100)*P0 +
                          fmpq(228*k, 3200)*P0,
                          -fmpq(114, 100)*P0 +
                          fmpq(228*(k+1), 3200)*P0)
            q = acb(x, pi+yy).exp()
            zeta = (1+q)/(1-q)
            assert zeta.real > arb(fmpq(-1, 5))
            assert zeta.real < arb(fmpq(3, 5))
            assert zeta.imag > arb(fmpq(-1, 10))
            assert zeta.imag < arb(fmpq(1, 10))

    # The seam map is univalent on a rectangle enclosing the crossing and
    # its short vertical segment to the real chord.
    theta = acb(interval(0, P0), interval(0, fmpq(1, 100)))
    sv, _ = series_s_c(theta*theta)
    seam_box = acb(interval(fmpq(-3, 10), fmpq(7, 10)),
                   interval(fmpq(-1, 10), fmpq(1, 10)))
    seam_derivative = (I*theta*seam_box).exp()/sv
    assert seam_derivative.real > arb(fmpq(9, 10))
    for tt, bound, is_left in ((fmpq(-7, 10), fmpq(-1, 5), True),
                               (fmpq(7, 10), fmpq(3, 5), False)):
        t_real = arb(tt)
        h = interpolation_h(theta, t_real)
        s_at_t = (t_real + (1-t_real*t_real)*theta*
                  theta_over_sin(theta)*h/I)
        if is_left:
            assert s_at_t.real < arb(bound)
        else:
            assert s_at_t.real > arb(bound)

    # At the interior endpoint used by the existing exterior corridor,
    # the first crossing is indeed the previously marked 28th iterate.
    th0 = acb(arb(P0), arb(fmpq(1, 100)))
    s0, co0 = series_s_c(th0*th0)
    r0 = (co0/s0).exp()
    a0 = (-co0/s0).exp()/s0
    w = acb(1)
    for n in range(29):
        zz = (w/r0-th0.cos())/(I*th0.sin())
        if n < 28:
            assert zz.imag > 0
        else:
            assert zz.imag < 0
        w = (a0*w).exp()

    print("PASS initial cross-ratio, Shell--Thron path constants, and first-crossing geometry")
    print("chi0/p enclosure:", chi0_over_p)
    print("(lambda-(1+i*theta))/p^2 enclosure:", delta_over_p2)
    print("derivative correction bound:", deriv/(2-sinhc)*theta_factor)


if __name__ == '__main__':
    main()
