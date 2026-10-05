#!/usr/bin/env python3
"""Arb certificate for B_1, B_2, B_3 of the inverse upper horn map.

The Fatou coordinates are enclosed by 100/1200 iterates of their defining
limits and an exact rational tail estimate.  Krawczyk boxes invert the
repelling coordinate.  A 256x40 box cover proves holomorphy and |D|<1 on
1.9 <= Im z <= 2.1; overlap and periodic-seam checks identify one branch.
The periodic trapezoid bound then turns 128 certified samples at Im z=2
into rigorous enclosures for the first three Fourier coefficients.
"""

import cmath
import sys
from fractions import Fraction
from pathlib import Path

import mpmath as mp
from flint import acb, arb, ctx, fmpq

from certify_horn_witness import (
    K, N, N0, alpha, alpha_derivative, formal_coefficients, tail_bound,
)
from parabolic_horn_inverse import Alpha, phi_rep_inverse

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from kneser._general import parabolic_engine  # noqa: E402


ctx.dps = 90
mp.mp.dps = 85
I = acb(0, 1)
COEFFS = formal_coefficients(K)
BOUNDARY = Fraction(19, 6) + sum(
    abs(COEFFS[j]) * (Fraction(2, 3)**j + Fraction(1, 2)**j)
    for j in range(1, K+1)
)
assert BOUNDARY < 4
TAIL = arb(fmpq(str(tail_bound())))
RHO = arb("1e-5")
N_SAMPLES = 128
Y_SAMPLE = 2
N_STRIP = 100
STRIP_NX = 256
STRIP_NY = 40
STRIP_RAD = arb("0.002")
STRIP_TAIL_Q = 4 * (Fraction(4, 80) ** (K + 2)) * (1 + Fraction(80, 1) / (Fraction(3, 4) * (K + 1)))
STRIP_TAIL = arb(fmpq(str(STRIP_TAIL_Q)))


def err_ball(radius):
    return acb(arb(0, radius), arb(0, radius))


def contains(outer, inner):
    return (outer.real.lower() < inner.real.lower()
            and inner.real.upper() < outer.real.upper()
            and outer.imag.lower() < inner.imag.lower()
            and inner.imag.upper() < outer.imag.upper())


def iterate(u, direction, n, derivative=False):
    d = acb(1)
    for _ in range(n):
        if direction == "rep":
            assert (1 + u).real > 0 and u.imag > 0
            if derivative:
                d /= 1 + u
            u = (1 + u).log()
        else:
            assert u.imag > 0
            if derivative:
                d *= u.exp()
            u = u.exp() - 1
    return u, d


def finite_phi(u, direction, derivative=False, steps=N):
    v, d = iterate(u, direction, steps, derivative)
    value = alpha(v, COEFFS) + (steps if direction == "rep" else -steps)
    return value, alpha_derivative(v, COEFFS) * d if derivative else None


FLOAT_COEFFS = {j: float(v) for j, v in COEFFS.items()}


def float_phi_rep(u):
    d = 1+0j
    for _ in range(N_STRIP):
        d /= 1 + u
        u = cmath.log(1 + u)
    poly = sum(FLOAT_COEFFS[j] * u ** j for j in range(1, K + 1))
    dpoly = sum(j * FLOAT_COEFFS[j] * u ** (j - 1) for j in range(1, K + 1))
    return (-2/u + cmath.log(-u)/3 + poly + N_STRIP,
            (2/u**2 + 1/(3*u) + dpoly) * d)


def float_root(z, guess):
    u = guess
    for _ in range(7):
        value, derivative = float_phi_rep(u)
        u -= (value - z) / derivative
    return u


def strip_z_box(i, j):
    return acb(arb(fmpq(2*i+1, 2*STRIP_NX), fmpq(1, 2*STRIP_NX)),
               arb(fmpq(19, 10) + fmpq(2*j+1, 10*STRIP_NY),
                   fmpq(1, 10*STRIP_NY)))


def strip_cell(i, j, center):
    m = acb(arb(repr(center.real)), arb(repr(center.imag)))
    box = acb(arb(m.real, STRIP_RAD), arb(m.imag, STRIP_RAD))
    wide = acb(arb(m.real, STRIP_RAD + arb("0.001")),
               arb(m.imag, STRIP_RAD + arb("0.001")))
    va, _ = iterate(wide, "att", N_STRIP)
    vr, _ = iterate(wide, "rep", N_STRIP)
    assert (-2 / va).real > 80 and (2 / vr).real > 80, (i, j, "tail")
    zm = strip_z_box(i, j)
    fm, dm = finite_phi(m, "rep", True, N_STRIP)
    _, db = finite_phi(box, "rep", True, N_STRIP)
    inverse = 1 / dm
    derivative = db + err_ball(STRIP_TAIL / arb("0.001"))
    base = m - inverse * (fm + err_ball(STRIP_TAIL))
    slope = 1 - inverse * derivative

    def krawczyk(z):
        return base + inverse * z + slope * (box - m)

    kval = krawczyk(zm)
    assert contains(box, kval) and abs(slope) < 1, (i, j, "root", kval, box)
    att, _ = finite_phi(box, "att", steps=N_STRIP)
    D = att - zm + err_ball(STRIP_TAIL)
    assert abs(D) < 1, (i, j, "bound", D)
    return box, krawczyk


def strip_certificate():
    eng = Alpha(list(parabolic_engine(40).coeffs))
    zfirst = mp.mpc(mp.mpf(1)/(2*STRIP_NX), mp.mpf(19)/10 + mp.mpf(1)/(10*STRIP_NY))
    seed = complex(phi_rep_inverse(eng, zfirst, mp.mpf("0.01")))
    row_seeds = []
    rows = []
    for j in range(STRIP_NY):
        row = []
        guess = seed if j == 0 else row_seeds[j-1]
        for i in range(STRIP_NX):
            z = complex((i+0.5)/STRIP_NX, 1.9 + 0.2*(j+0.5)/STRIP_NY)
            guess = float_root(z, guess)
            box, kval = strip_cell(i, j, guess)
            row.append((box, kval))
            if i == 0:
                row_seeds.append(guess)
        rows.append(row)
        if j % 5 == 4:
            print("strip rows %d/%d certified" % (j+1, STRIP_NY), flush=True)
    for j in range(STRIP_NY):
        for i in range(STRIP_NX):
            _, krawczyk = rows[j][i]
            if i + 1 < STRIP_NX:
                edge = acb(arb(fmpq(i+1, STRIP_NX)),
                           arb(fmpq(19, 10)+fmpq(2*j+1, 10*STRIP_NY),
                               fmpq(1, 10*STRIP_NY)))
                assert contains(rows[j][i+1][0], krawczyk(edge)), (i, j, "horizontal join")
            if j + 1 < STRIP_NY:
                edge = acb(arb(fmpq(2*i+1, 2*STRIP_NX), fmpq(1, 2*STRIP_NX)),
                           arb(fmpq(19, 10)+fmpq(j+1, 5*STRIP_NY)))
                assert contains(rows[j+1][i][0], krawczyk(edge)), (i, j, "vertical join")
        y = arb(fmpq(19, 10)+fmpq(2*j+1, 10*STRIP_NY), fmpq(1, 10*STRIP_NY))
        left = rows[j][0][1](acb(arb(0), y))
        assert contains(rows[j][-1][0], left.exp()-1), (j, "periodic seam")
    print("PASS: 10240 boxes, all joins and periodic seam; |D(z)|<1 on 1.9<=Im z<=2.1")
    return rows


def arb_midpoint_decimal(value):
    """A high-precision decimal guess; correctness comes from Krawczyk."""
    return str(value.mid()).split(" +/-")[0].lstrip("[")


def anchor_branch(rows):
    """Chain the strip branch to u=11i/20 on the canonical upper gate."""
    u0 = acb(0, arb(fmpq(11, 20)))
    z0, _ = finite_phi(u0, "rep")
    z0 += err_ball(TAIL)
    assert z0.imag > arb(fmpq(3, 1))
    segments = 400
    guess = complex(0, 0.55)
    previous_box = previous_krawczyk = None
    for k in range(segments):
        t = arb(fmpq(2*k+1, 2*segments), fmpq(1, 2*segments))
        z = acb(z0.real, z0.imag*(1-t) + 2*t)
        guess = float_root(complex(float(z.real.mid()), float(z.imag.mid())), guess)
        m = acb(arb(repr(guess.real)), arb(repr(guess.imag)))
        radius = arb("0.003")
        box = acb(arb(m.real, radius), arb(m.imag, radius))
        wide = acb(arb(m.real, radius+arb("0.001")),
                   arb(m.imag, radius+arb("0.001")))
        va, _ = iterate(wide, "att", N_STRIP)
        vr, _ = iterate(wide, "rep", N_STRIP)
        assert (-2/va).real > 80 and (2/vr).real > 80
        fm, dm = finite_phi(m, "rep", True, N_STRIP)
        _, db = finite_phi(box, "rep", True, N_STRIP)
        inverse = 1 / dm
        base = m - inverse*(fm + err_ball(STRIP_TAIL))
        slope = 1 - inverse*(db + err_ball(STRIP_TAIL/arb("0.001")))

        def krawczyk(target, base=base, inverse=inverse, slope=slope,
                     box=box, m=m):
            return base + inverse*target + slope*(box-m)

        assert contains(box, krawczyk(z)) and abs(slope) < 1, (k, "anchor path")
        if k == 0:
            assert contains(box, u0)
        if previous_box is not None:
            edge_t = arb(fmpq(k, segments))
            edge = acb(z0.real, z0.imag*(1-edge_t) + 2*edge_t)
            assert contains(box, previous_krawczyk(edge)), (k, "anchor join")
        previous_box, previous_krawczyk = box, krawczyk

    # Tighten the root at the end of the path, then use f(u) to enter the
    # periodic strip at x+1.  This fixes the horn branch without relying on
    # the mpmath guesses used to locate Krawczyk boxes.
    eng = Alpha(list(parabolic_engine(75).coeffs))
    xguess = mp.mpf(arb_midpoint_decimal(z0.real))
    uguess = phi_rep_inverse(eng, mp.mpc(xguess, 2), mp.mpf("0.01"))
    m = acb(arb(str(mp.re(uguess))), arb(str(mp.im(uguess))))
    check_tails_on_disc(m)
    fine = acb(arb(m.real, arb("1e-29")), arb(m.imag, arb("1e-29")))
    zend = acb(z0.real, arb(2))
    fm, dm = finite_phi(m, "rep", True)
    _, db = finite_phi(fine, "rep", True)
    inverse = 1/dm
    root = (m - inverse*(fm-zend+err_ball(TAIL))
            + (1-inverse*(db+err_ball(TAIL/RHO)))*(fine-m))
    assert contains(fine, root) and contains(previous_box, root)
    x1 = z0.real + 1
    index = int(float(x1.mid()) * STRIP_NX)
    assert (fmpq(index, STRIP_NX) < x1
            and x1 < fmpq(index+1, STRIP_NX))
    assert contains(rows[STRIP_NY//2][index][0], root.exp()-1)
    print("PASS: strip branch chained to u=11i/20 on the upper gate")


def check_tails_on_disc(center):
    # Every disc of radius RHO around a point in the eventual root box lies
    # in this larger rectangle.  The elementary tail proof in
    # certify_horn_witness.py applies once Re(+-2/u_100)>80.
    wide = acb(arb(center.real, 2 * RHO), arb(center.imag, 2 * RHO))
    va, _ = iterate(wide, "att", N0)
    vr, _ = iterate(wide, "rep", N0)
    assert (-2 / va).real > 80
    assert (2 / vr).real > 80


def certified_root(j, guess_engine):
    z_mp = mp.mpc(mp.mpf(j) / N_SAMPLES, Y_SAMPLE)
    u_mp = phi_rep_inverse(guess_engine, z_mp, mp.mpf("0.01"))
    center = acb(arb(str(mp.re(u_mp))), arb(str(mp.im(u_mp))))
    check_tails_on_disc(center)
    rad = arb("1e-29")
    box = acb(arb(center.real, rad), arb(center.imag, rad))
    z = acb(arb(fmpq(j, N_SAMPLES)), arb(Y_SAMPLE))
    fm, dm = finite_phi(center, "rep", derivative=True)
    _, db = finite_phi(box, "rep", derivative=True)
    # Cauchy on the RHO-disc bounds the derivative of the infinite tail.
    inverse = 1 / dm
    krawczyk = (center - inverse * (fm - z + err_ball(TAIL))
                + (1 - inverse * (db + err_ball(TAIL / RHO))) * (box - center))
    assert contains(box, krawczyk), (j, krawczyk, box)
    assert abs(1 - inverse * (db + err_ball(TAIL / RHO))) < 1
    return z, krawczyk


def main():
    assert TAIL < arb("1e-29")
    guess_engine = Alpha(list(parabolic_engine(75).coeffs))
    rows = strip_certificate()
    anchor_branch(rows)
    samples = []
    for j in range(N_SAMPLES):
        z, root = certified_root(j, guess_engine)
        assert contains(rows[STRIP_NY//2][2*j][0], root), (j, "sample branch")
        att, _ = finite_phi(root, "att")
        samples.append(att - z + err_ball(TAIL))
    delta = arb(fmpq(1, 10))
    q = (-2 * arb.pi() * N_SAMPLES * delta).exp()
    certified = {}
    for n in (1, 2, 3):
        avg = sum((samples[j] * (-2 * arb.pi() * I * n * j / N_SAMPLES).exp()
                   for j in range(N_SAMPLES)), acb(0)) / N_SAMPLES
        scaled = avg * (2 * arb.pi() * n * Y_SAMPLE).exp()
        # The strip certificate bounds |D| by 1.  For the periodic analytic
        # function D(x+2i)*exp(-2*pi*i*n*x), the two horizontal boundaries
        # at imaginary offset +/-delta have modulus <=exp(2*pi*n*delta).
        # Fourier coefficients at indices +/-k therefore decay by
        # exp(-2*pi*k*delta).  Sum the aliases at k=l*N_SAMPLES.
        alias = (2 * arb.pi() * n * (Y_SAMPLE+delta)).exp() * 2*q/(1-q)
        result = scaled + err_ball(alias.upper())
        certified[n] = result
        print("CERTIFIED B_%d in %s" % (n, result))
        print("CERTIFIED |B_%d| in %s" % (n, abs(result)))
        if n == 1:
            assert arb("0.0149216591537311398342") < result.real < arb("0.0149216591537311398344")
            assert arb("0.0877994828247189453137") < result.imag < arb("0.0877994828247189453139")
            assert abs(result) > arb("0.0890584364122133315631")
            assert abs(result) < arb("0.0890584364122133315633")
        elif n == 2:
            assert arb("-0.00393526116311540") < result.real < arb("-0.00393526116311538")
            assert arb("-0.01185109621629301") < result.imag < arb("-0.01185109621629299")
            assert abs(result) > arb("0.01248738411156469")
            assert abs(result) < arb("0.01248738411156471")
        else:
            assert arb("0.00075551030") < result.real < arb("0.00075551032")
            assert arb("0.00140220679") < result.imag < arb("0.00140220681")
            assert abs(result) > arb("0.00159278992")
            assert abs(result) < arb("0.00159278994")
    ratio2 = certified[2]/certified[1]**2
    ratio3 = certified[3]/certified[1]**3
    assert arb("-0.025320493100") < ratio2.real < arb("-0.025320493099")
    assert arb("1.574219065231") < ratio2.imag < arb("1.574219065233")
    assert arb("-2.25479914") < ratio3.real < arb("-2.25479910")
    assert arb("-0.02440873") < ratio3.imag < arb("-0.02440869")
    print("CERTIFIED B_2/B_1^2 in %s" % ratio2)
    print("CERTIFIED B_3/B_1^3 in %s" % ratio3)
    print("PASS: 128 samples plus rigorous trapezoid alias bound")


if __name__ == "__main__":
    main()
