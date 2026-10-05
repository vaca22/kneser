#!/usr/bin/env python3
"""Arb certificate for the remaining open upper Shell--Thron boundary arc.

This supplements certify_far_collar.py.  It certifies a marked straight
crescent along the neutral-multiplier arc from .935*pi to pi (excluding the
endpoint).  Near lambda=-1, the endpoint signs are handled by their exact
value -Im(lambda)/2 and a positive t derivative, rather than by interval
evaluation of a quantity tending to zero.
"""

import math
from fractions import Fraction

import mpmath as mp
from flint import acb, arb, fmpq, ctx

import certify_far_collar as old

ctx.dps = 40
mp.mp.dps = 70
I = acb(0, 1)
N = 80
R = arb(fmpq(5, 2))


def rat(x):
    if isinstance(x, fmpq):
        return x
    if isinstance(x, str):
        f = Fraction(x)
        return fmpq(f.numerator, f.denominator)
    f = Fraction(x).limit_denominator(10**15)
    return fmpq(f.numerator, f.denominator)


def ball(lo, hi):
    return old.ball(rat(lo), rat(hi))


def complex_box(re_lo, re_hi, im_lo, im_hi):
    return acb(ball(re_lo, re_hi), ball(im_lo, im_hi))


def lam(theta):
    return theta * theta.cos() / theta.sin() + I * theta


def lam_prime(theta):
    return theta.cos() / theta.sin() - theta / theta.sin()**2 + I


def h_and_derivative(theta, t):
    """Entire factor h of g and its t derivative, with explicit tails."""
    h, dh = acb(0), acb(0)
    power = acb(1)
    t2 = t * t
    for n in range(2, N):
        poly, dpoly = arb(0), arb(0)
        tp = arb(1)
        # P_n(t)=sum_{j=0}^{floor(n/2)-1} t^(2j+n mod 2).
        for j in range(n // 2):
            deg = 2*j + n % 2
            poly += tp * (t if n % 2 else 1)
            if deg:
                dpoly += deg * t**(deg - 1)
            tp *= t2
        coeff = -(I**(n % 4)) * power / math.factorial(n)
        h += coeff * poly
        dh += coeff * dpoly
        power *= theta
    # For |t|<=1 and n>=N: |P_n|<=n/2, |P'_n|<=n^2/2.
    first = R**(N-2) / math.factorial(N)
    ratio = R * arb(N+1) / arb(N)**2
    assert ratio < arb(fmpq(1, 20))
    ht = first * arb(N) / 2 / (1-ratio)
    dt = first * arb(N*N) / 2 / (1-ratio)
    h += acb(arb(0, ht.upper()), arb(0, ht.upper()))
    dh += acb(arb(0, dt.upper()), arb(0, dt.upper()))
    return h, dh


def signs(theta, t):
    h, dh = h_and_derivative(theta, t)
    factor = -I * theta*theta / theta.sin()
    g, dg = factor*h, factor*dh
    sp = theta * (I*theta*t).exp() / theta.sin()
    d_sp = I*theta*sp
    return (g.imag, (sp.conjugate()*g).imag,
            dg.imag, (d_sp.conjugate()*g+sp.conjugate()*dg).imag)


def check_t(theta, lo, hi, derivative=False, depth=0):
    t = ball(lo, hi)
    v = signs(theta, t)
    a, b = (v[2], v[3]) if derivative else (v[0], v[1])
    if (a > 0 and b > 0) if derivative else (a < 0 and b < 0):
        return 1
    if depth >= 22:
        raise AssertionError(("t derivative" if derivative else "t sign", lo, hi, theta, a, b))
    mid = (lo+hi)/2
    return (check_t(theta, lo, mid, derivative, depth+1)
            + check_t(theta, mid, hi, derivative, depth+1))


def endpoint_root():
    """Validated simple root of lambda(theta)=-1 in a rational disk."""
    re = rat('2.298579006651286638581162032025485887')
    im = rat('0.766046060993189952726996937583367902')
    z0 = acb(arb(re), arb(im))
    radius = arb(fmpq(1, 10**30))
    box = acb(arb(re, radius), arb(im, radius))
    d0 = lam_prime(z0)
    k = abs(1-lam_prime(box)/d0)
    err = abs((lam(z0)+1)/d0)
    assert k < arb(fmpq(1, 1000)) and err + k*radius < radius
    return z0


def endpoint_checks():
    z0 = endpoint_root()
    # This square surrounds theta(-1), and covers the final part of the arc.
    radius = rat('0.0002')
    whole = acb(arb(z0.real.mid(), arb(radius)), arb(z0.imag.mid(), arb(radius)))
    assert abs(whole) < R
    assert abs(lam_prime(whole)) > 0
    assert old.in_H(whole, I*whole.cos()/whole.sin())
    # All neutral multipliers with 0.9999 <= alpha/pi <= 1 have a root
    # within radius 0.00019 of theta(-1), hence inside the checked square.
    u = ball(fmpq(9999, 10000), fmpq(1))
    target = (I*arb.pi()*u).exp()
    inner_radius = arb(fmpq(19, 100000))
    inner = acb(arb(z0.real.mid(), inner_radius),
                arb(z0.imag.mid(), inner_radius))
    d0 = lam_prime(z0)
    k = abs(1-lam_prime(inner)/d0)
    err = abs((lam(z0)-target)/d0)
    assert k < arb(fmpq(1, 100)) and err+k*inner_radius < inner_radius
    count = 0
    # Subdivide theta to control dependency in the entire-series evaluation.
    tiles = 16
    re0, im0 = rat('2.298579006651286638581162032025485887'), rat('0.766046060993189952726996937583367902')
    for i in range(tiles):
        for j in range(tiles):
            th = complex_box(re0-radius+2*radius*i/tiles,
                             re0-radius+2*radius*(i+1)/tiles,
                             im0-radius+2*radius*j/tiles,
                             im0-radius+2*radius*(j+1)/tiles)
            count += check_t(th, rat(-1), rat('0.95'))
            count += check_t(th, rat('0.95'), rat(1), derivative=True)
    print('PASS endpoint neighbourhood: theta radius 0.0002, %d t boxes' % count, flush=True)


def check_global_injectivity():
    """lambda(theta) is injective on the convex rectangle containing the arc."""
    z0 = endpoint_root()
    root_radius = arb(fmpq(1, 10**30))
    root_box = acb(arb(z0.real.mid(), root_radius),
                   arb(z0.imag.mid(), root_radius))
    ref = lam_prime(root_box)
    n = 10
    for i in range(n):
        for j in range(n):
            th = complex_box(fmpq(219,100)+fmpq(12,100)*i/n,
                             fmpq(219,100)+fmpq(12,100)*(i+1)/n,
                             fmpq(71,100)+fmpq(7,100)*j/n,
                             fmpq(71,100)+fmpq(7,100)*(j+1)/n)
            assert (lam_prime(th)/ref).real > arb(fmpq(4,5))
    # Re(lambda'/ref)>0 on this convex rectangle; Noshiro--Warschawski.
    print('PASS lambda injective on [2.19,2.31]+i[0.71,0.78]', flush=True)


def arc_root_box(u0, u1):
    """Validated family of roots lambda(theta)=exp(i*pi*u), u0<=u<=u1.

    Banach's contraction theorem is applied to theta-F(theta,u)/F'(theta0)
    on a disk about a rational midpoint.  The mpmath solve is only a seed.
    """
    uq = (u0+u1)/2
    umid = mp.mpf(int(uq.numerator))/mp.mpf(int(uq.denominator))
    target_mid = mp.exp(mp.j*mp.pi*umid)
    seed = mp.findroot(lambda z: z*mp.cot(z)+mp.j*z-target_mid,
                       (2.2+.72j, 2.3+.77j))
    zre = rat(mp.nstr(mp.re(seed), 32))
    zim = rat(mp.nstr(mp.im(seed), 32))
    z0 = acb(arb(zre), arb(zim))
    radius_q = 3*(u1-u0)+fmpq(1, 10**25)
    radius = arb(radius_q)
    theta = acb(arb(zre, radius), arb(zim, radius))
    u = ball(u0, u1)
    target = (I*arb.pi()*u).exp()
    d0 = lam_prime(z0)
    k = abs(1-lam_prime(theta)/d0)
    err = abs((lam(z0)-target)/d0)
    if not (k < arb(fmpq(1, 5)) and err+k*radius < radius):
        raise AssertionError(('root contraction', u0, u1, k, err, radius))
    assert theta.real > arb(fmpq(219,100)) and theta.real < arb(fmpq(231,100))
    assert theta.imag > arb(fmpq(71,100)) and theta.imag < arb(fmpq(78,100))
    return theta


def compact_checks():
    left, right = fmpq(935, 1000), fmpq(9999, 10000)
    anchor = arc_root_box(left, left)
    assert anchor.real < arb(old.P1)
    assert anchor.imag > 0 and anchor.imag < arb(fmpq(18,100))*anchor.real**2
    assert old.mark_box(anchor) == -1
    todo = [(left, right, 0)]
    nboxes, ntboxes = 0, 0
    last = None
    while todo:
        lo, hi, depth = todo.pop()
        try:
            theta = arc_root_box(lo, hi)
            assert abs(theta) < R
            assert abs(lam_prime(theta)) > 0
            assert old.in_H(theta, I*theta.cos()/theta.sin())
            nt = check_t(theta, fmpq(-1), fmpq(19, 20))
            nt += check_t(theta, fmpq(19, 20), fmpq(1), derivative=True)
            # The parameter box actually encloses the neutral branch in H^+.
            assert (I*arb.pi()*ball(lo, hi)).exp().imag > 0
            nboxes += 1
            ntboxes += nt
            last = (lo, hi)
            if nboxes % 100 == 0:
                print('  compact boxes=%d, u interval [%s,%s]' % (nboxes, lo, hi), flush=True)
        except (AssertionError, ZeroDivisionError, ValueError):
            if depth >= 22:
                raise
            mid = (lo+hi)/2
            todo.append((mid, hi, depth+1))
            todo.append((lo, mid, depth+1))
    print('PASS compact arc [%s,%s]: %d parameter boxes, %d t boxes' %
          (left, right, nboxes, ntboxes), flush=True)


if __name__ == '__main__':
    check_global_injectivity()
    endpoint_checks()
    compact_checks()
