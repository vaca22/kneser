#!/usr/bin/env python3
"""Arb certificate for Section sec:endpoint: the family of Theorem thm:upper
is holomorphic on a full neighbourhood of b = e^{-e} (lambda_+ = -1).

The straight chord is used again, but the crescent is described in the
coordinate chi = log((zeta-1)/(zeta+1)), where the chord is Im chi = pi and
the image arc is Gamma(x) = x + i pi + phi(x), x = log((1-t)/(1+t)),
    phi(t) = i theta + log S(i theta (t-1)/2) - log S(i theta (t+1)/2),
    S(w) = sinh(w)/w  (entire, S(0) = 1),
phi(1) = log lambda_+, phi(-1) = -log lambda_-.  The interpolation
M(x, sigma) = x + i pi + sigma phi(x) is linear in chi and does not degenerate
at lambda_+ = -1.  For lambda in the square [-1.1,-0.9] x [-0.1,0.1] we check
  (R) the root theta of lambda_+(theta) = lambda is unique in the rectangle
      R' (Noshiro--Warschawski) and lies in a Krawczyk box;
  (a) Re(1 + dphi/dx) > 0          (Gamma is a graph over Re chi);
  (b) 0 < Im phi < 2 pi            (the strip embeds in the chi-cylinder);
  (c) Im(conj(1 + dphi/dx) phi) > 0 (M is orientation preserving);
  (d) where Re Gamma = 0, Im phi < pi   (the region avoids zeta = infinity);
  (e) zeta(0) = i cot theta lies strictly inside (the mark, index -1);
  (f) |theta| < pi, Re S > 0 on the relevant discs (principal logs analytic).
The same checks are then made on the strip lambda in [-12,-1/5] x [-1/1000,1/1000]
along the real axis (b in a neighbourhood of [exp(-12 e^12), 0.7832]), with the
theta-branch chained box by box (uniqueness in the hull of adjacent theta-boxes on
the common edge) from the square about lambda = -1.
"""

import sys
from math import factorial
from fractions import Fraction
from flint import acb, arb, ctx, fmpq

ctx.dps = 30
I = acb(0, 1)
PI = arb.pi()
NS = 45
THSTAR = acb(arb("2.29857900665128663858"), arb("0.76604606099318995273"))
RP = (fmpq(220, 100), fmpq(245, 100), fmpq(62, 100), fmpq(95, 100))   # R-prime


def ball(lo, hi):
    lo, hi = fmpq(lo), fmpq(hi)
    return arb((lo + hi) / 2, (hi - lo) / 2)


def fq(x):
    fr = Fraction(x)
    return fmpq(fr.numerator, fr.denominator)


def fail(msg):
    print("FAIL:", msg)
    sys.exit(1)


def S_and_dS(w):
    """S(w) = sinh(w)/w = sum w^{2k}/(2k+1)!, S'(w), for |w| <= 2.6."""
    S, dS = acb(0), acb(0)
    w2 = w * w
    wp = acb(1)
    for k in range(NS):
        S += wp / factorial(2 * k + 1)
        wp *= w2
    wp = acb(1)
    for k in range(1, NS):
        dS += 2 * k * wp * w / factorial(2 * k + 1)
        wp *= w2
    R = arb(fmpq(32, 10))
    tail = R ** (2 * NS) / factorial(2 * NS + 1) * 4
    e = acb(arb(0, tail.upper()), arb(0, tail.upper()))
    if not abs(w) < R:
        raise ValueError('w too large')
    return S + e, dS + e * 2 * NS


def lam_plus(theta):
    return theta * theta.cos() / theta.sin() + I * theta


def dlam_plus(theta):
    return theta.cos() / theta.sin() - theta / theta.sin() ** 2 + I


RADII = [1e-5 * 1.25 ** k for k in range(45)]      # 1e-5 ... ~0.2


def rect_ball(r):
    return acb(ball(r[0], r[1]), ball(r[2], r[3]))


def injectivity():
    """Re(lambda_+'(theta)/lambda_+'(theta*)) > 0 on the convex rectangle R'."""
    ref = dlam_plus(THSTAR)
    n = 24
    for i in range(n):
        for j in range(n):
            x0 = RP[0] + (RP[1] - RP[0]) * i / n
            x1 = RP[0] + (RP[1] - RP[0]) * (i + 1) / n
            y0 = RP[2] + (RP[3] - RP[2]) * j / n
            y1 = RP[2] + (RP[3] - RP[2]) * (j + 1) / n
            th = acb(ball(x0, x1), ball(y0, y1))
            if not (dlam_plus(th) / ref).real > 0:
                fail("injectivity on R'")
    print("PASS lambda_+ injective on R' = [2.20,2.45] x [0.62,0.95]")


def krawczyk_theta(L, thc, rad):
    B = acb(arb(thc.real, rad), arb(thc.imag, rad))
    m = acb(fq(thc.real), fq(thc.imag))
    dm = complex(float(dlam_plus(m).real.mid()), float(dlam_plus(m).imag.mid()))
    Y = acb(fq((1 / dm).real), fq((1 / dm).imag))
    K = m - Y * (lam_plus(m) - L) + (1 - Y * dlam_plus(B)) * (B - m)
    if (K.real.lower() > B.real.lower() and K.real.upper() < B.real.upper() and
            K.imag.lower() > B.imag.lower() and K.imag.upper() < B.imag.upper()):
        return K
    return None


def theta_float(L, th0=complex(2.2986, 0.766)):
    import cmath
    th = th0
    for _ in range(60):
        f = th * cmath.cos(th) / cmath.sin(th) + 1j * th - L
        d = cmath.cos(th) / cmath.sin(th) - th / cmath.sin(th) ** 2 + 1j
        th -= f / d
    return th


def phi_parts(theta, t):
    """phi(t), dphi/dt, x(t) not included."""
    w1 = I * theta * (t - 1) / 2
    w2 = I * theta * (t + 1) / 2
    try:
        S1, dS1 = S_and_dS(w1)
        S2, dS2 = S_and_dS(w2)
    except ValueError:
        return None
    if not (S1.real > 0 and S2.real > 0):
        return None
    phi = I * theta + S1.log() - S2.log()
    dphi = (I * theta / 2) * (dS1 / S1 - dS2 / S2)
    return phi, dphi


def xrange(tl, th_):
    """Re chi on the chord, x = log((1-t)/(1+t)), for [tl, th_] (may be infinite)."""
    lo = (arb(1 - th_) / arb(1 + th_)).log() if th_ < 1 else None     # -inf if th_=1
    hi = (arb(1 - tl) / arb(1 + tl)).log() if tl > -1 else None       # +inf if tl=-1
    return lo, hi


def check_t(theta, tl, th_, chi0, depth=0):
    t = ball(tl, th_)
    r = phi_parts(theta, t)
    ok = r is not None
    if ok:
        phi, dphi = r
        dtdx = -(1 - t * t) / 2
        phix = dphi * dtdx
        ok = ((1 + phix).real > 0 and phi.imag > 0 and phi.imag < 2 * PI and
              ((1 + phix).conjugate() * phi).imag > 0)
        if ok:
            # (d), (e): only boxes whose Re Gamma can meet 0 or Re chi0
            lo, hi = xrange(tl, th_)
            ReG_lo = None if lo is None else lo + phi.real.lower()
            ReG_hi = None if hi is None else hi + phi.real.upper()
            meets0 = ((ReG_lo is None or not (ReG_lo > 0)) and (ReG_hi is None or not (ReG_hi < 0)))
            if meets0:
                ok = ok and phi.imag < PI                               # (d)
            meetsM = ((ReG_lo is None or not (ReG_lo > chi0.real.upper())) and
                      (ReG_hi is None or not (ReG_hi < chi0.real.lower())))
            if meetsM:
                ok = ok and (PI + phi.imag) > chi0.imag                 # (e)
    if ok:
        return True
    if depth > 16:
        return False
    tm = (tl + th_) / 2
    return check_t(theta, tl, tm, chi0, depth + 1) and check_t(theta, tm, th_, chi0, depth + 1)


def check_lambda_box(x0, x1, y0, y1, depth=0):
    L = acb(ball(x0, x1), ball(y0, y1))
    thc = theta_float(complex(float((x0 + x1) / 2), float((y0 + y1) / 2)))
    B = None
    for rad in [1e-4, 1e-3, 1e-2, 3e-2]:
        B = krawczyk_theta(L, thc, rad)
        if B is not None:
            break
    ok = B is not None
    if ok:
        R = rect_ball(RP)
        ok = (B.real.lower() > R.real.lower() and B.real.upper() < R.real.upper() and
              B.imag.lower() > R.imag.lower() and B.imag.upper() < R.imag.upper())
    if ok:
        ok = abs(B) < PI                                          # (f)
    if ok:
        # the mark zeta(0) = i cot theta; chi0 with Im chi0 in (pi, 3 pi)
        z0 = I * B.cos() / B.sin()
        chi0 = ((z0 - 1) / (z0 + 1)).log()
        # principal log has Im in (-pi, pi]; shift by 2 pi
        chi0 = chi0 + 2 * PI * I
        ok = chi0.imag > PI and chi0.imag < 3 * PI
        if ok:
            n = 16
            for i in range(n):
                tl = fmpq(-1) + fmpq(2 * i, n)
                th_ = tl + fmpq(2, n)
                if not check_t(B, tl, th_, chi0):
                    ok = False
                    break
    if ok:
        return 1
    if depth > 6:
        fail("lambda box [%s,%s]x[%s,%s]" % (x0, x1, y0, y1))
    xm, ym = (x0 + x1) / 2, (y0 + y1) / 2
    return (check_lambda_box(x0, xm, y0, ym, depth + 1) + check_lambda_box(xm, x1, y0, ym, depth + 1) +
            check_lambda_box(x0, xm, ym, y1, depth + 1) + check_lambda_box(xm, x1, ym, y1, depth + 1))


def main():
    injectivity()
    n = 0
    k = 10
    for i in range(k):
        for j in range(k):
            x0 = fmpq(-11, 10) + fmpq(2 * i, 10 * k)
            y0 = fmpq(-1, 10) + fmpq(2 * j, 10 * k)
            n += check_lambda_box(x0, x0 + fmpq(2, 10 * k), y0, y0 + fmpq(2, 10 * k))
    print("PASS endpoint: lambda in [-1.1,-0.9] x [-0.1,0.1], %d boxes: (a)-(f)" % n)


def strip_box(x0, x1, y0, y1, thc_guess, parent=None, depth=0):
    """Conditions (a)-(f) on a lambda-box, with a theta-box that is the unique
    root in itself and (for sub-boxes) contained in the parent's theta-box."""
    L = acb(ball(x0, x1), ball(y0, y1))
    thc = theta_float(complex(float((x0 + x1) / 2), float((y0 + y1) / 2)), thc_guess)
    B = None
    for rad in RADII:
        B = krawczyk_theta(L, thc, rad)
        if B is not None:
            break
    ok = B is not None and abs(B) < PI
    if ok and parent is not None:
        ok = (B.real.lower() > parent.real.lower() and B.real.upper() < parent.real.upper() and
              B.imag.lower() > parent.imag.lower() and B.imag.upper() < parent.imag.upper())
    if ok:
        z0 = I * B.cos() / B.sin()
        chi0 = ((z0 - 1) / (z0 + 1)).log() + 2 * PI * I
        ok = chi0.imag > PI and chi0.imag < 3 * PI
        n = 16
        for i in range(n):
            if not ok:
                break
            tl = fmpq(-1) + fmpq(2 * i, n)
            ok = check_t(B, tl, tl + fmpq(2, n), chi0)
    if ok:
        return 1, B
    if depth > 7:
        fail("strip box [%s,%s]x[%s,%s]" % (x0, x1, y0, y1))
    # subdivide; children must stay inside this box's theta-box if it exists
    par = B if B is not None else parent
    if par is None:
        fail("strip: no parent theta-box at [%s,%s]x[%s,%s]" % (x0, x1, y0, y1))
    xm, ym = (x0 + x1) / 2, (y0 + y1) / 2
    if (y1 - y0) > 2 * (x1 - x0):
        kids = [(x0, x1, y0, ym), (x0, x1, ym, y1)]
    else:
        kids = [(x0, xm, y0, ym), (xm, x1, y0, ym), (x0, xm, ym, y1), (xm, x1, ym, y1)]
    tot = 0
    for k in kids:
        n, _ = strip_box(*k, thc, par, depth + 1)
        tot += n
    return tot, B


XR = fmpq(-1, 5)


def strip():
    """lambda in [-12, XR] x [-1/1000, 1/1000], chained from lambda = -1."""
    import cmath
    H = fmpq(1, 1000)
    W = fmpq(1, 200)
    edges = [fmpq(-1)]
    total = 0
    for direction in (-1, +1):
        x = fmpq(-1)
        prevB, prevEdge = None, None
        thg = complex(2.2986, 0.766)
        while (direction < 0 and x > -12) or (direction > 0 and x < XR):
            x1 = x + direction * W
            if direction > 0 and x1 > XR:
                x1 = XR
            if direction < 0 and x1 < -12:
                x1 = fmpq(-12)
            lo, hi = (x1, x) if direction < 0 else (x, x1)
            Wl = abs(x1 - x)
            while True:
                Lt = acb(ball(lo, hi), ball(-H, H))
                thc = theta_float(complex(float((lo + hi) / 2), 0.0), thg)
                if any(krawczyk_theta(Lt, thc, r) is not None
                       for r in RADII):
                    break
                Wl = Wl / 2
                if Wl < fmpq(1, 10 ** 6):
                    fail("strip: top box too small at %s" % float(x))
                x1 = x + direction * Wl
                lo, hi = (x1, x) if direction < 0 else (x, x1)
            n, B = strip_box(lo, hi, -H, H, thg)
            if B is None:
                # the top box failed Krawczyk; use a fresh one on the shared edge only
                fail("strip: no theta-box for top-level box at %s" % float(lo))
            total += n
            thg = complex(float(B.real.mid()), float(B.imag.mid()))
            # chain: common edge lambda = x, uniqueness in the hull of both boxes
            Lb = acb(arb(x), ball(-H, H))
            if prevB is None:
                # anchor at lambda = -1: root must lie in R' (unique there)
                R = rect_ball(RP)
                if not (B.real.lower() > R.real.lower() and B.real.upper() < R.real.upper() and
                        B.imag.lower() > R.imag.lower() and B.imag.upper() < R.imag.upper()):
                    fail("strip anchor not in R'")
            else:
                lo_r = min(float(B.real.lower()), float(prevB.real.lower()))
                hi_r = max(float(B.real.upper()), float(prevB.real.upper()))
                lo_i = min(float(B.imag.lower()), float(prevB.imag.lower()))
                hi_i = max(float(B.imag.upper()), float(prevB.imag.upper()))
                cen = complex((lo_r + hi_r) / 2, (lo_i + hi_i) / 2)
                rad = max(hi_r - lo_r, hi_i - lo_i) / 2 * 1.01 + 1e-12
                if not any(krawczyk_theta(Lb, cen, r) is not None for r in [rad, 2 * rad, 4 * rad]):
                    fail("strip chain at lambda = %s" % float(x))
            prevB = B
            x = x1
    print("PASS strip: lambda in [-12,%s] x [-0.001,0.001]" % float(XR) + ", %d boxes, chained from lambda=-1" % total)


if __name__ == '__main__':
    main()
    strip()
