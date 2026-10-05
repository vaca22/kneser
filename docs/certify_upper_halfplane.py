#!/usr/bin/env python3
"""Arb certificate for Section sec:upper (Kneser's family on the whole upper
half b-plane).

Coordinates.  lambda = lambda_+ is the multiplier of the fixed point
L_+ = e^lambda, a = log b = g(lambda) = lambda e^{-lambda}.  The partner
multiplier is lambda_- = lambda - 2 i theta, where theta solves
    Phi(theta, lambda) = (lambda - 2 i theta) e^{2 i theta} - lambda = 0
on the branch continued from the real exterior ray (theta real in (0,pi)).
The upper exterior E+ = {0 < Im a < pi} minus the closed Shell--Thron
region corresponds to a region Lambda of lambda with |lambda| > 1,
Im lambda > 0, 0 < Im g(lambda) < pi.

Checked (all strict, outward rounded), with f1 = Im g_theta(t),
f2 = Im(conj(s'_theta(t)) g_theta(t)), g = (s(t)-t)/(1-t^2):
  (K) f1, f2 < 0 for -1 < t < 1 and at t = -1; at t = 1 they equal
      -Im(lambda)/2 exactly, so near t = 1 we check d/dt f1, d/dt f2 > 0;
  (I) |theta| < pi (s_theta injective near [-1,1]);
  (M) the first-entry mark (index -1 in the tails).

Part T (tails): Re lambda <= -X0, 0 <= Im lambda <= pi, in the variables
eps = 1/X in [0, 1/X0], y = Im lambda, kappa = 1/lambda.  With
theta = pi - delta, D = delta/kappa solves the contraction
    D = -(pi - kappa D) ell(2 i kappa (pi - kappa D)),  ell(z) = -log(1-z)/z,
and all quantities are scaled by eps so that they are analytic at eps = 0.
"""

import sys
from fractions import Fraction
from math import factorial
from flint import acb, arb, ctx, fmpq

import certify_far_collar as C

ctx.dps = 30
I = acb(0, 1)
PI = arb.pi()
X0 = 12
NH = 90                     # terms of the entire series h


def ball(lo, hi):
    return C.ball(fmpq(lo), fmpq(hi))


def fail(msg):
    print("FAIL:", msg)
    sys.exit(1)


# ------------------------------------------------------------ series tools
def h_and_dh(theta, t, radius):
    """h = (e^{i theta t} - cos theta - i t sin theta)/((1-t^2) theta^2) and
    dh/dt, |theta| <= radius:  h = -sum_{n>=2} i^n theta^{n-2} P_n(t)/n!,
    P_n(t) = sum_{j < n//2} t^{2j + (n mod 2)},  |P_n| <= n/2, |P_n'| <= n^2/2."""
    tpow = [arb(1)]
    for k in range(NH + 2):
        tpow.append(tpow[-1] * t)
    h, dh = acb(0), acb(0)
    pw = acb(1)
    ipow = [acb(1), I, acb(-1), -I]
    for n in range(2, NH):
        r = n % 2
        poly, dpoly = arb(0), arb(0)
        for j in range(n // 2):
            e = 2 * j + r
            poly += tpow[e]
            if e > 0:
                dpoly += e * tpow[e - 1]
        c = ipow[n % 4] * pw / factorial(n)
        h -= c * poly
        dh -= c * dpoly
        pw *= theta
    R = arb(radius)
    assert 2 * R < NH
    tail = R ** (NH - 2) * arb(NH) * NH / (2 * factorial(NH)) / (1 - 2 * R / NH)
    e = acb(arb(0, tail.upper()), arb(0, tail.upper()))
    return h + e, dh + e


def ell(z):
    """-log(1-z)/z = sum z^k/(k+1), |z| <= 0.7."""
    res = acb(0)
    zp = acb(1)
    for k in range(60):
        res += zp / (k + 1)
        zp *= z
    r = abs(z)
    assert r < arb(fmpq(7, 10))
    tail = arb(fmpq(7, 10)) ** 60 / (1 - arb(fmpq(7, 10)))
    return res + acb(arb(0, tail.upper()), arb(0, tail.upper()))


# ------------------------------------------------------------ Part T
def tail_theta(eps, y):
    """kappa, D = delta/kappa, delta for eps-ball (may contain 0), y-ball."""
    kap_over_eps = -1 / (1 - I * y * eps)          # kappa/eps
    kap = kap_over_eps * eps
    # contraction for D on the ball |D + pi| <= 1/2
    Dball = acb(-PI, 0) + acb(arb(0, 0.5), arb(0, 0.5))
    for _ in range(40):
        Dn = -(PI - kap * Dball) * ell(2 * I * kap * (PI - kap * Dball))
        if (Dn.real.lower() > Dball.real.lower() and Dn.real.upper() < Dball.real.upper()
                and Dn.imag.lower() > Dball.imag.lower() and Dn.imag.upper() < Dball.imag.upper()):
            Dball = Dn
            # F maps Dball into itself and contracts: iterate to tighten
            for _ in range(40):
                Dn = -(PI - kap * Dball) * ell(2 * I * kap * (PI - kap * Dball))
                if float(Dn.real.rad()) + float(Dn.imag.rad()) >= 0.999 * (
                        float(Dball.real.rad()) + float(Dball.imag.rad())):
                    Dball = Dn
                    break
                Dball = Dn
            break
        rr = max(float(Dn.real.rad()), float(Dn.imag.rad())) * 1.2 + 1e-12
        Dball = acb(Dn.real.mid(), Dn.imag.mid()) + acb(arb(0, rr), arb(0, rr))
    else:
        return None
    # F(Dball) inside Dball: a fixed point exists (Brouwer); uniqueness:
    # |F'| = O(|kappa|) < 1 there (checked below via a crude Lipschitz bound)
    # Uniqueness: on the fixed convex set S = {|Re D + pi| <= 3/2, |Im D| <= 3/2}
    # (common to all tail boxes) F is a contraction, so the fixed point in S is
    # unique and depends continuously on kappa; the certified ball lies in S.
    S = acb(-PI, 0) + acb(arb(0, 1.5), arb(0, 1.5))
    if not ((Dball.real + PI).abs_upper() < 1.5 and Dball.imag.abs_upper() < 1.5):
        return None
    z = 2 * I * kap * (PI - kap * S)
    r = abs(z).upper()
    if not r < 0.7:
        return None
    dell = acb(0)
    zp = acb(1)
    for k in range(1, 60):
        dell += k * zp / (k + 1)
        zp *= z
    rr = arb(r)
    dtail = 60 * rr ** 59 / (1 - rr) ** 2          # sum_{k>=60} k r^{k-1}
    dell += acb(arb(0, dtail.upper()), arb(0, dtail.upper()))
    lip = abs(kap) * (abs(ell(z)) + 2 * abs(kap) * abs(PI - kap * S) * abs(dell))
    if not lip < 1:
        return None
    return kap, kap_over_eps, Dball, kap * Dball


def tail_box(elo, ehi, ylo, yhi, depth=0):
    eps = ball(elo, ehi)
    y = ball(ylo, yhi)
    res = tail_theta(eps, y)
    ok = res is not None
    if ok:
        kap, koe, D, delta = res
        theta = PI - delta
        lam = -1 / eps + I * y if elo > 0 else None
        # (I) |theta| < pi  <=>  Re(delta) > |delta|^2/(2 pi); divide by eps:
        #   Re(koe D) > eps |koe D|^2 / (2 pi)
        ok = (koe * D).real > eps * abs(koe * D) ** 2 / (2 * PI)
        # scale sigma := eps/sin(theta) = eps/sin(delta) = 1/(koe D sinc(delta))
        sinc = acb(0)
        dp = acb(1)
        for k in range(20):
            sinc += (-1) ** k * dp / factorial(2 * k + 1)
            dp *= delta * delta
        # remainder: |delta| <= 1, first omitted term |delta|^40/41!, geometric
        sinc += acb(arb(0, 1e-48), arb(0, 1e-48))
        if not abs(delta) < 1:
            ok = False
        sig = 1 / (koe * D * sinc)
        radius = fmpq(33, 10)
        # t-intervals
        TAU = fmpq(1, 8)
        segs = []
        n = 32
        for i in range(n):
            segs.append((fmpq(-1) + fmpq(2 * i, n), fmpq(-1) + fmpq(2 * (i + 1), n)))
        for (tl, th_) in segs:
            if not ok:
                break
            ok = tail_t(theta, sig, eps, y, D, koe, tl, th_, TAU)
        # (M) zeta(0) = i cot theta = N(t, sig) with (t,sig) near (0,1/2):
        # scaled target eps*zeta(0) = i eps cos(theta)/sin(theta) = i sig cos(theta)
        if ok:
            ok = tail_mark(theta, sig, eps)
    if ok:
        return 1
    if depth > 10:
        fail("tail box eps=[%s,%s] y=[%s,%s]" % (elo, ehi, ylo, yhi))
    em, ym = (elo + ehi) / 2, (ylo + yhi) / 2
    if (ehi - elo) * 30 > (yhi - ylo):
        return tail_box(elo, em, ylo, yhi, depth + 1) + tail_box(em, ehi, ylo, yhi, depth + 1)
    return tail_box(elo, ehi, ylo, ym, depth + 1) + tail_box(elo, ehi, ym, yhi, depth + 1)


def scaled_parts(theta, sig, eps, t, radius):
    """eps*g, eps*g', eps*s', eps*s'' at t (theta near pi)."""
    h, dh = h_and_dh(theta, t, radius)
    eg = sig * theta * theta * h / I
    edg = sig * theta * theta * dh / I
    esp = sig * theta * (I * theta * t).exp()
    espp = I * theta * esp
    return eg, edg, esp, espp


def tail_t(theta, sig, eps, y, D, koe, tl, th_, TAU, depth=0):
    t = C.ball(tl, th_)
    eg, edg, esp, espp = scaled_parts(theta, sig, eps, t, fmpq(33, 10))
    F1 = eg.imag
    F2 = (esp.conjugate() * eg).imag
    if F1 < 0 and F2 < 0:
        return True
    if th_ == 1 or tl >= 1 - TAU:
        # endpoint trick at t = 1: exact value -Im(lambda)/2 <= 0 (y >= 0),
        # derivative positive on [tl, 1]
        dF1 = edg.imag
        dF2 = (espp.conjugate() * eg + esp.conjugate() * edg).imag
        if th_ == 1 and dF1 > 0 and dF2 > 0:
            return True
    if tl == -1 or th_ <= -1 + TAU:
        # endpoint trick at t = -1: both f1, f2 equal Im(lambda_-)/2 =
        # (y - 2 Re theta)/2 < 0 there, and they decrease on [-1, th_]
        dF1 = edg.imag
        dF2 = (espp.conjugate() * eg + esp.conjugate() * edg).imag
        if tl == -1 and dF1 < 0 and dF2 < 0 and (y - 2 * theta.real) < 0:
            return True
    if depth > 14:
        return False
    tm = (tl + th_) / 2
    return (tail_t(theta, sig, eps, y, D, koe, tl, tm, TAU, depth + 1) and
            tail_t(theta, sig, eps, y, D, koe, tm, th_, TAU, depth + 1))


def tail_mark(theta, sig, eps):
    """Krawczyk for eps*N(t,s) = eps*zeta(0) with (t,s) near (0,1/2)."""
    target = I * sig * theta.cos()

    def eN(t, s):
        eg, _, _, _ = scaled_parts(theta, sig, eps, t, fmpq(33, 10))
        # eps*(s(t)-t) = (1-t^2) eps g
        return eps * t + s * (1 - t * t) * eg

    import numpy as np
    tc, sc = 0.0, 0.5
    for rad in [0.02, 0.05, 0.1, 0.2]:
        tX = arb(tc, rad)
        sX = arb(sc, rad)
        tm, sm = arb(tc), arb(sc)
        Fm = eN(tm, sm) - target
        # Jacobian on the box
        eg, edg, esp, _ = scaled_parts(theta, sig, eps, tX, fmpq(33, 10))
        # d/dt [eps t + s (1-t^2) eps g] = eps + s(-2t eps g + (1-t^2) eps g')
        dt = eps + sX * (-2 * tX * eg + (1 - tX * tX) * edg)
        ds = (1 - tX * tX) * eg
        # midpoint Jacobian (floats)
        egm, edgm, _, _ = scaled_parts(acb(theta.real.mid(), theta.imag.mid()),
                                        acb(sig.real.mid(), sig.imag.mid()),
                                        arb(eps.mid()), arb(tc), fmpq(33, 10))
        a1 = complex(float((arb(eps.mid()) + sc * (1 * edgm)).real.mid()),
                     float((arb(eps.mid()) + sc * (1 * edgm)).imag.mid()))
        a2 = complex(float(egm.real.mid()), float(egm.imag.mid()))
        Jm = np.array([[a1.real, a2.real], [a1.imag, a2.imag]])
        Y = np.linalg.inv(Jm)
        Yq = [[C.fq(Y[0, 0]), C.fq(Y[0, 1])], [C.fq(Y[1, 0]), C.fq(Y[1, 1])]]
        JX = [[dt.real, ds.real], [dt.imag, ds.imag]]
        F = [Fm.real, Fm.imag]
        dx = [tX - tm, sX - sm]
        K = []
        for r in range(2):
            val = [tm, sm][r] - (Yq[r][0] * F[0] + Yq[r][1] * F[1])
            for c in range(2):
                m = (1 if r == c else 0) - (Yq[r][0] * JX[0][c] + Yq[r][1] * JX[1][c])
                val += m * dx[c]
            K.append(val)
        if (K[0].lower() > tX.lower() and K[0].upper() < tX.upper() and
                K[1].lower() > sX.lower() and K[1].upper() < sX.upper()):
            return (K[0].lower() > -1 and K[0].upper() < 1 and
                    K[1].lower() > 0 and K[1].upper() < 1)
    return False


def tail_checks():
    # endpoint t = -1: Im(lambda_-) = y - 2 Re(theta) < 0 for y <= pi:
    # Re(theta) = pi - Re(delta) >= pi - |kappa||D| > pi/2 + tiny
    n = 0
    ecuts = [fmpq(k, 16 * X0) for k in range(17)]
    ycuts = [fmpq(k, 8) for k in range(26)] + [fmpq(3141593, 1000000)]
    for i in range(len(ecuts) - 1):
        for j in range(len(ycuts) - 1):
            n += tail_box(ecuts[i], ecuts[i + 1], ycuts[j], ycuts[j + 1])
    print("PASS tails: Re lambda <= -%d, 0 <= Im lambda <= pi: %d boxes" % (X0, n))




# ================================================================ Part K
# Core: lambda in [XL, XR] x [0, pi] minus the disc |lambda - 1| < R0.
XL, XR = -X0, 5
R0 = fmpq(2, 25)            # 0.08
import cmath as _cm
import numpy as _np


def gfun(L):
    return L * (-L).exp()


def psi_inv(psi):
    """float phi in [-pi,pi] with phi - sin(phi) = psi."""
    lo, hi = -_cm.pi, _cm.pi
    for _ in range(80):
        m = (lo + hi) / 2
        if m - _np.sin(m) < psi:
            lo = m
        else:
            hi = m
    return lo


def inside_gD(A):
    """True if the whole ball A lies in the open set g(D) (starlike, boundary
    rho = e^{-cos phi} at argument psi = phi - sin phi)."""
    if not (A.real.is_finite() and A.imag.is_finite()):
        return False
    if abs(A) < arb(fmpq(36, 100)):          # g(D) contains |a| < 1/e
        return True
    # argument range of A (A away from the negative axis and from 0)
    if not (abs(A) > 0):
        return False
    if not (A.real > 0 or A.imag > 0 or A.imag < 0):
        return False
    ang = A.arg() if not (A.real < 0 and not (A.imag > 0 or A.imag < 0)) else None
    if ang is None or not ang.is_finite():
        return False
    p1, p2 = float(ang.lower()), float(ang.upper())
    # phi range, rigorously bracketed: psi(phi) = phi - sin(phi) increasing
    f1 = psi_inv(p1) - 1e-9
    f2 = psi_inv(p2) + 1e-9
    a1, a2 = arb(C.fq(f1)), arb(C.fq(f2))
    if not ((a1 - a1.sin()) < ang.lower() and (a2 - a2.sin()) > ang.upper()):
        return False
    # min of e^{-cos phi} on [f1, f2]: cos maximal at the point closest to 0
    fstar = 0.0 if f1 <= 0 <= f2 else (f1 if abs(f1) < abs(f2) else f2)
    Rmin = (-(arb(C.fq(fstar)).cos())).exp()
    return abs(A) < Rmin


def Phi(theta, L):
    return (L - 2 * I * theta) * (2 * I * theta).exp() - L


def dPhi(theta, L):
    return 2 * I * (2 * I * theta).exp() * (L - 2 * I * theta - 1)


def theta_float(Lc, th0):
    th = th0
    for _ in range(60):
        F = (Lc - 2j * th) * _cm.exp(2j * th) - Lc
        dF = 2j * _cm.exp(2j * th) * (Lc - 2j * th - 1)
        th -= F / dF
        if abs(F) < 1e-15:
            break
    return th


def krawczyk_theta(Lball, thc, rad):
    """Unique root of Phi(., L) in the disc-box thc +- rad for all L in Lball."""
    B = acb(arb(thc.real, rad), arb(thc.imag, rad))
    m = acb(thc.real, thc.imag)
    dm = 2j * _cm.exp(2j * thc) * (complex(float(Lball.real.mid()), float(Lball.imag.mid())) - 2j * thc - 1)
    Y = acb(C.fq((1 / dm).real), C.fq((1 / dm).imag))
    K = m - Y * Phi(m, Lball) + (1 - Y * dPhi(B, Lball)) * (B - m)
    if (K.real.lower() > B.real.lower() and K.real.upper() < B.real.upper() and
            K.imag.lower() > B.imag.lower() and K.imag.upper() < B.imag.upper()):
        return K
    return None


def deriv_sign(theta, lo, hi, sign, pieces=8):
    """d/dt f1, d/dt f2 have the given sign on [lo, hi]."""
    for k in range(pieces):
        a = lo + (hi - lo) * k / pieces
        b = lo + (hi - lo) * (k + 1) / pieces
        gg, dg, sp, spp = raw_parts(theta, C.ball(a, b))
        d1 = dg.imag
        d2 = (spp.conjugate() * gg + sp.conjugate() * dg).imag
        if sign > 0 and not (d1 > 0 and d2 > 0):
            return False
        if sign < 0 and not (d1 < 0 and d2 < 0):
            return False
    return True


def core_conditions(theta, lam, depth=0):
    """(K) with endpoint tricks, (I), (M) for a theta-ball.
    Right end: f(1) = -Im(lambda)/2 <= 0 and f increasing on [1-tau, 1].
    Left end: f(-1) = Im(lambda_-)/2 < 0 and f decreasing on [-1, -1+tau]."""
    if not abs(theta) < PI:
        return False
    right = fmpq(1)
    for tau in [fmpq(1, 4), fmpq(1, 8), fmpq(1, 16), fmpq(1, 32)]:
        if deriv_sign(theta, 1 - tau, fmpq(1), +1):
            right = 1 - tau
            break
    left = fmpq(-1)
    if (lam - 2 * I * theta).imag < 0:
        for tau in [fmpq(1, 4), fmpq(1, 8), fmpq(1, 16), fmpq(1, 32)]:
            if deriv_sign(theta, fmpq(-1), -1 + tau, -1):
                left = -1 + tau
                break
    n = 32
    for i in range(n):
        a = left + (right - left) * i / n
        b = left + (right - left) * (i + 1) / n
        if not core_t(theta, lam, a, b):
            return False
    return C.mark_box(theta) is not None


def raw_parts(theta, t):
    h, dh = h_and_dh(theta, t, fmpq(33, 10))
    sn = theta.sin()
    gg = theta * theta * h / (I * sn)
    dg = theta * theta * dh / (I * sn)
    sp = theta * (I * theta * t).exp() / sn
    spp = I * theta * sp
    return gg, dg, sp, spp


def core_t(theta, lam, tl, th_, depth=0):
    t = C.ball(tl, th_)
    gg, dg, sp, spp = raw_parts(theta, t)
    f1 = gg.imag
    f2 = (sp.conjugate() * gg).imag
    if f1 < 0 and f2 < 0:
        return True
    if th_ == 1:
        d1 = dg.imag
        d2 = (spp.conjugate() * gg + sp.conjugate() * dg).imag
        if d1 > 0 and d2 > 0:          # f(1) = -Im(lambda)/2 <= 0
            return True
    if tl == -1:
        d1 = dg.imag
        d2 = (spp.conjugate() * gg + sp.conjugate() * dg).imag
        lam_minus = lam - 2 * I * theta
        if d1 < 0 and d2 < 0 and lam_minus.imag < 0:
            return True
    if depth > 14:
        return False
    tm = (tl + th_) / 2
    return core_t(theta, lam, tl, tm, depth + 1) and core_t(theta, lam, tm, th_, depth + 1)


def cell_ball(x0, x1, y0, y1, grow=fmpq(0)):
    wx, wy = (x1 - x0) * grow, (y1 - y0) * grow
    return acb(ball(x0 - wx, x1 + wx), ball(y0 - wy, y1 + wy))


def classify(x0, x1, y0, y1):
    L = cell_ball(x0, x1, y0, y1)
    if abs(L) < 1:
        return 'out'
    # inside the excluded disc about 1
    if abs(L - 1) < arb(R0):
        return 'disc'
    G = gfun(L)
    if G.imag > PI or G.imag < 0:
        return 'out'
    if inside_gD(G):
        return 'out'
    return 'active'


def core_checks():
    import collections
    H0 = fmpq(1, 4)
    cells = []
    nx = int((XR - XL) / H0)
    ny = 13                          # 13/4 > pi
    queue = collections.deque()
    for i in range(nx):
        for j in range(ny):
            queue.append((XL + i * H0, XL + (i + 1) * H0, j * H0, (j + 1) * H0))
    active = []
    while queue:
        x0, x1, y0, y1 = queue.popleft()
        c = classify(x0, x1, y0, y1)
        if c == 'active':
            # cells meeting the disc about 1 are refined until they are small
            L = cell_ball(x0, x1, y0, y1)
            if not (abs(L - 1) > arb(R0)) and x1 - x0 > fmpq(1, 256):
                xm, ym = (x0 + x1) / 2, (y0 + y1) / 2
                queue.extend([(x0, xm, y0, ym), (xm, x1, y0, ym), (x0, xm, ym, y1), (xm, x1, ym, y1)])
                continue
            active.append((x0, x1, y0, y1))
    print("  core: %d active cells" % len(active), flush=True)
    # ---- float theta by breadth-first continuation from the real-ray image
    seedL = complex(_cm.cos(1) / _cm.sin(1), 1.0)
    def centre(c):
        return complex(float((c[0] + c[1]) / 2), float((c[2] + c[3]) / 2))
    # spatial hash for adjacency
    def key(x, y):
        return (int(_np.floor(float(x) * 4)), int(_np.floor(float(y) * 4)))
    buckets = collections.defaultdict(list)
    for idx, c in enumerate(active):
        for kx in range(key(c[0], 0)[0] - 1, key(c[1], 0)[0] + 2):
            for ky in range(key(0, c[2])[1] - 1, key(0, c[3])[1] + 2):
                buckets[(kx, ky)].append(idx)
    def touching(i):
        c = active[i]
        out = set()
        kx, ky = key(c[0], c[2])
        for j in buckets[(kx, ky)]:
            d = active[j]
            if j != i and d[0] <= c[1] and c[0] <= d[1] and d[2] <= c[3] and c[2] <= d[3]:
                out.add(j)
        for j in buckets[key(c[1], c[3])]:
            d = active[j]
            if j != i and d[0] <= c[1] and c[0] <= d[1] and d[2] <= c[3] and c[2] <= d[3]:
                out.add(j)
        return out
    start = min(range(len(active)), key=lambda i: abs(centre(active[i]) - seedL))
    thf = {start: theta_float(centre(active[start]), 1.0 + 0j)}
    order = [start]
    q = collections.deque([start])
    while q:
        i = q.popleft()
        for j in touching(i):
            if j in thf:
                continue
            th = thf[i]
            a, b = centre(active[i]), centre(active[j])
            for k in range(1, 21):
                th = theta_float(a + (b - a) * k / 20, th)
            thf[j] = th
            order.append(j)
            q.append(j)
    unreached = [i for i in range(len(active)) if i not in thf]
    print("  core: reached %d, unreached %d" % (len(thf), len(unreached)), flush=True)
    return active, thf, unreached, touching


def in_certified_collar(B):
    """theta-ball inside the cone or collar of certify_far_collar.py, or inside
    their complex conjugates (the conditions are invariant under
    theta -> conj(theta), t -> -t, zeta -> -conj(zeta))."""
    pl, ph = B.real.lower(), B.real.upper()
    qm = abs(B.imag).upper() if hasattr(abs(B.imag), 'upper') else None
    qm = max(abs(float(B.imag.lower())), abs(float(B.imag.upper())))
    qm = arb(C.fq(qm)) * (1 + arb(fmpq(1, 10 ** 9)))
    if not pl > 0:
        return False
    if ph <= arb(C.P0):
        return qm <= arb(C.CMAX) * pl
    if ph <= arb(C.P1):
        # collar strips are certified up to max V on the strip >= V(p) >= V(ph)
        fr = Fraction(float(ph.upper()))
        phq = fmpq(fr.numerator, fr.denominator) + fmpq(1, 10 ** 12)
        if phq > C.P1:
            return False
        top = C.V(phq) * pl * pl
        if pl < arb(C.P0):
            top = min_arb(top, arb(C.CMAX) * pl)
        return qm <= top
    return False


def min_arb(x, y):
    return x if x < y else (y if y < x else arb(min(float(x.lower()), float(y.lower()))))


def process_cell(c, thguess, depth=0, stats=None):
    x0, x1, y0, y1 = c
    L = cell_ball(x0, x1, y0, y1)
    Lg = cell_ball(x0, x1, y0, y1, fmpq(1, 20))       # slightly enlarged
    cen = complex(float((x0 + x1) / 2), float((y0 + y1) / 2))
    thc = theta_float(cen, thguess)
    B = None
    for rad in [1e-4, 1e-3, 1e-2, 3e-2, 0.1]:
        B = krawczyk_theta(Lg, thc, rad)
        if B is not None:
            break
    ok = B is not None and (in_certified_collar(B) or core_conditions(B, L))
    if ok:
        stats['leaves'].append((c, B, thc))
        return True
    if depth > 9:
        stats['fail'] = ([float(v) for v in c], thc, B is not None)
        return False
    xm, ym = (x0 + x1) / 2, (y0 + y1) / 2
    kids = [(x0, xm, y0, ym), (xm, x1, y0, ym), (x0, xm, ym, y1), (xm, x1, ym, y1)]
    res = True
    for k in kids:
        cls = classify(*k)
        if cls in ('out', 'disc'):
            continue
        res = process_cell(k, thc, depth + 1, stats) and res
        if not res:
            return False
    return res


def branch_consistency(leaves):
    import collections
    S = fmpq(1, 64)
    def k(v):
        return int(_np.floor(float(v / S)))
    buckets = collections.defaultdict(list)
    for idx, (c, B, thc) in enumerate(leaves):
        for kx in range(k(c[0]), k(c[1]) + 1):
            for ky in range(k(c[2]), k(c[3]) + 1):
                buckets[(kx, ky)].append(idx)
    pairs = set()
    for lst in buckets.values():
        for a in lst:
            for b in lst:
                if a < b:
                    ca, cb = leaves[a][0], leaves[b][0]
                    if ca[0] <= cb[1] and cb[0] <= ca[1] and ca[2] <= cb[3] and cb[2] <= ca[3]:
                        pairs.add((a, b))
    bad = 0
    for a, b in pairs:
        (ca, Ba, ta), (cb, Bb, tb) = leaves[a], leaves[b]
        # common edge (or corner) of the two closed cells
        L = acb(ball(max(ca[0], cb[0]), min(ca[1], cb[1])), ball(max(ca[2], cb[2]), min(ca[3], cb[3])))
        # hull of the two theta boxes
        lo_r = min(float(Ba.real.lower()), float(Bb.real.lower()))
        hi_r = max(float(Ba.real.upper()), float(Bb.real.upper()))
        lo_i = min(float(Ba.imag.lower()), float(Bb.imag.lower()))
        hi_i = max(float(Ba.imag.upper()), float(Bb.imag.upper()))
        cen = complex((lo_r + hi_r) / 2, (lo_i + hi_i) / 2)
        rad = max(hi_r - lo_r, hi_i - lo_i) / 2 * 1.01 + 1e-12
        ok = False
        for r in [rad, rad * 2, rad * 4]:
            if krawczyk_theta(L, cen, r) is not None:
                ok = True
                break
        if not ok:
            bad += 1
            if bad <= 15 or bad % 2000 == 0:
                print("   bad pair", [float(v) for v in ca], [float(v) for v in cb],
                      "thc", ta, tb, "radB", float(Ba.real.rad()), float(Bb.real.rad()), flush=True)
    return len(pairs), bad


def core_run():
    active, thf, unreached, touching = core_checks()
    if unreached:
        fail("unreached core cells")
    stats = {'leaves': []}
    for n, i in enumerate(sorted(thf, key=lambda i: active[i])):
        if not process_cell(active[i], thf[i], 0, stats):
            fail("core")
        if n % 40 == 0:
            print("  core cells %d/%d, leaves %d" % (n, len(active), len(stats['leaves'])), flush=True)
    npairs, bad = branch_consistency(stats['leaves'])
    if bad:
        fail("branch consistency: %d of %d pairs" % (bad, npairs))
    print("PASS core: %d leaves, %d adjacent pairs with a common theta branch"
          % (len(stats['leaves']), npairs))


# ================================================================ Part P
# Near the cusp: lambda in D(1, R0) and in Lambda  =>  theta in the cone.
def cusp_quantities(rho, phi):
    """Q1=(|lam|^2-1)/rho, Q2=Im lam/rho, Q3=Im g(lam)/rho^2 and their
    phi-derivatives, for theta = rho e^{i phi} (rho-ball may contain 0)."""
    e = (I * phi).exp()
    theta = rho * e
    v = theta * theta
    # mu - 1 = theta^2 D(theta^2), D from the Bernoulli series
    Dser = acb(0)
    dD = acb(0)
    vp = acb(1)
    for k in range(1, 16):
        coef = (-1) ** k * 4 ** k * C.BERN[k] / factorial(2 * k)
        Dser += coef * vp
        if k >= 2:
            dD += (k - 1) * coef * vp / v if False else 0
        vp *= v
    # derivative dD/dv
    vp = acb(1)
    for k in range(2, 16):
        coef = (-1) ** k * 4 ** k * C.BERN[k] / factorial(2 * k)
        dD += (k - 1) * coef * vp
        vp *= v
    R = arb(fmpq(1, 10)) / PI
    err = PI ** 2 / 3 * R ** 30 / PI ** 2 / (1 - R * R) * 100
    Dser += acb(arb(0, err.upper()), arb(0, err.upper()))
    derr = err * 30 / R ** 2              # tail of sum (k-1) coef v^{k-2}: generous
    dD += acb(arb(0, derr.upper()), arb(0, derr.upper()))
    # zeta = lam - 1 = theta (i + theta D);  u := zeta/rho = e (i + theta D)
    u = e * (I + theta * Dser)
    # d/dphi: theta' = i theta, v' = 2 i v
    du = I * e * (I + theta * Dser) + e * (I * theta * Dser + theta * dD * 2 * I * v)
    Q1 = 2 * u.real + rho * abs(u) ** 2
    dQ1 = 2 * du.real + rho * 2 * (u.conjugate() * du).real
    Q2 = u.imag
    dQ2 = du.imag
    # g(1+zeta) - 1/e = -e^{-1} zeta^2 G(zeta), G = (1-(1+zeta)e^{-zeta})/zeta^2
    zeta = rho * u
    G = acb(0)
    dG = acb(0)
    zp = acb(1)
    # (1+z)e^{-z} = sum (-1)^n z^n (1 - n)/n!  ->  G = sum_{n>=2} (-1)^n (n-1) z^{n-2}/n!
    for n in range(2, 30):
        c = (-1) ** n * (n - 1) / factorial(n)
        G += c * zp
        if n >= 3:
            dG += c * (n - 2) * zp / zeta if False else 0
        zp *= zeta
    zp = acb(1)
    for n in range(3, 30):
        c = (-1) ** n * (n - 1) / factorial(n)
        dG += c * (n - 2) * zp
        zp *= zeta
    G += acb(arb(0, 1e-25), arb(0, 1e-25))
    dG += acb(arb(0, 1e-25), arb(0, 1e-25))
    W = u * u * G
    dW = 2 * u * du * G + u * u * dG * rho * du
    Q3 = -(W.imag) / arb(1).exp()
    dQ3 = -(dW.imag) / arb(1).exp()
    return Q1, dQ1, Q2, dQ2, Q3, dQ3


def cusp_lemma():
    """For 0 < rho <= 0.09: |lam|>=1, Im lam>0, Im g>0 force 0 <= phi <= atan(1/10).
    Also: for |lambda-1| < R0 the root theta with |theta| < 0.09 is unique."""
    # Rouche for lambda_+(theta) = lambda: lambda_+ - 1 - i theta = theta^2 D(theta^2),
    # |D| <= sum |coef_k| r^{2k-2} <= 0.34 for |theta| <= 0.09; on |theta| = 0.09,
    # |i theta| - 0.34*0.0081 > R0 >= |lambda - 1|, so exactly one root of
    # lambda_+(theta) = lambda with |theta| < 0.09 (theta = 0 solves Phi but not this).
    Dbound = arb(0)
    r2 = arb(fmpq(81, 10000))
    for k in range(1, 16):
        Dbound += abs(arb(4) ** k * arb(C.BERN[k]) / factorial(2 * k)) * r2 ** (k - 1)
    Dbound += arb(fmpq(1, 10 ** 20))
    assert Dbound < arb(fmpq(34, 100))
    assert arb(fmpq(9, 100)) - fmpq(34, 100) * arb(fmpq(81, 10000)) > arb(R0)
    rho = ball(0, fmpq(9, 100))
    PHI_C = arb(fmpq(1, 10)).atan()
    W = fmpq(3, 10)
    # windows about the real directions phi=0 and phi=-pi/2, where Q3 (and Q2)
    # vanish identically in rho; monotonicity certified on the whole window
    def window_ok(lo, hi, test):
        m = 400
        for k in range(m):
            a = lo + (hi - lo) * k / m
            b = lo + (hi - lo) * (k + 1) / m
            phi = arb((a + b) / 2, ((b - a) / 2).upper())
            if not test(*cusp_quantities(rho, phi)):
                return False
        return True
    assert window_ok(-arb(W), arb(0), lambda Q1, dQ1, Q2, dQ2, Q3, dQ3: dQ3 > 0)
    assert window_ok(-PI / 2 - W, -PI / 2 + W,
                     lambda Q1, dQ1, Q2, dQ2, Q3, dQ3: dQ2 > 0 and dQ3 < 0)
    n = 0
    cuts = [-PI + 2 * PI * k / 2000 for k in range(2001)]
    for k in range(2000):
        a, b = cuts[k], cuts[k + 1]
        phi = arb((a + b) / 2, ((b - a) / 2).upper())
        if phi.lower() >= 0 and phi.upper() <= PHI_C.lower():
            continue                       # inside the cone
        Q1, dQ1, Q2, dQ2, Q3, dQ3 = cusp_quantities(rho, phi)
        ok = Q1 < 0 or Q2 < 0 or Q3 < 0
        if not ok and phi.lower() > -W and phi.upper() <= PHI_C.lower():
            # phi < 0: Q3(phi) = -int_phi^0 dQ3 < 0; phi >= 0: in the cone
            ok = True
        if not ok and phi.lower() > -PI / 2 - W and phi.upper() < -PI / 2 + W:
            # Q2 > 0 forces phi > -pi/2 (Q2 increasing, zero at -pi/2), and then
            # Q3 < 0 (decreasing, zero at -pi/2)
            ok = True
        if not ok:
            fail("cusp lemma at phi in [%s, %s]" % (a, b))
        n += 1
    print("PASS cusp lemma: %d phi-boxes, rho <= 0.09" % n)


# ------------------------------------------------ parallel driver + interfaces
def _work(args):
    c, th = args
    c = tuple(fmpq(a, b) for (a, b) in c)
    st = {'leaves': []}
    ok = process_cell(c, th, 0, st)
    if not ok:
        return False, st.get('fail')
    def enc(x):
        m = float(x.mid())
        r = float(x.rad()) * 1.0001 + abs(m) * 1e-15 + 1e-300
        return (m, r)
    def cq(q):
        return (int(q.p), int(q.q))
    return ok, [(tuple(cq(v) for v in cc), enc(B.real) + enc(B.imag), t)
                for (cc, B, t) in st['leaves']]


def _unpack(rec):
    c, (rm, rr, im, ir), t = rec
    c = tuple(fmpq(a, b) for (a, b) in c)
    def exact(x):
        fr = Fraction(x)                 # floats are dyadic: exact
        return fmpq(fr.numerator, fr.denominator)
    return (c, acb(arb(exact(rm), rr), arb(exact(im), ir)), t)


def interface_checks(leaves):
    # core / cusp disc: leaves meeting D(1, R0) carry the small root
    n1 = 0
    for c, B, t in leaves:
        L = cell_ball(*c)
        if not (abs(L - 1) > arb(R0)):
            if not abs(B) < arb(fmpq(9, 100)):
                fail("core/disc interface at %s" % [float(v) for v in c])
            n1 += 1
    # core / tails at Re lambda = XL: common root
    n2 = 0
    for c, B, t in leaves:
        if c[0] != XL:
            continue
        y = ball(c[2], c[3])
        eps = arb(fmpq(1, X0))
        res = tail_theta(eps, y)
        if res is None:
            fail("tail theta at interface")
        kap, koe, D, delta = res
        T = PI - delta
        L = acb(arb(XL), y)
        lo_r = min(float(B.real.lower()), float(T.real.lower()))
        hi_r = max(float(B.real.upper()), float(T.real.upper()))
        lo_i = min(float(B.imag.lower()), float(T.imag.lower()))
        hi_i = max(float(B.imag.upper()), float(T.imag.upper()))
        cen = complex((lo_r + hi_r) / 2, (lo_i + hi_i) / 2)
        rad = max(hi_r - lo_r, hi_i - lo_i) / 2 * 1.01 + 1e-12
        if not any(krawczyk_theta(L, cen, r) is not None for r in [rad, 2 * rad, 4 * rad]):
            fail("core/tail interface at y=%s" % [float(c[2]), float(c[3])])
        n2 += 1
    print("PASS interfaces: %d core/disc leaves, %d core/tail leaves" % (n1, n2))


def core_run_parallel(procs=8):
    import multiprocessing as mp
    active, thf, unreached, touching = core_checks()
    if unreached:
        fail("unreached core cells")
    jobs = [(tuple((int(v.p), int(v.q)) for v in active[i]), thf[i]) for i in sorted(thf, key=lambda i: active[i])]
    leaves = []
    with mp.Pool(procs) as pool:
        for n, (ok, lv) in enumerate(pool.imap(_work, jobs)):
            if not ok:
                fail("core cell %s: leaf %s" % (jobs[n][0], lv))
            leaves.extend(_unpack(r) for r in lv)
            if n % 40 == 0:
                print("  core cells %d/%d, leaves %d" % (n, len(jobs), len(leaves)), flush=True)
    import pickle
    with open('/tmp/cusp/leaves.pkl', 'wb') as fh:
        pickle.dump([(tuple((int(v.p), int(v.q)) for v in c),
                      (float(B.real.mid()), float(B.real.rad()), float(B.imag.mid()), float(B.imag.rad())), t)
                     for (c, B, t) in leaves], fh)
    # anchor: the branch equals the real root theta = 1 at lambda = cot 1 + i
    lam_s = acb(arb(1).cos() / arb(1).sin(), arb(1))
    anchored = 0
    for c, B, t in leaves:
        Lc = cell_ball(*c)
        if lam_s.real > Lc.real.lower() and lam_s.real < Lc.real.upper() and \
                lam_s.imag > Lc.imag.lower() and lam_s.imag < Lc.imag.upper():
            if not (B.real.lower() < 1 and B.real.upper() > 1 and
                    B.imag.lower() < 0 and B.imag.upper() > 0):
                fail("anchor: theta-box %s does not contain the real root 1" % B)
            if not (B.real.lower() > 0):
                fail("anchor box contains theta = 0")
            anchored += 1
    if anchored == 0:
        fail("anchor leaf not found")
    print("PASS anchor: theta = 1 at lambda = cot 1 + i (%d leaf)" % anchored)
    npairs, bad = branch_consistency(leaves)
    if bad:
        fail("branch consistency: %d of %d pairs" % (bad, npairs))
    print("PASS core: %d leaves, %d adjacent pairs share one theta branch" % (len(leaves), npairs))
    interface_checks(leaves)


if __name__ == '__main__':
    cusp_lemma()
    tail_checks()
    core_run_parallel(10)
