#!/usr/bin/env python3
"""Arb certificate for the boundary collar of Section sec:far (crossing the
upper Shell--Thron boundary away from the cusp).

Parameter theta, base b(theta)=exp(a(theta)), a=theta*exp(-theta*cot theta)/sin theta,
fixed points L_pm=r*exp(+-i*theta), r=exp(theta*cot theta), multipliers
lambda_pm=theta*cot(theta)+-i*theta.  Chord coordinate
zeta(w)=(w/r-cos theta)/(i sin theta): L_pm -> +-1, chord -> [-1,1],
and zeta(E_b(w))=s(zeta), s(t)=(exp(i theta t)-cos theta)/(i sin theta).
g(t)=(s(t)-t)/(1-t^2).

Region.  Cone  C  = {p(1+ic): 0<p<=P0, 0<=c<=1/10},  P0=1/10;
         collar K = {p+i v p^2: P0<=p<=P1, 0<=v<=V(p)},  P1=11/5.
Checked on C u K (all strict, outward rounded):
 (K1) Im g(t) < 0,                         -1<=t<=1;
 (K2) Im(conj(s'(t)) g(t)) < 0,            -1<=t<=1;
 (ST) d/dq |lambda_+(p+iq)|^2 < 0, |lambda_+|<1 on the top edge;
 (A)  a'(theta) != 0;
 (M)  the first entry of 0,1,E(1),... into the crescent (marks), see below;
 (P)  |Im a| < pi for Re theta <= P2 = 19/10 (principal sheet).
On the cone (M) is the analytic lemma lem:far-cone; this script checks its
constants.  On the collar (M) is checked box by box.
"""

import sys
from math import factorial
from fractions import Fraction
import numpy as np
from flint import acb, arb, ctx, fmpq

ctx.dps = 30
I = acb(0, 1)
P0 = fmpq(1, 10)
P1 = fmpq(11, 5)
CMAX = fmpq(1, 10)
P2 = fmpq(19, 10)
NSER = 70


def ball(lo, hi):
    lo, hi = fmpq(lo), fmpq(hi)
    return arb((lo + hi) / 2, (hi - lo) / 2)


def V(p):
    """Top of the collar, in units of p^2 (piecewise linear, rational)."""
    p = fmpq(p)
    if p <= fmpq(8, 5):
        return fmpq(1, 4)
    return fmpq(1, 4) - (p - fmpq(8, 5)) * fmpq(7, 60)   # 0.18 at p=2.2


# ---------------------------------------------------------------- series
def h_series(theta, t, radius):
    """h=(e^{i theta t}-cos theta-i t sin theta)/((1-t^2) theta^2), |theta|<=radius."""
    t2 = t * t
    res = acb(0)
    pw = acb(1)          # theta^(n-2)
    ipow = [acb(1), I, acb(-1), -I]
    for n in range(2, NSER):
        poly = arb(0)
        tp = arb(1)
        for _ in range(n // 2):
            poly += tp
            tp *= t2
        if n % 2:
            poly *= t
        res -= ipow[n % 4] * pw * poly / factorial(n)
        pw *= theta
    R = arb(radius)
    tail = R ** (NSER - 2) * arb(NSER) / (2 * factorial(NSER)) / (1 - R / NSER)
    return res + acb(arb(0, tail.upper()), arb(0, tail.upper()))


BERN = [fmpq.bernoulli(2 * k) for k in range(0, 16)]


def mu_series(theta, radius):
    """mu=theta*cot(theta) and mu' for |theta|<=radius<=1 (Bernoulli series)."""
    v = theta * theta
    mu = acb(0)
    dmu = acb(0)
    vp = acb(1)
    for k in range(0, 16):
        coef = (-1) ** k * 4 ** k * BERN[k] / factorial(2 * k)
        mu += vp * coef
        vp *= v
    # derivative separately, as a polynomial in theta
    vp = acb(1)
    for k in range(1, 16):
        coef = (-1) ** k * 4 ** k * BERN[k] / factorial(2 * k)
        dmu += 2 * k * coef * vp * theta
        vp *= v
    R = arb(radius) / arb.pi()
    # |coef_k| <= 2 zeta(2k)/pi^{2k} <= (pi^2/3)/pi^{2k}
    tail = arb.pi() ** 2 / 3 * R ** 32 / (1 - R * R)
    dtail = arb.pi() ** 2 / 3 * 40 * R ** 31 / arb.pi() / (1 - R * R) ** 2
    mu += acb(arb(0, tail.upper()), arb(0, tail.upper()))
    dmu += acb(arb(0, dtail.upper()), arb(0, dtail.upper()))
    return mu, dmu


def theta_over_sin(theta, radius):
    """theta/sin(theta) via 1/sum (-1)^k theta^{2k}/(2k+1)!."""
    v = theta * theta
    s = acb(0)
    vp = acb(1)
    for k in range(0, 20):
        s += (-1) ** k * vp / factorial(2 * k + 1)
        vp *= v
    R = arb(radius)
    tail = R ** 40 / factorial(41) / (1 - R * R / 42)
    s += acb(arb(0, tail.upper()), arb(0, tail.upper()))
    return 1 / s


def fail(msg):
    print("FAIL:", msg)
    sys.exit(1)


# ------------------------------------------------------- K1, K2 (scaled)
def k12(theta, scale, radius, t):
    """Return (Im g/p, Im(conj s' g)/p) with theta/p = scale."""
    ts = theta_over_sin(theta, radius)
    gp = -I * scale * ts * h_series(theta, t, radius)
    sp = ts * (I * theta * t).exp()
    return gp.imag, (sp.conjugate() * gp).imag


def check_k12(theta, scale, radius, tsplit=16, depth=0):
    """Split t in [-1,1] until both quantities are certified negative."""
    stack = [(fmpq(-1), fmpq(1))]
    n = 0
    while stack:
        lo, hi = stack.pop()
        a, b = k12(theta, scale, radius, ball(lo, hi))
        if a < 0 and b < 0:
            n += 1
            continue
        if hi - lo < fmpq(1, 4096):
            return False
        mid = (lo + hi) / 2
        stack += [(lo, mid), (mid, hi)]
    return True


# ------------------------------------------------------------- the cone
def cone_checks():
    # parameter boxes p in [p_lo,p_hi] (p_lo may be 0), c in [c_lo,c_hi]
    pcuts = [fmpq(0)] + [fmpq(k, 400) for k in range(1, 41)]
    ccuts = [fmpq(k, 40) for k in range(0, 5)]
    for i in range(len(pcuts) - 1):
        for j in range(len(ccuts) - 1):
            pb = ball(pcuts[i], pcuts[i + 1])
            cb = ball(ccuts[j], ccuts[j + 1])
            scale = acb(1, cb)
            theta = pb * scale
            radius = fmpq(102, 1000)
            if not check_k12(theta, scale, radius):
                fail("cone K1/K2 at p=%s c=%s" % (pcuts[i], ccuts[j]))
            mu, dmu = mu_series(theta, radius)
            lam = mu + I * theta
            # d/dq |lambda|^2 = 2 Re(conj(lambda) * i * (mu' + i))
            dq = 2 * (lam.conjugate() * I * (dmu + I)).real
            if not dq < 0:
                fail("cone dq at p=%s" % pcuts[i])
            # a'/(a theta) = (1-mu)/theta^2 - mu'/theta, both even series
            # (1-mu)/theta^2 and mu'/theta as series:
            v = theta * theta
            s1 = acb(0)
            s2 = acb(0)
            vp = acb(1)
            for k in range(1, 16):
                coef = (-1) ** k * 4 ** k * BERN[k] / factorial(2 * k)
                s1 -= coef * vp
                s2 += 2 * k * coef * vp
                vp *= v
            ratio = s1 - s2
            R = arb(radius) / arb.pi()
            err = arb.pi() ** 2 / 3 * 40 * R ** 30 / arb.pi() ** 2 / (1 - R * R) ** 2
            ratio += acb(arb(0, err.upper()), arb(0, err.upper()))
            if not ratio.real > 0:
                fail("cone a' at p=%s" % pcuts[i])
            # principal sheet: Im a < pi, a = (theta/sin theta) e^{-mu}
            if not abs((theta_over_sin(theta, radius) * (-mu).exp()).imag) < arb.pi():
                fail("cone Im a")
            # w=0 lies above the chord: Im zeta(0) = Re cot(theta) > 0,
            # p*cot(theta) = mu/(1+ic)
            if not (mu / scale).real > 0:
                fail("cone zeta(0)")
    # top edge c = 1/10 lies in the Shell--Thron region:
    # (|lambda|^2-1)/p = -2c + 2p Re((1+ic)^2 D) + p |(1+ic)(i+theta D)|^2,
    # D=(mu-1)/theta^2.
    for i in range(len(pcuts) - 1):
        pb = ball(pcuts[i], pcuts[i + 1])
        scale = acb(1, arb(CMAX))
        theta = pb * scale
        v = theta * theta
        Dser = acb(0)
        vp = acb(1)
        for k in range(1, 16):
            coef = (-1) ** k * 4 ** k * BERN[k] / factorial(2 * k)
            Dser += coef * vp
            vp *= v
        R = arb(fmpq(102, 1000)) / arb.pi()
        err = arb.pi() ** 2 / 3 * R ** 30 / arb.pi() ** 2 / (1 - R * R)
        Dser += acb(arb(0, err.upper()), arb(0, err.upper()))
        val = (-2 * arb(CMAX) + 2 * pb * (scale * scale * Dser).real
               + pb * abs(scale * (I + theta * Dser)) ** 2)
        if not val < 0:
            fail("cone top edge not inside ST at p=%s" % pcuts[i])
    print("PASS cone: K1, K2, d|lambda|^2/dq<0, top edge in ST, a'!=0, 0 above chord")


# ------------------------------------------- analytic mark lemma constants
def cone_mark_constants():
    """Constants of Lemma lem:far-cone (first entry on the cone).

    With q=exp(chi), v=i theta/(1-q), T(w)=sinh(w)/w:
      chi_{n+1}-chi_n = i theta + log T(v-i theta) - log T(v)       (exact).
    The segment v-tau*i*theta = i theta (1/(1-q) - tau), 0<=tau<=1, has
    modulus <= |theta|(1+1/|1-q|); |1-q| >= sin y for 0<y<=pi/2 and >= 1 for
    pi/2<=y<=3pi/2.  No bound on x = Re chi is needed.
    """
    pi = arb.pi()
    p = arb(P0)
    th2 = arb(fmpq(101, 100))                 # |theta|^2 <= 1.01 p^2
    # radius of the segments while y >= 3p (increasing in p, checked at P0)
    rho = th2.sqrt() * p * (1 + 1 / (3 * p).sin())
    assert rho < arb(fmpq(45, 100)), rho
    rho = arb(fmpq(45, 100))
    x = rho * rho / (pi * pi)
    K = 1 / (3 * (1 - x))                     # |(log T)'(w)| <= K|w|
    K2 = (1 + x) / (3 * (1 - x) ** 2)         # |(log T)''(w)| <= K2
    assert K < arb(fmpq(341, 1000))
    # step correction C_n <= K |theta|^2 (1+1/|1-q_n|) <= 0.16 p
    cstep = arb(fmpq(341, 1000)) * th2 * p * (1 + 1 / (3 * p).sin())
    assert cstep < arb(fmpq(16, 100)), cstep
    # |log T(w)| small, so principal logs are continuous on the segments
    assert (rho.sinh() / rho - 1) < arb(fmpq(1, 10))
    # near the chord (|1-q|>=1): |f_chi' - 1| <= |theta| K2 |v q/(1-q)|
    #                                         <= 2 K2 |theta|^2 < 1/10
    assert 2 * K2 * th2 * p * p < arb(fmpq(1, 10))
    # s is injective on sets of diameter < 2 pi/|theta|; the crossing
    # segment and the chord lie in |zeta| <= 3
    assert 6 * th2.sqrt() * p < 2 * pi
    # initial point chi_0/p for the whole cone (series in v=theta^2)
    Rr = arb(fmpq(102, 1000))
    v = acb(ball(0, P0 * P0), ball(0, P0 * P0 / 5))
    s = sum(((-1) ** k * v ** k / factorial(2 * k + 1) for k in range(8)), acb(0))
    co = sum(((-1) ** k * v ** k / factorial(2 * k) for k in range(8)), acb(0))
    st = Rr ** 16 / factorial(16) / (1 - Rr * Rr / 272)
    s += acb(arb(0, st.upper()), arb(0, st.upper()))
    co += acb(arb(0, st.upper()), arb(0, st.upper()))
    rr = (co / s).exp()
    d = rr * s / (1 - rr * co)
    tt = -v * d * d
    assert abs(tt) < arb(fmpq(3, 100))
    at = sum((tt ** k / (2 * k + 1) for k in range(10)), acb(0))
    tail = arb(fmpq(3, 100)) ** 10 / (21 * (1 - arb(fmpq(3, 100))))
    at += acb(arb(0, tail.upper()), arb(0, tail.upper()))
    chi0 = acb(1, ball(0, CMAX)) * (-2 * I * d * at)
    assert chi0.imag > 3 and chi0.imag < arb(fmpq(33, 10)), chi0
    print("PASS cone mark constants: K=%s, step correction <= 0.16p, Im chi0/p in (3,3.3)"
          % K)


# ------------------------------------------------------------ the collar
def fq(x):
    fr = Fraction(x).limit_denominator(10 ** 12)
    return fmpq(fr.numerator, fr.denominator)


def s_raw(theta, z):
    return ((I * theta * z).exp() - theta.cos()) / (I * theta.sin())


def s_fun(theta, z):
    """Mean-value (centred) enclosure of s_theta(z) over the balls theta, z."""
    thm = acb(theta.real.mid(), theta.imag.mid())
    zm = acb(z.real.mid(), z.imag.mid())
    val = s_raw(thm, zm)
    e = (I * theta * z).exp()
    sn = theta.sin()
    d_th = (I * z * e + sn) / (I * sn) - (e - theta.cos()) * theta.cos() / (I * sn * sn)
    d_z = theta * e / sn
    return val + d_th * (theta - thm) + d_z * (z - zm)


def ds_fun(theta, z):
    return theta * (I * theta * z).exp() / theta.sin()


def krawczyk(theta, target_fn, t_c, s_c, rad_t, rad_s):
    """Prove: for every parameter in the balls, N(t,sig)=target has a unique
    solution in [t_c+-rad_t] x [s_c+-rad_s].  Returns the box or None."""
    tX = arb(t_c, rad_t)
    sX = arb(s_c, rad_s)
    tm, sm = arb(t_c), arb(s_c)
    tg = target_fn()

    def N(t, sg):
        st = s_fun(theta, acb(t))
        return acb(t) + sg * (st - t)

    Fm = N(tm, sm) - tg
    # Jacobian on box
    stX = s_fun(theta, acb(tX))
    dtX = 1 + sX * (ds_fun(theta, acb(tX)) - 1)
    dsX = stX - tX
    # float midpoint Jacobian
    thm = complex(float(theta.real.mid()), float(theta.imag.mid()))
    import cmath
    sT = (cmath.exp(1j * thm * t_c) - cmath.cos(thm)) / (1j * cmath.sin(thm))
    dT = thm * cmath.exp(1j * thm * t_c) / cmath.sin(thm)
    a1 = 1 + s_c * (dT - 1)
    a2 = sT - t_c
    Jm = np.array([[a1.real, a2.real], [a1.imag, a2.imag]])
    Y = np.linalg.inv(Jm)
    Yq = [[fq(Y[0, 0]), fq(Y[0, 1])], [fq(Y[1, 0]), fq(Y[1, 1])]]
    JX = [[dtX.real, dsX.real], [dtX.imag, dsX.imag]]
    F = [Fm.real, Fm.imag]
    dx = [tX - tm, sX - sm]
    K = []
    for r in range(2):
        val = [tm, sm][r] - (Yq[r][0] * F[0] + Yq[r][1] * F[1])
        for c in range(2):
            m = (1 if r == c else 0) - (Yq[r][0] * JX[0][c] + Yq[r][1] * JX[1][c])
            val += m * dx[c]
        K.append(val)
    lo_t, hi_t = tX.lower(), tX.upper()
    lo_s, hi_s = sX.lower(), sX.upper()
    if (K[0].lower() > lo_t and K[0].upper() < hi_t and
            K[1].lower() > lo_s and K[1].upper() < hi_s):
        return K
    return None


def float_solve(thm, zm, t0=None, s0=None):
    import cmath
    s = lambda t: (cmath.exp(1j * thm * t) - cmath.cos(thm)) / (1j * cmath.sin(thm))
    ds = lambda t: thm * cmath.exp(1j * thm * t) / cmath.sin(thm)
    starts = [(t0, s0)] if t0 is not None else [(a, b) for a in np.linspace(-.95, .95, 20)
                                                for b in np.linspace(.05, .95, 6)]
    for t, sg in starts:
        for _ in range(60):
            if abs(t) > 1.5 or abs(sg) > 3:
                break
            Fv = t + sg * (s(t) - t) - zm
            A = 1 + sg * (ds(t) - 1)
            B = s(t) - t
            M = np.array([[A.real, B.real], [A.imag, B.imag]])
            try:
                d = np.linalg.solve(M, [-Fv.real, -Fv.imag])
            except np.linalg.LinAlgError:
                break
            t += d[0]
            sg += d[1]
            if abs(t) > 1.5 or abs(sg) > 3:
                break
        try:
            if abs(t + sg * (s(t) - t) - zm) < 1e-12 and -1 < t < 1:
                return t, sg
        except (OverflowError, ValueError):
            continue
    return None


def in_H(theta, zball):
    """Certify zeta-ball lies in the open crescent: N(t,sig)=zeta with
    -1<t<1, 0<sig<1."""
    thm = complex(float(theta.real.mid()), float(theta.imag.mid()))
    if not (zball.real.is_finite() and zball.imag.is_finite()):
        return False
    zm = complex(float(zball.real.mid()), float(zball.imag.mid()))
    sol = float_solve(thm, zm)
    if sol is None:
        return False
    t0, s0 = sol
    for rad in [1e-6, 1e-4, 1e-3, 1e-2, 3e-2, 1e-1]:
        rad_t = rad
        rad_s = rad
        K = krawczyk(theta, lambda: zball, t0, s0, rad_t, rad_s)
        if K is not None:
            ok = (K[0].lower() > -1 and K[0].upper() < 1 and
                  K[1].lower() > 0 and K[1].upper() < 1)
            return ok
    return False


def seam_ok(theta, zball, thabs):
    """Straddle case: zeta-ball within D=[a,b]x[-rho,rho], with
    D_low subset of H (sigma>=0 automatically) and s(D_up) subset of H."""
    if not (zball.real.is_finite() and zball.imag.is_finite()):
        return False
    re_lo, re_hi = zball.real.lower(), zball.real.upper()
    im_lo, im_hi = zball.imag.lower(), zball.imag.upper()
    rho = max(abs(float(im_lo)), abs(float(im_hi)))
    rho = fq(rho * 1.5 + 1e-8)
    a, b = fq(float(re_lo) - 1e-8), fq(float(re_hi) + 1e-8)
    if not (a > -1 and b < 1) or rho > fmpq(1, 4):
        return False
    # injectivity of s on D u [-1,1]: |theta|*(2+2rho) < 2pi
    if not thabs * (2 + 2 * arb(rho)) < 2 * arb.pi():
        return False
    Dlow = acb(ball(a, b), ball(-rho, 0))
    Dup = acb(ball(a, b), ball(0, rho))
    # the zeta-ball lies in D (checked in Arb)
    if not (zball.real > arb(a) and zball.real < arb(b) and
            zball.imag > -arb(rho) and zball.imag < arb(rho)):
        return False
    thm = complex(float(theta.real.mid()), float(theta.imag.mid()))
    # (i) N(t,sig)=zeta for zeta in D_low: sigma in [-delta, smax<1]
    zm = complex(float(Dlow.real.mid()), float(Dlow.imag.mid()))
    sol = float_solve(thm, zm)
    if sol is None:
        return False
    ok1 = False
    for rad in [1e-3, 1e-2, 3e-2, 1e-1]:
        K = krawczyk(theta, lambda: Dlow, sol[0], sol[1], rad, rad)
        if K is not None:
            ok1 = (K[0].lower() > -1 and K[0].upper() < 1 and K[1].upper() < 1)
            break
    if not ok1:
        return False
    # (ii) N(t,sig)=s(zeta) for zeta in D_up: sigma in [smin>0, 1+delta]
    img = s_fun(theta, Dup)
    zm = complex(float(img.real.mid()), float(img.imag.mid()))
    sol = float_solve(thm, zm)
    if sol is None:
        return False
    # The box must contain the known roots (t,1), t in [a,b], of the real
    # edge, so that by uniqueness sigma=1 exactly there (then sigma<1 above).
    tc, sc = sol
    need_t = max(abs(tc - float(a)), abs(float(b) - tc)) + 1e-9
    need_s = abs(1 - sc) + 1e-9
    for rad in [1e-3, 1e-2, 3e-2, 1e-1]:
        rt, rs = max(rad, need_t), max(rad, need_s)
        K = krawczyk(theta, lambda: img, tc, sc, rt, rs)
        if K is not None:
            X_t = arb(tc, rt)
            X_s = arb(sc, rs)
            contains = (X_t.lower() < arb(a) and X_t.upper() > arb(b) and
                        X_s.lower() < 1 and X_s.upper() > 1)
            return (contains and K[0].lower() > -1 and K[0].upper() < 1
                    and K[1].lower() > 0)
    return False


def logT(w):
    return (w.sinh() / w).log()


def dlogT(w):
    """(log T)'(w) = coth w - 1/w = sum_k 4^k B_2k w^(2k-1)/(2k)!, |w|<=1."""
    res = acb(0)
    w2 = w * w
    wp = w
    for k in range(1, 16):
        res += 4 ** k * BERN[k] / factorial(2 * k) * wp
        wp *= w2
    x = arb(1) / (arb.pi() ** 2)
    tail = (arb.pi() ** 2 / 3) * x ** 16 / (1 - x)
    return res + acb(arb(0, tail.upper()), arb(0, tail.upper()))


def step_corr(theta, chi):
    """Centered enclosure of log T(v - i theta) - log T(v), v = i theta/(1-e^chi)."""
    q = chi.exp()
    v = I * theta / (1 - q)
    vm = acb(v.real.mid(), v.imag.mid())
    d0 = logT(vm - I * theta) - logT(vm)
    if abs(v) < 1 and abs(v - I * theta) < 1:
        dd = dlogT(v - I * theta) - dlogT(v)
    else:
        dd = (1 / (v - I * theta).tanh() - 1 / (v - I * theta)) - (1 / v.tanh() - 1 / v)
    return d0 + dd * (v - vm)


def dlogT_any(w):
    if abs(w) < 1:
        return dlogT(w)
    return 1 / w.tanh() - 1 / w


def orbit_step(theta, chi):
    """chi -> chi + i theta + D, and the partials of D."""
    q = chi.exp()
    v = I * theta / (1 - q)
    d1 = dlogT_any(v - I * theta)
    d0 = dlogT_any(v)
    D_chi = (d1 - d0) * v * q / (1 - q)
    D_th = d1 * (v / theta - I) - d0 * v / theta
    return D_chi, D_th


def chi_start(theta):
    """chi_0 = log((z0-1)/(z0+1)), z0 = zeta(1), and d chi_0/d theta."""
    if abs(theta) < 1:
        mu, dmu = mu_series(theta, 1)
    else:
        mu = theta * theta.cos() / theta.sin()
        dmu = theta.cos() / theta.sin() - theta / theta.sin() ** 2
    r = mu.exp()
    num = 1 / r - theta.cos()
    z0 = num / (I * theta.sin())
    dnum = -dmu / r + theta.sin()
    dz0 = (dnum * theta.sin() - num * theta.cos()) / (I * theta.sin() ** 2)
    chi0 = ((z0 - 1) / (z0 + 1)).log()
    return chi0, 2 / (z0 * z0 - 1) * dz0


def mark_box(theta):
    """First entry of 0, 1, E(1), ... into the crescent, for a theta-ball.
    The orbit of 1 is iterated in chi=log q, q=(zeta-1)/(zeta+1), by the exact
    step chi -> chi + i theta + log T(v - i theta) - log T(v), v=i theta/(1-q),
    in mean-value form around the midpoint parameter."""
    thabs = abs(theta)
    # w_{-1} = 0: zeta(0) = i cot(theta)
    z = I * theta.cos() / theta.sin()
    if not z.imag > 0:
        if z.imag < 0 and in_H(theta, z):
            return -1
        return -1 if seam_ok(theta, z, thabs) else None
    zprev = z                         # w_{-1} = 0 is above the chord
    thm = acb(theta.real.mid(), theta.imag.mid())
    delta = theta - thm
    Cm, _ = chi_start(thm)            # tight value at the midpoint
    Cb, J = chi_start(theta)          # derivative enclosure on the box
    B = Cm + J * delta
    for n in range(0, 400):
        q = B.exp()
        z = (1 + q) / (1 - q)
        if z.imag > 0:
            zprev = z
            D_chi, D_th = orbit_step(theta, B)
            J = J * (1 + D_chi) + I + D_th
            Cm = Cm + I * thm + step_corr(thm, Cm)
            B = Cm + J * delta
            continue
        if z.imag < 0 and in_H(theta, z):
            return n
        if seam_ok(theta, z, thabs):
            return n
        # the previous point is just above the chord: seam chart there
        if zprev is not None and seam_ok(theta, zprev, thabs):
            return n
        return None
    return None


def collar_box(plo, phi, vlo, vhi, depth=0, stats=None):
    pb = ball(plo, phi)
    vb = ball(vlo, vhi)
    theta = acb(pb, vb * pb * pb)
    scale = acb(1, vb * pb)
    radius = fmpq(245, 100)
    ok = check_k12(theta, scale, radius)
    # ST monotonicity and a' != 0 (direct formulas, |theta|>=0.1)
    if phi <= fmpq(4, 5):
        mu, dmu = mu_series(theta, 1)
    else:
        cot = theta.cos() / theta.sin()
        mu = theta * cot
        dmu = cot - theta / (theta.sin() ** 2)
    lam = mu + I * theta
    dq = 2 * (lam.conjugate() * I * (dmu + I)).real
    ok = ok and dq < 0
    aprime_over_a = (1 - mu) / theta - dmu
    ok = ok and (abs(aprime_over_a) > 0)
    if phi <= P2:
        # principal sheet: 0 <= Im a < pi on the fibre, a = theta e^{-mu}/sin(theta)
        a_val = theta * (-mu).exp() / theta.sin()
        ok = ok and a_val.imag < arb.pi() and a_val.imag > -arb.pi()
    n = mark_box(theta) if ok else None
    if ok and n is not None:
        stats['boxes'] += 1
        stats['marks'].setdefault(n, 0)
        stats['marks'][n] += 1
        return True
    if depth > 14:
        fail("collar box p=[%s,%s] v=[%s,%s] (k12/dq/a' ok=%s)" % (plo, phi, vlo, vhi, ok))
    pm = (plo + phi) / 2
    vm = (vlo + vhi) / 2
    if phi - plo > (vhi - vlo) * pm * pm * 4:
        return (collar_box(plo, pm, vlo, vhi, depth + 1, stats) and
                collar_box(pm, phi, vlo, vhi, depth + 1, stats))
    return (collar_box(plo, phi, vlo, vm, depth + 1, stats) and
            collar_box(plo, phi, vm, vhi, depth + 1, stats))


def top_edge(plo, phi, top, depth=0):
    pb = ball(plo, phi)
    theta = acb(pb, arb(top) * pb * pb)
    if phi <= fmpq(4, 5):
        mu, _ = mu_series(theta, 1)
    else:
        mu = theta * theta.cos() / theta.sin()
    if abs(mu + I * theta) < 1:
        return True
    if depth > 16:
        return False
    pm = (plo + phi) / 2
    return top_edge(plo, pm, top, depth + 1) and top_edge(pm, phi, top, depth + 1)


def collar_checks():
    stats = {'boxes': 0, 'marks': {}}
    npb = 440
    for i in range(npb):
        plo = P0 + (P1 - P0) * i / npb
        phi = P0 + (P1 - P0) * (i + 1) / npb
        # certify the box up to max V on the strip; |lambda_+| is decreasing
        # in q (checked), so the top-edge test at min V covers v = V(p).
        collar_box(plo, phi, fmpq(0), max(V(plo), V(phi)), 0, stats)
        if not top_edge(plo, phi, min(V(plo), V(phi))):
            fail("collar top edge at p=%s" % plo)
        if i % 40 == 0:
            print("  collar p<=%.3f boxes=%d marks=%s" % (float(phi), stats['boxes'],
                                                        stats['marks']), flush=True)
    print("PASS collar: K1, K2, dq<0, a'!=0, top in ST, first-entry mark on %d boxes %s"
          % (stats['boxes'], stats['marks']))


if __name__ == '__main__':
    cone_checks()
    cone_mark_constants()
    collar_checks()
