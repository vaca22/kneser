#!/usr/bin/env python3
"""
Independent re-verification of Proposition prop:upper-cert
(main.tex, Sec. sec:upper; Appendix app:upper), written only from the paper.

Arithmetic: mpmath.iv (outward-rounded real intervals) + a small complex
rectangle class built on it, Python Fractions for exact geometry.  Floats are
used only for guesses (Newton seeds, Krawczyk centres/preconditioners).

Parts
  (P) cusp     |lambda-1|<0.08 : Rouche root lies in Theta_C  (analytic + intervals)
  (T) tails    Re lambda<=-12  : contraction for D, crescent ineqs, |theta|<pi, mark -1
  (K) core     [-12,5]x[0,pi] minus |lambda-1|<0.08 : quadtree cover / exclusion,
               Krawczyk root boxes, crescent ineqs, |theta|<pi, Im lambda_-<0, mark
  (I) interfaces: adjacency (continuity), anchor theta=1 at cot1+i, tail/core, cusp/core

Reformulation of Lemma far-cert(1) used here (derived independently):
  with e=1-t on [0,1] (plus side, L0=lambda, tau=-i theta) resp. e=1+t on [-1,0]
  (minus side, L0=lambda-2i theta, tau=+i theta), phi(x)=(e^x-1)/x, chi(x)=(e^x-1-x)/x^2:
      g(t)   = -/+ P(e)/(2-e),          P = L0*phi(tau e) - 1
      conj(s'(t)) g(t) = -/+ Q(e)/(2-e), Q = conj(L0) e^{conj(tau) e} P
  so f1<0, f2<0  <=>  sgn*Im P>0, sgn*Im Q>0  (sgn=+1 plus side, -1 minus side), and
      Im P = Im L0 + e*Im(L0 tau chi(tau e))
      Im Q = Im L0 + e*Im(|L0|^2 [e^{tb e} tau chi(tau e) + tb phi(tb e)] - conj(L0) tb phi(tb e))
  (tb=conj(tau)) which removes the degeneracy Im lambda -> 0 at t=+-1.
"""
import sys, os, time, math, cmath, pickle, argparse
from fractions import Fraction as Fr
from mpmath import iv, mp, mpf

iv.prec = 64
mp.prec = 64

IV = iv.mpf
_IVT = type(IV(1))
PI = iv.pi
ONE = IV(1)
ZERO = IV(0)

LOGFILE = None


def log(*a):
    s = time.strftime('%H:%M:%S ') + ' '.join(str(x) for x in a)
    print(s, flush=True)
    if LOGFILE:
        with open(LOGFILE, 'a') as f:
            f.write(s + '\n')


# ----------------------------------------------------------------- basics
def I(x):
    if isinstance(x, _IVT):
        return x
    if isinstance(x, Fr):
        return IV(x.numerator) / IV(x.denominator)
    return IV(x)


def hull(a, b):
    return IV([min(a.a, b.a), max(a.b, b.b)])


def ivfrom(lo, hi):
    return IV([lo, hi])


def frac_of(thin):
    """exact Fraction of a thin ivmpf endpoint"""
    s, man, e, bc = thin._mpi_[0]
    v = Fr(man) * (Fr(2) ** e)
    return -v if s else v


def fl(x):
    return float(x.mid)


def sqrt_hi(x):
    """upper bound of sqrt(sup x) for x>=0"""
    return iv.sqrt(IV(x.b)).b


class C:
    __slots__ = ('re', 'im')

    def __init__(s, re, im=None):
        s.re = I(re)
        s.im = ZERO if im is None else I(im)

    def __add__(s, o):
        if isinstance(o, C):
            return C(s.re + o.re, s.im + o.im)
        return C(s.re + o, s.im)
    __radd__ = __add__

    def __sub__(s, o):
        if isinstance(o, C):
            return C(s.re - o.re, s.im - o.im)
        return C(s.re - o, s.im)

    def __rsub__(s, o):
        return C(o - s.re, -s.im)

    def __neg__(s):
        return C(-s.re, -s.im)

    def __mul__(s, o):
        if isinstance(o, C):
            return C(s.re * o.re - s.im * o.im, s.re * o.im + s.im * o.re)
        return C(s.re * o, s.im * o)
    __rmul__ = __mul__

    def conj(s):
        return C(s.re, -s.im)

    def abs2(s):
        return s.re ** 2 + s.im ** 2

    def __truediv__(s, o):
        if isinstance(o, C):
            d = o.abs2()
            if not (d.a > 0):
                raise ZeroDivisionError
            n = s * o.conj()
            return C(n.re / d, n.im / d)
        return C(s.re / o, s.im / o)

    def __rtruediv__(s, o):
        return C(o) / s

    def mid(s):
        return complex(fl(s.re), fl(s.im))

    def inside(s, o):
        """s strictly inside o"""
        return (s.re.a > o.re.a) and (s.re.b < o.re.b) and (s.im.a > o.im.a) and (s.im.b < o.im.b)

    def subset(s, o):
        return (s.re.a >= o.re.a) and (s.re.b <= o.re.b) and (s.im.a >= o.im.a) and (s.im.b <= o.im.b)

    def inter(s, o):
        ra, rb = max(s.re.a, o.re.a), min(s.re.b, o.re.b)
        ia, ib = max(s.im.a, o.im.a), min(s.im.b, o.im.b)
        if ra > rb or ia > ib:
            return None
        return C(IV([ra, rb]), IV([ia, ib]))

    def chull(s, o):
        return C(hull(s.re, o.re), hull(s.im, o.im))

    def raw(s):
        return (s.re._mpi_, s.im._mpi_)

    @staticmethod
    def fromraw(r):
        return C(iv.make_mpf(r[0]), iv.make_mpf(r[1]))

    def __repr__(s):
        return 'C(%s,%s)' % (s.re, s.im)


II = C(0, 1)


def cball(z, r):
    return C(IV([z.real - r, z.real + r]), IV([z.imag - r, z.imag + r]))


def sinh_iv(y):
    ea, eb = iv.exp(IV(y.a)), iv.exp(IV(y.b))
    sa = (ea - 1 / ea) / 2
    sb = (eb - 1 / eb) / 2
    return IV([sa.a, sb.b])


def cosh_iv(y):
    def ch(v):
        ev = iv.exp(IV(v))
        return (ev + 1 / ev) / 2
    if y.a >= 0:
        return IV([ch(y.a).a, ch(y.b).b])
    if y.b <= 0:
        return IV([ch(y.b).a, ch(y.a).b])
    return IV([ONE.a, max(ch(y.a).b, ch(y.b).b)])


def cexp(z):
    r = iv.exp(z.re)
    return C(r * iv.cos(z.im), r * iv.sin(z.im))


def csin(z):
    return C(iv.sin(z.re) * cosh_iv(z.im), iv.cos(z.re) * sinh_iv(z.im))


def ccos(z):
    return C(iv.cos(z.re) * cosh_iv(z.im), -(iv.sin(z.re) * sinh_iv(z.im)))


def errbox(eps):
    e = IV([-eps, eps])
    return C(e, e)


# ------------------------------------------------------------ series
FACT = [ONE]
for _k in range(1, 80):
    FACT.append(FACT[-1] * _k)
PHI_C = [1 / FACT[k + 1] for k in range(70)]   # phi(x)=sum x^k/(k+1)!
CHI_C = [1 / FACT[k + 2] for k in range(70)]   # chi(x)=sum x^k/(k+2)!


def _horner(coef, x, N):
    acc = C(coef[N - 1])
    for k in range(N - 2, -1, -1):
        acc = acc * x + coef[k]
    return acc


def _nterms(R, shift):
    # smallest N with R^N/(N+shift)! < 1e-19
    N = 4
    while True:
        t = R ** N / math.factorial(N + shift)
        if t < 1e-19 and R / (N + shift + 1) < 0.5:
            return N
        N += 1


def phi(x):
    R2 = x.abs2()
    R = float(sqrt_hi(R2)) * (1 + 1e-12) + 1e-300
    if R > 1.5 and R2.a > 0.25:
        return (cexp(x) - 1) / x
    N = _nterms(R, 1)
    acc = _horner(PHI_C, x, N)
    Ri = IV(R)
    tail = (Ri ** N / FACT[N + 1] / (1 - Ri / (N + 2))).b
    return acc + errbox(tail)


def chi(x):
    R2 = x.abs2()
    R = float(sqrt_hi(R2)) * (1 + 1e-12) + 1e-300
    if R > 1.5 and R2.a > 0.25:
        return (cexp(x) - 1 - x) / (x * x)
    N = _nterms(R, 2)
    acc = _horner(CHI_C, x, N)
    Ri = IV(R)
    tail = (Ri ** N / FACT[N + 2] / (1 - Ri / (N + 3))).b
    return acc + errbox(tail)


# ------------------------------------------------ crescent inequalities
def crescent_side(L0, tau, sgn, nu, ImL0=None, nE=16, maxdepth=9):
    """Check sgn*Im P(e)>0 and sgn*Im Q(e)>0 for all e in (0,1].
    ImL0: optional sharper enclosure of Im L0 (dependency control).
    Returns (ok, number of e-intervals)."""
    tb = tau.conj()
    imL0 = L0.im if ImL0 is None else ImL0
    kroute = (sgn * imL0).a >= 0
    aL2 = L0.abs2()
    L0c = L0.conj()
    stack = [(Fr(k, nE), Fr(k + 1, nE), 0) for k in range(nE)]
    cnt = 0
    while stack:
        e0, e1, d = stack.pop()
        cnt += 1
        E = IV([I(e0).a, I(e1).b])
        x = tau * E
        xb = tb * E
        ph = phi(x)
        P = L0 * ph - nu
        okP = (sgn * P.im).a > 0
        if not okP and kroute:
            KP = (L0 * tau * chi(x)).im
            okP = (sgn * KP).a > 0
        okQ = False
        if okP:
            ex = cexp(xb)
            Q = L0c * ex * P
            okQ = (sgn * Q.im).a > 0
            if not okQ and kroute:
                phb = phi(xb)
                KQ = (ex * tau * chi(x) + tb * phb) * aL2 - (L0c * tb * phb) * nu
                okQ = (sgn * KQ.im).a > 0
        if okP and okQ:
            continue
        if d >= maxdepth:
            return False, cnt
        m = (e0 + e1) / 2
        stack.append((e0, m, d + 1))
        stack.append((m, e1, d + 1))
    return True, cnt


# ------------------------------------------------ mark: N_theta(t,s)=zeta
def mark_kraw(th, sn, cs, c0, guess, radii=(1e-6, 1e-5, 1e-4, 1e-3, 1e-2, 3e-2, 0.06, 0.1, 0.16)):
    """Existence of (t,s) in (-1,1)x(0,1) with
       Psi(t,s)= i sn t (1-s) + s (e^{i th t} - cs) + c0 = 0,
    where th, sn=sin th, cs=cos th, c0 are complex intervals.  (For zeta given,
    c0 = -i sn zeta; for zeta(0)=i cot th, c0 = cs.)  Psi=0 <=> N_th(t,s)=zeta."""
    t0, s0 = guess
    isn = II * sn
    ith = II * th

    def Psi(t, s):
        return isn * t * (1 - s) + (cexp(ith * t) - cs) * s + c0

    def Jac(t, s):
        et = cexp(ith * t)
        dt = isn * (1 - s) + ith * et * s
        ds = -(isn * t) + et - cs
        return dt, ds
    # float preconditioner
    dtf, dsf = Jac(IV(t0), IV(s0))
    a11, a12, a21, a22 = fl(dtf.re), fl(dsf.re), fl(dtf.im), fl(dsf.im)
    det = a11 * a22 - a12 * a21
    if det == 0 or not math.isfinite(det):
        return None
    Y = [[a22 / det, -a12 / det], [-a21 / det, a11 / det]]
    # rigorous nonsingularity of Y
    detY = IV(Y[0][0]) * IV(Y[1][1]) - IV(Y[0][1]) * IV(Y[1][0])
    if not (detY.a > 0 or detY.b < 0):
        return None
    tm, sm = IV(t0), IV(s0)
    F = Psi(tm, sm)
    YF0 = IV(Y[0][0]) * F.re + IV(Y[0][1]) * F.im
    YF1 = IV(Y[1][0]) * F.re + IV(Y[1][1]) * F.im
    for r in radii:
        if t0 - r <= -1 or t0 + r >= 1 or s0 - r <= 0 or s0 + r >= 1:
            continue
        Xt = IV([t0 - r, t0 + r])
        Xs = IV([s0 - r, s0 + r])
        dt, ds = Jac(Xt, Xs)
        J = [[dt.re, ds.re], [dt.im, ds.im]]
        M = [[(1 if i == j else 0) - (IV(Y[i][0]) * J[0][j] + IV(Y[i][1]) * J[1][j]) for j in range(2)] for i in range(2)]
        dtv = Xt - tm
        dsv = Xs - sm
        K0 = tm - YF0 + M[0][0] * dtv + M[0][1] * dsv
        K1 = sm - YF1 + M[1][0] * dtv + M[1][1] * dsv
        if K0.a > Xt.a and K0.b < Xt.b and K1.a > Xs.a and K1.b < Xs.b:
            if Xt.a > -1 and Xt.b < 1 and Xs.a > 0 and Xs.b < 1:
                return (t0, s0, r)
    return None


def newton_N(thf, zf, t0=0.0, s0=0.5, it=60):
    """float Newton for t + s (s_th(t) - t) = zf"""
    sn, cs = cmath.sin(thf), cmath.cos(thf)
    t, s = t0, s0
    for _ in range(it):
        st = (cmath.exp(1j * thf * t) - cs) / (1j * sn)
        F = t + s * (st - t) - zf
        dst = thf * cmath.exp(1j * thf * t) / sn
        dt = (1 - s) + s * dst
        ds = st - t
        a11, a12, a21, a22 = dt.real, ds.real, dt.imag, ds.imag
        det = a11 * a22 - a12 * a21
        if det == 0:
            return None
        du = (a22 * F.real - a12 * F.imag) / det
        dv = (-a21 * F.real + a11 * F.imag) / det
        t -= du
        s -= dv
        if not (abs(t) < 5 and abs(s) < 5):
            return None
        if abs(du) + abs(dv) < 1e-15:
            break
    return (t, s)


def mark_direct(th, thf, nmax=0):
    """entry index by direct certification; returns n or None.
    th: complex interval box of theta; thf: float centre."""
    sn = csin(th)
    cs = ccos(th)
    snf, csf = cmath.sin(thf), cmath.cos(thf)
    # n = -1 : zeta(0) = i cot th ; c0 = cs
    zf = 1j * csf / snf
    g = newton_N(thf, zf)
    if g is not None and -1 < g[0] < 1 and 0 < g[1] < 1:
        if mark_kraw(th, sn, cs, cs, g):
            return -1
    if nmax < 0:
        return None
    # need zeta(0) above chord: Im(i cot th) = Re cot th > 0
    z = II * cs / sn
    if not (z.im.a > 0):
        return None
    # zeta_0 = zeta(1) = (1/r - cos th)/(i sin th), r = exp(th cot th)
    isn = II * sn
    ith = II * th
    mu = th * cs / sn
    z = (cexp(-mu) - cs) / isn
    muf = thf * csf / snf
    zf = (cmath.exp(-muf) - csf) / (1j * snf)
    for n in range(0, nmax + 1):
        if z.im.a > 0:
            z = (cexp(ith * z) - cs) / isn
            zf = (cmath.exp(1j * thf * zf) - csf) / (1j * snf)
            continue
        # try entry at n
        c0 = -(isn * z)
        for st in ((0.0, 0.5), (0.5, 0.5), (-0.5, 0.5), (0.0, 0.1), (0.0, 0.9), (0.8, 0.5), (-0.8, 0.5)):
            g = newton_N(thf, zf, *st)
            if g is not None and -1 < g[0] < 1 and 0 < g[1] < 1:
                if mark_kraw(th, sn, cs, c0, g):
                    return n
                break
        return None
    return None


# ------------------------------------------------ Theta membership (exact)
P0, P1 = Fr(1, 10), Fr(11, 5)


def Vfun(p):
    return Fr(1, 4) if p <= Fr(8, 5) else Fr(1, 4) - Fr(7, 60) * (p - Fr(8, 5))


def in_Theta_or_conj(B):
    p0, p1 = frac_of(B.re.a), frac_of(B.re.b)
    q0, q1 = frac_of(B.im.a), frac_of(B.im.b)
    qa = max(abs(q0), abs(q1))
    if p0 <= 0:
        return False
    if p1 <= P0:
        return qa <= P0 * p0
    if p0 >= P0 and p1 <= P1:
        return qa <= Vfun(p0) * p0 * p0
    if p0 < P0 < p1 <= P1:
        return qa <= min(P0 * p0, Vfun(P0) * P0 * P0)
    return False


# ------------------------------------------------ root of (lam-2i th)e^{2i th}=lam
def h_dh(th, lam):
    E = cexp(2 * (II * th))
    L = lam - 2 * (II * th)
    return L * E - lam, 2 * (II * E) * (L - 1)


def hf(th, lam):
    E = cmath.exp(2j * th)
    L = lam - 2j * th
    return L * E - lam, 2j * E * (L - 1)


def newton_theta(lam, th, it=50):
    for _ in range(it):
        h, d = hf(th, lam)
        if d == 0:
            return None
        step = h / d
        th = th - step
        if abs(step) < 1e-15 * max(1, abs(th)):
            break
    if abs(hf(th, lam)[0]) > 1e-10:
        return None
    return th


def continue_theta(lam0, th0, lam1, steps=12):
    th = th0
    for k in range(1, steps + 1):
        lam = lam0 + (lam1 - lam0) * k / steps
        th = newton_theta(lam, th)
        if th is None:
            return None
    return th


def kraw_root(lam, thf, lamf, scale):
    """Krawczyk for theta with lam a complex box. Returns B (C) or None."""
    _, dfl = hf(thf, lamf)
    if dfl == 0:
        return None
    Yf = 1 / dfl
    Y = C(Yf.real, Yf.imag)
    m = C(thf.real, thf.imag)
    hm, _ = h_dh(m, lam)
    Yhm = Y * hm
    for fac in (1.5, 3.0, 6.0, 12.0):
        r = fac * scale + 1e-14
        B = cball(thf, r)
        _, dB = h_dh(B, lam)
        M = 1 - Y * dB
        if not (M.abs2().b < 1):
            continue
        K = m - Yhm + M * (B - m)
        if K.inside(B):
            return B
    return None


def unique_in(H, lam):
    """uniqueness of the root in the convex box H for every lam in the box lam"""
    thf = H.mid()
    lamf = lam.mid()
    _, dfl = hf(thf, lamf)
    if dfl == 0:
        return False
    Yf = 1 / dfl
    Y = C(Yf.real, Yf.imag)
    _, dB = h_dh(H, lam)
    M = 1 - Y * dB
    return M.abs2().b < 1


# ------------------------------------------------ seeds
SEED = None


def build_seed():
    tab = {}
    p = 0.005
    while p < 3.14:
        q = -0.6
        while q < 1.6:
            th = complex(p, q)
            try:
                lam = th * cmath.cos(th) / cmath.sin(th) + 1j * th
            except ZeroDivisionError:
                q += 0.01
                continue
            if -12.6 <= lam.real <= 5.6 and -0.6 <= lam.imag <= 3.8:
                key = (math.floor(lam.real / 0.1), math.floor(lam.imag / 0.1))
                tab.setdefault(key, []).append((lam, th))
            q += 0.01
        p += 0.005
    return tab


def seed_theta(lam):
    global SEED
    if SEED is None:
        SEED = build_seed()
    kx, ky = math.floor(lam.real / 0.1), math.floor(lam.imag / 0.1)
    best = None
    for rad in (1, 2, 4, 8):
        for dx in range(-rad, rad + 1):
            for dy in range(-rad, rad + 1):
                for (l, t) in SEED.get((kx + dx, ky + dy), ()):
                    dd = abs(l - lam)
                    if best is None or dd < best[0]:
                        best = (dd, t)
        if best is not None:
            break
    if best is None:
        return None
    return newton_theta(lam, best[1])


# ============================================================ (P) cusp
def part_P():
    log('(P) cusp lemma')
    t0 = time.time()
    # M(w)=theta cot theta, A(w)=a(theta)=theta e^{-theta cot theta}/sin theta, w=theta^2.
    # maxima on |theta|=1 (i.e. |w|=1) by interval evaluation on arcs.
    narc = 720
    M1 = ZERO
    A1 = ZERO
    M2 = ZERO   # max |M - 1 + w/3| on |w|=1
    twopi = 2 * PI
    for k in range(narc):
        ph = IV([(twopi * k / narc).a, (twopi * (k + 1) / narc).b])
        th = C(iv.cos(ph), iv.sin(ph))
        sn, cs = csin(th), ccos(th)
        Mv = th * cs / sn
        Av = th * cexp(-Mv) / sn
        w = th * th
        M1 = IV(max(M1.b, sqrt_hi(Mv.abs2())))
        A1 = IV(max(A1.b, sqrt_hi(Av.abs2())))
        M2 = IV(max(M2.b, sqrt_hi((Mv - 1 + w / 3).abs2())))
    r = IV(81) / 10000          # |w| <= 0.09^2
    rho = IV(9) / 100
    Dmax = 1 / IV(3) + r * M2   # |D(w)|<=1/3+|w| max|M2| (max principle for (M-1+w/3)/w^2)
    log('  max|th cot th| on |th|=1 <=', M1.b, ' max|a| <=', A1.b, ' max|M-1+w/3| <=', M2.b)
    log('  |D| <=', Dmax.b)
    ok = True
    # Rouche: on |theta|=0.09, |theta^2 D| <= 0.0081*Dmax < 0.01 <= |i theta - (lam-1)|
    c1 = (r * Dmax).b < IV('0.01').a
    log('  Rouche |th^2 D| <', (r * Dmax).b, '< 0.01 :', c1)
    ok &= c1
    # Im lambda = Re th (1 + 2 Im th * c), |c| <= max|M'| <= M1/(1-r)
    Mp = M1 / (1 - r)
    c2 = (1 - 2 * rho * Mp).a > 0
    log('  Im lam = Re th*(1+2 Im th*c), 1-2*0.09*max|M\'| >=', (1 - 2 * rho * Mp).a, ':', c2)
    ok &= c2
    # Im a = 2 Re th Im th * Re avg A', Re A' >= 1/(2e) - r * 2 A1/(1-r)^2
    Ap = 1 / (2 * iv.e) - r * 2 * A1 / (1 - r) ** 2
    c3 = Ap.a > 0
    log('  Re A\'(w) >=', Ap.a, ':', c3)
    ok &= c3
    # |lam|>=1 forces arg th < arctan(1/10):  for phi in [arctan .1, pi/2]
    s0 = IV(1) / 10 / iv.sqrt(IV(101) / 100)
    bound = -2 * s0 + 2 * rho * Dmax + rho * (1 + rho * Dmax) ** 2
    c4 = bound.b < 0
    log('  (|lam|^2-1)/rho <= -2 sin(atan .1) + 2 rho|D| + rho(1+rho|D|)^2 <=', bound.b, ':', c4)
    ok &= c4
    log('(P) result:', 'PASS' if ok else 'FAIL', ' %.1fs' % (time.time() - t0))
    return ok


# ============================================================ (T) tails
OM0 = C(IV([-4.6, -1.7]), IV([-1.5, 1.5]))


def ell(z):
    R = float(sqrt_hi(z.abs2())) * (1 + 1e-12)
    if R >= 0.9:
        raise ValueError('ell radius')
    N = 10
    while R ** N / (N + 1) / (1 - R) > 1e-19:
        N += 1
    acc = C(1 / IV(N))
    for k in range(N - 2, -1, -1):
        acc = acc * z + 1 / IV(k + 1)
    Ri = IV(R)
    tail = (Ri ** N / (N + 1) / (1 - Ri)).b
    return acc + errbox(tail)


def dell(z):
    R = float(sqrt_hi(z.abs2())) * (1 + 1e-12)
    N = 10
    while R ** N / (1 - R) > 1e-19:
        N += 1
    acc = C(IV(N) / (N + 1))
    for j in range(N - 2, -1, -1):
        acc = acc * z + IV(j + 1) / (j + 2)
    Ri = IV(R)
    tail = (Ri ** N / (1 - Ri)).b
    return acc + errbox(tail)


def tail_D(kap):
    """contraction D = -(pi - kap D) ell(2 i kap (pi - kap D)) on OM0"""
    def F(D):
        w = C(PI) - kap * D
        return -(w * ell(2 * (II * (kap * w))))
    w = C(PI) - kap * OM0
    z = 2 * (II * (kap * w))
    FO = -(w * ell(z))
    dF = kap * ell(z) + 2 * (II * (kap * kap * w)) * dell(z)
    if not FO.subset(OM0) or not (dF.abs2().b < 1):
        return None
    D = FO
    for _ in range(8):
        Dn = F(D).inter(D)
        if Dn is None:
            return None
        D = Dn
    return D


def tail_params(u, Y):
    y = PI * Y
    uy = u * y
    den = 1 + uy ** 2
    sq = iv.sqrt(den)
    kou = C(-1 / den, -uy / den)          # kappa/u
    kap = kou * u
    omega = C(-1 / sq, uy / sq)            # lambda/|lambda|
    nu = u / sq                            # 1/|lambda|
    return y, kou, kap, omega, nu, sq


def tail_box(u0, u1, Y0, Y1):
    u = IV([I(u0).a, I(u1).b])
    Y = IV([I(Y0).a, I(Y1).b])
    y, kou, kap, omega, nu, sq = tail_params(u, Y)
    D = tail_D(kap)
    if D is None:
        return 'contraction'
    delta = kap * D
    th = C(PI) - delta
    # (a) Im lambda_- = y - 2 Re th < 0
    if not ((y - 2 * th.re).b < 0):
        return 'imlm'
    # (b) (pi^2-|th|^2)/u = 2 pi Re(kou D) - u |kou D|^2 > 0
    kD = kou * D
    if not ((2 * PI * kD.re - u * kD.abs2()).a > 0):
        return 'abs'
    # (c) crescent, scaled by 1/|lambda|
    ok, _ = crescent_side(omega, -(II * th), 1, nu)
    if not ok:
        return 'cres+'
    L0m = C(omega.re + 2 * nu * th.im, u * (y - 2 * th.re) / sq)   # (lambda-2i th)/|lambda|
    ok, _ = crescent_side(L0m, II * th, -1, nu)
    if not ok:
        return 'cres-'
    # (d) mark: zeta(0)=i cot th = N(t,s), (t,s) near (0,1/2)
    thf = th.mid()
    g = newton_N(thf, 1j * cmath.cos(thf) / cmath.sin(thf)) if abs(cmath.sin(thf)) > 1e-12 else (0.0, 0.5)
    if g is None:
        g = (0.0, 0.5)
    if not mark_kraw(th, csin(th), ccos(th), ccos(th), g):
        return 'mark'
    return None


def _tail_worker(args):
    u0, u1, Y0, Y1 = args
    out = []
    stack = [(u0, u1, Y0, Y1, 0)]
    fails = []
    while stack:
        a, b, c, d, dep = stack.pop()
        why = tail_box(a, b, c, d)
        if why is None:
            out.append((a, b, c, d))
            continue
        if dep >= 14:
            fails.append((a, b, c, d, why))
            continue
        # split the relatively larger side (u range scaled by 12, Y range)
        if (b - a) * 12 >= (d - c):
            m = (a + b) / 2
            stack += [(a, m, c, d, dep + 1), (m, b, c, d, dep + 1)]
        else:
            m = (c + d) / 2
            stack += [(a, b, c, m, dep + 1), (a, b, m, d, dep + 1)]
    return out, fails


def part_T(pool):
    log('(T) tails: u=1/|Re lam| in [0,1/12], Im lam = pi*Y, Y in [0,1]')
    t0 = time.time()
    nu_, ny_ = 4, 32
    jobs = [(Fr(i, 12 * nu_), Fr(i + 1, 12 * nu_), Fr(j, ny_), Fr(j + 1, ny_)) for i in range(nu_) for j in range(ny_)]
    boxes, fails = [], []
    for o, f in pool.imap_unordered(_tail_worker, jobs):
        boxes += o
        fails += f
    # coverage check (exact): total area equals area of the strip, boxes disjoint by construction
    area = sum((b - a) * (d - c) for a, b, c, d in boxes) + sum((b - a) * (d - c) for a, b, c, d, _ in fails)
    log('  tail boxes passed:', len(boxes), ' failed:', len(fails), ' area check:', area == Fr(1, 12))
    for f in fails[:20]:
        log('   FAIL', [float(v) for v in f[:4]], f[4])
    log('(T) result:', 'PASS' if not fails else 'FAIL', ' %.1fs' % (time.time() - t0))
    return not fails, boxes


def tail_theta_at_edge(Y0, Y1):
    """enclosure of the tail root theta for Re lam=-12, Im lam in pi*[Y0,Y1]"""
    u = I(Fr(1, 12))
    Y = IV([I(Y0).a, I(Y1).b])
    y, kou, kap, omega, nu, sq = tail_params(u, Y)
    D = tail_D(kap)
    if D is None:
        return None
    return C(PI) - kap * D


# ============================================================ (K) core
X0, X1 = Fr(-12), Fr(5)
NX, NY = 34, 8          # root grid: dx=1/2, dY=1/8 (Im lam = pi*Y)
LMAX = 15
EM2 = iv.exp(IV(-2))


def cell_geom(L, i, j):
    dx = (X1 - X0) / NX / (2 ** L)
    dY = Fr(1, NY) / (2 ** L)
    return X0 + i * dx, X0 + (i + 1) * dx, j * dY, (j + 1) * dY


def cell_lam(x0, x1, Y0, Y1):
    return C(IV([I(x0).a, I(x1).b]), PI * IV([I(Y0).a, I(Y1).b]))


def discard(lam):
    a2 = lam.abs2()
    if a2.b < 1:
        return 'disk'
    if (lam - 1).abs2().b < IV('0.0064').a:
        return 'cusp'
    g = lam * cexp(-lam)
    if g.im.b < 0:
        return 'img<0'
    if g.im.a > PI.b:
        return 'img>pi'
    if g.abs2().b < EM2.a:
        return '|g|<1/e'
    return None


def certify_cell(lam, thf, lamf, cellrad, want_direct=False):
    """returns (status, data)"""
    # Krawczyk root
    try:
        lp = thf * cmath.cos(thf) / cmath.sin(thf) + 1j * thf
        _, d = hf(thf, lamf)
        dlam = abs(1 / (cmath.cos(thf) / cmath.sin(thf) - thf / cmath.sin(thf) ** 2 + 1j))
    except (ZeroDivisionError, OverflowError):
        return 'root', None
    B = kraw_root(lam, thf, lamf, dlam * cellrad)
    if B is None:
        return 'root', None
    # 0 < |theta| < pi
    tb2 = B.abs2()
    if not (tb2.a > 0 and tb2.b < (PI ** 2).a):
        return 'abs', None
    # Im lambda_- < 0
    if not ((lam.im - 2 * B.re).b < 0):
        return 'imlm', None
    # cusp interface
    cuspmeet = not ((lam - 1).abs2().a >= IV('0.0064').b)
    if cuspmeet and not (tb2.b < IV('0.0081').a):
        return 'cuspif', None
    # crescent inequalities
    ok1, n1 = crescent_side(lam, -(II * B), 1, ONE)
    if not ok1:
        return 'cres+', None
    ok2, n2 = crescent_side(lam - 2 * (II * B), II * B, -1, ONE)
    if not ok2:
        return 'cres-', None
    # mark
    cited = in_Theta_or_conj(B)
    direct = None
    if not cited or want_direct:
        direct = mark_direct(B, thf, nmax=(80 if want_direct else 3))
        if direct is None and not cited:
            return 'mark', None
    return 'ok', {'B': B.raw(), 'cited': cited, 'direct': direct, 'ne': n1 + n2, 'thf': thf}


def _core_worker(args):
    rootkey, thseed, lamseed, want_direct = args
    L, i, j = rootkey
    out = []
    stack = [((L, i, j), thseed, lamseed)]
    while stack:
        (L, i, j), ths, lams = stack.pop()
        x0, x1, Y0, Y1 = cell_geom(L, i, j)
        lam = cell_lam(x0, x1, Y0, Y1)
        why = discard(lam)
        if why:
            out.append(((L, i, j), 'discard', why))
            continue
        lamf = complex(float((x0 + x1) / 2), math.pi * float((Y0 + Y1) / 2))
        thf = None
        if ths is not None:
            thf = continue_theta(lams, ths, lamf)
        if thf is None:
            thf = seed_theta(lamf)
        status = 'seed'
        data = None
        if thf is not None:
            cellrad = abs(complex(float(x1 - x0), math.pi * float(Y1 - Y0))) / 2
            status, data = certify_cell(lam, thf, lamf, cellrad, want_direct)
        if status == 'ok':
            out.append(((L, i, j), 'ok', data))
            continue
        if L >= LMAX:
            out.append(((L, i, j), 'FAIL', status))
            continue
        for di in (0, 1):
            for dj in (0, 1):
                stack.append(((L + 1, 2 * i + di, 2 * j + dj), thf, lamf))
    return rootkey, out


def part_K(pool, ckpt, want_direct=False):
    log('(K) core: [-12,5] x [0,pi], root grid %dx%d, LMAX=%d' % (NX, NY, LMAX))
    t0 = time.time()
    done = {}
    if os.path.exists(ckpt):
        with open(ckpt, 'rb') as f:
            done = pickle.load(f)
        log('  resumed', len(done), 'root cells from checkpoint')
    jobs = []
    for i in range(NX):
        for j in range(NY):
            if (0, i, j) in done:
                continue
            jobs.append(((0, i, j), None, None, want_direct))
    k = 0
    for key, out in pool.imap_unordered(_core_worker, jobs):
        done[key] = out
        k += 1
        nok = sum(1 for o in out if o[1] == 'ok')
        nf = sum(1 for o in out if o[1] == 'FAIL')
        log('  root', key, 'leaves', len(out), 'ok', nok, 'FAIL', nf, ' [%d/%d] %.0fs' % (k, len(jobs), time.time() - t0))
        with open(ckpt + '.tmp', 'wb') as f:
            pickle.dump(done, f)
        os.replace(ckpt + '.tmp', ckpt)
    log('(K) cells processed %.1fs' % (time.time() - t0))
    return done


# ============================================================ (I) interfaces
def _pair_worker(args):
    (ka, Ba), (kb, Bb), xint, Yint = args
    lam = cell_lam(*xint, *Yint)
    H = C.fromraw(Ba).chull(C.fromraw(Bb))
    return ka, kb, unique_in(H, lam)


def _edge_worker(args):
    key, Braw, Y0, Y1 = args
    B = C.fromraw(Braw)
    # subdivide Y if needed
    stack = [(Y0, Y1, 0)]
    while stack:
        a, b, d = stack.pop()
        T = tail_theta_at_edge(a, b)
        if T is not None and T.subset(B):
            continue
        if d > 12:
            return key, False
        m = (a + b) / 2
        stack += [(a, m, d + 1), (m, b, d + 1)]
    return key, True


def part_I(pool, done):
    log('(I) interfaces / continuity / anchor')
    t0 = time.time()
    leaves = {}
    for out in done.values():
        for o in out:
            leaves[o[0]] = o
    ok_leaves = {k: v for k, v in leaves.items() if v[1] == 'ok'}
    fails = [k for k, v in leaves.items() if v[1] == 'FAIL']
    ndisc = sum(1 for v in leaves.values() if v[1] == 'discard')
    log('  leaves: ok', len(ok_leaves), ' discarded', ndisc, ' FAIL', len(fails))
    # exact area check of the tiling
    area = Fr(0)
    for (L, i, j) in leaves:
        x0, x1, Y0, Y1 = cell_geom(L, i, j)
        area += (x1 - x0) * (Y1 - Y0)
    log('  tiling area check (x,Y units):', area == (X1 - X0) * 1)

    def find_leaf(L, i, j):
        while L >= 0:
            if (L, i, j) in leaves:
                return (L, i, j)
            L, i, j = L - 1, i // 2, j // 2
        return None
    pairs = set()
    for (L, i, j) in ok_leaves:
        for di in (-1, 0, 1):
            for dj in (-1, 0, 1):
                if di == 0 and dj == 0:
                    continue
                ii, jj = i + di, j + dj
                if ii < 0 or jj < 0 or ii >= NX * 2 ** L or jj >= NY * 2 ** L:
                    continue
                nb = find_leaf(L, ii, jj)
                if nb is None or nb not in ok_leaves:
                    continue
                pairs.add(tuple(sorted([(L, i, j), nb])))
    jobs = []
    for ka, kb in pairs:
        a = cell_geom(*ka)
        b = cell_geom(*kb)
        xint = (max(a[0], b[0]), min(a[1], b[1]))
        Yint = (max(a[2], b[2]), min(a[3], b[3]))
        assert xint[0] <= xint[1] and Yint[0] <= Yint[1]
        jobs.append(((ka, ok_leaves[ka][2]['B']), (kb, ok_leaves[kb][2]['B']), xint, Yint))
    nbad = 0
    bad = []
    for ka, kb, r in pool.imap_unordered(_pair_worker, jobs, chunksize=64):
        if not r:
            nbad += 1
            bad.append((ka, kb))
    log('  adjacent certified pairs (edge+corner):', len(jobs), ' hull-uniqueness failures:', nbad)
    for b_ in bad[:20]:
        log('   pair FAIL', b_, [float(v) for v in cell_geom(*b_[0])], [float(v) for v in cell_geom(*b_[1])])
    # anchor
    lam0 = C(iv.cos(ONE) / iv.sin(ONE), ONE)
    anc = []
    for k, v in ok_leaves.items():
        x0, x1, Y0, Y1 = cell_geom(*k)
        cl = cell_lam(x0, x1, Y0, Y1)
        if lam0.re.a <= cl.re.b and lam0.re.b >= cl.re.a and lam0.im.a <= cl.im.b and lam0.im.b >= cl.im.a:
            B = C.fromraw(v[2]['B'])
            u = unique_in(B, lam0)
            has1 = B.re.a < 1 < B.re.b and B.im.a < 0 < B.im.b
            no0 = not (B.re.a <= 0 <= B.re.b and B.im.a <= 0 <= B.im.b)
            anc.append((k, u, has1, no0))
    anchor_ok = bool(anc) and all(a[1] and a[2] and a[3] for a in anc)
    log('  anchor lam=cot1+i: cells', anc, ' ->', anchor_ok)
    # tail/core interface: cells with x0 == -12
    ejobs = []
    for k, v in ok_leaves.items():
        x0, x1, Y0, Y1 = cell_geom(*k)
        if x0 == X0:
            ejobs.append((k, v[2]['B'], Y0, Y1))
    ebad = [k for k, r in pool.imap_unordered(_edge_worker, ejobs) if not r]
    # did the left edge get fully covered by ok or discarded cells? (discarded ones are outside S)
    log('  tail/core interface cells:', len(ejobs), ' failures:', len(ebad))
    # cusp/core interface handled inside certify_cell ('cuspif'); count
    ncusp = 0
    for k, v in ok_leaves.items():
        x0, x1, Y0, Y1 = cell_geom(*k)
        cl = cell_lam(x0, x1, Y0, Y1)
        if not ((cl - 1).abs2().a >= IV('0.0064').b):
            ncusp += 1
    log('  core cells meeting |lam-1|<0.08 (theta-box checked inside 0<|theta|<0.09):', ncusp)
    # mark statistics
    ncited = sum(1 for v in ok_leaves.values() if v[2]['cited'])
    ndir = {}
    for v in ok_leaves.values():
        d = v[2]['direct']
        ndir[d] = ndir.get(d, 0) + 1
    log('  marks: theta-box in Theta or conj(Theta) (cited):', ncited, ' direct entry index histogram:', sorted(ndir.items(), key=lambda t: (t[0] is None, t[0] if t[0] is not None else 0)))
    nciteonly = sum(1 for v in ok_leaves.values() if v[2]['cited'] and v[2]['direct'] is None)
    log('  cells relying only on the paper for the mark:', nciteonly)
    necount = sum(v[2]['ne'] for v in ok_leaves.values())
    log('  total e-intervals in crescent checks:', necount)
    allok = (not fails) and nbad == 0 and anchor_ok and not ebad
    log('(I) result:', 'PASS' if allok else 'FAIL', ' %.1fs' % (time.time() - t0))
    return allok


# ------------------------------------------------ full direct mark (orbit + seam)
def kraw2(th, sn, cs, c0, t0, s0, slo, shi, tcontain=None, uniq=False):
    """Krawczyk for Psi(t,s)= i sn t(1-s) + s(e^{i th t}-cs) + c0 = 0 on boxes
    X = [t0-rt,t0+rt] x [s0-rs,s0+rs] with -1<X.t<1, slo<X.s<shi (strict),
    optionally X.t containing tcontain (an interval), optionally uniqueness
    via ||I - Y J(X)||_inf < 1.  Returns True on success."""
    isn = II * sn
    ith = II * th

    def Jac(t, s_):
        et = cexp(ith * t)
        return isn * (1 - s_) + ith * et * s_, -(isn * t) + et - cs
    dtf, dsf = Jac(IV(t0), IV(s0))
    a11, a12, a21, a22 = fl(dtf.re), fl(dsf.re), fl(dtf.im), fl(dsf.im)
    det = a11 * a22 - a12 * a21
    if det == 0 or not math.isfinite(det):
        return False
    Y = [[IV(a22 / det), IV(-a12 / det)], [IV(-a21 / det), IV(a11 / det)]]
    detY = Y[0][0] * Y[1][1] - Y[0][1] * Y[1][0]
    if not (detY.a > 0 or detY.b < 0):
        return False
    tm, sm = IV(t0), IV(s0)
    F = isn * tm * (1 - sm) + (cexp(ith * tm) - cs) * sm + c0
    YF0 = Y[0][0] * F.re + Y[0][1] * F.im
    YF1 = Y[1][0] * F.re + Y[1][1] * F.im
    tw = 0.0
    if tcontain is not None:
        tw = max(abs(float(tcontain.a) - t0), abs(float(tcontain.b) - t0))
    for r in (1e-7, 1e-6, 1e-5, 1e-4, 1e-3, 3e-3, 1e-2, 3e-2, 0.06, 0.1, 0.16):
        rt = r + tw * 1.02
        rs = r
        Xt = IV([t0 - rt, t0 + rt])
        Xs = IV([s0 - rs, s0 + rs])
        if not (Xt.a > -1 and Xt.b < 1 and Xs.a > slo and Xs.b < shi):
            continue
        if tcontain is not None and not (Xt.a <= tcontain.a and Xt.b >= tcontain.b):
            continue
        dt, ds = Jac(Xt, Xs)
        J = [[dt.re, ds.re], [dt.im, ds.im]]
        M = [[(1 if i == j else 0) - (Y[i][0] * J[0][j] + Y[i][1] * J[1][j]) for j in range(2)] for i in range(2)]
        dtv = Xt - tm
        dsv = Xs - sm
        K0 = tm - YF0 + M[0][0] * dtv + M[0][1] * dsv
        K1 = sm - YF1 + M[1][0] * dtv + M[1][1] * dsv
        if K0.a > Xt.a and K0.b < Xt.b and K1.a > Xs.a and K1.b < Xs.b:
            if uniq:
                n0 = abs(M[0][0]) + abs(M[0][1])
                n1 = abs(M[1][0]) + abs(M[1][1])
                if not (n0.b < 1 and n1.b < 1):
                    continue
            return True
    return False


def orbit_step(z, dz, th, sn, cs, isn):
    """s(z;th) and d/dth [s(z(th);th)] given dz = dz/dth (interval enclosures)"""
    ez = cexp(II * th * z)
    sv = (ez - cs) / isn
    ds_dz = th * ez / sn
    ds_dth = (II * z * ez + sn) / isn - sv * cs / sn
    return sv, ds_dth + ds_dz * dz


def rect_to_disc(R):
    """disc (float centre m, iv radius r) containing the rectangle R"""
    m = R.mid()
    d = R - C(m.real, m.imag)
    return m, IV(sqrt_hi(d.abs2()))


def mark_box(B, nmax=400):
    """entry index for all theta in the box B (orbit in centred form, seam
    rule).  Returns ('ok', n) or ('fail', reason)."""
    thc = B.mid()
    Tc = C(thc.real, thc.imag)        # thin centre
    dB = B - Tc
    snB, csB = csin(B), ccos(B)
    snC, csC = csin(Tc), ccos(Tc)
    isnB, isnC = II * snB, II * snC
    # injectivity of s_th on sets of diameter <= 2.1 needs |th|*2.1 < 2 pi
    if not ((B.abs2() * IV('4.41')).b < (4 * PI ** 2).a):
        return ('fail', 'inj')
    # derivative d zeta_n/d theta over B kept as a disc (centre mz, radius rz):
    # midpoint-radius complex arithmetic has no rotation wrapping.
    rth = IV(sqrt_hi(dB.abs2()))          # sup |theta - theta_c|
    zc = II * csC / snC                  # zeta_{-1} at centre
    mz, rz = rect_to_disc(C(0, -1) / (snB * snB))   # d/dth (i cot th) = -i/sin^2
    zB2 = zc + C(mz.real, mz.imag) * dB + errbox((rz * rth).b)
    zB = zB2.inter(II * csB / snB) or zB2
    n = -1
    zprev = None
    while n <= nmax:
        if zB.im.a > 0:                   # above the chord
            zprev = zB
            zc, _ = orbit_step(zc, C(0), Tc, snC, csC, isnC)
            ez = cexp(II * B * zB)
            sv = (ez - csB) / isnB
            mS, rS = rect_to_disc(B * ez / snB)                                   # d s/d zeta
            mA, rA = rect_to_disc((II * zB * ez + snB) / isnB - sv * csB / snB)   # d s/d theta
            P0 = C(mS.real, mS.imag) * C(mz.real, mz.imag) + C(mA.real, mA.imag)
            mz_new, r0 = rect_to_disc(P0)
            rz = rA + IV(abs(mS)) * (1 + IV(2) ** -50) * rz + rS * IV(abs(mz)) * (1 + IV(2) ** -50) + rS * rz + r0
            rz = IV(rz.b)
            mz = mz_new
            zB2 = zc + C(mz.real, mz.imag) * dB + errbox((rz * rth).b)
            zB = zB2.inter(sv) or zB2
            n += 1
            if zB.abs2().b > 1e6:
                return ('fail', 'blowup')
            continue
        zf = zc.mid()
        if zB.im.b < 0:                   # strictly below: interior via (0,1)
            for st in ((None, None), (0.0, 0.5), (0.5, 0.5), (-0.5, 0.5), (0.0, 0.1), (0.0, 0.9)):
                if st[0] is None:
                    g = newton_N(thc, zf, fl(zB.re), 0.2)
                else:
                    g = newton_N(thc, zf, *st)
                if g is not None and -1 < g[0] < 1 and 0 < g[1] < 1:
                    # sigma-range may extend below 0: Im zeta<=0 forces sigma>=0,
                    # because Im N(t,sigma) = sigma (1-t^2) Im g(t) and Im g<0 on (-1,1)
                    if kraw2(B, snB, csB, -(isnB * zB), g[0], g[1], -1.0, 1.0):
                        return ('ok', n)
                    break
            # seam from above: zeta_{n-1} lies (certified) above the chord, close to it.
            # D = Re zprev x [0, Im zprev]; D- is a real segment (N(t,0)=t), and
            # s(D) is certified to be N(t,sigma), sigma>0, unique in a box containing
            # (Re D) x {1}; by the argument of App. A (lem:far-mark) sigma<1 off the axis.
            if zprev is not None and zprev.re.a > -1 and zprev.re.b < 1 and zprev.im.b <= 0.25:
                Dp = C(zprev.re, IV([ZERO.a, zprev.im.b]))
                c0 = csB - cexp(II * B * Dp)
                if kraw2(B, snB, csB, c0, fl(zprev.re), 1.0, 0.0, 2.0, tcontain=zprev.re, uniq=True):
                    return ('ok', n)
            return ('fail', 'interior@%d' % n)
        # straddles the chord: seam rule with D = zB
        if not (zB.re.a > -1 and zB.re.b < 1 and zB.im.b <= 0.25 and zB.im.a >= -0.25):
            return ('fail', 'seamD@%d' % n)
        Dm = C(zB.re, IV([zB.im.a, ZERO.b]))
        Dp = C(zB.re, IV([ZERO.a, zB.im.b]))
        t0 = fl(zB.re)
        ok1 = kraw2(B, snB, csB, -(isnB * Dm), t0, 0.0, -1.0, 1.0)
        ok2 = False
        if ok1:
            c0 = csB - cexp(II * B * Dp)
            ok2 = kraw2(B, snB, csB, c0, t0, 1.0, 0.0, 2.0, tcontain=zB.re, uniq=True)
        if ok1 and ok2:
            return ('ok', n)
        return ('fail', 'seam@%d' % n)
    return ('fail', 'nmax')


def mark_cover(B, maxdepth=10):
    """subdivide the theta-box B until every piece passes mark_box"""
    stack = [(B, 0)]
    npieces = 0
    ns = set()
    while stack:
        b, d = stack.pop()
        st, v = mark_box(b)
        if st == 'ok':
            npieces += 1
            ns.add(v)
            continue
        if d >= maxdepth:
            return False, (v, [str(b.re), str(b.im)]), npieces
        rm = IV(b.re.mid)
        im_ = IV(b.im.mid)
        for R in (IV([b.re.a, rm.b]), IV([rm.a, b.re.b])):
            for Im in (IV([b.im.a, im_.b]), IV([im_.a, b.im.b])):
                stack.append((C(R, Im), d + 1))
    return True, sorted(ns), npieces


# ============================================================ (M) optional direct marks
def _mark_worker(args):
    key, Braw, thf = args
    B = C.fromraw(Braw)
    try:
        ok, info, npc = mark_cover(B)
    except (ZeroDivisionError, ValueError) as ex:
        ok, info, npc = False, repr(ex), 0
    return key, (ok, info, npc)


def part_M(pool, done):
    log('(M) direct (orbit + seam) marks on all certified core cells, theta-subdivision, no citation')
    t0 = time.time()
    ck = os.path.join(os.path.dirname(LOGFILE), 'marks.pkl')
    res = {}
    if os.path.exists(ck):
        with open(ck, 'rb') as f:
            res = pickle.load(f)
        log('  resumed', len(res))
    jobs = [(o[0], o[2]['B'], o[2]['thf']) for out in done.values() for o in out if o[1] == 'ok' and o[0] not in res]
    # expensive (small theta) jobs first for load balance
    # cheap (large |theta|) jobs first; the smallest-|theta| cells are the costly ones
    jobs.sort(key=lambda j: -abs(j[2]))
    tlast = time.time()
    for k, (key, r) in enumerate(pool.imap_unordered(_mark_worker, jobs, chunksize=4)):
        res[key] = r
        if (k + 1) % 500 == 0 or k + 1 == len(jobs) or time.time() - tlast > 600:
            tlast = time.time()
            nf = sum(1 for v in res.values() if not v[0])
            log('  ', k + 1, '/', len(jobs), ' failures so far', nf, ' current |theta|=%.4f' % abs(jobs[min(k, len(jobs) - 1)][2]), ' %.0fs' % (time.time() - t0))
            with open(ck + '.tmp', 'wb') as f:
                pickle.dump(res, f)
            os.replace(ck + '.tmp', ck)
    fails = [k for k, v in res.items() if not v[0]]
    hist = {}
    for v in res.values():
        if v[0]:
            for n in v[1]:
                hist[n] = hist.get(n, 0) + 1
    log('  entry indices occurring (cells):', sorted(hist.items()))
    log('  theta-pieces total:', sum(v[2] for v in res.values()))
    cited = {o[0]: o[2]['cited'] for out in done.values() for o in out if o[1] == 'ok'}
    log('  direct failures:', len(fails), ' of which theta-box in Theta u conj(Theta):', sum(1 for f in fails if cited[f]))
    for f in fails[:20]:
        log('   FAIL', f, res[f][1])
    log('(M) done %.1fs' % (time.time() - t0))
    return fails


def part_MF(pool, done):
    log('(MF) re-run direct marks on previously failed cells (patched seam rule)')
    ck = os.path.join(os.path.dirname(LOGFILE), 'marks.pkl')
    with open(ck, 'rb') as f:
        res = pickle.load(f)
    lv = {o[0]: o for out in done.values() for o in out if o[1] == 'ok'}
    jobs = [(k, lv[k][2]['B'], lv[k][2]['thf']) for k, v in res.items() if not v[0]]
    log('  failed cells to redo:', len(jobs))
    fails = []
    for key, r in pool.imap_unordered(_mark_worker, jobs):
        res[key] = r
        if not r[0]:
            fails.append(key)
            log('   still FAIL', key, r[1])
    with open(ck, 'wb') as f:
        pickle.dump(res, f)
    log('(MF) remaining failures:', len(fails))
    return fails


# ============================================================ main
def main():
    global LOGFILE
    ap = argparse.ArgumentParser()
    ap.add_argument('--parts', default='P,T,K,I')
    ap.add_argument('--procs', type=int, default=10)
    ap.add_argument('--dir', default=os.path.join(os.path.dirname(os.path.abspath(__file__)), 'upper_iv_out'))
    ap.add_argument('--direct-marks', action='store_true', help='also attempt direct orbit marks on cells in Theta')
    a = ap.parse_args()
    os.makedirs(a.dir, exist_ok=True)
    LOGFILE = os.path.join(a.dir, 'log.txt')
    parts = a.parts.split(',')
    log('==== verify_upper_iv start, parts', parts, 'iv.prec', iv.prec, 'direct-marks', a.direct_marks)
    from multiprocessing import Pool
    t0 = time.time()
    res = {}
    with Pool(a.procs) as pool:
        if 'P' in parts:
            res['P'] = part_P()
        if 'T' in parts:
            res['T'], _ = part_T(pool)
        done = None
        ck = os.path.join(a.dir, 'core%s.pkl' % ('_direct' if a.direct_marks else ''))
        if 'K' in parts:
            done = part_K(pool, ck, a.direct_marks)
        if 'I' in parts:
            if done is None:
                with open(ck, 'rb') as f:
                    done = pickle.load(f)
            res['I'] = part_I(pool, done)
        if 'MF' in parts:
            with open(ck, 'rb') as f:
                done = pickle.load(f)
            res['MF_fail'] = len(part_MF(pool, done))
        if 'M' in parts:
            if done is None:
                with open(ck, 'rb') as f:
                    done = pickle.load(f)
            res['M_fail'] = len(part_M(pool, done))
    log('==== summary', res, ' total %.1fs' % (time.time() - t0))


if __name__ == '__main__':
    main()
