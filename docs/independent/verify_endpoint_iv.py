#!/usr/bin/env python3
"""Independent interval re-verification of Theorem thm:endpoint (Appendix app:endpoint)
of docs/paper-submission/main.tex.

Written only from the paper.  Uses mpmath's interval context (outward rounding)
and exact rationals; floats are used only for Krawczyk centres / Newton guesses
and for the preconditioning constants Y, c (which may be arbitrary numbers).

Checks
  (NW)  Re(lambda_+'(theta) * conj(c)) > 0 on R' = [2.20,2.45]x[0.62,0.95],
        c = float approx of lambda_+'(theta_*)  => lambda_+ injective on R'.
  (SQ)  square [-1.1,-0.9]x[-0.1,0.1]: Krawczyk box for theta(lambda) inside R',
        then (a)-(f) of Lemma lem:chi-crescent for all t in [-1,1].
  (ST)  strip [-12,-1/5]x[-1e-3,1e-3]: Krawczyk boxes chained from the box
        containing lambda=-1 (whose root lies in R'); adjacent boxes carry the
        same root because lambda_+ is injective (Noshiro-Warschawski) on the
        convex hull of their two theta-enclosures; then (a)-(f).

Notation (paper, sec:far / sec:endpoint):
  lambda_+(theta) = theta cot theta + i theta
  S(w) = sinh(w)/w,  w1 = i theta (t-1)/2,  w2 = i theta (t+1)/2
  phi(t) = i theta + Log S(w1) - Log S(w2)
  x = log((1-t)/(1+t)),  dt/dx = -(1-t^2)/2,  phi_x = -(1-t^2)/2 * phi'(t)
  Gamma = x + i pi + phi
  chi(zeta(0)) = log((i cot th - 1)/(i cot th + 1)) = 2 i theta  (mod 2 pi i)
"""
import sys, time, cmath, math
from fractions import Fraction as Fr
from multiprocessing import Pool
from mpmath import iv, mpf

iv.prec = 60
PI = iv.pi
I = iv.mpc(0, 1)
NSER = 24  # series terms for S, S'
E_SHIFT = 0  # mutation-test hooks (0 in the real run)
D_SHIFT = 0


def ivq(q):
    """enclosure of a rational"""
    q = Fr(q)
    return iv.mpf(q.numerator) / q.denominator


def cx(re, im):
    return iv.mpc(re, im)


def re_(z):
    return z.real


def im_(z):
    return z.imag


def hull(a, b):
    return iv.mpf([min(a.a, b.a), max(a.b, b.b)])


def chull(z1, z2):
    return cx(hull(z1.real, z2.real), hull(z1.imag, z2.imag))


# factorial reciprocals as intervals
INVFACT = [None] * (2 * NSER + 4)
f = 1
for k in range(len(INVFACT)):
    if k > 0:
        f *= k
    INVFACT[k] = iv.mpf(1) / f


def S_and_dS(w):
    """S(w)=sinh(w)/w and S'(w), by the Taylor series with rigorous tail."""
    w2 = w * w
    # rho^2 upper bound
    r = w.real; i = w.imag
    rho2 = iv.mpf(max(abs(r.a), abs(r.b))) ** 2 + iv.mpf(max(abs(i.a), abs(i.b))) ** 2
    rho2 = iv.mpf(rho2.b)
    N = NSER
    # S = sum_{k<N} w^{2k}/(2k+1)!   (Horner in w2)
    s = cx(INVFACT[2 * N - 1], 0)
    for k in range(N - 2, -1, -1):
        s = s * w2 + INVFACT[2 * k + 1]
    # S' = sum_{1<=k<N} 2k w^{2k-1}/(2k+1)! = w * sum_{1<=k<N} 2k w^{2k-2}/(2k+1)!
    d = cx(2 * (N - 1) * INVFACT[2 * N - 1], 0)
    for k in range(N - 2, 0, -1):
        d = d * w2 + 2 * k * INVFACT[2 * k + 1]
    d = d * w
    # tails: sum_{k>=N} rho^{2k}/(2k+1)! <= rho^{2N}/(2N+1)! / (1 - rho^2/((2N+2)(2N+3)))
    q1 = rho2 / ((2 * N + 2) * (2 * N + 3))
    assert q1.b < 1
    t1 = (rho2 ** N) * INVFACT[2 * N + 1] / (1 - q1)
    # sum_{k>=N} 2k rho^{2k-1}/(2k+1)! <= sum rho^{2k-1}/(2k)! <= rho^{2N-1}/(2N)! /(1-rho^2/((2N+1)(2N+2)))
    q2 = rho2 / ((2 * N + 1) * (2 * N + 2))
    rho = iv.sqrt(rho2)
    t2 = (rho ** (2 * N - 1)) * INVFACT[2 * N] / (1 - q2)
    e1 = iv.mpf([-t1.b, t1.b]); e2 = iv.mpf([-t2.b, t2.b])
    return s + cx(e1, e1), d + cx(e2, e2)


def cot(th):
    # cot(theta) = -i (1+q)/(1-q), q = exp(2 i theta): far less wrapping than cos/sin
    # for Im(theta) > 0 (|q| < 1).
    q = iv.exp(2 * I * th)
    return -I * (1 + q) / (1 - q)


def lam(th):
    return th * cot(th) + I * th


def dlam(th):
    # lambda_+' = cot - theta / sin^2 + i,  1/sin^2 = 1 + cot^2
    c = cot(th)
    return c - th * (1 + c * c) + I


def lam_f(th):
    return th * cmath.cos(th) / cmath.sin(th) + 1j * th


def dlam_f(th):
    return cmath.cos(th) / cmath.sin(th) - th / cmath.sin(th) ** 2 + 1j


def newton(l, g):
    for _ in range(60):
        g = g - (lam_f(g) - l) / dlam_f(g)
    return g


def inside(a, b):
    """real interval a strictly inside b"""
    return a.a > b.a and a.b < b.b


def cinside(z, B):
    return inside(z.real, B.real) and inside(z.imag, B.imag)


def cbox(c, r):
    return cx(iv.mpf([c.real - r, c.real + r]), iv.mpf([c.imag - r, c.imag + r]))


def krawczyk(L, guess):
    """L: complex interval of lambda.  Returns (K, B) with K subset int B and the unique
    root of lambda_+(theta)=lambda in B for every lambda in L lying in K; or None."""
    lc = complex(float(L.real.mid), float(L.imag.mid))
    m = newton(lc, guess)
    Y = 1 / dlam_f(m)
    rl = max(float(L.real.delta), float(L.imag.delta))
    r = 2.0 * abs(Y) * rl + 1e-12
    mI = cx(iv.mpf(m.real), iv.mpf(m.imag))
    YI = cx(iv.mpf(Y.real), iv.mpf(Y.imag))
    for _ in range(12):
        B = cbox(m, r)
        K = mI - YI * (lam(mI) - L) + (1 - YI * dlam(B)) * (B - mI)
        if cinside(K, B):
            return K, B, m
        r *= 1.6
    return None


def logpos(z):
    """principal log, requires Re z > 0 (checked by caller)"""
    return iv.log(z)


R_PRIME = cx(iv.mpf([ivq(Fr(22, 10)).b, ivq(Fr(245, 100)).a]), iv.mpf([ivq(Fr(62, 100)).b, ivq(Fr(95, 100)).a]))
# (shrunk inward by rounding: points certified to lie in this set lie in R')


def check_T(th, t0, t1):
    """Check (a),(b),(c),(f: Re S>0), (d),(e) for all theta in box th and t in [t0,t1]
    (t0,t1 exact Fractions, -1<=t0<t1<=1).  Returns (ok, reason, margins)."""
    T = iv.mpf([ivq(t0).a, ivq(t1).b])
    half = iv.mpf(0.5)
    w1 = I * th * (T - 1) * half
    w2 = I * th * (T + 1) * half
    S1, dS1 = S_and_dS(w1)
    S2, dS2 = S_and_dS(w2)
    if not (S1.real.a > 0 and S2.real.a > 0):
        return False, 'f'
    phi = I * th + logpos(S1) - logpos(S2)
    dphi = I * th * half * (dS1 / S1 - dS2 / S2)
    one_m_t2 = (1 - T) * (1 + T)
    phix = -one_m_t2 * half * dphi
    A = 1 + phix
    if not (A.real.a > 0):
        return False, 'a'
    ip = phi.imag
    if not (ip.a > 0 and ip.b < (2 * PI).a):
        return False, 'b'
    c = (A.real * phi.imag - A.imag * phi.real)  # Im(conj(A) phi)
    if not (c.a > 0):
        return False, 'c'
    # Re Gamma = x + Re phi, x = log((1-t)/(1+t)) decreasing in t
    rp = phi.real
    xhi = None if t0 == -1 else iv.log((1 - ivq(t0)) / (1 + ivq(t0))).b   # +inf if t0=-1
    xlo = None if t1 == 1 else iv.log((1 - ivq(t1)) / (1 + ivq(t1))).a    # -inf if t1=1
    G_hi = None if xhi is None else (iv.mpf(xhi) + rp).b
    G_lo = None if xlo is None else (iv.mpf(xlo) + rp).a

    def excludes(v):  # interval v certainly disjoint from ReGamma range
        return (G_hi is not None and G_hi < v.a) or (G_lo is not None and G_lo > v.b)
    # (d)
    if not excludes(iv.mpf(0)):
        if not (ip.b + D_SHIFT < PI.a):
            return False, 'd'
    # (e): chi0 = 2 i theta ;  X0 = -2 Im th, Y0 = 2 Re th
    X0 = -2 * th.imag
    Y0 = 2 * th.real + E_SHIFT
    if not excludes(X0):
        if not ((PI + ip).a > Y0.b):
            return False, 'e'
    return True, None


def check_theta_box(th, depth0=3, maxdepth=9):
    """all t in [-1,1] by adaptive dyadic subdivision.  Returns (ok, n_intervals, fail)"""
    # global parts of (f), and (e) lift condition
    if not ((th.real ** 2 + th.imag ** 2).b < (PI ** 2).a):
        return False, 0, '|theta|<pi'
    Y0 = 2 * th.real
    if not (Y0.a > PI.b and Y0.b < (3 * PI).a):
        return False, 0, 'e-lift'
    n = 1 << depth0
    stack = [(Fr(-1) + Fr(2 * k, n), Fr(-1) + Fr(2 * (k + 1), n), depth0) for k in range(n)]
    cnt = 0
    while stack:
        a, b, d = stack.pop()
        ok, why = check_T(th, a, b)
        if ok:
            cnt += 1
            continue
        if d >= maxdepth:
            return False, cnt, (why, float(a), float(b))
        m = (a + b) / 2
        stack.append((a, m, d + 1)); stack.append((m, b, d + 1))
    return True, cnt, None


def nw_box(args):
    """Re(lambda'(B) * conj(c)) > 0 on a box of R' (with subdivision)"""
    (x0, x1, y0, y1), c = args
    cc = cx(iv.mpf(c.real), iv.mpf(-c.imag))
    stack = [(x0, x1, y0, y1, 0)]
    n = 0
    while stack:
        a, b, p, q, d = stack.pop()
        B = cx(iv.mpf([ivq(a).a, ivq(b).b]), iv.mpf([ivq(p).a, ivq(q).b]))
        v = (dlam(B) * cc).real
        if v.a > 0:
            n += 1
            continue
        if d > 8:
            return False, n, (a, b, p, q)
        ma = (a + b) / 2; mp = (p + q) / 2
        stack += [(a, ma, p, mp, d + 1), (ma, b, p, mp, d + 1), (a, ma, mp, q, d + 1), (ma, b, mp, q, d + 1)]
    return True, n, None


def lam_box(re0, re1, im0, im1):
    return cx(iv.mpf([ivq(re0).a, ivq(re1).b]), iv.mpf([ivq(im0).a, ivq(im1).b]))


THSTAR = 2.29857900665128663858 + 0.76604606099318995273j


def square_task(args):
    re0, re1, im0, im1 = args
    L = lam_box(re0, re1, im0, im1)
    lc = complex(float((re0 + re1) / 2), float((im0 + im1) / 2))
    g = newton(lc, THSTAR)
    kr = krawczyk(L, g)
    if kr is None:
        return (args, False, 'krawczyk', 0)
    K, B, m = kr
    if not cinside(K, R_PRIME):
        return (args, False, 'K not in R\'', 0)
    ok, cnt, why = check_theta_box(K)
    return (args, ok, why, cnt)


def strip_task(args, depth=0):
    """returns a list of (box, ok, why, cnt, Kd) for the box, bisected in Re lambda
    where Krawczyk fails (only the partition is adaptive; every piece is certified)."""
    (re0, re1, im0, im1), g = args
    L = lam_box(re0, re1, im0, im1)
    g = newton(complex(float((re0 + re1) / 2), float((im0 + im1) / 2)), g)
    kr = krawczyk(L, g)
    if kr is None:
        if depth < 6:
            mid = (re0 + re1) / 2
            return (strip_task(((re0, mid, im0, im1), g), depth + 1)
                    + strip_task(((mid, re1, im0, im1), g), depth + 1))
        return [(args[0], False, 'krawczyk', 0, None)]
    K, B, m = kr
    ok, cnt, why = check_theta_box(K)
    Kd = (float(K.real.a), float(K.real.b), float(K.imag.a), float(K.imag.b))
    return [(args[0], ok, why, cnt, Kd)]


def main():
    t_start = time.time()
    pool = Pool(10)
    allok = True
    # ---------------- (NW) injectivity on R' ----------------
    c = dlam_f(THSTAR)
    nx, ny = 25, 33
    xs = [Fr(220, 100) + Fr(25, 100) * Fr(k, nx) for k in range(nx + 1)]
    ys = [Fr(62, 100) + Fr(33, 100) * Fr(k, ny) for k in range(ny + 1)]
    jobs = [((xs[i], xs[i + 1], ys[j], ys[j + 1]), c) for i in range(nx) for j in range(ny)]
    res = pool.map(nw_box, jobs)
    nwok = all(r[0] for r in res)
    print('NW on R\': ok=%s  boxes=%d' % (nwok, sum(r[1] for r in res)))
    # margin (min over coarse boxes, informational)
    cc = cx(iv.mpf(c.real), iv.mpf(-c.imag))
    mins = min(float((dlam(cx(iv.mpf([ivq(a).a, ivq(b).b]), iv.mpf([ivq(p).a, ivq(q).b]))) * cc).real.a) / abs(c) ** 2
               for (a, b, p, q), _ in jobs)
    print('   min lower bound of Re(lambda\'/c) over the %d boxes: %.4f' % (len(jobs), mins))
    allok &= nwok
    # ---------------- square ----------------
    nsq = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    h = Fr(2, 10) / nsq
    jobs = []
    for i in range(nsq):
        for j in range(nsq):
            jobs.append((Fr(-11, 10) + i * h, Fr(-11, 10) + (i + 1) * h, Fr(-1, 10) + j * h, Fr(-1, 10) + (j + 1) * h))
    res = pool.map(square_task, jobs, chunksize=4)
    bad = [r for r in res if not r[1]]
    print('square: %d lambda-boxes, %d t-intervals total, failures=%d' % (len(res), sum(r[3] for r in res), len(bad)))
    for r in bad[:10]:
        print('   FAIL', [float(v) for v in r[0]], r[2])
    allok &= not bad
    # ---------------- strip ----------------
    # boxes along Re lambda, full Im range [-1/1000,1/1000]
    im0, im1 = Fr(-1, 1000), Fr(1, 1000)
    w = Fr(1, 50)
    edges = [Fr(-12)]
    while edges[-1] < Fr(-1, 5):
        edges.append(min(edges[-1] + w, Fr(-1, 5)))
    boxes = [(edges[k], edges[k + 1], im0, im1) for k in range(len(edges) - 1)]
    # float Newton guesses by continuation from theta_* (only guesses)
    k1 = [k for k, b in enumerate(boxes) if b[0] <= -1 <= b[1]][0]
    guesses = [None] * len(boxes)
    g = THSTAR
    for k in range(k1, len(boxes)):
        g = newton(complex(float((boxes[k][0] + boxes[k][1]) / 2), 0), g); guesses[k] = g
    g = THSTAR
    for k in range(k1, -1, -1):
        g = newton(complex(float((boxes[k][0] + boxes[k][1]) / 2), 0), g); guesses[k] = g
    res = [x for lst in pool.map(strip_task, list(zip(boxes, guesses)), chunksize=2) for x in lst]
    boxes = [r[0] for r in res]
    for k in range(len(boxes) - 1):
        assert boxes[k][1] == boxes[k + 1][0]
    assert boxes[0][0] == -12 and boxes[-1][1] == Fr(-1, 5)
    k1 = [k for k, b in enumerate(boxes) if b[0] <= -1 <= b[1]][0]
    bad = [r for r in res if not r[1]]
    print('strip: %d lambda-boxes, %d t-intervals total, failures=%d' % (len(res), sum(r[3] for r in res), len(bad)))
    for r in bad[:10]:
        print('   FAIL', [float(v) for v in r[0]], r[2])
    allok &= not bad
    # anchor: box containing lambda=-1 has its root in R' (hence the square's branch)
    Kd = res[k1][4]
    K1 = cx(iv.mpf([Kd[0], Kd[1]]), iv.mpf([Kd[2], Kd[3]]))
    anchor = cinside(K1, R_PRIME) and boxes[k1][0] >= Fr(-11, 10) and boxes[k1][1] <= Fr(-9, 10)
    print('strip anchor box', [float(v) for v in boxes[k1]], 'root in R\':', anchor)
    allok &= anchor
    # chaining: injectivity on hull of adjacent theta-enclosures (Noshiro-Warschawski)
    chain_ok = True
    worst = 1e9
    for k in range(len(boxes) - 1):
        if res[k][4] is None or res[k + 1][4] is None:
            chain_ok = False; continue
        a, b = res[k][4], res[k + 1][4]
        H = cx(iv.mpf([min(a[0], b[0]), max(a[1], b[1])]), iv.mpf([min(a[2], b[2]), max(a[3], b[3])]))
        cm = dlam_f(complex(float(H.real.mid), float(H.imag.mid)))
        v = (dlam(H) * cx(iv.mpf(cm.real), iv.mpf(-cm.imag))).real
        if not v.a > 0:
            chain_ok = False
            print('   chain FAIL between', k, k + 1)
        worst = min(worst, float(v.a) / abs(cm) ** 2)
    print('strip chaining: ok=%s (min Re(lambda\'/c) lower bound on hulls %.4f)' % (chain_ok, worst))
    allok &= chain_ok
    print('ALL PASS' if allok else 'SOMETHING FAILED', ' time %.1fs' % (time.time() - t_start))


if __name__ == '__main__':
    main()
