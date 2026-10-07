"""Variation formula for the first-order coefficient kappa^(n) (beauty-plan-zh.md, P2).

Setting.  g(u) = u + a2 u^2 + ... is a real parabolic germ, f_s = g - s h + O(s^2) a real
unfolding with gamma = h(0) > 0.  For s > 0 small, f_s has two real fixed points and
    log( tau_n(s) / (B_n e^{2 pi i n a}) ) = kappa^(n)[g; h] p + O(p^2),   p = -log lam1 log lam2,
where tau_n is the normalised transition coefficient (base point u*), B_n the inverse upper
horn coefficients of g, a = Phi_att(u*)  (paper Thm D; general form Thm D' in
general-statements-zh.md).

Claim tested here (Variation formula).  Put c = h'(0)/(2 a2),
    h~ = h + c (1 - g')          (= gamma + O(u^2): the linear term is removed by the
                                  infinitesimal conjugacy u -> u - s c),
    h1 = h~ - gamma = O(u^2),    g_t = g - t h1   (a parabolic germ for every small t).
Then
    4 a2 gamma kappa^(n)[g; h] = 4 a2 gamma kappa^(n)[g; 1]                    (I)  universal
                               + d/dt log(B_n(g_t) e^{2 pi i n a(g_t)}) |_{t=0} (II) horn variation
                               - 2 pi i n c gamma ... (see `gauge` below)       (III) base-point gauge
(III) is purely imaginary.  So Re kappa = (germ constant) + (Melnikov derivative of |B_n|).

The three ingredients are computed by DIFFERENT code paths:
  * kappa[g; h] for each unfolding: uniform-model regularisation at s = +-eps (as in
    mrr_derivative.py, generalised to an arbitrary germ g and direction h);
  * (II): parabolic Fatou coordinates of the germs g_{+-delta} (generality_check.Parab);
  * (III): Phi_att'(u*) of g.

Usage: python3 docs/kappa_variation.py GERM [dps]      GERM in exp, quad
"""
from __future__ import annotations

import sys

import mpmath as mp

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from generality_check import Alpha as GAlpha, Parab  # noqa: E402
from mrr_derivative import ser_mul, ser_log1, poly_rem  # noqa: E402


# --------------------------------------------------------------------------- analytic maps
class Fn:
    """An entire (or disc-analytic) function given by value, derivative and Taylor series at 0."""

    def __init__(self, val, der, taylor):
        self.val, self.der, self.taylor = val, der, taylor

    def __add__(self, o):
        return Fn(lambda u: self.val(u) + o.val(u), lambda u: self.der(u) + o.der(u),
                  lambda M: [x + y for x, y in zip(self.taylor(M), o.taylor(M))])

    def scale(self, c):
        return Fn(lambda u: c * self.val(u), lambda u: c * self.der(u),
                  lambda M: [c * x for x in self.taylor(M)])


def const(c):
    return Fn(lambda u: mp.mpc(c), lambda u: mp.mpc(0), lambda M: [mp.mpc(c)] + [mp.mpc(0)] * M)


def poly(cs):
    """sum cs[k] u^k."""
    cs = [mp.mpc(x) for x in cs]
    return Fn(lambda u: sum(c * u**k for k, c in enumerate(cs)),
              lambda u: sum(k * c * u**(k - 1) for k, c in enumerate(cs) if k),
              lambda M: (cs + [mp.mpc(0)] * (M + 1))[:M + 1])


def exp_times_poly(cs):
    """e^u * sum cs[k] u^k."""
    P = poly(cs)

    def tay(M):
        e = [1 / mp.factorial(k) for k in range(M + 1)]
        return ser_mul(P.taylor(M), e, M + 1)
    return Fn(lambda u: mp.exp(u) * P.val(u), lambda u: mp.exp(u) * (P.val(u) + P.der(u)), tay)


GERMS = {
    # g, its parabolic a2
    "exp": (Fn(mp.expm1, mp.exp, lambda M: [mp.mpc(0)] + [1 / mp.factorial(k) for k in range(1, M + 1)]),
            mp.mpf(1) / 2),
    "quad": (poly([0, 1, 1]), mp.mpf(1)),
}


# --------------------------------------------------------------------------- hyperbolic side
class Model:
    """Uniform model time for the map F = g - s h (s complex, tiny)."""

    def __init__(self, g, h, s, a2, N=6, M=48):
        self.s = s = mp.mpc(s)
        self.g, self.h, self.N = g, h, N
        F = lambda u: g.val(u) - s * h.val(u) - u  # noqa: E731
        r = mp.sqrt(s * h.val(0) / a2)
        self.u1, self.u2 = mp.findroot(F, -r), mp.findroot(F, r)
        self.lam1, self.lam2 = self.fprime(self.u1), self.fprime(self.u2)
        self.A1, self.A2 = 1 / mp.log(self.lam1), 1 / mp.log(self.lam2)
        self.nu = self.A1 + self.A2
        self.p = -mp.log(self.lam1) * mp.log(self.lam2)
        fs = [x - s * y for x, y in zip(g.taylor(M), h.taylor(M))]
        Flog = [mp.mpc(0)] * M
        for A, uj in ((self.A1, self.u1), (self.A2, self.u2)):
            b = [mp.mpc(0)] * M          # f(u) - uj = (u - uj) b(u)
            a2_ = list(fs)
            a2_[0] -= uj
            b[M - 1] = a2_[M]
            for k in range(M - 1, 0, -1):
                b[k - 1] = a2_[k] + uj * b[k]
            L = ser_log1([x / b[0] for x in b], M)
            L[0] = mp.log(b[0])
            for k in range(M):
                Flog[k] += A * L[k]
        Flog[0] -= 1
        q = [self.u1 * self.u2, -(self.u1 + self.u2), mp.mpc(1)]
        Q = [mp.mpc(1)]
        for _ in range(N):
            Q = ser_mul(Q + [0] * 3, q + [0] * len(Q), len(Q) + 2)
        nun = 2 * N - 2
        fpow = [mp.mpc(1)] + [mp.mpc(0)] * (M - 1)
        cols = []
        for i in range(1, nun + 1):
            fpow = ser_mul(fpow, fs[:M], M)
            D = list(fpow)
            D[i] -= 1
            cols.append(poly_rem(D, Q))
        rhs = poly_rem(Flog, Q)
        Am = mp.matrix(len(rhs), nun)
        for i in range(len(rhs)):
            for j in range(nun):
                Am[i, j] = cols[j][i]
        y = mp.matrix([-x for x in rhs])
        AH = Am.H
        e = mp.lu_solve(AH * Am, AH * y)
        self.e = [e[j] for j in range(nun)]
        res = Am * e - y
        self.res = max(abs(res[i]) for i in range(len(rhs)))

    def f(self, u):
        return self.g.val(u) - self.s * self.h.val(u)

    def fprime(self, u):
        return self.g.der(u) - self.s * self.h.der(u)

    def finv(self, v, ref):
        x = ref
        for _ in range(60):
            st = (self.f(x) - v) / self.fprime(x)
            x -= st
            if abs(st) < mp.mpf(10) ** (-mp.mp.dps + 3):
                break
        return x

    def P(self, u):
        acc = mp.mpc(0)
        for c in reversed(self.e):
            acc = (acc + c) * u
        return acc

    def F(self, u):
        fu = self.f(u)
        return (self.A1 * mp.log((fu - self.u1) / (u - self.u1))
                + self.A2 * mp.log((fu - self.u2) / (u - self.u2))
                + self.P(fu) - self.P(u) - 1)

    def Psi(self, u):
        return (self.nu * mp.log(u) + self.A1 * mp.log(1 - self.u1 / u)
                + self.A2 * mp.log(1 - self.u2 / u) + self.P(u))


def phi_att(mo, u, n, r0):
    m, uk, acc = None, u, mp.mpc(0)
    for k in range(n):
        if m is None and abs(uk) < r0 and mp.re(uk) < 0:
            m = k
            acc = mo.Psi(uk) - m
        if m is not None:
            acc += mo.F(uk)
        uk = mo.f(uk)
    return acc


def phi_rep(mo, path, n, r0):
    """path[k] = g^{-k}(u) (the s = 0 backward orbit, used as Newton seeds)."""
    m, vk, acc = None, path[0], mp.mpc(0)
    for k in range(n + 1):
        if m is None and abs(vk) < r0 and mp.re(vk) > 0:
            m = k
            acc = mo.Psi(vk) + m
        elif m is not None:
            acc -= mo.F(vk)
        if k + 1 >= len(path):
            break
        vk = mo.finv(vk, path[k + 1])
    return acc


def gate_points(g, a2, Y, Nz, n):
    """Points z_j = j/Nz + iY in repelling Fatou time of g, with the backward g-orbit
    of Phi_rep^{-1}(z_j) of length n (deep end near 0 on the positive side)."""
    al = GAlpha([mp.mpf(0)] + [mp.re(x) for x in g.taylor(34)[1:]], 30)
    pts = []
    for j in range(Nz):
        z = mp.mpc(mp.mpf(j) / Nz, Y)
        n0 = int(mp.ceil(1 / (a2 * mp.mpf('0.005')) + mp.re(z))) + 4
        t = z - n0
        u = -1 / (a2 * t)
        for _ in range(100):
            st = (al(u, cont=False) - t) / al.deriv(u)
            u -= st
            if abs(st) < mp.mpf(10) ** (-(mp.mp.dps - 5)):
                break
        fw = [u]
        for _ in range(n0):
            fw.append(g.val(fw[-1]))
        path = fw[::-1]                         # path[k] = g^{-k}(gate point)
        # extend the backward orbit deeper, toward 0 from the right
        while len(path) < n + 2:
            v = path[-1]
            x = v
            for _ in range(60):
                st = (g.val(x) - v) / g.der(x)
                x -= st
                if abs(st) < mp.mpf(10) ** (-mp.mp.dps + 3):
                    break
            path.append(x)
        pts.append((z, path))
    return pts


def dlogtau(g, a2, h, ustar, gp, eps, n=1500, r0=mp.mpf('0.05'), N=6, nmax=3):
    """d/ds log tau_k at s = 0 (k = 1..nmax) and dp/ds, for F_s = g - s h."""
    mods = {sg: Model(g, h, sg * eps, a2, N=N) for sg in (1, -1)}
    dpds = (mods[1].p - mods[-1].p) / (2 * eps)
    PA = {sg: phi_att(mo, ustar, n, r0) for sg, mo in mods.items()}
    T0, dT, dR, zs = [], [], [], []
    for z, path in gp:
        u = path[0]
        a = {sg: phi_att(mo, u, n, r0) - PA[sg] for sg, mo in mods.items()}
        r = {sg: phi_rep(mo, path, n, r0) for sg, mo in mods.items()}
        zs.append((r[1] + r[-1]) / 2)
        T0.append((a[1] + a[-1]) / 2)
        dT.append((a[1] - a[-1]) / (2 * eps))
        dR.append((r[1] - r[-1]) / (2 * eps))
    Nz = len(gp)

    def dft(vals, k):
        return sum(vals[j] * mp.exp(-2j * mp.pi * k * zs[j]) for j in range(Nz)) / Nz
    gg = [T0[j] - zs[j] for j in range(Nz)]
    t = {k: dft(gg, k) for k in range(-3, Nz // 2)}
    d1 = [1 + sum(2j * mp.pi * k * t[k] * mp.exp(2j * mp.pi * k * zs[j]) for k in range(1, Nz // 2))
          for j in range(Nz)]
    dTz = [dT[j] - d1[j] * dR[j] for j in range(Nz)]
    dt = {k: dft(dTz, k) for k in range(0, nmax + 1)}
    out = {k: dt[k] / t[k] - 2j * mp.pi * k * dt[0] for k in range(1, nmax + 1)}
    tau0 = {k: t[k] * mp.exp(-2j * mp.pi * k * t[0]) for k in range(1, nmax + 1)}
    return out, dpds, tau0, max(mods[1].res, mods[-1].res), abs(t[-1])


# --------------------------------------------------------------------------- parabolic side
class GermFam:
    """Adapter so generality_check.Parab can treat g_t as a 'family' at its saddle-node."""

    def __init__(self, G):
        self.G, self.wstar, self.c0 = G, mp.mpf(0), None

    def f(self, w, c):
        return self.G.val(w)

    def taylor(self, x0, c, K):
        return [None] + [mp.re(x) for x in self.G.taylor(K)[1:]]


def horn_data(G, ustar, Y, nmax=3):
    par = Parab(GermFam(G), K=30, umax="0.004")
    a = par.phi_att(ustar)
    B = par.horn_inverse(Y, N=24, nmax=nmax)
    return {k: B[k] * mp.exp(2j * mp.pi * k * a) for k in range(1, nmax + 1)}, a, par


# --------------------------------------------------------------------------- driver
def main():
    germ = sys.argv[1] if len(sys.argv) > 1 else "exp"
    mp.mp.dps = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    g, a2 = GERMS[germ]
    eps = mp.mpf(10) ** (-(mp.mp.dps // 3))
    delta = mp.mpf(10) ** (-(mp.mp.dps // 3))
    if germ == "exp":
        ustar = 1 / mp.e - 1
        # tetration direction: d/ds of -(exp(-s+(1-s)u) - 1) at s=0 is (1+u)e^u
        dirs = {"1": const(1), "tet": exp_times_poly([1, 1]),
                "1+u2": poly([1, 0, '0.6']), "1+u+u4": poly([1, '0.3', 0, 0, '0.5'])}
        Y = mp.mpf('1.0')
    else:
        ustar = mp.mpf('-0.5')          # w0 = 0 for w^2 + c (w = 1/2 + u)
        dirs = {"1": const(1), "1+u2": poly([1, 0, '0.7']), "1+u+u3": poly([1, '0.3', 0, '-0.4'])}
        Y = mp.mpf('1.0')
    gp = gate_points(g, a2, Y, 24, 1500)
    print(f"germ {germ}: a2={a2}, u*={mp.nstr(ustar, 12)}, dps={mp.mp.dps}", flush=True)

    # universal constant K_n = kappa[g; 1]
    res = {}
    for name, h in dirs.items():
        out, dpds, tau0, fitres, tneg = dlogtau(g, a2, h, ustar, gp, eps)
        gam = mp.re(h.val(0))
        res[name] = {k: v / dpds for k, v in out.items()}
        print(f"[{name}] gamma={mp.nstr(gam, 6)} dp/ds={mp.nstr(dpds, 15)} (pred {mp.nstr(4 * a2 * gam, 6)}) "
              f"fit res={mp.nstr(fitres, 3)} |t_-1|={mp.nstr(tneg, 3)}", flush=True)
        for k, v in res[name].items():
            print(f"     kappa^({k}) = {mp.nstr(v, 22)}", flush=True)

    # Phi_att'(u*) of g, for the gauge term
    _, a0, par0 = horn_data(g, ustar, Y)
    hh = mp.mpf(10) ** (-(mp.mp.dps // 3))
    dphi = (par0.phi_att(ustar + hh) - par0.phi_att(ustar - hh)) / (2 * hh)

    for name, h in dirs.items():
        if name == "1":
            continue
        gam = mp.re(h.val(0))
        c = h.der(0) / (2 * a2)
        Gp = Fn(lambda u: g.val(u) - delta * (h.val(u) + c * (1 - g.der(u)) - gam), None,
                lambda M: [x - delta * (y - c * z - (gam if i == 0 else 0))
                           for i, (x, y, z) in enumerate(zip(g.taylor(M), h.taylor(M), gprime_minus1_taylor(g, M)))])
        Gm = Fn(lambda u: g.val(u) + delta * (h.val(u) + c * (1 - g.der(u)) - gam), None,
                lambda M: [x + delta * (y - c * z - (gam if i == 0 else 0))
                           for i, (x, y, z) in enumerate(zip(g.taylor(M), h.taylor(M), gprime_minus1_taylor(g, M)))])
        assert abs(Gp.taylor(3)[0]) < mp.mpf(10) ** (-mp.mp.dps + 5)
        assert abs(Gp.taylor(3)[1] - 1) < mp.mpf(10) ** (-mp.mp.dps + 5), Gp.taylor(3)
        Lp, _, _ = horn_data(Gp, ustar, Y)
        Lm, _, _ = horn_data(Gm, ustar, Y)
        print(f"[{name}] c = h'(0)/(2a2) = {mp.nstr(c, 10)}", flush=True)
        for k in res[name]:
            II = (mp.log(Lp[k]) - mp.log(Lm[k])) / (2 * delta)
            III = 2j * mp.pi * k * c * dphi
            pred = res["1"][k] + (II - III) / (4 * a2 * gam)
            got = res[name][k]
            print(f"     n={k}: kappa = {mp.nstr(got, 20)}", flush=True)
            print(f"           K_n + (II - III)/4a2g = {mp.nstr(pred, 20)}   |diff| = {mp.nstr(abs(got - pred), 3)}",
                  flush=True)
            print(f"           Re: K_n = {mp.nstr(mp.re(res['1'][k]), 15)}, "
                  f"Melnikov Re(II)/4a2g = {mp.nstr(mp.re(II) / (4 * a2 * gam), 15)}", flush=True)


def gprime_minus1_taylor(g, M):
    """Taylor series of g'(u) - 1."""
    t = g.taylor(M + 1)
    out = [(k + 1) * t[k + 1] for k in range(M + 1)]
    out[0] -= 1
    return out




# --------------------------------------------------------------------------- Melnikov orbit series
def melnikov(G, X1, ustar, Y, nmax=3, Nz=24, umax="0.004", delta=None):
    """M_n(g)[X1] = d/dt log(B_n e^{2 pi i n a})(g - t X1) at t = 0, by the regularised
    orbit series of kappa-variation-zh.md 2.5 (no finite difference of horn data).
    Only the formal Abel function is differentiated in t (its coefficients are polynomial
    in the Taylor coefficients of the germ)."""
    delta = delta or mp.mpf(10) ** (-(mp.mp.dps // 2))
    umax = mp.mpf(umax)
    tay = lambda M, sg: [x - sg * delta * y for x, y in zip(G.taylor(M), X1.taylor(M))]  # noqa: E731
    al0 = GAlpha([mp.mpf(0)] + [mp.re(x) for x in G.taylor(34)[1:]], 30)
    alp = GAlpha([mp.mpf(0)] + [mp.re(x) for x in tay(34, 1)[1:]], 30)
    alm = GAlpha([mp.mpf(0)] + [mp.re(x) for x in tay(34, -1)[1:]], 30)
    a2 = mp.re(G.taylor(3)[2])

    def adot(u):
        return (alp(u, cont=False) - alm(u, cont=False)) / (2 * delta)

    def att(u):
        """Phi_att(u), Phi_att'(u), dot Phi_att(u)."""
        orb = [u]
        while abs(orb[-1]) > umax or mp.re(orb[-1]) > 0:
            orb.append(G.val(orb[-1]))
            if len(orb) > 10**6:
                raise RuntimeError("orbit does not enter the petal")
        for _ in range(8):
            orb.append(G.val(orb[-1]))
        K = len(orb) - 1
        al0.reset()
        for w in orb:
            al0(w)
        phi = al0(orb[-1]) - K
        dphi = al0.deriv(orb[-1])               # Phi'(u_K)
        dot = adot(orb[-1])
        for k in range(K - 1, -1, -1):          # Phi'(u_{k+1}) known as dphi
            dot -= dphi * X1.val(orb[k])
            dphi *= G.der(orb[k])               # Phi'(u_k) = Phi'(u_{k+1}) g'(u_k)
        return phi, dphi, dot

    def rep(z):
        """u = Phi_rep^{-1}(z), Phi_rep'(u), dot Phi_rep(u)."""
        n = max(int(mp.ceil(1 / (a2 * umax) + mp.re(z))) + 6, 1)
        t = z - n
        v = -1 / (a2 * t)
        for _ in range(100):
            st = (al0(v, cont=False) - t) / al0.deriv(v)
            v -= st
            if abs(st) < mp.mpf(10) ** (-(mp.mp.dps - 5)):
                break
        path = [v]                              # v_n, v_{n-1}, ..., v_0
        for _ in range(n):
            path.append(G.val(path[-1]))
        dphi = al0.deriv(path[0])
        dot = adot(path[0])
        for j in range(1, n + 1):               # v_{k-1} = path[j], v_k = path[j-1]
            dphi = dphi / G.der(path[j - 1])    # Phi'(v_{k-1}) = Phi'(v_k)/g'(v_k)
            dot += dphi * X1.val(path[j - 1])
        return path[-1], dphi, dot

    zs = [mp.mpc(mp.mpf(j) / Nz, Y) for j in range(Nz)]
    vals, dvals = [], []
    for z in zs:
        u, dr, drot = rep(z)
        pa, da, dat = att(u)
        vals.append(pa - z)
        dvals.append(dat - (da / dr) * drot)
    B = {k: sum(vals[j] * mp.exp(-2j * mp.pi * k * zs[j]) for j in range(Nz)) / Nz for k in range(1, nmax + 1)}
    dB = {k: sum(dvals[j] * mp.exp(-2j * mp.pi * k * zs[j]) for j in range(Nz)) / Nz for k in range(1, nmax + 1)}
    _, _, adt = att(mp.mpc(ustar))
    return {k: dB[k] / B[k] + 2j * mp.pi * k * adt for k in range(1, nmax + 1)}


def check_melnikov(germ="exp", dps=45):
    mp.mp.dps = dps
    g, a2 = GERMS[germ]
    if germ == "exp":
        ustar, X1s = 1 / mp.e - 1, {"0.6u2": poly([0, 0, '0.6']), "-0.15(1-g')+0.5u4": None}
    else:
        ustar, X1s = mp.mpf('-0.5'), {"0.3u-0.4u3 class": None}
    Y = mp.mpf('1.0')
    delta = mp.mpf(10) ** (-(dps // 3))
    # direction X = 1 + 0.6u^2 (exp) / 1 + 0.3u - 0.4u^3 (quad), as in main()
    dirs = {"exp": [poly([1, 0, '0.6']), poly([1, '0.3', 0, 0, '0.5'])],
            "quad": [poly([1, '0.3', 0, '-0.4']), poly([1, 0, '0.7'])]}[germ]
    for X in dirs:
        gam = mp.re(X.val(0))
        c = X.der(0) / (2 * a2)
        X1 = Fn(lambda u, X=X, c=c, gam=gam: X.val(u) + c * (1 - g.der(u)) - gam, None,
                lambda M, X=X, c=c, gam=gam: [x - c * y - (gam if i == 0 else 0)
                                              for i, (x, y) in enumerate(zip(X.taylor(M), gprime_minus1_taylor(g, M)))])
        Ms = melnikov(g, X1, ustar, Y)
        Gp = Fn(lambda u, X1=X1: g.val(u) - delta * X1.val(u), None,
                lambda M, X1=X1: [x - delta * y for x, y in zip(g.taylor(M), X1.taylor(M))])
        Gm = Fn(lambda u, X1=X1: g.val(u) + delta * X1.val(u), None,
                lambda M, X1=X1: [x + delta * y for x, y in zip(g.taylor(M), X1.taylor(M))])
        Lp, _, _ = horn_data(Gp, ustar, Y)
        Lm, _, _ = horn_data(Gm, ustar, Y)
        print(f"[{germ}] X = {[mp.nstr(mp.re(x), 3) for x in X.taylor(4)]}", flush=True)
        for k in Ms:
            fd = (mp.log(Lp[k]) - mp.log(Lm[k])) / (2 * delta)
            print(f"   n={k}: orbit series {mp.nstr(Ms[k], 20)}   finite diff {mp.nstr(fd, 20)}   "
                  f"|diff|={mp.nstr(abs(Ms[k] - fd), 3)}", flush=True)


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "melnikov":
        check_melnikov(sys.argv[2] if len(sys.argv) > 2 else "exp", int(sys.argv[3]) if len(sys.argv) > 3 else 45)
    else:
        main()
