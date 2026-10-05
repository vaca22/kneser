"""Generality test (theory-framework-zh.md §7, Q10): does the transition-map
machinery of the separation paper work for NON-exponential families?

For a real one-parameter family f with two real fixed points p < q
(p attracting, multiplier lam; q repelling, multiplier lam2) that merge in a
saddle-node, we compute -- with nothing specific to the exponential:

  hyperbolic side   R = attracting Koenigs coordinate, R^{-1}(w0) = 0
                    S = repelling Koenigs coordinate, S(R) = (p, q)
                    T = R^{-1} o S,  T(z) - z = sum t_n e^{2 pi i n z}
                    tau_n = t_n e^{-2 pi i n t0}   (t0 on the branch Im t0 = h/2)
  parabolic side    germ g(u) = u + a2 u^2 + ...  at the saddle-node,
                    formal Abel function alpha = A/u + rho log(-u) + sum d_k u^k,
                    Fatou coordinates normalised by alpha,
                    Phi_att o Phi_rep^{-1}(z) = z + sum B_n e^{2 pi i n z},
                    a = Phi_att(u(w0)).

Predictions transferred verbatim from the exponential case (Theorem A, D):
  (P1) tau_n -> B_n e^{2 pi i n a}
  (P2) t_n / t_1^n -> B_n / B_1^n
  (P3) log(tau_1 / B_1 e^{2 pi i a}) / p -> kappa  (finite),  p = |log lam| log lam2
  (P4) the sewing solution has hat c_n = c_n / Lambda^n = tau_n + O(Lambda).

Usage: [GC_Y0=y0[,y0check]] python3 generality_check.py FAMILY [lam ...]   FAMILY in quad, sine, expq, exp
GC_Y0 = height of the sampling line above Im z = -h2/2 in S-time (default 1.5); it must lie in
the part of the strip whose S-image is in the basin of p (family dependent).
"""
from __future__ import annotations

import sys

import mpmath as mp

# --------------------------------------------------------------------------- families
# Each family: from(lam) -> parameter; fixed(c) -> (p, q); f(w, c); taylor(x0, c, K) ->
# [None, g1, g2, ...] with f(x0 + x) = f(x0) + sum g_k x^k; c0, wstar (saddle-node);
# w0 (base point, w0 < p, in the immediate basin of p).


class Quad:
    """f(w) = w^2 + c, c < 1/4.  p = lam/2, q = 1 - lam/2, germ u + u^2."""
    name, w0 = "quad  w^2+c", property(lambda self: mp.mpf("0.2"))

    def param(self, lam):
        return (1 - (1 - lam) ** 2) / 4

    def fixed(self, c):
        r = mp.sqrt(1 - 4 * c)
        return (1 - r) / 2, (1 + r) / 2

    def f(self, w, c):
        return w * w + c

    def taylor(self, x0, c, K):
        g = [None] + [mp.mpf(0)] * K
        g[1], g[2] = 2 * x0, mp.mpf(1)
        return g

    c0 = property(lambda self: mp.mpf(1) / 4)
    wstar = property(lambda self: mp.mpf(1) / 2)


class Sine:
    """f(v) = v - sin v + c, c < 1.  p = arcsin c, q = pi - p, germ u + u^2/2 - u^4/24 + ..."""
    name, w0 = "sine  v-sin v+c", property(lambda self: mp.mpf("0.8"))

    def param(self, lam):
        return mp.sin(mp.acos(1 - lam))

    def fixed(self, c):
        p = mp.asin(c)
        return p, mp.pi - p

    def f(self, w, c):
        return w - mp.sin(w) + c

    def taylor(self, x0, c, K):
        s, co = mp.sin(x0), mp.cos(x0)
        der = [s, co, -s, -co]          # sin^{(k)}(x0)
        g = [None] + [mp.mpf(0)] * K
        for k in range(1, K + 1):
            g[k] = -der[k % 4] / mp.factorial(k)
        g[1] += 1
        return g

    c0 = property(lambda self: mp.mpf(1))
    wstar = property(lambda self: mp.pi / 2)


class ExpQ:
    """f(w) = w + (w^2 - eps) e^w.  p = -sqrt eps, q = +sqrt eps (asymmetric multipliers),
    germ u + u^2 e^u."""
    name, w0 = "expq  w+(w^2-eps)e^w", property(lambda self: mp.mpf("-0.8"))

    def param(self, lam):
        # 1 - lam = 2 s e^{-s}, s = sqrt eps < 1
        s = mp.findroot(lambda s: 2 * s * mp.exp(-s) - (1 - lam), (1 - lam) / 2)
        return s * s

    def fixed(self, c):
        s = mp.sqrt(c)
        return -s, s

    def f(self, w, c):
        return w + (w * w - c) * mp.exp(w)

    def taylor(self, x0, c, K):
        e0 = mp.exp(x0)
        poly = [x0 * x0 - c, 2 * x0, mp.mpf(1)]
        g = [None] + [mp.mpf(0)] * K
        for k in range(1, K + 1):
            g[k] = e0 * sum(poly[j] / mp.factorial(k - j) for j in range(3) if k - j >= 0)
        g[1] += 1
        return g

    c0 = property(lambda self: mp.mpf(0))
    wstar = property(lambda self: mp.mpf(0))


class Exp:
    """Control: w -> b^w, the case of the paper.  w0 = 1."""
    name, w0 = "exp   b^w (control)", property(lambda self: mp.mpf(1))

    def param(self, lam):
        return lam * mp.exp(-lam)          # log b

    def fixed(self, lb):
        lam2 = mp.findroot(lambda t: t * mp.exp(-t) - lb, mp.mpf(2) + 2 * (1 - lb * mp.e))
        lam = mp.findroot(lambda t: t * mp.exp(-t) - lb, mp.mpf("0.5"))
        return mp.exp(lam), mp.exp(lam2)

    def f(self, w, lb):
        return mp.exp(lb * w)

    def taylor(self, x0, lb, K):
        y0 = mp.exp(lb * x0)
        return [None] + [y0 * lb**k / mp.factorial(k) for k in range(1, K + 1)]

    c0 = property(lambda self: 1 / mp.e)
    wstar = property(lambda self: +mp.e)


FAMILIES = {"quad": Quad, "sine": Sine, "expq": ExpQ, "exp": Exp}

# --------------------------------------------------------------------------- series


def schroeder(lam, g, N):
    """sigma with sigma(g(x)) = lam sigma(x), sigma'(0) = 1 (g[1] = lam)."""
    gp = [[mp.mpf(0)] * (N + 1) for _ in range(N + 1)]
    gp[0][0] = mp.mpf(1)
    for j in range(1, N + 1):
        for a_ in range(N + 1):
            if gp[j - 1][a_] == 0:
                continue
            for k in range(1, N + 1 - a_):
                gp[j][a_ + k] += gp[j - 1][a_] * g[k]
    s = [mp.mpf(0)] * (N + 1)
    s[1] = mp.mpf(1)
    for k in range(2, N + 1):
        s[k] = sum(s[j] * gp[j][k] for j in range(1, k)) / (lam - lam**k)
    return s


def peval(c, x):
    r = mp.mpf(0)
    for a_ in reversed(c[1:]):
        r = (r + a_) * x
    return r


def pderiv(c, x):
    r = mp.mpf(0)
    for k in range(len(c) - 1, 0, -1):
        r = r * x + k * c[k]
    return r


def smul(a_, b_, M):
    out = [mp.mpf(0)] * (M + 1)
    for i, x in enumerate(a_):
        if x == 0:
            continue
        for j in range(0, M + 1 - i):
            if j < len(b_):
                out[i + j] += x * b_[j]
    return out


# --------------------------------------------------------------------------- hyperbolic side


class Hyper:
    def __init__(self, fam, lam, N=60):
        self.fam = fam
        self.c = fam.param(lam)
        self.p, self.q = fam.fixed(self.c)
        g1 = fam.taylor(self.p, self.c, N)
        g2 = fam.taylor(self.q, self.c, N)
        self.lam, self.lam2 = g1[1], g2[1]
        assert 0 < self.lam < 1 < self.lam2, (self.lam, self.lam2)
        self.s = schroeder(self.lam, g1, N)
        self.t = schroeder(self.lam2, g2, N)
        self.h = 2 * mp.pi / abs(mp.log(self.lam))
        self.h2 = 2 * mp.pi / mp.log(self.lam2)
        self.Lam = mp.exp(4 * mp.pi**2 / mp.log(self.lam))
        self.logsig0, self.n0 = self._logsig(fam.w0)

    def F(self, w):
        return self.fam.f(w, self.c)

    def _logsig(self, w, r=mp.mpf("1e-4")):
        n = 0
        while abs(w - self.p) > r:
            w = self.F(w)
            n += 1
            if abs(mp.im(w)) > 40 or abs(w) > 1000 or n > 10**6:
                raise RuntimeError("no convergence to p")
        return mp.log(peval(self.s, w - self.p)), n

    def Rinv(self, w):
        ls, n = self._logsig(w)
        return self.n0 - n + (ls - self.logsig0) / mp.log(self.lam)

    def tau_inv(self, y):
        x = y
        for _ in range(80):
            dx = (peval(self.t, x) - y) / pderiv(self.t, x)
            x -= dx
            if abs(dx) < mp.mpf(10) ** (-mp.mp.dps + 5) * (abs(x) + mp.mpf(10) ** -mp.mp.dps):
                break
        return x

    def S(self, z, r=mp.mpf("1e-4")):
        m = max(int(mp.ceil((mp.re(z) * mp.log(self.lam2) - mp.log(r)) / mp.log(self.lam2))) + 1, 0)
        w = self.q + self.tau_inv(-mp.power(self.lam2, z - m))
        for _ in range(m):
            w = self.F(w)
        return w

    def modes(self, y, N=32, nmax=3):
        ih = 1j * 2 * mp.pi / mp.log(self.lam)
        vals, prev = [], None
        for k in range(N):
            z = mp.mpf(k) / N + 1j * y
            v = self.Rinv(self.S(z)) - z
            if prev is not None:
                v += mp.nint(mp.im(prev - v) / mp.im(ih)) * ih
            vals.append(v)
            prev = v
        out = {n: sum(vals[k] * mp.exp(-2j * mp.pi * n * (mp.mpf(k) / N + 1j * y))
                      for k in range(N)) / N for n in range(-nmax, nmax + 1)}
        out[0] += mp.nint((self.h / 2 - mp.im(out[0])) / self.h) * self.h * 1j
        return out


# --------------------------------------------------------------------------- parabolic side


class Alpha:
    """Formal Abel function of g(u) = u + a2 u^2 + ...:  A/u + rho log(-u) + sum_{k=1}^K d_k u^k."""

    def __init__(self, a, K=30):
        M = K + 3
        G = [mp.mpf(0)] + [a[j + 1] if j + 1 < len(a) else mp.mpf(0) for j in range(1, M + 1)]
        # IG = 1/(1+G) - 1,  LG = log(1+G),  P_k = (1+G)^k - 1
        IG = [mp.mpf(0)] * (M + 1)
        powG = [mp.mpf(1)] + [mp.mpf(0)] * M
        LG = [mp.mpf(0)] * (M + 1)
        for j in range(1, M + 1):
            powG = smul(powG, G, M)
            for i in range(M + 1):
                IG[i] += (-1) ** j * powG[i]
                LG[i] += (-1) ** (j + 1) * powG[i] / j
        onepG = [mp.mpf(1)] + G[1:]
        P = {}
        cur = [mp.mpf(1)] + [mp.mpf(0)] * M
        for k in range(1, K + 1):
            cur = smul(cur, onepG, M)
            P[k] = [mp.mpf(0)] + cur[1:]
        self.A = 1 / IG[1]
        self.rho = -self.A * IG[2] / LG[1]
        d = [mp.mpf(0)] * (K + 1)
        for m in range(2, K + 2):
            known = self.A * IG[m + 1] + self.rho * LG[m] + sum(d[k] * P[k][m - k] for k in range(1, m - 1))
            d[m - 1] = -known / P[m - 1][1]
        self.d = d
        self.prev = None

    def reset(self):
        self.prev = None

    def logc(self, u, cont=True):
        L = mp.log(-u)
        if cont and self.prev is not None:
            L += 2j * mp.pi * mp.nint((mp.im(self.prev) - mp.im(L)) / (2 * mp.pi))
        if cont:
            self.prev = L
        return L

    def __call__(self, u, cont=True):
        return self.A / u + self.rho * self.logc(u, cont) + peval(self.d, u)

    def deriv(self, u):
        return -self.A / u**2 + self.rho / u + pderiv(self.d, u)


class Parab:
    def __init__(self, fam, K=30, umax="0.004"):
        self.fam = fam
        g = fam.taylor(fam.wstar, fam.c0, K + 4)
        assert abs(g[1] - 1) < mp.mpf(10) ** (-mp.mp.dps + 10), g[1]
        self.a2 = g[2]
        self.al = Alpha(g, K)
        self.umax = mp.mpf(umax)

    def g(self, u):
        return self.fam.f(self.fam.wstar + u, self.fam.c0) - self.fam.wstar

    def phi_att(self, u, nextra=8):
        al = self.al
        al.reset()
        al(u)
        k = 0
        while (abs(u) > self.umax or mp.re(u) > 0) and k < 10**6:
            u = self.g(u)
            k += 1
            if abs(u) > 50:
                raise RuntimeError("gate point outside the parabolic basin")
            al(u)
        for _ in range(nextra):
            u = self.g(u)
            k += 1
            al(u)
        return al(u) - k

    def phi_rep_inv(self, z, nextra=6):
        al = self.al
        n = max(int(mp.ceil(1 / (self.a2 * self.umax) + mp.re(z))) + nextra, 1)
        t = z - n
        u = -1 / (self.a2 * t)
        for _ in range(100):
            step = (al(u, cont=False) - t) / al.deriv(u)
            u -= step
            if abs(step) < mp.mpf(10) ** (-(mp.mp.dps - 5)):
                break
        for _ in range(n):
            u = self.g(u)
        return u

    def horn_inverse(self, Y, N=24, nmax=3):
        vals = []
        for j in range(N):
            z = mp.mpc(mp.mpf(j) / N, Y)
            vals.append(self.phi_att(self.phi_rep_inv(z)) - z)
        return {n: sum(vals[j] * mp.exp(-2j * mp.pi * n * mp.mpc(mp.mpf(j) / N, Y))
                       for j in range(N)) / N for n in range(-nmax, nmax + 1)}


# --------------------------------------------------------------------------- driver


def main():
    import os
    fam = FAMILIES[sys.argv[1]]()
    if os.environ.get("GC_W0"):                      # override the base point w0
        w0 = os.environ["GC_W0"]
        type(fam).w0 = property(lambda self: mp.mpf(w0))
    Y0S = [mp.mpf(x) for x in os.environ.get("GC_Y0", "1.5").split(",")]
    Y0 = Y0S[0]
    lams = sys.argv[2:] or ["0.5", "0.7", "0.8", "0.9", "0.95"]
    mp.mp.dps = 60
    par = Parab(fam)
    a = par.phi_att(fam.w0 - fam.wstar)
    YB = [mp.mpf(x) for x in os.environ.get("GC_YB", "1.0,1.5").split(",")]
    Bs = {Y: par.horn_inverse(Y) for Y in YB}
    B = Bs[YB[-1]]
    print(f"== {fam.name}   germ a2={mp.nstr(par.a2, 8)}  A={mp.nstr(par.al.A, 8)}  "
          f"rho={mp.nstr(par.al.rho, 10)}  a=Phi_att(u0)={mp.nstr(a, 14)}")
    print(f"   B_0={mp.nstr(B[0], 6)}  B_-1={mp.nstr(B[-1], 3)}   (Y-stability |dB1|="
          f"{mp.nstr(abs(Bs[YB[0]][1] - B[1]), 3)})")
    lim = {n: B[n] * mp.exp(2j * mp.pi * n * a) for n in (1, 2, 3)}
    k2i, k3i = B[2] / B[1] ** 2, B[3] / B[1] ** 3
    print(f"   |B1|={mp.nstr(abs(B[1]), 14)}  lim arg tau1={mp.nstr(mp.arg(lim[1]), 12)}")
    print(f"   B2/B1^2={mp.nstr(k2i, 12)}   B3/B1^3={mp.nstr(k3i, 10)}")
    for ls in lams:
        lam = mp.mpf(ls)
        H = Hyper(fam, lam)
        try:
            f = H.modes(-H.h2 / 2 + Y0)
        except RuntimeError as exc:
            print(f"lam={ls:<5} sampling line Y0={mp.nstr(Y0, 3)} leaves the basin of p ({exc})", flush=True)
            continue
        if len(Y0S) > 1:
            g = H.modes(-H.h2 / 2 + Y0S[1])
            print(f"   line check Y0={mp.nstr(Y0S[1], 3)}: |dt1/t1|={mp.nstr(abs(g[1] / f[1] - 1), 3)} "
                  f"|dt2/t2|={mp.nstr(abs(g[2] / f[2] - 1), 3)}")
        tau = {n: f[n] * mp.exp(-2j * mp.pi * n * f[0]) for n in (1, 2, 3)}
        p = abs(mp.log(H.lam)) * mp.log(H.lam2)
        r1 = mp.log(tau[1] / lim[1])
        k2, k3 = f[2] / f[1] ** 2, f[3] / f[1] ** 3
        print(f"lam={ls:<5} lam2={mp.nstr(H.lam2, 8):<11} Lambda={mp.nstr(H.Lam, 4):<10} "
              f"|t_-1|={mp.nstr(abs(f[-1]), 3):<9} Im t0-h/2={mp.nstr(mp.im(f[0]) - H.h / 2, 3)}")
        print(f"   |tau1|/|B1|={mp.nstr(abs(tau[1]) / abs(B[1]), 12):<15} "
              f"arg tau1 - lim={mp.nstr(mp.arg(tau[1] / lim[1]), 6):<12} "
              f"log(tau1/lim)/p={mp.nstr(r1 / p, 10)}")
        print(f"   tau1={mp.nstr(tau[1], 20)}  tau2={mp.nstr(tau[2], 15)}  t2/t1^2={mp.nstr(k2, 15)}")
        print(f"   |k2-lim|={mp.nstr(abs(k2 - k2i), 4):<10} |k3-lim|={mp.nstr(abs(k3 - k3i), 4):<10} "
              f"|tau2/lim2-1|={mp.nstr(abs(tau[2] / lim[2] - 1), 4)}", flush=True)


if __name__ == "__main__":
    main()
