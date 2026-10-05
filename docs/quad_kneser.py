"""Kneser-type solution of F(z+1) = F(z)^2 + c: the two-fixed-point construction.

Port of kneser/_cbuild.py (theta iteration of Kouznetsov/Paulsen type) from
w -> b^w to the quadratic family f_c(w) = w^2 + c.  This is the test of
Theorem F of the separation paper on a non-exponential family
(general-statements-zh.md section 6):

    c > 1/4 real    two complex-conjugate repelling fixed points; the real axis
                    escapes.  Kneser situation (tetration with b > eta).
    main cardioid   one attracting fixed point (Shell--Thron region analogue);
                    cusp c = 1/4 <-> b = eta.

Representations (Theorem W1(2) orientation: Im c > 0 => arg lambda_p > 0):
    upper   F(z) = superf_up(z + theta_up(z)),   theta_up 1-periodic, modes m >= 0
    lower   F(z) = superf_dn(z + theta_dn(z)),   theta_dn 1-periodic, modes m <= 0
    band    F(z+1) = f(F(z))  from the current Taylor series at 0.

Normalisation F(-3) = 0, i.e. F(0) = f^3(0): -3 is the square-root branch point
(F = 0 is the critical point), the analogue of sexp(-2) = -inf.  It is
continuous in c across 1/4. No global lower bound for the Taylor radius is
proved here. This numerical iteration is not defined on the neutral arc:
it rejects |lambda| near 1, and at roots of unity its Schroeder recurrence
has genuine resonant obstructions, not merely a precision problem.

Usage: python3 quad_kneser.py c_re [c_im] [digits]
"""
from __future__ import annotations

import math
import sys
import time

import mpmath as mp

_BIG = mp.mpf("1e60")
_U_TERMS = 80


def fixed_points(c):
    r = mp.sqrt(mp.mpf(1) / 4 - c)
    out = []
    for L in (mp.mpf(1) / 2 + r, mp.mpf(1) / 2 - r):
        out.append((L, 2 * L))
    up = [x for x in out if mp.arg(x[1]) > 0]
    dn = [x for x in out if mp.arg(x[1]) < 0]
    if not up or not dn:
        raise ValueError("need one fixed point with arg lambda > 0 and one with < 0 (c not real <= 1/4)")
    return up[0], dn[0]


def schroeder_inverse(L, lam, K=_U_TERMS):
    """u(s) = sum u_k s^k with f(L + u(s)) = L + u(lam s):  2L u + u^2 = u(lam s)."""
    u = [mp.mpc(0), mp.mpc(1)]
    for k in range(2, K + 1):
        u.append(sum(u[i] * u[k - i] for i in range(1, k)) / (lam**k - lam))
    return u


class Side:
    """superf / isuperf for one fixed point of f(w) = w^2 + c."""

    def __init__(self, c, L, lam, dps, radius=mp.mpf(2)):
        self.c, self.L, self.lam = c, L, lam
        self.logl = mp.log(lam)
        self.period = 2j * mp.pi / self.logl
        self.u = schroeder_inverse(L, lam)
        self.attr = abs(lam) < 1
        ratio = max(abs(self.u[k + 1] / self.u[k]) for k in range(_U_TERMS // 2, _U_TERMS))
        self.smax = min(mp.mpf("0.05"), 1 / (8 * ratio))
        self.eps = mp.mpf(10) ** (-(dps + 2))
        lr = abs(mp.log(abs(lam)))
        # forward depth (repelling) / backward depth (attracting) for |z| <= radius
        self.depth = int(math.ceil(float((mp.log(1 / self.smax) + radius * lr + abs(mp.im(self.logl)) * radius) / lr))) + 4

    def useries(self, s):
        r = mp.mpc(0)
        for a in reversed(self.u[1:]):
            r = (r + a) * s
        return r

    def duseries(self, s):
        r = mp.mpc(0)
        for k in range(len(self.u) - 1, 0, -1):
            r = r * s + k * self.u[k]
        return r

    def inv_u(self, w):
        s = w
        for _ in range(100):
            step = (self.useries(s) - w) / self.duseries(s)
            s -= step
            if abs(step) < self.eps * max(1, abs(s)):
                break
        return s

    def f(self, w):
        if abs(w) > _BIG:
            raise OverflowError("orbit overflow")
        return w * w + self.c

    def finv(self, w, target):
        r = mp.sqrt(w - self.c)
        return r if abs(r - target) <= abs(-r - target) else -r

    # ---- regular superfunction and its inverse (Abel coordinate) ----
    def superf(self, z, prev=None):
        if not self.attr:                     # forward iteration from near L
            w = self.L + self.useries(mp.exp((z - self.depth) * self.logl))
            for _ in range(self.depth):
                w = self.f(w)
            return w, None
        s = mp.exp((z + self.depth) * self.logl)  # backward iteration, branch continued
        extra = 0
        while abs(s) > self.smax:
            s *= self.lam
            extra += 1
        w = self.L + self.useries(s)
        for _ in range(extra):
            w = self.finv(w, self.L)
        chain = []
        for i in range(self.depth):
            w = self.finv(w, prev[i] if prev is not None else self.L)
            chain.append(w)
        return w, chain

    def isuperf(self, w, prev=None):
        if self.attr:                          # forward to L, branch-free
            m = 0
            while abs(w - self.L) > self.smax / 4:
                w = self.f(w)
                m += 1
                if m > 200000:
                    raise ValueError("isuperf: no convergence to the attracting point")
            return mp.log(self.inv_u(w - self.L)) / self.logl - m, None
        chain = []
        i = 0
        while i < self.depth or abs(w - self.L) > self.smax / 4:
            w = self.finv(w, prev[i] if prev is not None and i < len(prev) else self.L)
            chain.append(w)
            i += 1
            if i > 2000:
                raise ValueError("isuperf: backward chain did not reach the fixed point")
        return mp.log(self.inv_u(w - self.L)) / self.logl + i, chain

    def unwrap(self, theta):
        out = [theta[0]]
        for th in theta[1:]:
            k = int(mp.nint(mp.re((th - out[-1]) / self.period)))
            out.append(th - k * self.period)
        return out


def build(c, digits=20, idelta="0.1", n_loops=None, seed=None, verbose=True, max_loops_bad=8, kcrit=3, nt=None):
    dps = 2 * digits + 20
    with mp.workdps(dps):
        c = mp.mpc(c)
        (Lu, lu), (Ld, ld) = fixed_points(c)
        for lam, side in ((lu, "up"), (ld, "dn")):
            if abs(abs(lam) - 1) < 0.02:
                raise ValueError(f"|lambda_{side}| = {float(abs(lam)):.4f} too close to 1")
        up, dn = Side(c, Lu, lu, dps), Side(c, Ld, ld, dps)
        W0 = mp.mpc(0)                               # F(0) = f^kcrit(0), F(-kcrit) = 0 (default 3)
        for _ in range(kcrit):
            W0 = W0 * W0 + c
        nt = nt or max(48, 4 * digits)
        delta = mp.mpf(idelta)
        n_modes = int(math.ceil(digits * math.log(10) / (2 * math.pi * float(delta)))) + 8
        nf = 2 * n_modes + 20
        n_circ = max(4 * nt, 256)
        n_loops = n_loops or 3 * digits + 30
        log = (lambda *a: print(*a, flush=True)) if verbose else (lambda *a: None)
        log(f"[quad_kneser] c={mp.nstr(c, 10)} up: L={mp.nstr(Lu, 8)} |lam|={float(abs(lu)):.4f} "
            f"arg={float(mp.arg(lu)):.4f} {'attr' if up.attr else 'rep'} depth={up.depth}; "
            f"dn: L={mp.nstr(Ld, 8)} |lam|={float(abs(ld)):.4f} {'attr' if dn.attr else 'rep'} depth={dn.depth}; "
            f"dps={dps} nt={nt} modes={n_modes}")
        if seed is None:
            coeffs = [mp.mpc(0)] * nt
            coeffs[0] = W0
            coeffs[1] = W0 - (c * c + c)              # F(0) - F(-1)
        else:
            coeffs = [mp.mpc(x) for x in seed][:nt] + [mp.mpc(0)] * max(0, nt - len(seed))
            coeffs[0] = W0

        def series(z):
            r = mp.mpc(0)
            for a in reversed(coeffs):
                r = r * z + a
            return r

        def residual():
            return abs(series(mp.mpf("0.5")) - up.f(series(mp.mpf("-0.5"))))

        ts = [mp.mpf(j) / nf - mp.mpf("0.5") for j in range(nf)]
        circle = [mp.exp(2j * mp.pi * mp.mpf(k) / n_circ) for k in range(n_circ)]

        def line(side, sign):
            out, prev = [], None
            for t in ts:
                z = t + sign * 1j * delta
                v, prev = side.isuperf(series(z), prev)
                out.append(v - z)
            return side.unwrap(out)

        def modes(theta, sign):
            # theta(t + i sign delta) = sum_m a_m e^{2 pi i sign m t}
            return [sum(theta[j] * mp.exp(-2j * mp.pi * sign * m * ts[j]) for j in range(nf)) / nf
                    for m in range(n_modes)]

        def ev(a, w):
            r, p = mp.mpc(0), mp.mpc(1)
            for x in a:
                r += x * p
                p *= w
            return r

        t0 = time.time()
        res = [residual()]
        log(f"  seed residual {mp.nstr(res[0], 4)}")
        target = mp.mpf(10) ** (-(digits + 1))
        fa_u = fa_d = None
        for loop in range(n_loops):
            fa_u = modes(line(up, +1), +1)
            fa_d = modes(line(dn, -1), -1)
            vals, cu, cd = [], None, None
            for cz in circle:
                y = mp.im(cz)
                if y >= delta:
                    th = ev(fa_u, mp.exp(2j * mp.pi * (cz - 1j * delta)))
                    v, cu = up.superf(cz + th, cu)
                elif y <= -delta:
                    th = ev(fa_d, mp.exp(-2j * mp.pi * (cz + 1j * delta)))
                    v, cd = dn.superf(cz + th, cd)
                elif mp.re(cz) > 0:
                    v = up.f(series(cz - 1))
                else:
                    v = up.finv(series(cz + 1), series(cz))
                vals.append(v)
            new = [sum(vals[j] * circle[j] ** (-k) for j in range(n_circ)) / n_circ for k in range(nt)]
            new[0] = W0
            coeffs = new
            res.append(residual())
            if loop % 5 == 0 or res[-1] < target:
                log(f"  loop {loop:3d}: residual {mp.nstr(res[-1], 4)}  [{time.time() - t0:.0f}s]")
            if res[-1] < target:
                break
            if loop >= max_loops_bad and res[-1] > 10 * min(res):
                raise ValueError("theta iteration diverging")
        return dict(c=c, coeffs=coeffs, residuals=res, fa_up=fa_u, fa_dn=fa_d, delta=delta,
                    up=up, dn=dn, W0=W0, dps=dps)


if __name__ == "__main__":
    cre = sys.argv[1]
    cim = sys.argv[2] if len(sys.argv) > 2 else "0"
    digits = int(sys.argv[3]) if len(sys.argv) > 3 else 20
    with mp.workdps(60):
        r = build(mp.mpc(cre, cim), digits)
        co = r["coeffs"]
        print("F(0..3) coeffs:", [mp.nstr(x, 12) for x in co[:4]])
        s = lambda z: sum(a * z**k for k, a in enumerate(co))  # noqa: E731
        print("F(0.5) =", mp.nstr(s(mp.mpf("0.5")), 15), "  F(-0.5) =", mp.nstr(s(mp.mpf("-0.5")), 15))
        print("F(0.3i) =", mp.nstr(s(0.3j), 12), "  F(-0.3i) =", mp.nstr(s(-0.3j), 12))
