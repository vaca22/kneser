"""The rank-8 critical base b_c8: heptation built at hexation's REAL fixed point.

The repository's analytic ladder alternates (docs/hyperoperation-program-zh.md
sections 4.12-4.17): pentation is regular at sexp's real repelling point x*,
hexation H is a theta (Kneser-type) level at pentation's complex point z*_5,
and heptation is again regular -- at H's real repelling fixed point

    z_fix in (-4, -3),   H(z_fix) = z_fix,   mu = H'(z_fix) > 1   (base e: -3.807, 10.70).

Section 4.17(c) got stuck on H's Taylor series at z_fix: z_fix is far outside
the disc where H is a series, and the Cauchy circle through four backward
pen^{-1} steps jumped branches.  This file needs no circle around z_fix at all.
z_fix + 4 is inside the series disc, so

    G_4(t) = H(z_fix + 4 + t)                                 (series shift)
    G_k(t) = pen^{-1}(G_{k+1}(t)),   k = 3, 2, 1, 0           (series algebra)

where pen^{-1} at y = G_{k+1}(0) is the reversion of pen's Taylor series at the
REAL point x_k = G_k(0).  Pentation is single-valued and real-analytic on the
whole real line (range (x*, oo)), so those Taylor series come from small
circles around real points with no branch to track.  Then heptation is

    Hep(z) = z_fix + u(C mu^z),     Hep(0) = 1,

and b_c8 is the zero of m8(b) = min_{z >= 0} (Hep_b(z) - z), the base where
the rank-8 tower 1, b, Hep(b), ... stops converging.

Run:  PYTHONPATH=src python3 docs/demo_rank8_constant.py --check-e
      PYTHONPATH=src python3 docs/demo_rank8_constant.py 1.83 1.85
"""

from __future__ import annotations

import argparse
import json
import sys
import time

import mpmath as mp

from kneser._koenigs import Superfunction, series_eval, series_mul, series_shift

sys.path.insert(0, "docs")
from demo_rank7_constant import DPS, hexation                     # noqa: E402

KT = 24          # Taylor order at z_fix (hexation itself is a 24-term series)
RPEN = mp.mpf("0.2")
CAP = mp.mpf(6)  # pen of anything above this is a tower (see demo_rank7_constant)


def series_reversion(d, K):
    """s(w) with sum_{j>=1} d_j s^j = w, i.e. the inverse of d - d_0."""
    s = [mp.mpf(0), 1 / d[1]] + [mp.mpf(0)] * (K - 1)
    for _ in range(K):
        acc = [mp.mpf(0)] * (K + 1)
        power = list(s)
        for j in range(2, K + 1):
            power = series_mul(power, s, K)
            for k in range(K + 1):
                acc[k] += d[j] * power[k]
        new = [-(acc[k]) / d[1] for k in range(K + 1)]
        new[1] += 1 / d[1]
        s = new
    return s


def series_compose(r, a, K):
    """r(a(t)) with a(0) = 0."""
    out = [mp.mpf(0)] * (K + 1)
    for c in reversed(r[: K + 1]):
        out = series_mul(out, a, K)
        out[0] += c
    return out


class Ladder:
    """Real hexation and heptation at one base."""

    def __init__(self, base, verbose=False):
        t0 = time.time()
        self.base = base
        self.say = (lambda m: print(f"      [{time.time()-t0:6.1f}s] {m}", flush=True)) \
            if verbose else (lambda m: None)
        coeffs, pen_g, z5, anchor, E = hexation(base, verbose=verbose)
        self.coeffs, self.pen_g, self.E, self.anchor = coeffs, pen_g, E, anchor
        self.say(f"hexation built, anchor |H(1)-b| = {mp.nstr(anchor, 3)}")
        hi = mp.mpf(-3)                                         # H(-3) - (-3) = 1 > 0
        lo = hi - mp.mpf("0.05")
        while self.H(lo) - lo > 0:
            hi, lo = lo, lo - mp.mpf("0.05")
        for _ in range(30):                                     # H(lo) may be -inf
            mid = (lo + hi) / 2
            if self.H(mid) - mid > 0:
                hi = mid
            else:
                lo = mid
        self.zfix = mp.findroot(lambda z: self.H(z) - z, (lo + hi) / 2)
        self.say(f"z_fix = {mp.nstr(self.zfix, 16)}  "
                 f"|H-z| = {mp.nstr(abs(self.H(self.zfix) - self.zfix), 3)}")
        self.tau = self._taylor_at_zfix()
        self.mu = self.tau[1]
        self.say(f"mu = H'(z_fix) = {mp.nstr(self.mu, 14)}")
        self.Hep = Superfunction(self.zfix, self.tau, forward=self.H_fwd,
                                 inverse=self.Hinv)
        self.C_by_steps = {}
        for steps in (6, 7, 8):
            self.C_by_steps[steps] = self.Hep.normalize(target=mp.mpf(1), z0=0, steps=steps)
        self.say("C by normalize steps 6/7/8: "
                 + ", ".join(mp.nstr(c, 12) for c in self.C_by_steps.values()))

    # -- pentation on the real line ------------------------------------------
    def pen(self, x):
        return mp.re(self.pen_g(mp.mpf(x)))

    def pen_inv(self, y, guess=None):
        """Real pen^{-1}; pen maps R increasingly onto (x*, oo)."""
        y = mp.mpf(y)
        if y <= self.E.xs:
            return -mp.inf
        f = lambda v: self.pen(v) - y                          # noqa: E731
        hi = y - 1 if guess is None else mp.mpf(guess)
        while f(hi) < 0:
            hi += 1
        lo = hi - 1
        while f(lo) > 0:
            lo -= 1
        return mp.findroot(f, (lo, hi), solver="anderson")

    # -- hexation on the real line -------------------------------------------
    def H(self, z):
        z = mp.mpf(z)
        if z > 4 * CAP:                    # pen can return 10**(10**13); never int() that
            raise OverflowError("hexation would tower")
        k = int(mp.nint(z))
        v = series_eval(self.coeffs, z - k)
        for _ in range(max(k, 0)):
            if abs(v) > CAP:
                raise OverflowError("hexation would tower")
            v = self.pen(v)
        for _ in range(max(-k, 0)):
            v = self.pen_inv(v)
        return v

    def H_fwd(self, w):
        return self.H(mp.re(w))

    def Hinv(self, y):
        y = mp.re(y)
        guess = self.zfix + (y - self.zfix) / self.mu if hasattr(self, "mu") else y - 1
        return mp.findroot(lambda z: self.H(z) - y, guess)

    # -- Taylor series of H at z_fix, by series algebra ------------------------
    def _taylor_at_zfix(self):
        G = series_shift(self.coeffs, self.zfix + 4, KT)       # H(z_fix + 4 + t)
        for k in (3, 2, 1, 0):
            xk = self.H(self.zfix + k)
            d = [mp.re(c) for c in self.E.taylor(xk, RPEN, KT)]  # pen(x_k + s)
            self.say(f"  pen taylor at x_{k} = {mp.nstr(xk, 10)}: "
                     f"|pen(x_k) - G(0)| = {mp.nstr(abs(d[0] - G[0]), 3)}")
            R = series_reversion(d, KT)
            # pen^{-1}(d0 + w) = x_k + R(w),  with w = G(t) - d0 = A0 + A(t)
            A0, A = G[0] - d[0], [mp.mpf(0)] + list(G[1:])
            Rs = series_shift(R, A0, KT)
            G = series_compose(Rs, A, KT)
            G[0] += xk
        tau = list(G)
        tau[0] = mp.mpf(0)
        self.tau_residual = G[0] - self.zfix
        return tau

    # -- the tower margin -----------------------------------------------------
    def hep(self, z):
        try:
            return mp.re(self.Hep.value(mp.mpf(z)))
        except OverflowError:
            return mp.inf

    def trap(self, n=32):
        """How far Hep stays under the line 1+(b-1)z on [1, L], L=1/(2-b).

        Proposition D: if this violation is <= 0 and Hep is nondecreasing,
        the octation tower converges, so b <= b_c9.
        """
        b = mp.e if self.base == "e" else mp.mpf(self.base)
        if not (1 < b < 2):
            return None
        L = 1 / (2 - b)
        worst, at = mp.mpf(0), mp.mpf(1)
        for k in range(n + 1):
            z = 1 + (L - 1) * k / n
            try:
                v = self.hep(z)
            except OverflowError:
                return {"L": mp.nstr(L, 6), "violation": "overflow", "at": mp.nstr(z, 4)}
            d = v - (1 + (b - 1) * z)
            if d > worst:
                worst, at = d, z
        return {"L": mp.nstr(L, 6), "violation": mp.nstr(worst, 6), "at": mp.nstr(at, 4)}

    def m8(self, zmax=12, grid=16):
        best, vals = None, {}
        for j in range(grid):
            vals[j] = self.hep(mp.mpf(j) / grid)
        for k in range(zmax):
            for j in range(grid):
                if vals[j] == mp.inf:
                    continue
                d = vals[j] - (k + mp.mpf(j) / grid)
                if best is None or d < best[0]:
                    best = (d, k + mp.mpf(j) / grid)
            if all(v == mp.inf or v > CAP for v in vals.values()):
                break
            nv = {}
            for j in range(grid):
                try:
                    nv[j] = self.H(vals[j]) if vals[j] != mp.inf else mp.inf
                except OverflowError:
                    nv[j] = mp.inf
            vals = nv
        # refine: golden section on [z - h, z + h]
        h = mp.mpf(1) / grid
        lo, hi = max(best[1] - h, mp.mpf(0)), best[1] + h
        f = lambda z: self.hep(z) - z                         # noqa: E731
        for _ in range(30):
            a, c = lo + (hi - lo) * mp.mpf("0.382"), lo + (hi - lo) * mp.mpf("0.618")
            if f(a) < f(c):
                hi = c
            else:
                lo = a
        zc = (lo + hi) / 2
        return min(best[0], f(zc)), zc


def report(base, verbose):
    t0 = time.time()
    L = Ladder(base, verbose=verbose)
    out = {"base": base, "zfix": mp.nstr(L.zfix, 16), "mu": mp.nstr(L.mu, 14),
           "anchor": mp.nstr(L.anchor, 3), "tau_residual": mp.nstr(L.tau_residual, 3)}
    # self-checks: Hep(1) = b, Hep(2) = H(b), walk independence
    half = mp.mpf(1) / 2
    bval = mp.e if base == "e" else mp.mpf(base)
    out["Hep1_minus_b"] = mp.nstr(L.hep(1) - bval, 3)
    out["walk_indep_half"] = mp.nstr(mp.re(L.Hep.value(half) - L.Hep.value(half, extra=2)), 3)
    out["Hep_half"] = mp.nstr(L.hep(half), 12)
    if getattr(report, "trap", False):
        out["trap"] = L.trap()
    m, zc = L.m8()
    out["m8"], out["argmin"] = mp.nstr(m, 10), mp.nstr(zc, 8)
    out["seconds"] = round(time.time() - t0)
    print(json.dumps(out), flush=True)
    return out, m


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("bases", nargs="*")
    ap.add_argument("--check-e", action="store_true",
                    help="base e: compare z_fix, mu with section 4.17(b)")
    ap.add_argument("--secant", nargs=2, default=None, metavar=("B0", "B1"))
    ap.add_argument("--iters", type=int, default=4)
    ap.add_argument("--trap", action="store_true",
                    help="also test the Proposition D envelope, a lower bound for b_c9")
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--dps", type=int, default=DPS,
                    help="working precision; tetration table uses max(17, dps-5) digits")
    ap.add_argument("--json", default=None)
    args = ap.parse_args(argv)
    mp.mp.dps = args.dps
    report.trap = args.trap
    rows = []
    if args.check_e:
        r, _ = report("e", not args.quiet)
        print("  section 4.17(b):  z_fix = -3.80701079126504147   mu = 10.70204235269409")
        rows.append(r)
    for b in args.bases:
        rows.append(report(b, not args.quiet)[0])
    if args.secant:
        b0, b1 = (mp.mpf(x) for x in args.secant)
        r0, m0 = report(mp.nstr(b0, 15), not args.quiet)
        r1, m1 = report(mp.nstr(b1, 15), not args.quiet)
        rows += [r0, r1]
        for _ in range(args.iters):
            b2 = b1 - m1 * (b1 - b0) / (m1 - m0)
            r2, m2 = report(mp.nstr(b2, 15), not args.quiet)
            rows.append(r2)
            b0, m0, b1, m1 = b1, m1, b2, m2
            print(f"  secant: b = {mp.nstr(b2, 12)}  m8 = {mp.nstr(m2, 6)}", flush=True)
    if args.json:
        with open(args.json, "w") as fh:
            json.dump(rows, fh, indent=1)
    return 0


if __name__ == "__main__":
    sys.exit(main())
