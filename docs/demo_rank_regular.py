"""Second anchor table: the regular hyperoperation ladder at a base 1 < b < eta.

`essay-rank-1000-zh.md` proposed, as the next rank-continuation candidate to
screen, James Nixon's bounded analytic hyper-operators (arXiv:2106.03935),
defined only for 1 < alpha < e^(1/e).  This script does the screen and then
pushes the ladder far enough up to ask what happens as the rank s -> infinity.

A.  Nixon's chain IS the regular chain.  His Theorem 3.1 writes the iterate as
    Psi^{-1}(lam^z Psi(xi)) at the attracting fixed point and the fractional
    derivative d^{z-1}/dw^{z-1} sum phi^{n+1}(1) w^n/n! is only a second
    representation of it (Ramanujan's master theorem).  We check the identity
    numerically at rank 4 using nothing but the integer tower values
    phi^n(1): the brute-force Mellin integral reproduces the Koenigs value.
    So his rank index n stays discrete: his chain is a source of anchors, not
    a rank interpolation.

B.  The ladder.  In the attracting regime every level is
        S_s(z) = p_s + U_s(C_s lam_s**z),       S_s(z+1) = S_{s-1}(S_s(z)),
    with p_s the attracting fixed point of S_{s-1}, lam_s = S_{s-1}'(p_s) and
    S_s(0) = 1.  Because S_{s-1} is itself a power series in lam_{s-1}**z, the
    Taylor series of T_s = S_{s-1} at p_s is closed-form:
        T_s(p_s + t) = p_{s-1} + sum_j u_j c**j exp(j t log lam_{s-1}),
        c = C_{s-1} lam_{s-1}**p_s,
    so no Cauchy integral and no theta iteration is needed.  That is why this
    side of the ladder is cheap and can be climbed to high rank.

C.  The rank limit.  The fixed points p_s, multipliers lam_s and anchors
    b[s]1/2 converge as s -> infinity, and the convergence rate is measured.
    A limit S_inf would be a fixed point of the successor operator Sigma
    (S_inf(z+1) = S_inf(S_inf(z))), the object whose linearisation would give a
    regular iteration IN THE RANK.  This script only measures; see the
    write-up in essay-rank-1000-zh.md for what is and is not claimed.

Run:  PYTHONPATH=src python3 docs/demo_rank_regular.py
      PYTHONPATH=src python3 docs/demo_rank_regular.py --base 1.3 --top 14 --json out.json
"""

from __future__ import annotations

import argparse
import json
import sys
import time

import mpmath as mp

from kneser._koenigs import inverse_schroeder, series_eval, tau_of_exponential


class Level:
    """S_s for s >= 4 at base b, regular iteration at the attracting point."""

    C_FRAC = mp.mpf(1) / 3      # re-expansion point |c| must stay below C_FRAC * radius

    def __init__(self, b, prev, K):
        self.b = b
        self.prev = prev                      # None for s = 4 (T = b**w)
        self.s = 4 if prev is None else prev.s + 1
        self.K = K
        self.p = self._fixed_point()
        self.tau = self._tau()
        self.lam = self.tau[1]
        if not 0 < self.lam < 1:
            raise ValueError(f"rank {self.s}: multiplier {self.lam} not in (0,1)")
        self.loglam = mp.log(self.lam)
        self.u = inverse_schroeder(self.tau)
        ratios = [abs(self.u[k + 1] / self.u[k]) for k in range(K // 2, K)
                  if self.u[k] != 0]
        self.radius = 1 / max(ratios)
        self.smax = self.radius / 6
        self.C = mp.mpf(1)
        self.C = self.sigma(mp.mpf(1))

    # -- the map T_s = S_{s-1} -------------------------------------------
    def T(self, w):
        return mp.power(self.b, w) if self.prev is None else self.prev.S(w)

    def Tinv(self, y):
        if self.prev is None:
            return mp.log(y) / mp.log(self.b)
        return self.prev.Sinv(y)

    def _fixed_point(self):
        x = mp.mpf(1)
        for _ in range(400):
            x_new = self.T(x)
            if abs(x_new - x) < mp.mpf(10) ** (-mp.mp.dps // 3):
                x = x_new
                break
            x = x_new
        return mp.findroot(lambda y: self.T(y) - y, x)

    def _tau(self):
        if self.prev is None:
            return tau_of_exponential(self.b, self.p, self.K)
        q = self.prev
        c = q.C * mp.power(q.lam, self.p)
        if abs(c) > q.radius * self.C_FRAC:
            raise ValueError(f"rank {self.s}: c = {c} too close to the radius "
                             f"{q.radius} of rank {q.s}")
        terms = [q.u[j] * mp.power(c, j) for j in range(len(q.u))]
        tau = [q.p + mp.fsum(terms) - self.p]
        fact = mp.mpf(1)
        for k in range(1, self.K + 1):
            fact *= k
            tau.append(mp.fsum(terms[j] * mp.power(j * q.loglam, k)
                               for j in range(1, len(q.u))) / fact)
        tau[0] = mp.mpf(0)                    # p is a fixed point to working precision
        return tau

    # -- the superfunction and its inverse -------------------------------
    def S(self, z, extra=0):
        n = 0
        arg = self.C * mp.power(self.lam, z)
        while abs(arg) > self.smax:
            arg *= self.lam
            n += 1
        for _ in range(extra):
            arg *= self.lam
            n += 1
        w = self.p + series_eval(self.u, arg)
        for _ in range(n):
            w = self.Tinv(w)
        return w

    def sigma(self, y):
        """Schroeder function, sigma(T(y)) = lam sigma(y), sigma'(p) = 1."""
        m = 0
        while abs(y - self.p) > self.smax / 2:
            y = self.T(y)
            m += 1
            if m > 2000:
                raise ValueError(f"rank {self.s}: {y} not in the basin")
        t = y - self.p
        s = t
        du = [k * self.u[k] for k in range(1, len(self.u))]
        for _ in range(100):
            f = series_eval(self.u, s) - t
            step = f / series_eval(du, s)
            s -= step
            if abs(step) <= mp.mpf(10) ** (-mp.mp.dps + 3) * max(1, abs(s)):
                break
        return s / mp.power(self.lam, m)

    def Sinv(self, y):
        return mp.log(self.sigma(y) / self.C) / self.loglam


def build(b, top, K):
    levels, t0 = [], time.time()
    prev = None
    for _ in range(4, top + 1):
        lev = Level(b, prev, K)
        levels.append(lev)
        prev = lev
        print(f"    built rank {lev.s:>2}  p = {mp.nstr(lev.p, 20)}  "
              f"lam = {mp.nstr(lev.lam, 12)}  [{time.time() - t0:.1f}s]",
              flush=True)
    return levels


def nixon_mellin(b, z, tmax, dps):
    """Nixon's representation at rank 4, from integer towers only.

        b^^z = (1/Gamma(1-z)) int_0^inf t^{-z} theta(-t) dt,
        theta(w) = sum_n b^^(n+1) w^n / n!,      0 < z < 1.

    theta(-t) is an alternating sum of size e^t, hence the working precision.
    """
    with mp.workdps(dps):
        towers, w = [], mp.mpf(1)
        nmax = int(mp.e * tmax) + 60
        for _ in range(nmax + 1):
            w = mp.power(b, w)
            towers.append(w)

        def theta_neg(t):
            acc, term = mp.mpf(0), mp.mpf(1)
            for n in range(nmax + 1):
                acc += towers[n] * term
                term *= -t / (n + 1)
            return acc

        # t = v**(1/(1-z)) removes the t^{-z} endpoint singularity
        e = 1 / (1 - z)
        f = lambda v: theta_neg(mp.power(v, e)) * e
        vmax = mp.power(tmax, 1 - z)
        pts = [mp.mpf(0)] + [vmax * mp.mpf(k) / 12 for k in range(1, 13)]
        val = mp.quad(f, pts) / mp.gamma(1 - z)
        tail = towers[-1] * mp.gammainc(1 - z, tmax) / mp.gamma(1 - z)
        return val, tail


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", default="1.3")
    ap.add_argument("--top", type=int, default=14)
    ap.add_argument("--dps", type=int, default=40)
    ap.add_argument("--terms", type=int, default=60)
    ap.add_argument("--json", default=None)
    args = ap.parse_args(argv)
    mp.mp.dps = args.dps
    b = mp.mpf(args.base)
    half = mp.mpf(1) / 2
    eta = mp.exp(1 / mp.e)
    if not 1 < b < eta:
        raise SystemExit("base must satisfy 1 < b < e^(1/e)")

    print("=" * 72)
    print(f"B.  the regular ladder at base b = {args.base}  "
          f"(dps {args.dps}, {args.terms} Koenigs terms)")
    print("=" * 72)
    levels = build(b, args.top, args.terms)

    print("\n  checks.  S(z+1) = S_{s-1}(S(z)) holds by fiat wherever S walks with")
    print("  the inverse map, and S(-1) = 0 follows from C = sigma(1); neither is")
    print("  a test.  The tests are the functional equation where BOTH sides are")
    print("  summed series (no walking), and independence of the walk length:")
    print(f"    {'s':>2}  {'FE, series only':>15}  {'S(2) - S_(s-1)(b)':>17}"
          f"  {'walk +3 at 1/2':>14}  {'walk +3 at -1/2':>15}")
    checks = {}
    for lev in levels:
        z = -half                             # first z whose series is summed directly
        while abs(lev.C * mp.power(lev.lam, z)) > lev.smax:
            z += mp.mpf(1) / 8
        rfe = abs(lev.S(z + 1) - lev.T(lev.S(z)))
        r2 = abs(lev.S(2, extra=4) - lev.T(b))
        rx = abs(lev.S(half) - lev.S(half, extra=3))
        rxm = abs(lev.S(-half) - lev.S(-half, extra=3))
        worst = max(rfe, r2, rx, rxm)
        checks[lev.s] = mp.nstr(worst, 3)
        print(f"    {lev.s:>2}  {mp.nstr(rfe, 2):>15}  {mp.nstr(r2, 2):>17}  "
              f"{mp.nstr(rx, 2):>14}  {mp.nstr(rxm, 2):>15}")

    rows = [(1, b + half), (2, b * half), (3, mp.power(b, half))]
    rows += [(lev.s, lev.S(half)) for lev in levels]
    print(f"\n  anchors  A(s) = {args.base}[s]1/2")
    print(f"    {'s':>2}  {'A(s)':<28}  {'A(s)-A(s-1)':>14}  {'ratio':>9}")
    prev_d = None
    for i, (s, v) in enumerate(rows):
        d = v - rows[i - 1][1] if i else None
        ratio = d / prev_d if (d is not None and prev_d) else None
        print(f"    {s:>2}  {mp.nstr(v, 22):<28}  "
              f"{(mp.nstr(d, 6) if d is not None else ''):>14}  "
              f"{(mp.nstr(ratio, 6) if ratio is not None else ''):>9}")
        prev_d = d

    print("\n" + "=" * 72)
    print("C.  does the ladder converge as s -> infinity?")
    print("=" * 72)
    print(f"    {'s':>2}  {'p_s':<24} {'dp ratio':>9}   {'lam_s':<16} {'dlam ratio':>10}")
    for i, lev in enumerate(levels):
        rp = rl = ""
        if i >= 2:
            dp0 = levels[i - 1].p - levels[i - 2].p
            dp1 = lev.p - levels[i - 1].p
            dl0 = levels[i - 1].lam - levels[i - 2].lam
            dl1 = lev.lam - levels[i - 1].lam
            rp = mp.nstr(dp1 / dp0, 6) if dp0 else ""
            rl = mp.nstr(dl1 / dl0, 6) if dl0 else ""
        print(f"    {lev.s:>2}  {mp.nstr(lev.p, 20):<24} {rp:>9}   "
              f"{mp.nstr(lev.lam, 12):<16} {rl:>10}")

    print("\n  local power-law exponents  x_s ~ s^(-k):  k_s = log(x_{s-1}/x_s) / log(s/(s-1))")
    print(f"    {'s':>2}  {'k for p_s - b':>14}  {'k for lam_s':>12}  {'k for A(s)-A(s-1)':>18}")
    anch = dict(rows)
    expo = {}
    for i in range(1, len(levels)):
        s = levels[i].s
        if s < 8:
            continue
        ls = mp.log(mp.mpf(s) / (s - 1))
        kp = mp.log((levels[i - 1].p - b) / (levels[i].p - b)) / ls
        kl = mp.log(levels[i - 1].lam / levels[i].lam) / ls
        ka = mp.log((anch[s - 1] - anch[s - 2]) / (anch[s] - anch[s - 1])) / ls
        expo[s] = (kp, kl, ka)
        print(f"    {s:>2}  {mp.nstr(kp, 6):>14}  {mp.nstr(kl, 6):>12}  {mp.nstr(ka, 6):>18}")
    print("  A geometric approach (|x_s/x_{s-1}| -> r < 1) would make k_s grow")
    print("  like s; here k_s settles, so the approach is ALGEBRAIC.")

    top = levels[-1]
    print(f"\n  shape of the top level S_{top.s}(z): heading for the kink min(1+z, b),")
    print("  see docs/demo_rank_limit.py")
    shape = {}
    for zs in ("-1", "-0.5", "-0.1", "0", "0.1", "0.2", "0.3", "0.5", "0.9", "1", "1.5", "3"):
        v = top.S(mp.mpf(zs))
        shape[zs] = mp.nstr(v, 12)
        print(f"    S_{top.s}({zs:>4}) = {mp.nstr(v, 15)}")
    print(f"  (b = {args.base}, p_{top.s} - b = {mp.nstr(top.p - b, 4)})")

    print("\n" + "=" * 72)
    print("A.  Nixon's fractional-calculus formula vs. the Koenigs value, rank 4")
    print("=" * 72)
    print("  theta(-t) = sum_m u_m (C lam^m) e^{-lam^m t} + ..., so the integrand")
    print("  carries modes decaying only like e^{-lam^m t}: a cut at t = T misses")
    print("  roughly the modes with lam^m T < 1, and the gap must shrink as T grows.")
    kv = levels[0].S(half)
    print(f"    Koenigs S_4(1/2)            = {mp.nstr(kv, 22)}")
    nixon = []
    for tmax in (20, 60, 180):
        nix, _tail = nixon_mellin(b, half, tmax, dps=int(tmax * 0.45) + args.dps + 10)
        nixon.append((tmax, nix, abs(nix - kv)))
        print(f"    Mellin, towers only, t<={tmax:<4}= {mp.nstr(nix, 22)}"
              f"   gap {mp.nstr(abs(nix - kv), 3)}")
    print("  The gap falls with T and the integral uses ONLY the integer towers")
    print("  b, b^b, ...: Nixon's chain is the Koenigs chain (his Thm 3.1).")

    if args.json:
        payload = {
            "base": args.base,
            "anchor_point": {"a": args.base, "b": "1/2"},
            "construction": "regular (Koenigs) iteration at the attracting "
                            "fixed point of each level = Nixon's bounded chain",
            "anchors": [{"s": s, "value": mp.nstr(v, 25)} for s, v in rows],
            "fixed_points": [{"s": l.s, "p": mp.nstr(l.p, 25),
                              "lam": mp.nstr(l.lam, 25)} for l in levels],
            "check_worst_residual": checks,
            "local_exponents": {s: {"p_minus_b": mp.nstr(k[0], 5),
                                    "lam": mp.nstr(k[1], 5),
                                    "anchor_step": mp.nstr(k[2], 5)}
                                for s, k in expo.items()},
            "top_level_shape": {"s": top.s, "values": shape},
            "nixon_mellin_rank4": {"koenigs": mp.nstr(kv, 25),
                                   "cuts": [{"tmax": t, "value": mp.nstr(v, 25),
                                             "gap": mp.nstr(g, 3)}
                                            for t, v, g in nixon]},
        }
        with open(args.json, "w") as fh:
            json.dump(payload, fh, indent=2)
        print(f"\nwrote {args.json}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
