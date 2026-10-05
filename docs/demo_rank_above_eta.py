"""The tropical rank limit above eta: bases e^(1/e) < b < b_c5 = 1.6353...

Below eta every level of the ladder is regular and docs/demo_rank_limit.py
shows b[s]z -> min(1+z, b).  Above eta tetration has no real fixed point --
rank 4 is Kneser's solution -- but for b < b_c5 the tetration S_4 = sexp_b has
an attracting real fixed point p_5 > 1, so rank 5 is again a regular
(Koenigs) iteration, and from there on the ladder of docs/demo_rank_regular.py
climbs unchanged.  Nixon's chain stops at eta; this one does not.

Rank 5 needs the Taylor series of sexp_b at p_5.  It is closed-form from the
shipped Taylor table of sexp_b at 0 (radius 2, the singularity at -2):
    sexp_b(p + t) = b ** sexp_b(p - 1 + t),     0 < p - 1 < 1/2,
i.e. re-expand the table at p - 1 and exponentiate the series.

The prediction carried over from below eta, with a = (2-b)/(b-1):
    S_s(z) -> min(1+z, b),   S_s ~ softmin at temperature 1/|log lam_s|,
    s * lam_s**(b-1) -> a,   (b - S_s(b-1)) * |log lam_{s-1}| -> log 2.

Run:  PYTHONPATH=src python3 docs/demo_rank_above_eta.py --base 1.5 --top 32
"""

from __future__ import annotations

import argparse
import json
import sys
import time

import mpmath as mp

import kneser
from kneser.hp import _base_coeffs

sys.path.insert(0, "docs")
from demo_rank_regular import Level  # noqa: E402
from kneser._koenigs import inverse_schroeder, series_shift  # noqa: E402


def series_exp(c, K):
    """Coefficients of exp(sum c_k t^k) truncated at t^K (c[0] included)."""
    out = [mp.exp(c[0])] + [mp.mpf(0)] * K
    for n in range(1, K + 1):
        out[n] = mp.fsum(k * c[k] * out[n - k] for k in range(1, min(n, len(c) - 1) + 1)) / n
    return out


class KneserRank5(Level):
    """Rank 5 over Kneser tetration: regular iteration of sexp_b at p_5."""

    def __init__(self, b, K, digits):
        self.digits = digits
        self.coeffs = [mp.mpf(c) for c in _base_coeffs(mp.nstr(b, 20), digits)]
        super().__init__(b, None, K)
        self.s = 5

    def T(self, w):
        return kneser.hp.sexp(w, dps=self.digits, base=mp.nstr(self.b, 20))

    def Tinv(self, y):
        return kneser.hp.slog(y, dps=self.digits, base=mp.nstr(self.b, 20))

    def _tau(self):
        K = self.K
        shifted = series_shift(self.coeffs, self.p - 1, K)       # sexp(p-1+t)
        lb = mp.log(self.b)
        tau = series_exp([lb * c for c in shifted], K)            # b ** that
        tau[0] -= self.p
        tau[0] = mp.mpf(0)
        return tau


def run(b_str, top, K, digits):
    b = mp.mpf(b_str)
    beta = b - 1
    a = (2 - b) / (b - 1)
    print("=" * 76)
    print(f"base b = {b_str}  (eta = {mp.nstr(mp.exp(1/mp.e), 8)})   "
          f"table {digits} digits   a = (2-b)/(b-1) = {mp.nstr(a, 6)}")
    print("=" * 76)
    t0 = time.time()
    lev = KneserRank5(b, K, digits)
    levels = [lev]
    print(f"    rank  5  p = {mp.nstr(lev.p, 16)}  lam = {mp.nstr(lev.lam, 10)}  "
          f"[{time.time() - t0:.0f}s]", flush=True)
    while lev.s < top:
        lev = Level(b, lev, K)
        levels.append(lev)
        if lev.s % 8 == 0:
            print(f"    rank {lev.s:>2}  p = {mp.nstr(lev.p, 16)}  "
                  f"lam = {mp.nstr(lev.lam, 10)}  [{time.time() - t0:.0f}s]", flush=True)

    half = mp.mpf(1) / 2
    print("\n  self-checks (table accuracy limits these to ~10^-digits):")
    for L in levels[:3] + levels[-1:]:
        print(f"    s = {L.s:>2}  S(1) - b = {mp.nstr(L.S(1, extra=2) - b, 3):>10}   "
              f"walk-independence at 1/2: {mp.nstr(L.S(half) - L.S(half, extra=3), 3)}")
    r5 = levels[0]
    print(f"    rank 5 vs library tetration:  S_5(1/2) = {mp.nstr(r5.S(half), 15)}, "
          f"S_5(2) - sexp_b(b) = {mp.nstr(r5.S(2) - r5.T(b), 3)}")

    print("\n  the tropical picture")
    print(f"     {'s':>3}  {'max|S-min|':>11} {'at z':>5}  {'max|S-softmin|':>14}  "
          f"{'g_s L_(s-1)':>11}  {'s lam^(b-1)':>11}")
    zs = [mp.mpf(k) / 20 for k in range(-18, 41)]
    rows = []
    for prev, L in zip(levels, levels[1:]):
        La, Ls = abs(mp.log(prev.lam)), abs(mp.log(L.lam))
        e0, zat, e1 = mp.mpf(0), None, mp.mpf(0)
        for z in zs:
            v = L.S(z)
            d = abs(v - min(1 + z, b))
            if d > e0:
                e0, zat = d, z
            e1 = max(e1, abs(v + mp.log(mp.exp(-Ls * (1 + z)) + mp.exp(-Ls * b)) / Ls))
        gL = (b - L.S(beta)) * La
        sq = L.s * mp.power(L.lam, beta)
        rows.append({"s": L.s, "to_min": mp.nstr(e0, 4), "argmax": mp.nstr(zat, 3),
                     "to_softmin": mp.nstr(e1, 4), "gap_times_L": mp.nstr(gL, 6),
                     "s_q": mp.nstr(sq, 8), "p": mp.nstr(L.p, 15),
                     "lam": mp.nstr(L.lam, 15)})
        if L.s in (6, 8, 12, 16, 24, 32, 40, 48) or L.s == top:
            print(f"     {L.s:>3}  {mp.nstr(e0, 4):>11} {mp.nstr(zat, 3):>5}  "
                  f"{mp.nstr(e1, 4):>14}  {mp.nstr(gL, 6):>11}  {mp.nstr(sq, 7):>11}")
    print(f"  (predictions: max at z = b-1 = {mp.nstr(beta, 3)}, g L -> log 2 = 0.6931, "
          f"s lam^(b-1) -> {mp.nstr(a, 5)} + 1/log s + ...)")
    return {"base": b_str, "digits": digits, "rank5": {"p": mp.nstr(r5.p, 16),
            "lam": mp.nstr(r5.lam, 16), "S_half": mp.nstr(r5.S(half), 16)},
            "levels": rows}


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", default="1.5")
    ap.add_argument("--top", type=int, default=32)
    ap.add_argument("--terms", type=int, default=60)
    ap.add_argument("--digits", type=int, default=17,
                    help="tetration table digits (17 is built in ~90 s and cached)")
    ap.add_argument("--cfrac", type=float, default=1 / 3,
                    help="allowed |c| / radius when re-expanding the previous rank "
                         "(near b_c5 rank 5 is almost parabolic; raise with --terms)")
    ap.add_argument("--json", default=None)
    args = ap.parse_args(argv)
    mp.mp.dps = max(30, args.digits + 10)
    Level.C_FRAC = mp.mpf(args.cfrac)
    out = [run(b, args.top, args.terms, args.digits) for b in args.base.split(",")]
    if args.json:
        with open(args.json, "w") as fh:
            json.dump(out, fh, indent=1)
        print(f"\nwrote {args.json}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
