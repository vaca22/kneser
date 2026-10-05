"""The rounding of the kink has a universal slope: a hyperbolic tangent.

The softmin of the two lines 1+z and b,
    S(z) = b - (1/L) log(1 + exp(L (b-1-z))),
has derivative
    S'(z) = 1 / (1 + exp(L (z - (b-1)))) = (1/2) (1 - tanh(L (z-(b-1))/2)).
So at the kink, for every base and every temperature,
    S'(b-1) = 1/2,    S''(b-1) = -L/4,
and the graph is symmetric in the deficits:
    b - S((b-1)+t) = (b-t) - S((b-1)-t).

Run:  PYTHONPATH=src python3 docs/demo_kink_slope.py --bases 1.2,1.3,1.4 --top 20
"""

from __future__ import annotations

import argparse
import json
import sys

import mpmath as mp

sys.path.insert(0, "docs")
from demo_rank_regular import Level  # noqa: E402


def derivs(f, z, h):
    a, b, c, d = f(z - 2 * h), f(z - h), f(z + h), f(z + 2 * h)
    fp = (-d + 8 * c - 8 * b + a) / (12 * h)         # O(h^4)
    fpp = (-d + 16 * c - 30 * f(z) + 16 * b - a) / (12 * h * h)
    return fp, fpp


def profile(lev, b):
    beta = b - 1
    L = abs(mp.log(lev.lam))
    h = mp.mpf(10) ** (-8)
    fp, fpp = derivs(lev.S, beta, h)
    # reflection at a few temperatures of the previous level
    refl = []
    for t_over_L in ("0.5", "1", "2"):
        t = mp.mpf(t_over_L) / L
        if t >= beta:
            continue
        left = b - lev.S(beta + t)
        right = (b - t) - lev.S(beta - t)
        refl.append(mp.nstr(L * (left - right), 4))
    # slope profile against tanh, coordinate u = L_s * (z - beta)
    us = ["-2", "-1", "0", "1", "2"]
    slope_err = []
    for u in us:
        z = beta + mp.mpf(u) / L
        fp_z, _ = derivs(lev.S, z, h)
        pred = 1 / (1 + mp.exp(mp.mpf(u)))
        slope_err.append(mp.nstr(fp_z - pred, 4))
    return {
        "s": lev.s,
        "slope": mp.nstr(fp, 8),
        "half_gap_times_L": mp.nstr((mp.mpf("1/2") - fp) * L, 5),
        "curv_vs_prev": mp.nstr(-4 * fpp / L, 6),
        "curv_vs_self": mp.nstr(-4 * fpp / L, 6),
        "reflection": refl,
        "slope_err": slope_err,
    }


def run(b_str, top, K):
    b = mp.mpf(b_str)
    print("=" * 78)
    print(f"base {b_str}   kink slope should -> 1/2,   -4 S''(kink)/L -> 1")
    print("    s     slope(b-1)   (1/2-slope)*L   -4 S''/L    reflection, then slope error")
    print("                              slope error at u = -2,-1,0,1,2")
    prev, rows = None, []
    for _ in range(4, top + 1):
        lev = Level(b, prev, K)
        if prev is not None and lev.s in (6, 8, 12, 16, 20, 24, 32) or lev.s == top:
            row = profile(lev, b)
            rows.append(row)
            print(f"  {lev.s:>3}  {row['slope']:>12}  {row['half_gap_times_L']:>8}  "
                  f"{row['curv_vs_prev']:>8}  {row['reflection']}  {row['slope_err']}",
                  flush=True)
        prev = lev
    return {"base": b_str, "rows": rows}


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--bases", default="1.3")
    ap.add_argument("--top", type=int, default=20)
    ap.add_argument("--terms", type=int, default=50)
    ap.add_argument("--dps", type=int, default=30)
    ap.add_argument("--json", default=None)
    args = ap.parse_args(argv)
    mp.mp.dps = args.dps
    out = [run(b, args.top, args.terms) for b in args.bases.split(",")]
    if args.json:
        with open(args.json, "w") as fh:
            json.dump(out, fh, indent=1)
    return 0


if __name__ == "__main__":
    sys.exit(main())
