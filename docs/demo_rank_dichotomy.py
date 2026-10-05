"""Does the regular ladder stay under the line 1+z?  (the b_inf dichotomy)

docs/rank-tropical-limit-zh.md §7 conjectures that a ladder of increasing
levels has b_inf = 2 iff S_s(z) <= 1+z on [0, 1] (near the critical bases).
The seeded family saturates that: (1+z)^q with q < 1 overshoots 1+z and
stalls; q >= 1 stays under and reaches 2.  The regular (Koenigs) ladder's
pointwise limit is exactly the kink min(1+z, b), so the finite-s sign of
S_s - (1+z) is the remaining datum.

This script measures, on the regular ladder below eta,
    over_s = max_{z in [0,1]} (S_s(z) - (1+z)),
    under_s = max_{z in [0,1]} ((1+z) - S_s(z)),
and the same quantities against the chord 1+(b-1)z (the lower envelope of
the concave fixed-point family in Proposition C).

Run:  PYTHONPATH=src python3 docs/demo_rank_dichotomy.py --bases 1.3 --top 24
"""

from __future__ import annotations

import argparse
import json
import sys

import mpmath as mp

sys.path.insert(0, "docs")
from demo_rank_regular import Level  # noqa: E402


def scan(lev, b, n=40):
    over = over_c = under_c = mp.mpf(0)
    z_over = None
    vals = []
    for k in range(n + 1):
        z = mp.mpf(k) / n
        v = lev.S(z)
        vals.append(v)
        d = v - (1 + z)
        if d > over:
            over, z_over = d, z
        c = 1 + (b - 1) * z
        over_c = max(over_c, v - c)
        under_c = max(under_c, c - v)
    # second differences on [0,1]: concave iff d2 <= 0
    h = mp.mpf(1) / n
    d2max, d2at = -mp.inf, None
    for k in range(1, n):
        d2 = vals[k - 1] - 2 * vals[k] + vals[k + 1]
        if d2 > d2max:
            d2max, d2at = d2, k / n
    return {
        "s": lev.s, "p": mp.nstr(lev.p, 12), "lam": mp.nstr(lev.lam, 12),
        "over_1plusz": mp.nstr(over, 6), "at": None if z_over is None else mp.nstr(z_over, 3),
        "over_chord": mp.nstr(over_c, 6), "under_chord": mp.nstr(under_c, 6),
        "d2_max": mp.nstr(d2max / h ** 2, 6), "d2_at": mp.nstr(d2at, 3),
        "S_half": mp.nstr(lev.S(mp.mpf("0.5")), 12),
    }


def run(b_str, top, K):
    b = mp.mpf(b_str)
    print("=" * 72)
    print(f"base {b_str}   regular ladder through rank {top}")
    print(f"  {'s':>3}  {'over 1+z':>10} {'at':>5}  {'over chord':>10}  "
          f"{'S\" max':>10} {'at':>5}  {'S(1/2)':>12}")
    prev, rows = None, []
    for _ in range(4, top + 1):
        prev = Level(b, prev, K)
        row = scan(prev, b)
        rows.append(row)
        if prev.s in (4, 5, 6, 8, 12, 16, 24, 32, 40, 48) or prev.s == top:
            at = row["at"] or "-"
            print(f"  {prev.s:>3}  {row['over_1plusz']:>10} {at:>5}  "
                  f"{row['over_chord']:>10}  {row['d2_max']:>10} {row['d2_at']:>5}  "
                  f"{row['S_half']:>12}")
    return {"base": b_str, "levels": rows}


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--bases", default="1.3")
    ap.add_argument("--top", type=int, default=24)
    ap.add_argument("--terms", type=int, default=50)
    ap.add_argument("--dps", type=int, default=40)
    ap.add_argument("--json", default=None)
    args = ap.parse_args(argv)
    mp.mp.dps = args.dps
    out = [run(b, args.top, args.terms) for b in args.bases.split(",")]
    if args.json:
        with open(args.json, "w") as fh:
            json.dump(out, fh, indent=1)
        print(f"\nwrote {args.json}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
