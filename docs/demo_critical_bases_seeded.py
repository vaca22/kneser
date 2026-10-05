"""Critical bases of seeded ladders.

docs/rank-tropical-limit-zh.md §7 proves, for any ladder of increasing
levels, that b_c(s) is nondecreasing and at most 2.  The limit is not
universal: concave seeds stall strictly below 2, while the rate-law
closed logarithm has b_∞ = 2.  The analytic ladder stays in [1.83976, 2].
Here every level s >= 4 is seeded by a fixed increasing function on (-1, 0],

    S_s(z) = seed(z)  (-1 < z <= 0),     S_s(z) = S_{s-1}(S_s(z-1))  (z > 0),

with seed(-1) = 0, seed(0) = 1.  These ladders are crude (not smooth at the
integers) but satisfy every hypothesis of the two lemmas, and b_c(s) is cheap:
the rank-s tower converges iff m_s(b) = min_{x >= 1} (S_{s-1}(x) - x) <= 0.

Run:  python3 docs/demo_critical_bases_seeded.py --top 16
"""

from __future__ import annotations

import argparse
import json
import math
import sys

CAP = 1e6

SEEDS = {
    "linear": lambda z: 1 + z,
    "sqrt": lambda z: math.sqrt(1 + z),
    "square": lambda z: (1 + z) ** 2,
}
for _q in ("0.8", "0.9", "0.95", "1.05"):
    SEEDS[f"pow{_q}"] = (lambda q: lambda z: (1 + z) ** q)(float(_q))


def make_S(b, seed):
    def S(s, x):
        if x == math.inf:
            return math.inf
        if s == 3:
            return b ** x if x * math.log(b) < math.log(CAP) else math.inf
        n = max(0, math.ceil(x))
        v = seed(x - n)
        for _ in range(n):                    # S_s(x) = S_{s-1}^n(seed(x - n))
            w = S(s - 1, v)
            if w == math.inf or w == v:       # escaped, or sitting on a fixed point
                return w
            v = w
        return v
    return S


def margin(b, s, seed, xmax=4.0, n=400):
    """min over x in [1, xmax] of S_{s-1}(x) - x (the rank-s tower margin)."""
    S = make_S(b, seed)
    f = lambda x: S(s - 1, x) - x
    xs = [1 + (xmax - 1) * k / n for k in range(n + 1)]
    vals = [f(x) for x in xs]
    k = min(range(len(vals)), key=vals.__getitem__)
    lo, hi = xs[max(k - 1, 0)], xs[min(k + 1, n)]
    for _ in range(60):                       # golden section on the bracket
        m1, m2 = lo + (hi - lo) * 0.382, lo + (hi - lo) * 0.618
        if f(m1) < f(m2):
            hi = m2
        else:
            lo = m1
    return min(vals[k], f((lo + hi) / 2))


def critical_base(s, seed, lo=1.3, hi=2.0, tol=1e-12):
    for _ in range(80):
        mid = (lo + hi) / 2
        if margin(mid, s, seed) <= 0:
            lo = mid
        else:
            hi = mid
        if hi - lo < tol:
            break
    return (lo + hi) / 2


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--top", type=int, default=16)
    ap.add_argument("--seeds", default="linear,sqrt,square")
    ap.add_argument("--json", default=None)
    args = ap.parse_args(argv)
    out = {}
    for name in args.seeds.split(","):
        seed = SEEDS[name]
        rows, prev = [], None
        print(f"seed {name}")
        print(f"   s   b_c(s)            2 - b_c       local exponent")
        for s in range(4, args.top + 1):
            bc = critical_base(s, seed)
            k = (math.log((2 - prev) / (2 - bc)) / math.log(s / (s - 1))
                 if prev is not None else None)
            rows.append({"s": s, "b_c": bc, "gap": 2 - bc, "local_exponent": k})
            print(f"  {s:>2}   {bc:.12f}   {2 - bc:.6e}   "
                  f"{'' if k is None else f'{k:.4f}'}", flush=True)
            prev = bc
        out[name] = rows
    if args.json:
        with open(args.json, "w") as fh:
            json.dump(out, fh, indent=1)
    return 0


if __name__ == "__main__":
    sys.exit(main())
