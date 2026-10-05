"""Proposition D: an envelope traps the next tower for every b < 2.

Let f be nondecreasing on [0, L], f(1) = b in (1, 2), L = 1/(2-b), and
    f(x) <= 1 + (b-1) x     for x in [1, L].
Then 1, f(1), f(f(1)), ... converges to a fixed point in [b, L].
Slope-decreasing (second differences <= 0) plus f(0) = 1 implies the
envelope. Sufficient, not necessary: the linear seed reaches b_inf = 2
while convex on (0,1], and tetration at b = 1.63 already pokes above the
line while the pentation tower still converges (b_c5 = 1.6353).

Staying under 1+z on [0,1] is NOT the criterion. Kneser tetration at
b = 1.65 > b_c5 satisfies sexp(z) <= 1+z on [0,1] and the tower diverges.

Run:  PYTHONPATH=src python3 docs/demo_slope_trap.py
"""

from __future__ import annotations

import sys

import mpmath as mp

sys.path.insert(0, "docs")
from demo_critical_bases_seeded import SEEDS, make_S  # noqa: E402
from demo_rank_regular import Level  # noqa: E402


def second_diff_scan(f, lo, hi, n):
    """Return (max discrete second derivative, where, first z with d2>0 or None)."""
    h = (hi - lo) / n
    vs = [f(lo + h * k) for k in range(n + 1)]
    worst, at, first = -mp.inf, None, None
    for k in range(1, n):
        d2 = (vs[k - 1] - 2 * vs[k] + vs[k + 1]) / h ** 2
        z = lo + h * k
        if d2 > worst:
            worst, at = d2, z
        if first is None and d2 > mp.mpf("1e-8"):
            first = z
    return worst, at, first


def envelope_violation(f, b, hi, n):
    h = hi / n
    worst, at = mp.mpf(0), None
    for k in range(n + 1):
        z = h * k
        d = f(z) - (1 + (b - 1) * z)
        if d > worst:
            worst, at = d, z
    return worst, at


def report(name, f, b, hi, n=80):
    L = 1 / (2 - b)
    w, at, first = second_diff_scan(f, mp.mpf(0), hi, n)
    ev, ez = envelope_violation(f, b, hi, n)
    print(f"  {name:<22} L={mp.nstr(L, 4):>6}  S''max={mp.nstr(w, 4):>10} at {mp.nstr(at, 3):>6}"
          f"  first+ {('-' if first is None else mp.nstr(first, 3)):>6}"
          f"  envelope {mp.nstr(ev, 3):>8} at {mp.nstr(ez, 3)}")


def main():
    mp.mp.dps = 25
    print("regular ladder, b=1.3, on [0, 3]")
    b = mp.mpf("1.3")
    prev = None
    for s in range(4, 9):
        prev = Level(b, prev, 40)
        report(f"rank {s}", prev.S, b, mp.mpf(3))

    print("\nKneser tetration (rank 4)")
    import kneser
    for bstr in ("1.5", "1.6", "1.7", "1.8"):
        b = mp.mpf(bstr)
        f = lambda z, bstr=bstr: kneser.hp.sexp(z, dps=17, base=bstr)
        report(f"sexp b={bstr}", f, b, min(mp.mpf(4), 1 / (2 - b) + 1))

    print("\nseeded ladders, rank 12, on [0, 4]")
    cases = [("sqrt", "1.70"), ("sqrt", "1.74"), ("linear", "1.90"), ("pow0.9", "1.85"),
             ("pow0.9", "1.90")]
    for name, bstr in cases:
        b = float(bstr)
        S = make_S(b, SEEDS[name])
        f = lambda z, S=S: S(12, float(z))
        # float scan
        L = 1 / (2 - b)
        n, hi = 80, 4.0
        h = hi / n
        vs = []
        for k in range(n + 1):
            try:
                vs.append(f(h * k))
            except Exception:
                vs.append(float("inf"))
        worst, at, first = -1e99, None, None
        for k in range(1, n):
            if any(v == float("inf") or v != v for v in vs[k - 1:k + 2]):
                continue
            d2 = (vs[k - 1] - 2 * vs[k] + vs[k + 1]) / h ** 2
            if d2 > worst:
                worst, at = d2, h * k
            if first is None and d2 > 1e-6:
                first = h * k
        ev, ez = 0.0, None
        for k in range(n + 1):
            if vs[k] == float("inf"):
                continue
            d = vs[k] - (1 + (b - 1) * h * k)
            if d > ev:
                ev, ez = d, h * k
        print(f"  {name:>8} b={bstr} L={L:.3f}  S''max={worst:.4g} at {at}  "
              f"first+ {first}  envelope {ev:.3g} at {ez}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
