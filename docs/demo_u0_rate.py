"""The kink offset u0 is the temperature step.

    u0(s) = -log(exp(L_{s-1} eps_s) - 1) + (b - 2) L_s

On an orbit of the reduced map this cancellation is the temperature step:
u0(s) = (L_{s+1} - L_s) plus two smaller terms, so
s u0 -> 1/(b-1), with the next piece 1/log(s/a).  The script checks the
ladder up to rank 24, then continues with (R1, R2).

Run:  PYTHONPATH=src python3 docs/demo_u0_rate.py
"""

from __future__ import annotations

import math
import sys

import mpmath as mp

sys.path.insert(0, "docs")
from demo_rank_regular import Level  # noqa: E402


def u0_of(b, eps, lam, lam_prev):
    beta = b - 1
    M = -mp.log(lam_prev)
    L = -mp.log(lam)
    return -mp.log(mp.exp(M * eps) - 1) + (beta - 1) * L, L


def reduced_u0(b, eps, lam, lam_prev, s, marks):
    """Float iteration of (R1, R2).  Returns u0 at the marked ranks."""
    beta = float(b) - 1
    x, y = float(mp.log(eps)), float(mp.log(lam))
    y_prev = float(mp.log(lam_prev))
    out = {}
    while s <= max(marks):
        M = -y_prev
        L = -y
        # u0 = -log(exp(M eps)-1) + (beta-1) L
        arg = math.expm1(M * math.exp(x))
        u0 = -math.log(arg) + (beta - 1) * L
        if s in marks:
            out[s] = (u0, L, L - M)
        e = math.exp(x)
        e_next = e
        for _ in range(4):
            e_next = e * -math.expm1((beta + e_next) * y)
        # (R2) uses eps_s, not eps_{s+1}: log lam' = log eps + (beta+eps') log lam + log L
        y_prev = y
        y = math.log(e) + (beta + e_next) * y + math.log(-y)
        x = math.log(e_next)
        s += 1
    return out


def main():
    mp.mp.dps = 20
    marks = {8, 12, 16, 24, 48, 128, 512, 2048, 8192, 32768, 10**5, 10**6}
    for bstr, top in (("1.2", 24), ("1.3", 24), ("1.4", 24)):
        b = mp.mpf(bstr)
        beta = b - 1
        target = 1 / beta
        prev = None
        seed = None
        print(f"\nbase {bstr}    1/(b-1) = {mp.nstr(target, 5)}")
        print(f"  ladder: {'s':>5} {'u0':>9} {'s*u0':>8}")
        for _ in range(4, top + 1):
            lev = Level(b, prev, 32)
            if prev is not None and lev.s in (8, 12, 16, 24):
                u0, _ = u0_of(b, lev.p - b, lev.lam, prev.lam)
                print(f"          {lev.s:>5} {mp.nstr(u0, 5):>9} {mp.nstr(lev.s * u0, 5):>8}")
            if lev.s == 16:
                seed = (prev.lam, lev.p - b, lev.lam, lev.s)
            prev = lev
        lam_prev, eps, lam, s0 = seed
        reduced = reduced_u0(b, eps, lam, lam_prev, s0, marks)
        a = (2 - b) / beta
        print("  reduced map from rank 16,   pred = 1/(b-1) + 1/log(s/a):")
        for s in sorted(reduced):
            u0, L, dL = reduced[s]
            pred = float(target + 1 / mp.log(s / a))
            print(f"    s={s:<7} u0={u0:.6e}  s*u0={s * u0:.4f}  "
                  f"pred={pred:.4f}  u0/dL={u0 / dL:.4f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
