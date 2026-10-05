"""The kink z = b-1 is not the inflection of the rank-s operation.

The closed logarithm of the previous temperature,
    Phi(z) = p - (1/M) log(1 - M C lam^z),    M = |log lam| of rank s-1,
has derivative
    Phi'(z) = (L/M) / (1 + exp(L (z - z_half))),    L = |log lam| of rank s.
Passing through (1, b) fixes the offset of the kink from that inflection:
    u0 = L ((b-1) - z_half) = -log(exp(M (p-b)) - 1) + (b-2) L.
Two large terms cancel.  Every derivative of Phi at z = b-1 is the logistic
jet at u0, and the ladder agrees with Phi there.

Run:  PYTHONPATH=src python3 docs/demo_kink_next.py
"""

from __future__ import annotations

import sys

import mpmath as mp

sys.path.insert(0, "docs")
from demo_rank_regular import Level  # noqa: E402


def sigma(u, n=0):
    return mp.diff(lambda t: 1 / (1 + mp.exp(t)), u, n)


def report(b, top):
    beta = b - 1
    prev = None
    print(f"\nbase {mp.nstr(b, 2)}")
    print("    s    -log(e^(M eps)-1)   (b-2)L       u0     slope   (L/M)sig   |S-Phi|")
    out = None
    for _ in range(4, top + 1):
        lev = Level(b, prev, 40)
        if prev is not None and lev.s in (8, 12, 16, 24):
            M = abs(mp.log(prev.lam))
            Ls = abs(mp.log(lev.lam))
            eps = lev.p - b
            big = -mp.log(mp.exp(M * eps) - 1)
            other = (beta - 1) * Ls
            A = -M * lev.C
            q = mp.power(lev.lam, beta)
            u0 = -mp.log(A * q)
            pred = (Ls / M) * sigma(u0)
            h = mp.mpf("1e-6")
            slope = (-lev.S(beta + 2 * h) + 8 * lev.S(beta + h)
                     - 8 * lev.S(beta - h) + lev.S(beta - 2 * h)) / (12 * h)
            Phi = lev.p - mp.log(1 + mp.exp(-u0)) / M
            err = abs(lev.S(beta) - Phi)
            print(f"  {lev.s:>3} {mp.nstr(big, 6):>18} {mp.nstr(other, 6):>8} "
                  f"{mp.nstr(u0, 5):>8} {mp.nstr(slope, 6):>9} "
                  f"{mp.nstr(pred, 6):>9} {mp.nstr(err, 3):>9}")
            out = (lev, prev, u0, Ls / M)
        prev = lev
    return out


def main():
    mp.mp.dps = 25
    report(mp.mpf("1.2"), 16)
    lev, prev, u0, ratio = report(mp.mpf("1.3"), 24)
    report(mp.mpf("1.4"), 16)
    print("\nbase 1.3, rank 24: S^{(n)}(b-1) / L^{n-1} against (L/M) σ^{(n-1)}(u0)")
    M = abs(mp.log(prev.lam))
    beta = lev.b - 1
    for n in range(1, 5):
        got = mp.diff(lev.S, beta, n) / abs(mp.log(lev.lam)) ** (n - 1)
        want = ratio * sigma(u0, n - 1)
        print(f"  n={n}  ladder {mp.nstr(got, 6):>12}   logistic {mp.nstr(want, 6):>12}")
    print("Koenigs u_k * k / M^{k-1}, M of the previous rank")
    print(" ", "  ".join(mp.nstr(lev.u[k] * k / M ** (k - 1), 6) for k in range(2, 6)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
