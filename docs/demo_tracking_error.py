"""How far the closed logarithm sits from the softmin, and how fast that dies.

Section 2.10 of docs/rank-tropical-limit-zh.md.  With v = L (z - (b-1)),

    Phi(z) - Sigma(z) = E(v)
    E(v) = eps + log(1+e^{-v})/L - log(1+e^{-(v+u_0)})/M

E has one maximum, where sigma(v+u_0)/sigma(v) = M/L.  Its height is

    eps + (u_0/L) (1 - kappa - kappa log(1/kappa)) + higher order,
    kappa = (L - M)/(u_0 L) -> 0,

so the height is ~ u_0/L ~ 1/(s log(s/a)).  The old fit s^{-1.3} was this
law seen through ranks 16..48.

Run:  PYTHONPATH=src python3 docs/demo_tracking_error.py
"""

from __future__ import annotations

import sys

import mpmath as mp

sys.path.insert(0, "docs")
from demo_rank_regular import Level  # noqa: E402


def sigma(v):
    return 1 / (1 + mp.exp(v))


def tracking_gap(eps, L, M, u0, v):
    return (eps + mp.log(1 + mp.exp(-v)) / L
            - mp.log(1 + mp.exp(-(v + u0))) / M)


def tracking_peak(eps, L, M, u0):
    """Return (v_at_max, E(v), h-formula).  One critical point, and it is the max."""
    kappa = (L - M) / (u0 * L)

    def slope(v):
        return -sigma(v) / L + sigma(v + u0) / M

    v_star = mp.findroot(slope, mp.log(kappa / (1 - kappa)))
    h = 1 - kappa - kappa * mp.log(1 / kappa)
    return v_star, tracking_gap(eps, L, M, u0, v_star), eps + (u0 / L) * h


def report(b, top):
    beta = b - 1
    prev = None
    print(f"\nbase {mp.nstr(b, 3)}")
    print(f"{'s':>3}  {'max Phi-Sig':>12}  {'E(v*)':>12}  {'h-formula':>12}  {'z*':>8}")
    for _ in range(4, top + 1):
        lev = Level(b, prev, 28)
        prev = lev
        if lev.s < 8 or lev.s % 4:
            continue
        M = abs(mp.log(lev.prev.lam))
        Ls = abs(mp.log(lev.lam))
        eps = lev.p - b
        u0 = -mp.log(mp.exp(M * eps) - 1) + (beta - 1) * Ls
        v_star, exact, approx = tracking_peak(eps, Ls, M, u0)
        seen = mp.mpf("-1")
        for k in range(-40, 60):
            z = mp.mpf(k) / 20
            Phi = lev.p - mp.log(1 - M * lev.C * mp.power(lev.lam, z)) / M
            Sig = b - mp.log(1 + mp.exp(Ls * (beta - z))) / Ls
            seen = max(seen, Phi - Sig)
        print(f"{lev.s:3}  {mp.nstr(seen, 6):>12}  {mp.nstr(exact, 6):>12}  "
              f"{mp.nstr(approx, 6):>12}  {mp.nstr(beta + v_star / Ls, 4):>8}")


def main():
    mp.mp.dps = 20
    report(mp.mpf("1.2"), 16)
    report(mp.mpf("1.3"), 24)
    report(mp.mpf("1.4"), 16)
    return 0


if __name__ == "__main__":
    sys.exit(main())
