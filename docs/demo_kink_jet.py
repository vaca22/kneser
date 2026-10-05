"""The whole derivative jet at the kink is the logistic jet, and the softmin
almost obeys the successor equation at non-integer rank.

Logistic:  σ(u) = 1/(1+e^u) = (1/2)(1 - tanh(u/2)).
If S'(β + u/L) = σ(u), then
    S^{(n)}(β) = L^{n-1} σ^{(n-1)}(0).
In particular S'''(β) = 0 and S''''(β) = L^3 / 8.

L(s) is the two-term rate law of section 2.4, used as written for
non-integer and complex s (principal logarithm).  The successor defect
of that family is what decides whether non-integer rank is more than a
fitted curve.

Run:  PYTHONPATH=src python3 docs/demo_kink_jet.py
"""

from __future__ import annotations

import sys

import mpmath as mp

sys.path.insert(0, "docs")
from demo_rank_regular import Level  # noqa: E402


def sigma_derivs(n):
    """σ^{(k)}(0) for k = 0..n-1, σ(u) = 1/(1+e^u)."""
    return [mp.diff(lambda u: 1 / (1 + mp.exp(u)), 0, k) for k in range(n)]


def softmin(z, b, L):
    beta = b - 1
    return b - mp.log(1 + mp.exp(L * (beta - z))) / L


def L_of(b, r):
    """|log λ| from the two-term rate law, extended by the same formula."""
    beta = b - 1
    a = (2 - b) / beta
    lr = mp.log(r)
    q = (a + 1 / lr + (1 + mp.log(a)) / lr ** 2) / r
    return -mp.log(q) / beta


def successor_defect(b, s, z, L=None, Lprev=None):
    """Σ_s(z+1) - Σ_{s-1}(Σ_s(z)). Default L is the rate law."""
    if L is None:
        L = L_of(b, s)
    if Lprev is None:
        Lprev = L_of(b, s - 1)
    left = softmin(z + 1, b, L)
    right = softmin(softmin(z, b, L), b, Lprev)
    return left - right, L


def ladder_jet(b, top, K, n_deriv=4):
    prev = None
    for _ in range(4, top + 1):
        prev = Level(b, prev, K)
    beta = b - 1
    L = abs(mp.log(prev.lam))
    target = sigma_derivs(n_deriv)
    got = []
    for n in range(1, n_deriv + 1):
        d = mp.diff(prev.S, beta, n)
        scale = L ** (n - 1)
        got.append((n, d, d / scale, target[n - 1]))
    return prev.s, L, got


def main():
    mp.mp.dps = 25
    print("logistic jet σ^{(k)}(0), σ(u)=1/(1+e^u)")
    for k, v in enumerate(sigma_derivs(6)):
        print(f"  k={k}  {mp.nstr(v, 8)}")

    print("\nsoftmin successor defect, base 1.3, grid z=-0.5..1.5")
    print(f"  {'s':>6} {'L':>8}  {'rate-law':>10} {'same L':>10} {'s+1/2':>10}  defect*s^2")
    b = mp.mpf("1.3")
    zs = [mp.mpf(k) / 4 for k in range(-2, 8)]
    for s in (mp.mpf(k) for k in (8, 12, 24, 48, 96)):
        worst = max(abs(successor_defect(b, s, z)[0]) for z in zs)
        L = L_of(b, s)
        frozen = max(abs(successor_defect(b, s, z, L=L, Lprev=L)[0]) for z in zs)
        half = max(abs(successor_defect(b, s + mp.mpf("1/2"), z)[0]) for z in zs)
        print(f"  {mp.nstr(s, 3):>6} {mp.nstr(L, 5):>8}  {mp.nstr(worst, 4):>10} "
              f"{mp.nstr(frozen, 4):>10} {mp.nstr(half, 4):>10}  {mp.nstr(worst * s**2, 4)}")

    print("\npeak defect at z=b-2, over log(2)*(L-Lprev)/L^2")
    for s in (24, 48, 100, 500):
        s = mp.mpf(s)
        L, N = L_of(b, s), L_of(b, s - 1)
        z = b - 2
        d = softmin(z + 1, b, L) - softmin(softmin(z, b, L), b, N)
        pred = mp.log(2) * (L - N) / L ** 2
        print(f"  s={int(s):4}  ratio={mp.nstr(d / pred, 6)}  delta={mp.nstr(d, 4)}")

    print("\ncomplex rank, base 1.3, max |defect| on the same grid")
    for im in ("0", "0.3", "1", "2", "5"):
        s = mp.mpc(24, im)
        worst = max(abs(successor_defect(b, s, z)[0]) for z in zs)
        print(f"  s=24+{im}i   max|defect|={mp.nstr(worst, 4)}")

    print("\nladder jet at the kink, scaled by L^{n-1}, against σ^{(n-1)}(0)")
    for bstr, top in (("1.3", 12), ("1.3", 24)):
        s, L, got = ladder_jet(mp.mpf(bstr), top, 40, 4)
        print(f"  base {bstr} rank {s}  L={mp.nstr(L, 6)}")
        for n, d, scaled, want in got:
            if abs(want) < mp.mpf("1e-8"):
                how = f"should be 0, got {mp.nstr(scaled, 4)}"
            else:
                how = f"ratio {mp.nstr(scaled / want, 5)}"
            print(f"    n={n}  S^(n)/L^(n-1) = {mp.nstr(scaled, 6):>12}   "
                  f"σ = {mp.nstr(want, 6):>12}   {how}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
