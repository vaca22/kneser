"""Companion demo for essay-infinite-systems-zh.md.

Solves the infinite polynomial system arising from f(f(x)) = e^x - 1
degree by degree, in exact rational arithmetic (standard library only):
the fixed point at 0 grades the system, so each new Taylor coefficient
a_k appears linearly, exactly once, with nonzero factor (mu + mu^k) = 2.

Run:  python3 docs/demo_infinite_system.py
"""

from fractions import Fraction
from math import factorial

N = 32

# g(x) = e^x - 1: fixed point at 0 with g'(0) = 1
g = [Fraction(0)] + [Fraction(1, factorial(k)) for k in range(1, N + 1)]


def compose(f, h, n):
    """(f o h)(x) truncated to x^n; f and h have zero constant term."""
    res = [Fraction(0)] * (n + 1)
    cur = [Fraction(1)] + [Fraction(0)] * n          # h^0
    for j in range(1, n + 1):
        new = [Fraction(0)] * (n + 1)                # cur <- cur * h
        for i1, c1 in enumerate(cur):
            if c1:
                for i2 in range(1, n - i1 + 1):
                    if h[i2]:
                        new[i1 + i2] += c1 * h[i2]
        cur = new
        if f[j]:
            for d in range(j, n + 1):
                res[d] += f[j] * cur[d]
    return res


def main():
    # door 1 (algebra): triangular solve, one unknown per degree
    f = [Fraction(0), Fraction(1)] + [Fraction(0)] * (N - 1)
    for k in range(2, N + 1):
        c = compose(f, f, k)
        f[k] = (g[k] - c[k]) / 2

    resid = compose(f, f, N)
    assert all(resid[k] == g[k] for k in range(N + 1))
    print("exact check: f(f(x)) == e^x - 1  (mod x^33)  PASS")
    print("\nfirst coefficients (exact):")
    for k in range(2, 9):
        print(f"  a[{k}] = {f[k]}")

    # door 2 (analysis): the same series has zero radius of convergence
    print("\ntail growth (formal solvability is not convergence):")
    for k in [6, 10, 14, 18, 22, 26, 30, 32]:
        print(f"  |a[{k}]| = {float(abs(f[k])):.3e}")
    return f


if __name__ == "__main__":
    main()
