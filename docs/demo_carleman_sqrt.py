"""Square roots of truncated Carleman matrices (问题 4.2).

f o f = exp becomes M_f^2 = M_exp for Carleman matrices
M_g[i, j] = [x^j] g(x)^i (so M_{f o g} = M_f M_g, row 1 = Taylor row).
This demo takes the order-n truncation of M_exp, forms the principal
matrix square root through the eigendecomposition, reads row 1 off as a
candidate Taylor series of exp^[1/2], and asks two questions:

  1. Does it converge to Kneser's half-exponential as n grows?
     (exp has *no* real fixed point, so the classical regular-iteration
     route is unavailable; the truncation has to pick something.)
  2. What limits the accuracy -- the truncation itself, or the
     conditioning of the eigenbasis in float64?

To separate the two, orders up to 16 are recomputed with mpmath at 40
digits.  Reference values come from the shipped 50-digit kneser package.

Run:  PYTHONPATH=src python3 docs/demo_carleman_sqrt.py
"""

import math

import mpmath as mp

import kneser.hp as hp


def carleman_exp(n):
    """Truncated Carleman matrix of exp: M[i][j] = i^j / j!, 0 <= i,j <= n."""
    return [[mp.mpf(i) ** j / mp.factorial(j) for j in range(n + 1)]
            for i in range(n + 1)]


def half_row_float64(n):
    """Row 1 of the principal square root of the order-n truncation (numpy)."""
    import cmath

    import numpy as np

    M = np.array([[float(i) ** j / math.factorial(j) for j in range(n + 1)]
                  for i in range(n + 1)])
    vals, V = np.linalg.eig(M)
    half = np.array([cmath.exp(0.5 * cmath.log(v)) for v in vals])
    F = V @ np.diag(half) @ np.linalg.inv(V)
    cond = np.linalg.cond(V)
    return [complex(c) for c in F[1, :]], cond


def half_row_mp(n, dps=40):
    """Same, in mpmath arithmetic (separates truncation from roundoff)."""
    with mp.workdps(dps):
        M = mp.matrix(carleman_exp(n))
        vals, V = mp.eig(M)
        D = mp.zeros(n + 1)
        for k in range(n + 1):
            D[k, k] = mp.exp(mp.log(vals[k]) / 2)
        F = V * D * (V ** -1)
        return [F[1, j] for j in range(n + 1)]


def eval_row(row, x):
    acc = 0
    for c in reversed(row):
        acc = acc * x + c
    return acc


def main():
    mp.mp.dps = 30
    ref_half = {x: hp.half_exp(x, dps=40) for x in ("0", "0.5", "1")}
    ref_f0 = hp.sexp("-1.5", dps=40) + 0  # f(0) = sexp(-1/2 + slog(0)) = sexp(-3/2)...
    # f(0) = sexp(slog(0) + 1/2) = sexp(-1/2):
    ref_f0 = hp.sexp("-0.5", dps=40)

    print("principal sqrt of the truncated Carleman matrix of exp -> exp^[1/2]?")
    print("(errors against the shipped Kneser values)\n")
    print(f"{'n':>4} {'arith':>8} {'|f(0)-ref|':>12} {'|f(0.5)-ref|':>14} "
          f"{'|f(1)-ref|':>12} {'max|Im row|':>12} {'cond(V)':>10}")

    for n in [8, 12, 16, 20, 24, 28, 32]:
        row, cond = half_row_float64(n)
        ims = max(abs(c.imag) for c in row)
        errs = [abs(eval_row([c.real for c in row], float(mp.mpf(xs)))
                    - float(ref_half[xs])) for xs in ("0", "0.5", "1")]
        print(f"{n:>4} {'f64':>8} {errs[0]:>12.2e} {errs[1]:>14.2e} "
              f"{errs[2]:>12.2e} {ims:>12.2e} {cond:>10.1e}")

    for n in [8, 12, 16]:
        row = half_row_mp(n, dps=40)
        ims = max(abs(mp.im(c)) for c in row)
        errs = [abs(eval_row([mp.re(c) for c in row], mp.mpf(xs)) - ref_half[xs])
                for xs in ("0", "0.5", "1")]
        print(f"{n:>4} {'mp40':>8} {float(errs[0]):>12.2e} {float(errs[1]):>14.2e} "
              f"{float(errs[2]):>12.2e} {float(ims):>12.2e} {'':>10}")

    print(f"\nreference: f(0) = sexp(-1/2) = {mp.nstr(ref_f0, 25)}")
    print(f"           f(1) = sexp(1/2)  = {mp.nstr(ref_half['1'], 25)}")

    # which branch did the truncation pick?  compare low-order Taylor
    # coefficients with Kneser's (from the shipped series, via slog/sexp).
    row = half_row_mp(16, dps=40)
    h = mp.mpf(10) ** -10
    with mp.workdps(60):
        d1 = (hp.half_exp(h, dps=60) - hp.half_exp(-h, dps=60)) / (2 * h)
        d2 = (hp.half_exp(h, dps=60) - 2 * hp.half_exp(0, dps=60)
              + hp.half_exp(-h, dps=60)) / h ** 2
    print("\nTaylor at 0, truncation (n=16, mp) vs Kneser (finite differences):")
    for k, ref in [(0, ref_f0), (1, d1), (2, d2 / 2)]:
        print(f"  a_{k}: {mp.nstr(mp.re(row[k]), 12):>16}  vs  {mp.nstr(ref, 12):>16}"
              f"   (|diff| = {mp.nstr(abs(mp.re(row[k]) - ref), 2)})")


if __name__ == "__main__":
    main()
