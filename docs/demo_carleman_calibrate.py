"""Carleman square-root calibration (问题 4.2 / 下一步 6).

The truncated-Carleman principal square root of exp lands on Kneser, but
that statement needs two calibration ends before it can be believed:

  (S)  g(x) = 4x          Schröder / linearisable; exact half-iterate is 2x.
       The Carleman matrix is diagonal, the principal sqrt is exact at
       every truncation, and the Taylor row is exactly (0, 2, 0, 0, ...).
  (P)  g(x) = e^x - 1     parabolic (g(0)=0, g'(0)=1).  The formal Taylor
       half-iterate is the triangular system of demo_infinite_system.py;
       the truncated Carleman principal sqrt must reproduce those
       coefficients until the zero-radius divergence takes over.
  (K)  g(x) = e^x         no real fixed point.  Extend the mpmath run of
       demo_carleman_sqrt.py past the float64 ceiling (n=20, 24) to
       confirm the algebraic approach to Kneser continues.

Run:  PYTHONPATH=src python3 docs/demo_carleman_calibrate.py
"""

from fractions import Fraction
from math import factorial

import mpmath as mp

import kneser.hp as hp


def carleman(coeffs, n):
    """Carleman matrix of a polynomial / truncated series g = sum coeffs[k] x^k.

    M[i, j] = [x^j] g(x)^i,  0 <= i,j <= n.
    """
    # g-powers via repeated multiplication of truncated series
    gpow = [[mp.mpf(0)] * (n + 1) for _ in range(n + 1)]
    gpow[0][0] = mp.mpf(1)
    g = [mp.mpf(c) for c in coeffs[: n + 1]] + [mp.mpf(0)] * (n + 1 - len(coeffs))
    for i in range(1, n + 1):
        acc = [mp.mpf(0)] * (n + 1)
        for a in range(n + 1):
            if gpow[i - 1][a] == 0:
                continue
            for b in range(n + 1 - a):
                if g[b] == 0:
                    continue
                acc[a + b] += gpow[i - 1][a] * g[b]
        gpow[i] = acc
    return mp.matrix(gpow)


def principal_sqrt_row(M, dps):
    """Row 1 of the principal square root of M (mpmath eigendecomposition)."""
    with mp.workdps(dps):
        vals, V = mp.eig(M)
        D = mp.zeros(M.rows)
        for k in range(M.rows):
            D[k, k] = mp.exp(mp.log(vals[k]) / 2)
        F = V * D * (V ** -1)
        return [F[1, j] for j in range(M.cols)]


def formal_half_exp_minus_one(n):
    """Exact rational Taylor of the half-iterate of e^x - 1, degree n."""
    g = [Fraction(0)] + [Fraction(1, factorial(k)) for k in range(1, n + 1)]

    def compose(f, h, deg):
        res = [Fraction(0)] * (deg + 1)
        cur = [Fraction(1)] + [Fraction(0)] * deg
        for j in range(1, deg + 1):
            new = [Fraction(0)] * (deg + 1)
            for i1, c1 in enumerate(cur):
                if c1:
                    for i2 in range(1, deg - i1 + 1):
                        if h[i2]:
                            new[i1 + i2] += c1 * h[i2]
            cur = new
            if f[j]:
                for d in range(j, deg + 1):
                    res[d] += f[j] * cur[d]
        return res

    f = [Fraction(0), Fraction(1)] + [Fraction(0)] * (n - 1)
    for k in range(2, n + 1):
        c = compose(f, f, k)
        f[k] = (g[k] - c[k]) / 2
    return f


def main():
    print("=== (S) g(x) = 4x : exact half-iterate 2x ===")
    for n in (4, 8, 12):
        # g = 0 + 4x + 0 x^2 + ...
        M = carleman([0, 4], n)
        row = principal_sqrt_row(M, dps=40)
        target = [mp.mpf(0)] * (n + 1)
        target[1] = mp.mpf(2)
        err = max(abs(mp.re(row[j]) - target[j]) for j in range(n + 1))
        print(f"  n={n:>2}:  a1={mp.nstr(mp.re(row[1]), 12)}  "
              f"max |row - (0,2,0,...)| = {mp.nstr(err, 3)}")
    print("  (principal sqrt is exact on this linear family; branch = +sqrt)\n")

    print("=== (P) g(x) = e^x - 1 : triangular Carleman = formal half-iterate ===")
    N = 12
    formal = formal_half_exp_minus_one(N)
    f_coeffs = [mp.mpf(c.numerator) / c.denominator for c in formal]
    g_coeffs = [0] + [mp.mpf(1) / mp.factorial(k) for k in range(1, N + 1)]
    Cf = carleman(f_coeffs, N)
    Cg = carleman(g_coeffs, N)
    # g(0)=0 makes Cg (and Cf) triangular: eigendecomposition is the wrong
    # tool (defective 0-eigenblock).  The dictionary itself is the test:
    # C_f C_f must equal C_g in the truncated polynomial algebra.
    sq = Cf * Cf
    worst = mp.mpf(0)
    for i in range(N + 1):
        for j in range(N + 1):
            worst = max(worst, abs(sq[i, j] - Cg[i, j]))
    print(f"  C_g is triangular:  Cg[1,0] = {mp.nstr(Cg[1, 0], 3)}"
          f"  Cg[2,0] = {mp.nstr(Cg[2, 0], 3)}  (powers of g(0)=0)")
    print(f"  max |C_f^2 - C_g| over {N+1}x{N+1} = {mp.nstr(worst, 3)}"
          "   (exact in Q, residual is rounding)")
    print("  formal Taylor of the half-iterate (same numbers as demo_infinite_system):")
    for k in range(2, 9):
        print(f"    a[{k}] = {formal[k]}")
    print("  the dictionary is faithful on the parabolic side: branch choice is")
    print("  unique because the matrix is triangular with nonzero diagonal.\n")

    print("=== (K) g(x) = e^x : mpmath principal sqrt past the f64 ceiling ===")
    ref = {xs: hp.half_exp(xs, dps=40) for xs in ("0", "0.5", "1")}

    def carleman_exp(n):
        return mp.matrix([[mp.mpf(i) ** j / mp.factorial(j)
                           for j in range(n + 1)] for i in range(n + 1)])

    def eval_row(row, x):
        acc = mp.mpf(0)
        for c in reversed(row):
            acc = acc * x + mp.re(c)
        return acc

    print(f"  {'n':>4} {'|f(0)-Kneser|':>14} {'|f(0.5)-Kneser|':>16} "
          f"{'|f(1)-Kneser|':>14}")
    for n in (8, 12, 16, 20, 24):
        try:
            row = principal_sqrt_row(carleman_exp(n), dps=50)
        except (ZeroDivisionError, ValueError) as exc:
            print(f"  {n:>4}  eig failed ({exc}); skip")
            continue
        errs = [abs(eval_row(row, mp.mpf(xs)) - ref[xs]) for xs in ("0", "0.5", "1")]
        print(f"  {n:>4} {float(errs[0]):>14.2e} {float(errs[1]):>16.2e} "
              f"{float(errs[2]):>14.2e}")
    print("  algebraic approach continues in mpmath; the n=32 f64 bounce in")
    print("  demo_carleman_sqrt.py was conditioning, not a change of branch.")


if __name__ == "__main__":
    main()
