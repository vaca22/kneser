"""The continuous operation path  x +_t y  between + and x (问题 2.1 / 2.2).

For each t the conjugated operation

    x +_t y = E_t( E_{-t}(x) + E_{-t}(y) ),     E_t = exp^[t]

is commutative and associative (Aczel: it is addition transported by E_t),
with identity 0_t = E_t(0).  +_0 is addition, +_1 is multiplication (on
x, y > 0).  The path itself, t -> x +_t y, is the object of study.

Domain note: everything below keeps x, y > 0 and t in [0, 1], where
E_{-t}(x) (slog(x) - t > -2) and the outer E_t are always defined.

Endpoint slopes are exact in terms of the flow generator V (see
demo_flow_generator.py):

    d/dt (x +_t y) |_{t=0} = V(x+y) - V(x) - V(y)
    d/dt (x +_t y) |_{t=1} = xy * [ V(log xy) - V(log x) - V(log y) ]

so sub/super-additivity of V decides where the path starts upward or
downward -- non-monotonicity (猜想 B) becomes a checkable sign condition.

Run:  PYTHONPATH=src python3 docs/demo_operation_path.py
"""

import mpmath as mp

import kneser.hp as hp
from kneser import _coeffs

DPS = 40

with mp.workdps(DPS + 10):
    _C = [mp.mpf(s) for s in _coeffs.COEFFS]
    _C1 = [k * c for k, c in enumerate(_C)][1:]


def _horner(coeffs, z):
    r = mp.mpf(0)
    for c in reversed(coeffs):
        r = r * z + c
    return r


def sexp_d(z):
    """sexp'(z) via base series and the shift S'(z+1) = S(z+1) S'(z)."""
    z = mp.mpf(z)
    k = 0
    while z > mp.mpf("0.5"):
        z -= 1
        k += 1
    while z < mp.mpf("-0.5"):
        z += 1
        k -= 1
    s, s1 = _horner(_C, z), _horner(_C1, z)
    for _ in range(k):
        s = mp.exp(s)
        s1 = s * s1
    for _ in range(-k):
        s1 = s1 / s
        s = mp.log(s)
    return s1


def V(x):
    return sexp_d(hp.slog(x, dps=DPS))


def op(x, y, t):
    """x +_t y, for x, y > 0 and 0 <= t <= 1."""
    a = hp.exp_iter(x, -t, dps=DPS)
    b = hp.exp_iter(y, -t, dps=DPS)
    return hp.exp_iter(a + b, t, dps=DPS)


def curve_shape(x, y, n=64):
    """Sample t -> x +_t y; return (values, #interior sign changes of slope)."""
    vals = [op(x, y, mp.mpf(j) / n) for j in range(n + 1)]
    flips, last = 0, None
    for a, b in zip(vals, vals[1:]):
        s = mp.sign(b - a)
        if s and last and s != last:
            flips += 1
        if s:
            last = s
    return vals, flips


def main():
    mp.mp.dps = DPS

    # --- the basic curve: 2 +_t 3 ------------------------------------------
    x, y = mp.mpf(2), mp.mpf(3)
    print("t -> 2 +_t 3   (endpoints: 2+3 = 5, 2*3 = 6)")
    for j in range(11):
        t = mp.mpf(j) / 10
        print(f"  t={mp.nstr(t, 3):>5}:  {mp.nstr(op(x, y, t), 25)}")
    tmax = mp.findroot(
        lambda t: (op(x, y, t + mp.mpf(10) ** -12) - op(x, y, t - mp.mpf(10) ** -12)),
        mp.mpf("0.65"), solver="secant")
    vmax = op(x, y, tmax)
    print(f"  interior maximum: t* = {mp.nstr(tmax, 12)},  value = {mp.nstr(vmax, 20)}")
    print(f"  overshoot above 2*3:  {mp.nstr(vmax - 6, 10)}")

    # --- endpoint slopes from V (exact), vs finite differences --------------
    print("\nendpoint slopes  s0 = V(x+y)-V(x)-V(y),  s1 = xy*[V(log xy)-V(log x)-V(log y)]")
    h = mp.mpf(10) ** -14
    print(f"{'(x,y)':>10} {'s0 (V formula)':>18} {'s0 (numeric)':>16} "
          f"{'s1 (V formula)':>18} {'s1 (numeric)':>16}")
    for xs, ys in [(2, 3), (2, 2), (1, 1), ("0.5", "0.5"), (1, 2), (5, 5)]:
        a, b = mp.mpf(xs), mp.mpf(ys)
        s0 = V(a + b) - V(a) - V(b)
        s1 = a * b * (V(mp.log(a * b)) - V(mp.log(a)) - V(mp.log(b)))
        n0 = (op(a, b, h) - (a + b)) / h
        n1 = (a * b - op(a, b, 1 - h)) / h
        print(f"({xs:>3},{ys:>3})  {mp.nstr(s0, 12):>18} {mp.nstr(n0, 8):>16} "
              f"{mp.nstr(s1, 12):>18} {mp.nstr(n1, 8):>16}")

    # --- 猜想 B census: how often is the path monotone? ---------------------
    grid = [mp.mpf(s) for s in ["0.25", "0.5", "1", "1.5", "2", "3", "5"]]
    mono, nonmono = [], []
    for i, a in enumerate(grid):
        for b in grid[i:]:
            _, flips = curve_shape(a, b)
            (nonmono if flips else mono).append((a, b, flips))
    print(f"\nmonotone paths on the {len(grid)}x{len(grid)} grid: {len(mono)}, "
          f"non-monotone: {len(nonmono)}")
    print("  non-monotone pairs (x, y, slope sign changes):")
    for a, b, f in nonmono:
        print(f"    ({mp.nstr(a, 4)}, {mp.nstr(b, 4)})  flips={f}")

    # --- the self-dual pair x = y = 2 (2+2 = 2*2): forced interior extremum --
    print("\nt -> 2 +_t 2  (both endpoints equal 4):")
    vals, _ = curve_shape(mp.mpf(2), mp.mpf(2), n=8)
    for j, v in enumerate(vals):
        print(f"  t={mp.nstr(mp.mpf(j) / 8, 4):>6}:  {mp.nstr(v, 20)}")

    # --- D_t sign structure --------------------------------------------------
    print("\nsign of D_t(x,y) = x +_t y - xy at t = 1/2  ('+' above product):")
    hdr = "        " + "".join(f"{mp.nstr(b, 4):>7}" for b in grid)
    print(hdr)
    for a in grid:
        row = f"{mp.nstr(a, 4):>7} "
        for b in grid:
            d = op(a, b, mp.mpf("0.5")) - a * b
            row += f"{'+' if d > 0 else '-':>7}"
        print(row)

    print("\nsign of (x +_t y) - (x + y) at t = 1/2  ('+' above sum):")
    print(hdr)
    for a in grid:
        row = f"{mp.nstr(a, 4):>7} "
        for b in grid:
            d = op(a, b, mp.mpf("0.5")) - (a + b)
            row += f"{'+' if d > 0 else '-':>7}"
        print(row)

    # --- 问题 2.2: the identity path 0_t = E_t(0) = sexp(t-1) ----------------
    print("\nidentity path 0_t = E_t(0) = sexp(t-1), with speed V(0_t):")
    print(f"{'t':>6} {'0_t':>32} {'d/dt 0_t (numeric)':>22} {'V(0_t)':>22}")
    h = mp.mpf(10) ** -15
    for j in range(9):
        t = mp.mpf(j) / 8
        v = hp.sexp(t - 1, dps=DPS)
        dv = (hp.sexp(t - 1 + h, dps=DPS) - hp.sexp(t - 1 - h, dps=DPS)) / (2 * h)
        print(f"{mp.nstr(t, 4):>6} {mp.nstr(v, 28):>32} "
              f"{mp.nstr(dv, 14):>22} {mp.nstr(V(v), 14):>22}")
    print(f"  midpoint 0_(1/2) = sexp(-1/2) = {mp.nstr(hp.sexp('-0.5', dps=DPS), 30)}")

    # --- the inverse path of 2: from -2 (additive) to 1/2 (multiplicative) ---
    print("\ninverse path  -_t 2 = E_t(-E_{-t}(2)):")
    for j in range(9):
        t = mp.mpf(j) / 8
        m = hp.exp_iter(-hp.exp_iter(2, -t, dps=DPS), t, dps=DPS)
        print(f"  t={mp.nstr(t, 4):>6}:  {mp.nstr(m, 20)}")


if __name__ == "__main__":
    main()
