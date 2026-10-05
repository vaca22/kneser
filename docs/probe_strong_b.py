"""Search for a same-sign endpoint pair whose path is not monotone.

Under V''>0 the velocity deficit
    rho(t) = V(p+q) - V(p) - V(q),   p=E_{-t}x, q=E_{-t}y
satisfies rho'<0 when p,q>0 and rho'>0 when p,q<0, and rho=-V(0)
whenever either argument is 0.  A counterexample to
"endpoint signs classify monotonicity" is therefore a pair 0<x,y<1
with rho(0)>0 and rho(1)>0: the orbit enters the third quadrant, where
rho has already been negative, and ends positive again.

Run: PYTHONPATH=src python3 docs/probe_strong_b.py
"""

import math

import kneser
from kneser import _coeffs

_CF = tuple(float(c) for c in _coeffs.COEFFS)
_DCF = tuple(k * c for k, c in enumerate(_CF))


def _horner(cs, z):
    value = 0.0
    for c in reversed(cs):
        value = value * z + c
    return value


def sexp_d(z):
    shift = 0
    while z > 0.5:
        z -= 1.0
        shift += 1
    while z < -0.5:
        z += 1.0
        shift -= 1
    s = _horner(_CF, z)
    s1 = _horner(_DCF[1:], z)
    for _ in range(shift):
        s = math.exp(s)
        s1 = s * s1
    for _ in range(-shift):
        s1 /= s
        s = math.log(s)
    return s1


def V(x):
    return sexp_d(kneser.slog(x))


def rho_ends(x, y):
    s0 = V(x + y) - V(x) - V(y)
    s1 = V(math.log(x * y)) - V(math.log(x)) - V(math.log(y))
    return s0, s1


def main():
    # log-spaced square (0, 1)^2
    xs = [10 ** (-2 + 2 * i / 80) for i in range(81)]  # 0.01 .. 1
    hits = []
    both_pos = both_neg = opposite = 0
    for x in xs:
        for y in xs:
            if y < x:
                continue
            s0, s1 = rho_ends(x, y)
            if s0 > 0 and s1 > 0:
                both_pos += 1
                hits.append((s0, s1, x, y))
            elif s0 < 0 and s1 < 0:
                both_neg += 1
            else:
                opposite += 1
    print(f"pairs {both_pos + both_neg + opposite}")
    print(f"both endpoint slopes > 0: {both_pos}")
    print(f"both endpoint slopes < 0: {both_neg}")
    print(f"opposite or touching: {opposite}")
    if hits:
        hits.sort(reverse=True)
        print("largest s0 among double-positive pairs:")
        for row in hits[:8]:
            print(f"  s0={row[0]:.6e} s1={row[1]:.6e} x={row[2]:.6g} y={row[3]:.6g}")
    else:
        print("no same-sign positive pair on this grid")

    # also the region x>1, y in (0,1): phase I+II only, look for s0>0, s1>0
    # together with an interior negative sample of rho
    mixed = 0
    mixed_dip = []
    ys = xs
    big = [1.1, 1.5, 2, 3, 5, 8]
    for x in big:
        for y in ys:
            s0, s1 = rho_ends(x, y)
            if s0 > 0 and s1 > 0:
                # sample the axis-crossing time, where rho must be -V(0) if
                # the smaller argument has already hit 0 and the larger has not
                mixed += 1
                # t when E_{-t}y = 0: slog(y)+1
                # rho there is exactly -V(0) < 0, so this is already a dip
                mixed_dip.append((x, y, s0, s1))
    print(f"mixed pairs with both slopes > 0: {mixed}")
    if mixed_dip[:5]:
        print("examples", mixed_dip[:5])


if __name__ == "__main__":
    main()
