"""Crossing of the main-cardioid boundary by the two-fixed-point family of w^2 + c.

Points are c = mu/2 - mu^2/4 with mu = r e^{i pi theta}: the upper fixed point has
multiplier exactly mu, so r = |lambda_up| and the boundary is r = 1.  For each theta,
the point nearest the neutral band on each side (r = 0.96 and 1.04) is predicted by
Lagrange interpolation through three points on each side, skipping the held-out
point.  A branch change across the boundary would make this error comparable to
the jump |a1(0.96) - a1(1.04)|.  Analogue of thm:far / thm:last-arc (numerics only).

Usage: python3 quad_cross_check.py cross.out
"""
import cmath
import sys
from collections import defaultdict

groups = defaultdict(dict)
fails = []
for line in open(sys.argv[1]):
    f = line.split()
    if len(f) < 4:
        continue
    c = complex(float(f[0]), float(f[1]))
    mu = 1 - cmath.sqrt(1 - 4 * c)
    if cmath.phase(mu) <= 0:
        mu = 2 - mu
    th = round(cmath.phase(mu) / cmath.pi, 3)
    r = round(abs(mu), 3)
    if f[3] != "ok":
        fails.append((th, r, f[3]))
        continue
    groups[th][r] = (complex(float(f[6]), float(f[7])), complex(float(f[8]), float(f[9])))


def lag(xs, vs, x):
    s = 0
    for i, xi in enumerate(xs):
        t = vs[i]
        for j, xj in enumerate(xs):
            if j != i:
                t *= (x - xj) / (xi - xj)
        s += t
    return s


for th, r, st in sorted(fails):
    print(f"no value: theta/pi={th} r={r}: {st[:70]}")
print(f"{'theta/pi':>8} {'coef':>4} {'band':>9} {'jump':>14} {'err pred inner':>14} {'err pred outer':>14} "
      f"{'same-side ref':>14}")
for th in sorted(groups):
    g = groups[th]
    for idx, name in ((0, "a1"), (1, "a2")):
        v = {r: g[r][idx] for r in g}
        ins = sorted(r for r in v if r < 1)
        out = sorted(r for r in v if r > 1)
        if len(ins) < 4 or len(out) < 4:
            print(f"{th:>8} {name:>4}  too few points: have {sorted(v)}")
            continue
        ri, ro = ins[-1], out[0]            # nearest the band on each side
        jump = abs(v[ro] - v[ri])
        tr1 = ins[-4:-1] + out[:3]
        e1 = abs(lag(tr1, [v[r] for r in tr1], ri) - v[ri])
        tr2 = ins[-3:] + out[1:4]
        e2 = abs(lag(tr2, [v[r] for r in tr2], ro) - v[ro])
        ref = None
        if len(ins) >= 5:   # same-side extrapolation: predict ri from the four inner points before it
            tr3 = ins[-5:-1]
            ref = abs(lag(tr3, [v[r] for r in tr3], ri) - v[ri])
        print(f"{th:>8} {name:>4} {ri}|{ro} {jump:>14.3e} {e1:>14.3e} {e2:>14.3e} {('%.3e' % ref) if ref is not None else '-':>14}")
