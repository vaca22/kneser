"""Continuity scan of the two-fixed-point family of w^2 + c over the upper half c-plane.

Reads the output of quad_point.py over a grid (one line per point) and tests every
column Re c = const and every row Im c = const for jumps: each interior point is
predicted by cubic interpolation from its two nearest neighbours on each side, and
the error is compared with the same test far from the cardioid boundary.  Points
whose stencil straddles the neutral band (|lambda_up| crosses 1) are reported
separately: a monodromy/branch change of the continuation would show up there.

Usage: python3 quad_grid_check.py grid.out
"""
import sys
from collections import defaultdict

rows = []
for line in open(sys.argv[1]):
    f = line.split()
    if len(f) < 4:
        continue
    x, y, lam, st = float(f[0]), float(f[1]), float(f[2]), f[3]
    if st == "ok":
        a1 = complex(float(f[6]), float(f[7]))
        rows.append((x, y, lam, a1))
    else:
        rows.append((x, y, lam, None))
pts = {(x, y): (lam, a) for x, y, lam, a in rows}
ok = {k: v for k, v in pts.items() if v[1] is not None}
print(f"points {len(pts)}, converged {len(ok)}, refused near |lambda|=1 or failed {len(pts) - len(ok)}")
for k, v in sorted(pts.items()):
    if v[1] is None:
        print(f"   no value at c = {k[0]:+.2f} + {k[1]:.2f}i   |lambda_up| = {v[0]:.4f}")


def lagrange(xs, vs, x):
    s = 0
    for i, xi in enumerate(xs):
        t = vs[i]
        for j, xj in enumerate(xs):
            if j != i:
                t *= (x - xj) / (xi - xj)
        s += t
    return s


def scan(lines, label):
    errs_cross, errs_plain = [], []
    for key, seq in sorted(lines.items()):
        seq = sorted(seq)
        for i in range(2, len(seq) - 2):
            sten = seq[i - 2:i] + seq[i + 1:i + 3]
            t, lam, val = seq[i]
            pred = lagrange([s[0] for s in sten], [s[2] for s in sten], t)
            e = abs(pred - val) / max(abs(val), 1e-12)
            lams = [s[1] for s in sten] + [lam]
            crosses = min(lams) < 1 < max(lams)
            (errs_cross if crosses else errs_plain).append((e, key, t))
    errs_plain.sort(reverse=True)
    errs_cross.sort(reverse=True)
    print(f"\n{label}: stencils not crossing |lambda|=1: {len(errs_plain)}, "
          f"max rel err {errs_plain[0][0]:.2e}, median {errs_plain[len(errs_plain)//2][0]:.2e}")
    if errs_cross:
        print(f"{label}: stencils crossing the cardioid boundary: {len(errs_cross)}, "
              f"max rel err {errs_cross[0][0]:.2e}, median {errs_cross[len(errs_cross)//2][0]:.2e}")
        for e, key, t in errs_cross[:6]:
            print(f"     {e:.2e}  at line {key:+.2f}, position {t:.2f}")
    print(f"{label}: worst non-crossing stencils:")
    for e, key, t in errs_plain[:4]:
        print(f"     {e:.2e}  at line {key:+.2f}, position {t:.2f}")


cols, rws = defaultdict(list), defaultdict(list)
for (x, y), (lam, a) in ok.items():
    cols[x].append((y, lam, a))
    rws[y].append((x, lam, a))
scan(cols, "columns (Re c fixed, along Im c)")
scan(rws, "rows (Im c fixed, along Re c)")
