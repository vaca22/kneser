"""Radius of convergence of the Taylor series at 0 of the two-fixed-point build of w^2 + c.

The build (quad_kneser.build) assumes F holomorphic on the closed unit disc.  For complex c a
branch point of F (a zero of F, cf. F(-3) = 0) may move inside; then the build is not the
continued solution.  Estimates the radius from the coefficient decay and locates zeros of F
in |z| < 1.3.
Usage: python3 quad_radius.py c_re c_im [digits]
"""
import sys

import mpmath as mp

from quad_kneser import build

digits = int(sys.argv[3]) if len(sys.argv) > 3 else 15
with mp.workdps(2 * digits + 20):
    c = mp.mpc(sys.argv[1], sys.argv[2])
    r = build(c, digits, verbose=False, n_loops=80)
    a = r["coeffs"]
    n = len(a)
    est = [abs(a[k]) ** (-1.0 / k) for k in range(n // 2, n - 4) if a[k] != 0]
    F = lambda z: sum(x * z**k for k, x in enumerate(a))  # noqa: E731
    zeros = []
    for x in [i / 4 for i in range(-5, 6)]:
        for y in [i / 4 for i in range(-5, 6)]:
            if x * x + y * y > 1.69:
                continue
            try:
                z = mp.findroot(F, mp.mpc(x, y), tol=mp.mpf(10) ** (-digits))
                if abs(z) < 1.3 and all(abs(z - w) > 1e-6 for w in zeros):
                    zeros.append(z)
            except Exception:  # noqa: BLE001
                pass
    print(f"c={sys.argv[1]}{'+' if float(sys.argv[2]) >= 0 else ''}{sys.argv[2]}i res={mp.nstr(r['residuals'][-1], 3)} "
          f"loops={len(r['residuals']) - 1} radius~{float(min(est)):.3f}..{float(max(est)):.3f} "
          f"zeros in |z|<1.3: {[mp.nstr(z, 5) for z in zeros]}", flush=True)
