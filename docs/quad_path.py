"""Numerical analytic continuation of the two-fixed-point solution of w^2 + c along a path in c.

Each build is seeded with the Taylor coefficients of the previous point (normalisation F(-K) = 0,
F(0) = f^K(0)), so the family is followed continuously; a failure to converge marks where the
continuation (or the unit-disc Taylor representation) breaks down.  Prints residual, a1 and the
coefficient-decay radius estimate at each step.
Usage: python3 quad_path.py c0_re c0_im c1_re c1_im nsteps [K] [digits]
       (path: straight segment; several segments can be chained with QP_SEED=<file> / QP_SAVE=<file>)
"""
import json
import os
import sys

import mpmath as mp

from quad_kneser import build

c0 = complex(float(sys.argv[1]), float(sys.argv[2]))
c1 = complex(float(sys.argv[3]), float(sys.argv[4]))
n = int(sys.argv[5])
K = int(sys.argv[6]) if len(sys.argv) > 6 else 3
digits = int(sys.argv[7]) if len(sys.argv) > 7 else 15
seed = None
if os.environ.get("QP_SEED"):
    seed = [complex(*x) for x in json.load(open(os.environ["QP_SEED"]))]
with mp.workdps(2 * digits + 20):
    for k in range(n + 1):
        c = c0 + (c1 - c0) * k / n
        try:
            r = build(mp.mpc(c), digits, verbose=False, n_loops=60, seed=seed, kcrit=K, max_loops_bad=60,
                      idelta=os.environ.get("QP_DELTA", "0.1"))
        except Exception as exc:  # noqa: BLE001
            print(f"{c.real:+.4f} {c.imag:+.4f} FAIL {type(exc).__name__}: {str(exc)[:60]}", flush=True)
            break
        a = r["coeffs"]
        res = r["residuals"][-1]
        m = len(a)
        est = min(float(abs(a[j])) ** (-1.0 / j) for j in range(m // 2, m - 4) if a[j] != 0)
        lam = abs(r["up"].lam)
        print(f"{c.real:+.4f} {c.imag:+.4f} |lam_up|={float(lam):.4f} res={mp.nstr(res, 3)} loops={len(r['residuals'])-1} "
              f"radius~{est:.3f} a1={mp.nstr(a[1], 14)}", flush=True)
        if res > mp.mpf(10) ** (-digits + 2):
            print("   not converged -> stop", flush=True)
            break
        seed = [complex(x) for x in a]
    if os.environ.get("QP_SAVE") and seed is not None:
        json.dump([[z.real, z.imag] for z in seed], open(os.environ["QP_SAVE"], "w"))
