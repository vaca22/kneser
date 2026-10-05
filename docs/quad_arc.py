"""Continuity of the two-fixed-point solution of w^2 + c along c = 1/4 + r e^{i phi}, 0 <= phi < pi.

phi = 0: real c > 1/4 (Kneser, both fixed points repelling).  The upper fixed point's multiplier
lambda = 1 + 2 i sqrt(r) e^{i phi/2} crosses the unit circle (main-cardioid boundary) at
phi* = 2 arcsin sqrt(r); beyond it the upper side is attracting.  Prints the first Taylor
coefficients of F (F(0) = f^3(0)) so that continuity across the neutral band can be checked.
Usage: python3 quad_arc.py r phi_over_pi [digits]
"""
import sys

import mpmath as mp

from quad_kneser import build

r = mp.mpf(sys.argv[1])
ph = mp.mpf(sys.argv[2])
digits = int(sys.argv[3]) if len(sys.argv) > 3 else 15
with mp.workdps(2 * digits + 20):
    c = mp.mpf(1) / 4 + r * mp.exp(1j * mp.pi * ph)
    res = build(c, digits, verbose=False)
    a = res["coeffs"]
    lam = res["up"].lam
    print(f"phi/pi={ph} c={mp.nstr(c, 10)} |lam_up|={mp.nstr(abs(lam), 6)} res={mp.nstr(res['residuals'][-1], 3)} "
          f"loops={len(res['residuals']) - 1}")
    for k in (1, 2, 3):
        print(f"  a{k} = {mp.nstr(a[k], 14)}", flush=True)
