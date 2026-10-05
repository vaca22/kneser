"""One two-fixed-point build of w^2 + c at a complex c (upper half-plane); one line of output.
Usage: python3 quad_point.py c_re c_im [digits]
Output: c_re c_im |lam_up| status residual loops a1 a2   (status ok / unconverged / fail:<reason>)
"""
import sys

import mpmath as mp

from quad_kneser import build

cre, cim = sys.argv[1], sys.argv[2]
digits = int(sys.argv[3]) if len(sys.argv) > 3 else 12
with mp.workdps(2 * digits + 20):
    c = mp.mpc(cre, cim)
    lam = 1 + mp.sqrt(1 - 4 * c)
    lam = lam if mp.arg(lam) > 0 else 2 - lam          # upper fixed point's multiplier
    try:
        r = build(c, digits, verbose=False, n_loops=80)
        a = r["coeffs"]
        st = "ok" if r["residuals"][-1] < mp.mpf(10) ** (-digits + 3) else "unconverged"
        print(cre, cim, mp.nstr(abs(lam), 6), st, mp.nstr(r["residuals"][-1], 3), len(r["residuals"]) - 1,
              mp.nstr(mp.re(a[1]), 15), mp.nstr(mp.im(a[1]), 15), mp.nstr(mp.re(a[2]), 15), mp.nstr(mp.im(a[2]), 15),
              flush=True)
    except Exception as exc:  # noqa: BLE001
        print(cre, cim, mp.nstr(abs(lam), 6), "fail:" + type(exc).__name__ + ":" + str(exc)[:60].replace(" ", "_"),
              flush=True)
