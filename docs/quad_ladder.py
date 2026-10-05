"""Theorem F for w^2 + c: Kneser ladder c = c_r + i y, y -> 0, against tau_n of the sewn side.

For each y the two-fixed-point solution K (quad_kneser.build, K(0) = f^3(0)) is
written above as R o (id + theta_up) with R the regular superfunction at the
attracting point p(c).  So P = R^{-1} o K - id = theta_up + const, and with the
base point w0 = K(0) = f^3(0) the separation coefficients are
    c_n = a_n e^{2 pi n delta},   hat c_n = c_n / Lambda^n,   Lambda = exp(4 pi^2 / log lambda_p),
where theta_up(t + i delta) = sum a_n e^{2 pi i n t}.  kappa_2 = c_2/c_1^2 needs no normalisation.
Prediction (Theorem F + Theorem B): as y -> 0, hat c_n -> tau_n(c_r) + O(Lambda), with tau_n computed
by generality_check.py quad (GC_W0 = f^3(0)).

Usage: python3 quad_ladder.py lam y [digits]       (c_r = (1 - (1 - lam)^2)/4)
"""
import sys

import mpmath as mp

from quad_kneser import build

lam = mp.mpf(sys.argv[1])
y = mp.mpf(sys.argv[2])
digits = int(sys.argv[3]) if len(sys.argv) > 3 else 25
with mp.workdps(2 * digits + 20):
    cr = (1 - (1 - lam) ** 2) / 4
    r = build(mp.mpc(cr, y), digits, verbose=False)
    lp = r["up"].lam
    Lam = mp.exp(4 * mp.pi**2 / mp.log(lp))
    c = {n: r["fa_up"][n] * mp.exp(2 * mp.pi * n * r["delta"]) for n in (1, 2, 3)}
    ch = {n: c[n] / Lam**n for n in c}
    k2 = c[2] / c[1] ** 2
    print(f"lam={lam} y={y} c={mp.nstr(r['c'], 12)} res={mp.nstr(r['residuals'][-1], 3)} loops={len(r['residuals'])-1} "
          f"|Lambda|={mp.nstr(abs(Lam), 5)}")
    print(f"  hat c1 = {mp.nstr(ch[1], 16)}")
    print(f"  hat c2 = {mp.nstr(ch[2], 12)}")
    print(f"  kappa2 = {mp.nstr(k2, 12)}")
    print(f"  w0 = f^3(0) at c_r = {mp.nstr((cr * cr + cr) ** 2 + cr, 25)}", flush=True)
