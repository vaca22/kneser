"""The invariant c1-hat = c1 / Lambda of the Kneser-vs-regular separation.

First-mode law (see docs/first_mode_check.py, verified to 7 digits):

    D(z) = K(z) - R(z) = c_1 * R'(z) * (e^{2 pi i z} - 1) + O(higher modes)

so the whole separation on (1, eta) is ONE complex number c_1(b).  Divide by the
forced scale Lambda(b) = exp(4 pi^2 / log lambda_up(b)) and extrapolate Im b -> 0:

    c1hat(b) = lim_{y -> 0+} c_1(b + iy) / Lambda(b + iy).

Usage: python3 docs/c1_invariant.py
"""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path

import mpmath as mp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from kneser._cbuild import choose_fixed_points  # noqa: E402
from kneser._general import GeneralRegularEngine  # noqa: E402

ROOT = str(Path(__file__).resolve().parent / "_generated" / "separation")
Z = "0.5"


def cval(s):
    return mp.mpc(mp.mpf(s[0]), mp.mpf(s[1]))


def lam_up(base_name):
    with mp.workdps(50):
        _, _, lu, _, _, _ = choose_fixed_points(base_name, dps=50)
        return lu


def c1_of(rec, digits=24):
    """c_1 from D(1/2) = -2 c_1 R'(1/2), and c_1 / Lambda."""
    with mp.workdps(digits + 16):
        g = GeneralRegularEngine(rec["base"], digits)
        _, dR = g.sexp(mp.mpf("0.5"), derivative=True)
        D = cval(rec["D"][Z])
        c1 = D / (dR * (mp.exp(1j * mp.pi) - 1))
        lu = lam_up(rec["base"])
        Lam = mp.exp(4 * mp.pi**2 / mp.log(lu))
        return c1, Lam, c1 / Lam, lu


def load(d):
    out = []
    for name in sorted(os.listdir(d)):
        if not name.endswith(".json"):
            continue
        with open(os.path.join(d, name)) as fh:
            r = json.load(fh)
        if "D" in r and r["b"][1] > 0:
            out.append(r)
    return sorted(out, key=lambda r: -r["b"][1])


def richardson(ys, vals):
    """Linear extrapolation to y = 0 from the two smallest y (and a 3-point check)."""
    (y1, v1), (y2, v2) = (ys[-1], vals[-1]), (ys[-2], vals[-2])
    lin = v1 + (v2 - v1) * (0 - y1) / (y2 - y1)
    if len(ys) >= 3:
        y3, v3 = ys[-3], vals[-3]
        quad = (v1 * (y2 * y3) / ((y1 - y2) * (y1 - y3))
                + v2 * (y1 * y3) / ((y2 - y1) * (y2 - y3))
                + v3 * (y1 * y2) / ((y3 - y1) * (y3 - y2)))
        return lin, quad
    return lin, None


def main():
    dirs = []
    for sub in ("post-fix", "post-fix-fine"):
        p = os.path.join(ROOT, sub)
        if os.path.isdir(p):
            dirs += [os.path.join(p, x) for x in sorted(os.listdir(p))]
    summary = {}
    for d in dirs:
        rs = load(d)
        if not rs:
            continue
        tag = os.path.relpath(d, ROOT)
        ys, hats = [], []
        print(f"\n=== {tag}")
        for rec in rs:
            noise = max(float(rec.get("residual_check", 0)), float(rec.get("residual", 0)))
            if rec["absD"][Z] < 100 * noise:
                continue
            c1, Lam, hat, lu = c1_of(rec)
            ys.append(mp.mpf(rec["b"][1]))
            hats.append(hat)
            print(f"  y={rec['b'][1]:<9.4g} |c1|={float(abs(c1)):.6e} "
                  f"|Lam|={float(abs(Lam)):.4e} |c1hat|={float(abs(hat)):.8f} "
                  f"arg c1hat={float(mp.arg(hat)):+.8f}  (snr {rec['absD'][Z] / max(noise, 1e-300):.1e})")
        if len(ys) >= 2:
            lin, quad = richardson(ys, hats)
            print(f"  --> y=0 linear : |c1hat|={float(abs(lin)):.8f} arg={float(mp.arg(lin)):+.8f}")
            if quad is not None:
                print(f"  --> y=0 quad   : |c1hat|={float(abs(quad)):.8f} arg={float(mp.arg(quad)):+.8f}"
                      f"   (arg/pi = {float(mp.arg(quad) / mp.pi):.6f})")
            summary[tag] = (float(abs(quad if quad is not None else lin)),
                            float(mp.arg(quad if quad is not None else lin)))
    print("\n=== summary (quadratic extrapolation to Im b = 0)")
    for tag, (m, a) in sorted(summary.items()):
        print(f"  {tag:<28} |c1hat| = {m:.8f}   arg = {a:+.8f}   arg/pi = {float(a / mp.pi):.6f}")
    external()


EXTERNAL = [
    # base, K(1/2) from fatou.gp (tests/data/external_reference.json), source
    ("0.8+0.4j",
     "9.908526571258773392541932250185490972246406044059919392817541610151432583593194380034840043003434043e-1",
     "3.176860704644888547129127739198439325817233045992937678405273094923687600318714681357986452390762878e-1"),
    ("1+1j",
     "1.262363131617097022743895114790950104728735852118580725590799486145621429335150976293385722819893636",
     "4.705989028949844651997716777444476519739644111770827794970447387864431621445082602004659720886211344e-1"),
    ("2+1j",
     "1.526768345757420205996151752905565038683789847142819671823739872031472357678721145115882353056132071",
     "2.812250037597122330428736332222205836591873866105407726932562277775664536764164638938739855663345971e-1"),
]


def external(digits=40):
    """Same invariant for the three interior complex bases whose K comes from fatou.gp
    (PARI/GP, completely outside this repository)."""
    print("\n=== external K (fatou.gp) at z = 1/2, interior complex bases")
    for name, re_s, im_s in EXTERNAL:
        with mp.workdps(digits + 20):
            K = mp.mpc(mp.mpf(re_s), mp.mpf(im_s))
            g = GeneralRegularEngine(name, digits)
            R, dR = g.sexp(mp.mpf("0.5"), derivative=True)
            D = K - R
            c1 = D / (dR * (mp.exp(1j * mp.pi) - 1))
            lu = lam_up(name)
            Lam = mp.exp(4 * mp.pi**2 / mp.log(lu))
            hat = c1 / Lam
            print(f"  b={name:<9} |lam_up|={float(abs(lu)):.5f} |Lam|={float(abs(Lam)):.4e} "
                  f"|D|={float(abs(D)):.4e} |c1hat|={float(abs(hat)):.6f} "
                  f"arg={float(mp.arg(hat)):+.5f}")


if __name__ == "__main__":
    main()
