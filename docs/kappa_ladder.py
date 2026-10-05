"""The gauge invariants kappa_n = c_n / c_1^n of the separation, and the horn map.

Companion to docs/separation-first-mode-zh.md sec.4.2, which asked the sharpest
open question of that round: the first mode matches the parabolic horn map
(|c1hat| -> |A_1|) but the naive extension c_n / Lambda^n -> A_n fails at n = 2
by a factor of three.

The honest comparison is between quantities that no normalisation can move.
Under a shift of origin z -> z + delta (which is all the normalisation F(0) = 1
fixes) both sides transform the same way,

    c_n -> c_n e^{2 pi i n delta},        A_n -> A_n e^{2 pi i n delta},

so kappa_n = c_n / c_1^n and A_n / A_1^n are gauge invariant, complex, and
directly comparable -- no alignment step needed.

The point of this script: the hyperbolic-side P is the transition map in the
OPPOSITE direction from the parabolic h computed by docs/parabolic_horn.py.

    P  = (R-time as a function of K-time)   = alpha_att o alpha_rep^{-1} - id
    h  = Phi_rep o Phi_att^{-1} - id

so the limit of kappa_n is the invariant of h^{-1}, not of h.  Inverting a
1-periodic near-identity map mixes the modes:

    B_1 = -A_1,   B_2 = -A_2 + 2 pi i A_1^2,   ...

which is invisible at n = 1 (|B_1| = |A_1|) and is exactly the missing factor at
n = 2:  B_2 / B_1^2 = 2 pi i - A_2 / A_1^2.

Usage: python3 docs/kappa_ladder.py            # all ladders, both sample lines
       python3 docs/kappa_ladder.py 1.05 1.1   # selected Re b
"""

from __future__ import annotations

import json
import os
import sys

import mpmath as mp

sys.path.insert(0, "/Volumes/dream/halfexp/kneser/docs")
sys.path.insert(0, "/Volumes/dream/halfexp/kneser/src")

from theta_spectrum import spectrum  # noqa: E402

ROOT = "/Volumes/dream/halfexp/kneser/docs/_generated/separation"

# |A_n| and arg A_n of the parabolic (b = eta) horn map, from docs/parabolic_horn.py
# (30-50 digits of working precision, all digits below stable across settings).
HORN = {
    1: ("0.0890584364122", "-1.7391394"),
    2: ("0.037349258777", "-1.9128595"),
    3: ("0.02246384013", "-2.0900662"),
}

LADDERS = [
    ("post-fix/re1.05_d20_i0.10", "1.05"),
    ("post-fix-fine/re1.05_fine", "1.05"),
    ("post-fix/re1.1_d20_i0.10", "1.10"),
    ("post-fix-fine/re1.1_fine", "1.10"),
    ("post-fix/re1.15_d20_i0.10", "1.15"),
    ("out4/re1.2_d20_i0.10", "1.20"),
    ("out4/re1.25_d24_i0.10", "1.25"),
    ("out4/re1.3_d32_i0.10", "1.30"),
    ("out5/re1.2_d32_i0.10", "1.20"),
    ("out5/re1.25_d32_i0.10", "1.25"),
    ("out5/re1.25_d44_i0.10", "1.25"),
    ("out6/re1.15_d24_i0.10", "1.15"),
    ("out6/re1.2_d32_i0.10", "1.20"),
    ("out6/re1.25_d32_i0.10", "1.25"),
    ("out6/re1.3_d52_i0.10", "1.30"),
    ("out5/re1.3_d52_i0.10", "1.30"),
]


def horn_modes():
    A = {n: mp.mpf(m) * mp.exp(1j * mp.mpf(a)) for n, (m, a) in HORN.items()}
    tp = 2j * mp.pi
    B = {1: -A[1], 2: -A[2] + tp * A[1] ** 2}
    B[3] = -(A[1] * (tp * B[2] + (tp**2 / 2) * B[1] ** 2) + A[2] * (2 * tp * B[1]) + A[3])
    return A, B


def load(d, reb=None):
    """the ladder of a single Re b; the walk points of neighbouring Re b that
    share the directory are dropped (they also duplicate y = 0.1)."""
    out = []
    for name in sorted(os.listdir(d)):
        if not name.endswith(".json"):
            continue
        with open(os.path.join(d, name)) as fh:
            r = json.load(fh)
        if "coeffs" not in r or r["b"][1] <= 0:
            continue
        if reb is not None and abs(r["b"][0] - float(reb)) > 1e-9:
            continue
        out.append((mp.mpf(r["b"][1]), r, os.path.join(d, name)))
    return sorted(out, key=lambda t: -t[0])


def extrap(ys, vals):
    """Linear from the two smallest y, quadratic from the three smallest."""
    (y1, v1), (y2, v2) = (ys[-1], vals[-1]), (ys[-2], vals[-2])
    lin = v1 + (v2 - v1) * (0 - y1) / (y2 - y1)
    quad = None
    if len(ys) >= 3:
        y3, v3 = ys[-3], vals[-3]
        quad = (v1 * (y2 * y3) / ((y1 - y2) * (y1 - y3))
                + v2 * (y1 * y3) / ((y2 - y1) * (y2 - y3))
                + v3 * (y1 * y2) / ((y3 - y1) * (y3 - y2)))
    return lin, quad


def main(select=None):
    A, B = horn_modes()
    with mp.workdps(30):
        kB2 = B[2] / B[1] ** 2
        kA2 = A[2] / A[1] ** 2
        kB3 = B[3] / B[1] ** 3
        print("parabolic end (b = eta), gauge invariants of the horn map:")
        print(f"  A_2 / A_1^2  (h)        = {float(abs(kA2)):.7f} @ {float(mp.arg(kA2)):+.7f}")
        print(f"  B_2 / B_1^2  (h^{{-1}})   = {float(abs(kB2)):.7f} @ {float(mp.arg(kB2)):+.7f}"
              f"   = 2 pi i - A_2/A_1^2")
        print(f"  B_3 / B_1^3  (h^{{-1}})   = {float(abs(kB3)):.7f} @ {float(mp.arg(kB3)):+.7f}")

    rows = []
    for tag, reb in LADDERS:
        if select and reb not in select:
            continue
        d = os.path.join(ROOT, tag)
        if not os.path.isdir(d):
            continue
        recs = load(d, reb)
        if len(recs) < 2:
            continue
        print(f"\n=== {tag}   (Re b = {reb})")
        ys, k2s, k3s = [], [], []
        for y, rec, _ in recs:
            got = {}
            for y0 in ("-0.5", "-1.0"):
                cs, _ = spectrum(rec, mp.mpf(y0), N=32, nmodes=5)
                got[y0] = cs
            c1 = got["-1.0"][1]
            c2a, c2b = got["-0.5"][2], got["-1.0"][2]
            c3a, c3b = got["-0.5"][3], got["-1.0"][3]
            # agreement between the two sample lines is the noise test
            d2 = abs(c2a - c2b) / abs(c2b) if c2b else mp.inf
            d3 = abs(c3a - c3b) / abs(c3b) if c3b else mp.inf
            k2 = c2b / c1**2
            k3 = c3b / c1**3
            ok2 = d2 < mp.mpf(os.environ.get("KAPPA_TOL", "1e-4"))
            print(f"  y={float(y):<8.4g} |c1|={float(abs(c1)):.5e} |c2|={float(abs(c2b)):.4e} "
                  f"(lines agree {float(d2):.1e}) kappa2={float(abs(k2)):.6f} @ {float(mp.arg(k2)):+.6f}"
                  f"{'' if ok2 else '   <-- c2 NOISE, dropped'}")
            if float(d3) < 1e-2:
                print(f"           |c3|={float(abs(c3b)):.4e} (lines agree {float(d3):.1e}) "
                      f"kappa3={float(abs(k3)):.5f} @ {float(mp.arg(k3)):+.6f}")
                k3s.append((y, k3))
            if ok2:
                ys.append(y)
                k2s.append(k2)
        if len(ys) >= 2:
            lin, quad = extrap(ys, k2s)
            v = quad if quad is not None else lin
            print(f"  --> y=0  kappa2 = {float(abs(v)):.6f} @ {float(mp.arg(v)):+.6f}"
                  f"   (linear {float(abs(lin)):.6f} @ {float(mp.arg(lin)):+.6f})")
            print(f"      ratio to B_2/B_1^2 : |.| {float(abs(v) / abs(kB2)):.5f}   "
                  f"arg diff {float(mp.arg(v) - mp.arg(kB2)):+.5f}")
            rows.append((reb, tag, v))
        if len(k3s) >= 2:
            lin3, quad3 = extrap([y for y, _ in k3s], [k for _, k in k3s])
            v3 = quad3 if quad3 is not None else lin3
            print(f"  --> y=0  kappa3 = {float(abs(v3)):.5f} @ {float(mp.arg(v3)):+.6f}"
                  f"   ratio to B_3/B_1^3 : {float(abs(v3) / abs(kB3)):.5f}")

    print("\n=== summary: kappa2(b) -> B_2/B_1^2 = "
          f"{float(abs(kB2)):.7f} @ {float(mp.arg(kB2)):+.7f}")
    for reb, tag, v in rows:
        print(f"  Re b = {reb}  {tag:<30} kappa2 = {float(abs(v)):.6f} @ {float(mp.arg(v)):+.6f}"
              f"   |.|/|B2/B1^2| = {float(abs(v) / abs(kB2)):.5f}")


if __name__ == "__main__":
    main(set(sys.argv[1:]) or None)
