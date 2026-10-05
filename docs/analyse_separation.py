"""Cross-precision audit of D(b) = K(b) - R(b) near the real axis of the Shell-Thron region.

Reads the `decay` ladders produced by `demo_base_separation.py` (one directory per
(Re b, digits, idelta) setting) and answers one question: **is the low-`Im b` plateau of |D| a
property of the functions, or of the algorithm?**

The scale it is measured against is

    Lambda(b) = exp(4 pi^2 / log lambda_up(b)),

which is not a fitted constant: two Abel functions of the same map differ by a 1-periodic
function of the Abel coordinate `alpha = log kappa / log lambda`, and the first Fourier mode
`exp(2 pi i alpha) = kappa^{2 pi i / log lambda}` has modulus `Lambda` after one turn around the
fixed point.  So *any* nonzero difference between two tetrations at an attracting fixed point is
forced to sit at size `Lambda`.  The dimensionless quantity to watch is therefore

    E(b) = D(b) / Lambda(b),

and the claim "D vanishes identically on (1, eta)" is the claim "E -> 0 as Im b -> 0".

Run: python3 analyse_separation.py <dir-with-out/> [--key 0.5]
"""

import argparse
import cmath
import json
import math
import os
import re as _re


def lam_and_scale(d):
    lam = d["lam_up_abs"] * cmath.exp(1j * d["lam_up_arg"])
    ll = cmath.log(lam)
    return ll, cmath.exp(4 * math.pi ** 2 / ll)


def load_dir(path, key):
    rows = []
    for fn in sorted(os.listdir(path)):
        if not fn.endswith(".json") or fn in ("meta.json", "analysis.json", "fit.json", "law.json"):
            continue
        d = json.load(open(os.path.join(path, fn)))
        if "D" not in d or not d.get("attracting_up"):
            continue
        ll, Lam = lam_and_scale(d)
        D = complex(float(d["D"][key][0]), float(d["D"][key][1]))
        rows.append({
            "y": d["b"][1], "absD": abs(D), "absLam": abs(Lam), "absE": abs(D / Lam),
            "argE": cmath.phase(D / Lam), "a1": d["a1_up"],
            "resid": float(d["residual"]), "chk": float(d["residual_check"]),
            "loops": d["loops"], "capped": d.get("loop_limit_reached"), "digits": d["digits"],
        })
    rows.sort(key=lambda r: -r["y"])
    return rows


TAG = _re.compile(r"re([\d.]+)_d(\d+)_i([\d.]+)")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("root")
    ap.add_argument("--key", default="0.5")
    a = ap.parse_args()

    data = {}
    for tag in sorted(os.listdir(a.root)):
        m = TAG.fullmatch(tag)
        if not m:
            continue
        data[(m.group(1), int(m.group(2)), float(m.group(3)))] = load_dir(os.path.join(a.root, tag), a.key)

    res = sorted({k[0] for k in data}, key=float)
    settings = sorted({(k[1], k[2]) for k in data})

    for rb in res:
        print(f"\n################  Re b = {rb}   (D at z = {a.key})")
        for dg, idl in settings:
            rows = data.get((rb, dg, idl))
            if not rows:
                continue
            print(f"\n--- digits={dg} idelta={idl}")
            print("    y      |D|         |Lambda|     |E|=|D/L|   argE     a1_up      resid      |D|/resid  loops cap")
            for r in rows:
                print("  %5.3f  %9.3e  %10.3e  %9.3e  %+6.3f  %9.3e  %9.3e  %9.1f  %4d %s"
                      % (r["y"], r["absD"], r["absLam"], r["absE"], r["argE"], r["a1"],
                         r["chk"], r["absD"] / r["chk"] if r["chk"] else float("nan"),
                         r["loops"], "Y" if r["capped"] else "n"))

        # cross-setting stability at each y
        ys = sorted({r["y"] for s in settings for r in data.get((rb,) + s, [])}, reverse=True)
        print(f"\n=== cross-setting |E| at Re b = {rb}  (spread = max/min over settings)")
        head = "    y   " + "".join(f"  d{dg}/i{idl:<4}" for dg, idl in settings) + "   spread"
        print(head)
        for y in ys:
            vals, cells = [], []
            for s in settings:
                r = next((r for r in data.get((rb,) + s, []) if abs(r["y"] - y) < 1e-12), None)
                cells.append("  %9.3e" % r["absE"] if r else "  %9s" % "-")
                if r:
                    vals.append(r["absE"])
            spread = max(vals) / min(vals) if len(vals) > 1 and min(vals) > 0 else float("nan")
            print("  %5.3f" % y + "".join(cells) + "   %6.3f" % spread)


if __name__ == "__main__":
    main()
