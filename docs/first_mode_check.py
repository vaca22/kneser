"""First-mode law for D = K - R on (1, eta), with the normalisation constant.

Model.  K and R are two superfunctions of the same map E(w) = b^w, both
normalised by F(0) = 1.  Hence K(z) = R(z + P(z)) with P 1-periodic, and
P(0) = 0.  Writing P = c_0 + sum_{n>=1} c_n e^{2 pi i n z} (no negative modes:
K is bounded in the upper half plane), the normalisation forces
c_0 = -sum_{n>=1} c_n, so to first order

    D(z) = K(z) - R(z) = R'(z) * c_1 * (e^{2 pi i z} - 1) + O(c_1^2, c_2).

Test: q(z) := D(z) / (R'(z) (e^{2 pi i z} - 1)) must be the SAME complex number
for every z.  Compare with the naive normalisation D / (R' e^{2 pi i z}), which
omits the constant mode.

Usage:  python3 docs/first_mode_check.py [dir ...]
"""

from __future__ import annotations

import json
import os
import sys

import mpmath as mp

sys.path.insert(0, "/Volumes/dream/halfexp/kneser/src")

from kneser._general import GeneralRegularEngine  # noqa: E402

ZS = ["0.5", "-0.5", "0.25", "0.5-0.5j"]
ROOT = "/Volumes/dream/halfexp/kneser/docs/_generated/separation"


def cval(s):
    return mp.mpc(mp.mpf(s[0]), mp.mpf(s[1]))


def rows(d):
    out = []
    for name in sorted(os.listdir(d)):
        if not name.endswith(".json"):
            continue
        with open(os.path.join(d, name)) as fh:
            r = json.load(fh)
        if "D" in r:
            r["_dir"] = d
            out.append(r)
    return sorted(out, key=lambda r: -r["b"][1])


def check(rec, digits=24):
    with mp.workdps(digits + 12):
        g = GeneralRegularEngine(rec["base"], digits)
        qs, ns = [], []
        for z in ZS:
            zz = mp.mpc(complex(z))
            _, dR = g.sexp(zz, derivative=True)
            D = cval(rec["D"][z])
            e = mp.exp(2j * mp.pi * zz)
            qs.append(D / (dR * (e - 1)))
            ns.append(D / (dR * e))
        return qs, ns


def main(dirs):
    for d in dirs:
        rs = rows(d)
        if not rs:
            continue
        print(f"\n=== {os.path.relpath(d, ROOT)}   ({len(rs)} points)")
        print("  with constant mode:  q(z) = D / (R' (e^{2pi i z} - 1))")
        print("  naive:               n(z) = D / (R' e^{2pi i z})")
        for rec in rs:
            if rec["absD"]["0.5"] < 1e3 * float(rec.get("residual_check", 1e-30)):
                continue
            qs, ns = check(rec)
            sq = max(abs(q) for q in qs) / min(abs(q) for q in qs)
            sn = max(abs(q) for q in ns) / min(abs(q) for q in ns)
            aq = max(float(mp.arg(q / qs[0])) for q in qs) - min(float(mp.arg(q / qs[0])) for q in qs)
            print(f"  y={rec['b'][1]:<8.4g} |q| " + " ".join(f"{float(abs(q)):.6e}" for q in qs) +
                  f"  spread {float(sq):.4f}")
            print(f"  {'':10} arg " + " ".join(f"{float(mp.arg(q)):+.6f}" for q in qs) +
                  f"  argspread {aq:.5f}   [naive spread {float(sn):.3f}]")


if __name__ == "__main__":
    args = sys.argv[1:]
    if not args:
        args = [os.path.join(ROOT, "post-fix-fine", x)
                for x in sorted(os.listdir(os.path.join(ROOT, "post-fix-fine")))]
    main(args)
