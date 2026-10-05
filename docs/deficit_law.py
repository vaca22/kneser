"""How fast does the hyperbolic side converge to the parabolic horn map?

docs/separation-mode-two-zh.md leaves one number open: the exponent of the
deficits

    delta_1(b) = 1 - |c1hat(b)| / |B_1|,
    delta_2(b) = 1 - |c2hat(b)| / |B_2|,     c2hat = kappa_2 c1hat^2,

where B_1, B_2 are the modes of the reversed horn map h^{-1} of the parabolic
germ at b = eta.  Both vanish as b -> eta^-; the question is the power.

The natural variable is not obvious a priori, so the script reports the law in
all three candidates,

    eps = |log lambda|   (the multiplier scale, eps ~ sqrt(2 e (log eta - log b))),
    eta - b              (the distance in the base),
    lambda,

and fits the exponent both by consecutive local slopes and by a three-parameter
fit log delta = log C + p log x + a x that lets the local slope drift.

The structural expectation: near a saddle-node the analytic unfolding parameter
is the one in which the fixed points sit at +-sqrt(parameter), so it is
proportional to (log lambda)^2, i.e. to eta - b.  A correction linear in the
unfolding parameter therefore shows up as p = 2 in eps, p = 1 in eta - b.

Usage: python3 docs/deficit_law.py
"""

from __future__ import annotations

import json
import math
import os
import sys
from pathlib import Path

import mpmath as mp

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from c1_invariant import c1_of, richardson  # noqa: E402
from kneser._general import GeneralRegularEngine  # noqa: E402

ROOT = str(Path(__file__).resolve().parent / "_generated" / "separation")

# modes of h^{-1} at b = eta (docs/parabolic_horn_inverse.py, 21 digits stable)
B1 = mp.mpf("0.089058436412213331563")
B2 = mp.mpf("0.012487384111564700811")

# best ladder per base, plus alternates used only as a spread estimate
PRIMARY = [
    ("1.05", "post-fix/re1.05_d20_i0.10"),
    ("1.10", "post-fix/re1.1_d20_i0.10"),
    ("1.15", "post-fix/re1.15_d20_i0.10"),
    ("1.20", "out6/re1.2_d32_i0.10"),
    ("1.25", "out6/re1.25_d32_i0.10"),
    ("1.30", "out6/re1.3_d52_i0.10"),
    ("1.35", "out5/re1.35_d36_i0.10"),
    ("1.40", "out5/re1.4_d52_i0.10"),
]
ALTERNATE = {
    "1.05": ["post-fix/re1.05_d16_i0.10", "post-fix-fine/re1.05_fine"],
    "1.10": ["post-fix/re1.1_d16_i0.15", "post-fix-fine/re1.1_fine"],
    "1.15": ["post-fix/re1.15_d16_i0.15"],
    "1.20": ["out4/re1.2_d20_i0.10", "out5/re1.2_d32_i0.10"],
    "1.25": ["out4/re1.25_d24_i0.10", "out5/re1.25_d44_i0.10"],
    "1.30": ["out4/re1.3_d32_i0.10", "out5/re1.3_d52_i0.10"],
    "1.35": ["out4/re1.35_d36_i0.10"],
}

# kappa_2 at Im b = 0, from docs/kappa_ladder.py (modulus only; see that script)
KAPPA2 = {"1.05": "1.374049", "1.10": "1.440851", "1.15": "1.479111",
          "1.20": "1.505578", "1.25": "1.525582", "1.30": "1.541516"}
KAPPA2_ARG = {"1.05": "1.413420", "1.10": "1.477690", "1.15": "1.511255",
              "1.20": "1.533318", "1.25": "1.549420", "1.30": "1.561918"}

# Paulsen 2019, Section 5: Im kappa_{sqrt2^+}(1/2), 120-digit contour computation
PAULSEN_IM = ("-1.18899697185401045226976795872715599664e-48")


def lam_att(b):
    """attracting multiplier: log b = lam e^{-lam} with lam in (0,1), i.e.
    lam = -W_0(-log b)."""
    with mp.workdps(50):
        return -mp.lambertw(-mp.log(mp.mpf(b)), 0)


def sqrt2_name(digits=60):
    with mp.workdps(digits + 10):
        return mp.nstr(mp.sqrt(2), digits)


def ladder(dirname):
    """(|c1hat|, arg c1hat) extrapolated to Im b = 0, or None."""
    d = os.path.join(ROOT, dirname)
    if not os.path.isdir(d):
        return None
    ys, hats = [], []
    for name in sorted(os.listdir(d)):
        if not name.endswith(".json"):
            continue
        with open(os.path.join(d, name)) as fh:
            rec = json.load(fh)
        if "D" not in rec or rec["b"][1] <= 0:
            continue
        if abs(rec["b"][0] - float(dirname.split("re")[1].split("_")[0])) > 1e-9:
            continue          # the walk point of a neighbouring Re b
        noise = max(float(rec.get("residual_check", 0)), float(rec.get("residual", 0)))
        if rec["absD"]["0.5"] < 100 * noise:
            continue
        _, _, hat, _ = c1_of(rec)
        ys.append(mp.mpf(rec["b"][1]))
        hats.append(hat)
    if len(ys) < 2:
        return None
    order = sorted(range(len(ys)), key=lambda i: -ys[i])
    ys = [ys[i] for i in order]
    hats = [hats[i] for i in order]
    lin, quad = richardson(ys, hats)
    v = quad if quad is not None else lin
    return abs(v), mp.arg(v), len(ys)


def paulsen_point(arg_c1):
    """|c1hat| at b = sqrt(2) from Paulsen's imaginary part.

    D(1/2) = -2 c_1 R'(1/2) (first-mode law), R real on (1, eta), so
    Im D(1/2) = -2 |c_1| R'(1/2) sin(arg c_1): recovering |c_1| from the
    imaginary part alone needs arg c_1, and dropping the sine (i.e. assuming
    c_1 purely imaginary) underestimates |c_1| by 1/sin(arg c_1).
    """
    with mp.workdps(60):
        g = GeneralRegularEngine(sqrt2_name(), 40)
        _, dR = g.sexp(mp.mpf("0.5"), derivative=True)
        dR = mp.re(dR)
        lu = lam_att(mp.sqrt(2))
        Lam = mp.exp(4 * mp.pi**2 / mp.log(lu))
        imD = abs(mp.mpf(PAULSEN_IM))
        naive = imD / (2 * dR * Lam)
        return naive, naive / mp.sin(arg_c1), lu


def fit_power(xs, ds):
    """least squares log d = log C + p log x, and the 3-parameter drifting fit."""
    import numpy as np
    X = np.array([[1.0, math.log(x)] for x in xs])
    y = np.array([math.log(d) for d in ds])
    (lc, p), *_ = np.linalg.lstsq(X, y, rcond=None)
    res = y - X @ np.array([lc, p])
    X3 = np.array([[1.0, math.log(x), x] for x in xs])
    (lc3, p3, a3), *_ = np.linalg.lstsq(X3, y, rcond=None)
    res3 = y - X3 @ np.array([lc3, p3, a3])
    return (p, math.exp(lc), float(np.sqrt((res**2).mean())),
            p3, math.exp(lc3), a3, float(np.sqrt((res3**2).mean())))


def main():
    eta = mp.e ** (1 / mp.e)
    print(f"eta = {mp.nstr(eta, 17)}   |B1| = {mp.nstr(B1, 12)}   |B2| = {mp.nstr(B2, 12)}\n")
    rows = []
    for tag, d in PRIMARY:
        got = ladder(d)
        if got is None:
            print(f"  {tag}: no usable ladder in {d}")
            continue
        c1h, arg1, n = got
        lu = lam_att(tag)
        eps = abs(mp.log(lu))
        gap = eta - mp.mpf(tag)
        d1 = 1 - c1h / B1
        alt = []
        for a in ALTERNATE.get(tag, []):
            g2 = ladder(a)
            if g2:
                alt.append(float(g2[0]))
        spread = (max(alt + [float(c1h)]) - min(alt + [float(c1h)])) if alt else 0.0
        d2 = None
        if tag in KAPPA2:
            c2h = mp.mpf(KAPPA2[tag]) * c1h**2
            d2 = 1 - c2h / B2
        rows.append(dict(tag=tag, lam=lu, eps=eps, gap=gap, c1h=c1h, arg1=arg1,
                         d1=d1, d2=d2, n=n, spread=spread))
        print(f"  b={tag}  lam={float(lu):.6f}  eps={float(eps):.5f}  eta-b={float(gap):.5f}  "
              f"|c1hat|={float(c1h):.8f} (arg {float(arg1):.6f}, {n} rungs, "
              f"spread {spread:.1e})  delta1={float(d1):.6f}"
              + (f"  delta2={float(d2):.6f}" % () if d2 is not None else ""))

    # --- the sqrt(2) point -------------------------------------------------
    args = [(float(r["gap"]), float(r["arg1"])) for r in rows]
    # arg c1hat is smooth in b; extrapolate linearly in (eta - b) from the two
    # closest bases to eta
    args.sort()
    (x1, a1), (x2, a2) = args[0], args[1]
    gap_s = float(eta - mp.sqrt(2))
    arg_s = a1 + (a2 - a1) * (gap_s - x1) / (x2 - x1)
    naive, corrected, lu2 = paulsen_point(mp.mpf(arg_s))
    print(f"\n  b=sqrt(2)  lam={float(lu2):.6f}  eps={float(abs(mp.log(lu2))):.5f}  "
          f"eta-b={gap_s:.5f}")
    print(f"     arg c1 extrapolated  = {arg_s:.6f}  (pi/2 = {float(mp.pi/2):.6f})")
    print(f"     |c1hat| from Im D alone   = {float(naive):.8f}   delta1 = "
          f"{float(1 - naive/B1):.6f}")
    print(f"     |c1hat| with the sin(arg) = {float(corrected):.8f}   delta1 = "
          f"{float(1 - corrected/B1):.6f}   <-- used below")
    rows.append(dict(tag="sqrt2", lam=lu2, eps=abs(mp.log(lu2)), gap=eta - mp.sqrt(2),
                     c1h=corrected, arg1=mp.mpf(arg_s), d1=1 - corrected / B1,
                     d2=None, n=1, spread=float(corrected - naive)))

    for r in rows:
        r["one_minus_lam"] = 1 - r["lam"]
    for key, label in (("eps", "eps = |log lambda|"), ("one_minus_lam", "1 - lambda"),
                       ("gap", "eta - b")):
        print(f"\n=== delta_1 as a function of {label}")
        xs = [float(r[key]) for r in rows]
        ds = [float(r["d1"]) for r in rows]
        print("   x          delta_1      delta/x     delta/x^2    local slope")
        for i, r in enumerate(rows):
            x, dd = xs[i], ds[i]
            slope = ""
            if i + 1 < len(rows):
                slope = f"{math.log(ds[i+1]/dd)/math.log(xs[i+1]/x):+.4f}"
            print(f"   {x:9.5f}  {dd:.7f}  {dd/x:.6f}   {dd/x**2:.6f}    {slope}")
        p, C, rms, p3, C3, a3, rms3 = fit_power(xs, ds)
        print(f"   power fit      : delta = {C:.5f} x^{p:.4f}          (log-RMS {rms:.4f})")
        print(f"   drifting fit   : delta = {C3:.5f} x^{p3:.4f} e^{{{a3:+.4f} x}}  "
              f"(log-RMS {rms3:.4f})")

    # --- is the exponent exactly 2 in eps? --------------------------------
    import numpy as np
    xs = np.array([float(r["eps"]) for r in rows])
    ds = np.array([float(r["d1"]) for r in rows])
    print("\n=== is p = 2 in eps?  (fits of log delta)")

    def fit(cols, fixed=0.0, tag=""):
        X = np.array([[f(x) for f in cols] for x in xs])
        y = np.log(ds) - fixed * np.log(xs)
        sol, *_ = np.linalg.lstsq(X, y, rcond=None)
        rms = float(np.sqrt(((y - X @ sol) ** 2).mean()))
        print(f"   {tag:<46} RMS {rms:.5f}   " +
              "  ".join(f"{v:+.5f}" for v in sol))
        return sol, rms

    fit([lambda x: 1.0, np.log, lambda x: x], tag="free p:  C x^p e^{a x}       (C,p,a)")
    fit([lambda x: 1.0, lambda x: x], fixed=2.0, tag="p := 2:  C x^2 e^{a x}       (log C, a)")
    fit([lambda x: 1.0, lambda x: x, lambda x: x * x], fixed=2.0,
        tag="p := 2:  C x^2 e^{a x + b x^2} (log C, a, b)")
    fit([lambda x: 1.0, np.log, lambda x: x, lambda x: x * x],
        tag="free p:  C x^p e^{a x + b x^2} (C,p,a,b)")
    fit([lambda x: 1.0, lambda x: x], fixed=1.75,
        tag="p := 7/4: C x^1.75 e^{a x}     (log C, a)")
    # sensitivity to the sqrt(2) convention
    ds_naive = ds.copy()
    ds_naive[-1] = float(1 - naive / B1)
    for label, dd in (("with sin(arg) correction", ds), ("Im D alone", ds_naive)):
        X = np.array([[1.0, math.log(x), x] for x in xs])
        sol, *_ = np.linalg.lstsq(X, np.log(dd), rcond=None)
        print(f"   free-p exponent, sqrt(2) point via {label:<26}: p = {sol[1]:.4f}")
    X = np.array([[1.0, math.log(x), x] for x in xs[:-1]])
    sol, *_ = np.linalg.lstsq(X, np.log(ds[:-1]), rcond=None)
    print(f"   free-p exponent, sqrt(2) point dropped entirely      : p = {sol[1]:.4f}")

    print("\n=== deficit of the invariant kappa_2 against the deficit of c_1")
    K2INF = mp.mpf("1.5744226855297069304")
    prev = None
    for r in rows:
        if r["tag"] in KAPPA2:
            dk = 1 - mp.mpf(KAPPA2[r["tag"]]) / K2INF
            print(f"   b={r['tag']}  deficit(kappa2) = {float(dk):.6f}   "
                  f"/ delta1 = {float(dk / r['d1']):.4f}"
                  + (f"   (increment {float(dk/r['d1']) - prev:+.4f})" if prev else ""))
            prev = float(dk / r["d1"])
    seq = [float((1 - mp.mpf(KAPPA2[r["tag"]]) / K2INF) / r["d1"])
           for r in rows if r["tag"] in KAPPA2]
    if len(seq) >= 3:
        a, b, c = seq[-3:]
        aitken = c - (c - b) ** 2 / ((c - b) - (b - a))
        print(f"   Aitken extrapolation of the ratio: {aitken:.4f}   (3 ?)")
        seq2 = [float(r["d2"] / r["d1"]) for r in rows if r["d2"] is not None]
        a, b, c = seq2[-3:]
        print(f"   same for delta_2/delta_1:          "
              f"{c - (c - b) ** 2 / ((c - b) - (b - a)):.4f}   (5 = 3 + 2 ?)")

    print("\n=== one complex number: is the correction a common relative factor?")
    print("   model: the cylinder germ at finite lambda has a_2 -> a_2 (1+s) and")
    print("   a_3 -> a_3 (1+s) with the SAME complex s (so delta_1 = -Re s), whence")
    print("   1 - kappa_2/kappa_2^inf = P s,  P = (1-rho)/(1/2-rho).")
    print("   Test: q := (1 - kappa_2/kappa_2^inf)/delta_1 must satisfy Re(q/P) -> -1.")
    print("   Values near +1 contradict this common-factor model; they do not validate it.")
    RHO = mp.mpc("0.249455254258832068", "-0.0040298816383506416")
    K2INF_C = mp.mpc("-0.02532049309975755123", "1.5742190652319516267")
    P = (1 - RHO) / (mp.mpf("0.5") - RHO)
    print(f"   P = {mp.nstr(P, 9)}   |P| = {float(abs(P)):.6f}")
    for r in rows:
        if r["tag"] not in KAPPA2_ARG:
            continue
        k2 = mp.mpf(KAPPA2[r["tag"]]) * mp.exp(1j * mp.mpf(KAPPA2_ARG[r["tag"]]))
        q = (1 - k2 / K2INF_C) / r["d1"]
        qp = q / P
        print(f"   b={r['tag']}  Re(q/P) = {float(mp.re(qp)):.5f}   "
              f"Im(q/P) = {float(mp.im(qp)):.5f}   (common-factor target: Re -> -1)")

    print("\n=== delta_2 (mode 2), same treatment")
    r2 = [r for r in rows if r["d2"] is not None]
    for key, label in (("eps", "eps"), ("gap", "eta - b")):
        xs = [float(r[key]) for r in r2]
        ds = [float(r["d2"]) for r in r2]
        p, C, rms, p3, C3, a3, rms3 = fit_power(xs, ds)
        print(f"   in {label:<8}: power {p:.4f} (RMS {rms:.4f})   drifting {p3:.4f} "
              f"(RMS {rms3:.4f})   ratios delta2/delta1: "
              + " ".join(f"{float(r['d2']/r['d1']):.2f}" for r in r2))


if __name__ == "__main__":
    main()
