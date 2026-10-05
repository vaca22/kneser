"""The regular hyperoperation ladder as the rank s -> infinity, for 1 < b < eta.

Notation (docs/demo_rank_regular.py): S_s(z+1) = S_{s-1}(S_s(z)), S_s(0) = 1,
S_s = p_s + U_s(C_s lam_s**z) with p_s the attracting fixed point of S_{s-1}.
Write beta = b - 1, eps_s = p_s - b, q_s = lam_s**beta.

1.  The limit is the KINK  F_b(z) = min(1 + z, b),  not a step.
    F_b solves the successor fixed-point equation F(z+1) = F(F(z)), F(0) = 1:
        F(z+1) = min(2+z, b),   F(F(z)) = min(1 + min(1+z, b), b) = min(2+z, b).
    It is continuous and fails to be differentiable only at z = b - 1.

2.  A two-variable reduction.  Since S_s(1) = b and U_s(w) = w (1 + O(w)),
        S_s(z) = p_s - eps_s lam_s**(z-1) (1 + O(eps_s))        for z >= 1,
    and the next fixed point and multiplier follow:
        eps_{s+1} = eps_s (1 - lam_s**(beta + eps_{s+1}))           (R1)
        lam_{s+1} = eps_s lam_s**(beta + eps_{s+1}) |log lam_s|      (R2)
    each up to a relative O(eps_s).  The one-step test below feeds the TRUE
    (eps_s, lam_s) into (R1, R2) and compares with the true next level.

3.  Asymptotics of (R1, R2).  With q = lam**beta slowly varying, (R2) at
    quasi-equilibrium gives eps = beta q**(1/beta - 1) / |log q|, and (R1),
    Delta log eps = -q, then forces
        s q_s  ->  1/beta - 1 = (2 - b)/(b - 1),   correction ~ +1/log s,
    i.e.  lam_s ~ ((2-b)/((b-1) s))**(1/(b-1)),
          eps_s ~ (b-1) ((2-b)/((b-1) s))**((2-b)/(b-1)) / log s.
    The ladder approaches its limit algebraically, with exponents set by b.

Run:  PYTHONPATH=src python3 docs/demo_rank_limit.py                # b = 1.3, top 48
      PYTHONPATH=src python3 docs/demo_rank_limit.py --bases 1.1,1.2,1.3,1.4 --top 32
      PYTHONPATH=src python3 docs/demo_rank_limit.py --json out.json
"""

from __future__ import annotations

import argparse
import json
import sys
import time

import mpmath as mp

sys.path.insert(0, "docs")
from demo_rank_regular import Level  # noqa: E402

ZGRID = ["-0.9", "-0.5", "-0.1", "0.05", "0.1", "0.2", "0.3", "0.4", "0.5",
         "0.7", "0.9", "1.5", "2"]


def kink(z, b):
    return min(1 + z, b)


def ladder(b, top, K, report):
    levels, prev, t0 = [], None, time.time()
    for _ in range(4, top + 1):
        prev = Level(b, prev, K)
        levels.append(prev)
        if report and prev.s % 8 == 0:
            print(f"      rank {prev.s:>3} built  [{time.time() - t0:.0f}s]", flush=True)
    return levels


def reduced_step(b, eps, lam):
    """(R1, R2): next (eps, lam) from the current one."""
    beta = b - 1
    e_next = mp.findroot(lambda e: e - eps * (1 - mp.power(lam, beta + e)), eps)
    l_next = eps * mp.power(lam, beta + e_next) * abs(mp.log(lam))
    return e_next, l_next


def reduced_orbit(b, eps, lam, s0, s_end, marks):
    """Iterate (R1, R2) in logarithms, in floats: x = log eps, y = log lam."""
    import math
    out, s = {}, s0
    beta = float(b) - 1
    x, y = float(mp.log(eps)), float(mp.log(lam))
    while s < s_end:
        e = math.exp(x)
        e_next = e
        for _ in range(3):                    # eps_{s+1} in the exponent is o(1)
            e_next = e * -math.expm1((beta + e_next) * y)
        x_next = math.log(e_next)
        y = x + (beta + e_next) * y + math.log(-y)
        x = x_next
        s += 1
        if s in marks:
            out[s] = (mp.e ** x, mp.e ** y)
    return out


def rate_prediction(b, s):
    a = (2 - b) / (b - 1)
    L = mp.log(s)
    return a + 1 / L + (1 + mp.log(a)) / L ** 2


def analyse(b_str, top, K, verbose=True):
    b = mp.mpf(b_str)
    beta = b - 1
    target = (2 - b) / (b - 1)
    print("=" * 76)
    print(f"base b = {b_str}   beta = b-1 = {mp.nstr(beta, 4)}   "
          f"predicted lim s*q_s = (2-b)/(b-1) = {mp.nstr(target, 6)}")
    print("=" * 76)
    levels = ladder(b, top, K, verbose)
    res = {"base": b_str, "top": top, "levels": []}

    print("\n  1. distance to the kink  F_b(z) = min(1+z, b)  on the grid")
    print(f"     {'s':>3}  {'max|S_s - F_b|':>14}  {'at z':>5}  "
          + "  ".join(f"{z:>8}" for z in ("-0.5", "0.1", "0.5", "2")))
    for lev in levels:
        vals = {z: lev.S(mp.mpf(z)) for z in ZGRID}
        dev = {z: abs(vals[z] - kink(mp.mpf(z), b)) for z in ZGRID}
        zmax = max(dev, key=dev.get)
        rec = {"s": lev.s, "p": mp.nstr(lev.p, 20), "lam": mp.nstr(lev.lam, 20),
               "S": {z: mp.nstr(v, 15) for z, v in vals.items()},
               "max_dev": mp.nstr(dev[zmax], 5), "argmax": zmax}
        res["levels"].append(rec)
        if lev.s in (4, 6, 8, 12, 16, 24, 32, 40, 48, 64, 80, 96) or lev.s == top:
            print(f"     {lev.s:>3}  {mp.nstr(dev[zmax], 4):>14}  {zmax:>5}  "
                  + "  ".join(f"{mp.nstr(dev[z], 3):>8}"
                              for z in ("-0.5", "0.1", "0.5", "2")))

    print("\n  1b. the gap at the kink, g_s = b - S_s(b-1).  Linearising U_s, the")
    print("      exponents cancel exactly there: g_s ~ eps lam^(beta-1) ~ (b-1)/log s.")
    print(f"     {'s':>3}  {'g_s':>12}  {'g_s * log s':>12}   (-> b-1 = {mp.nstr(beta, 3)})")
    gaps = []
    for lev in levels:
        g = b - lev.S(beta)
        gaps.append((lev.s, g))
        if lev.s in (4, 8, 12, 16, 24, 32, 40, 48, 64) or lev.s == top:
            print(f"     {lev.s:>3}  {mp.nstr(g, 6):>12}  {mp.nstr(g * mp.log(lev.s), 6):>12}")
    res["kink_gap"] = [{"s": s, "g": mp.nstr(g, 10)} for s, g in gaps]

    print("\n  1c. concavity defect and monotonicity in the rank, grid z in [-0.95, 2.95]")
    print("      expected: S_s falls in s on (-1,0) and (1,inf), rises on (0,1)")
    h = mp.mpf(1) / 20
    zs = [mp.mpf(-19) / 20 + k * h for k in range(0, 79)]
    prev_vals, mono_bad, defects = None, 0, []
    for lev in levels:
        vals = [lev.S(z) for z in zs]
        d2, zat = max((vals[i - 1] - 2 * vals[i] + vals[i + 1], zs[i])
                      for i in range(1, len(vals) - 1))
        defects.append((lev.s, d2, zat))
        if prev_vals is not None:
            for z, v, w in zip(zs, vals, prev_vals):
                up = 0 < z < 1
                if abs(z) > h / 2 and abs(z - 1) > h / 2 and ((v > w) != up):
                    mono_bad += 1
        prev_vals = vals
    for s, d2, zat in defects:
        if s in (4, 6, 8, 16, 24, 32, 48) or s == top:
            print(f"     s = {s:>2}: max second difference {mp.nstr(d2, 3):>10} at z = {mp.nstr(zat, 3)}")
    print(f"     monotonicity violations: {mono_bad}")
    print("     The positive defect sits just right of z = -1 and decays with s, so")
    print("     the LIMIT is concave even though each S_s is not quite.")
    res["concavity_defect"] = [{"s": s, "d2": mp.nstr(d, 3), "z": mp.nstr(z, 3)}
                               for s, d, z in defects]
    res["monotone_violations"] = mono_bad

    print("\n  1d. the soft-min (Maslov dequantisation) form.  With L = |log lam|,")
    print("      U_s(w) -> -(1/L) log(1 - L w) as lam -> 0, which turns S_s into")
    print("          S_s(z) ~ -(1/L_s) log( exp(-L_s (1+z)) + exp(-L_s b) ),")
    print("      a log-sum-exp smoothing of min(1+z, b) at temperature 1/L_s.")
    print(f"     {'s':>3}  {'max|S-min|':>11}  {'max|S-softmin|':>14}  "
          f"{'max|S-closed U|':>15}  {'g_s L_(s-1)':>11}  (-> log 2 = 0.6931)")
    zs2 = [mp.mpf(k) / 20 for k in range(-18, 41)]
    soft = []
    for a, lev in zip(levels, levels[1:]):
        La, Ls = abs(mp.log(a.lam)), abs(mp.log(lev.lam))
        e0 = e1 = e2 = mp.mpf(0)
        for z in zs2:
            v = lev.S(z)
            e0 = max(e0, abs(v - kink(z, b)))
            e1 = max(e1, abs(v + mp.log(mp.exp(-Ls * (1 + z)) + mp.exp(-Ls * b)) / Ls))
            e2 = max(e2, abs(v - lev.p + mp.log(1 - La * lev.C * mp.power(lev.lam, z)) / La))
        gL = (b - lev.S(beta)) * La
        soft.append((lev.s, e0, e1, e2, gL))
        if lev.s in (6, 8, 12, 16, 24, 32, 40, 48) or lev.s == top:
            print(f"     {lev.s:>3}  {mp.nstr(e0, 4):>11}  {mp.nstr(e1, 4):>14}  "
                  f"{mp.nstr(e2, 4):>15}  {mp.nstr(gL, 6):>11}")
    res["softmin"] = [{"s": s, "to_min": mp.nstr(a, 4), "to_softmin": mp.nstr(c, 4),
                       "to_closed_U": mp.nstr(d, 4), "gap_times_L": mp.nstr(g, 6)}
                      for s, a, c, d, g in soft]

    print("\n  2. one-step test of the reduction (R1, R2), fed the TRUE level s")
    print(f"     {'s':>3}  {'eps_s':>10}  {'rel.err eps_s+1':>15}  "
          f"{'rel.err lam_s+1':>15}  {'(both)/eps_s':>12}")
    onestep = []
    for a, nxt in zip(levels, levels[1:]):
        if a.s < 6:
            continue
        e_pred, l_pred = reduced_step(b, a.p - b, a.lam)
        re = abs(e_pred / (nxt.p - b) - 1)
        rl = abs(l_pred / nxt.lam - 1)
        onestep.append((a.s, re, rl, max(re, rl) / (a.p - b)))
        if a.s in (6, 8, 12, 16, 24, 32, 40, 47, 63, 79, 95) or nxt.s == top:
            print(f"     {a.s:>3}  {mp.nstr(a.p - b, 3):>10}  {mp.nstr(re, 3):>15}  "
                  f"{mp.nstr(rl, 3):>15}  {mp.nstr(max(re, rl) / (a.p - b), 3):>12}")
    res["onestep"] = [{"s": s, "rel_eps": mp.nstr(x, 3), "rel_lam": mp.nstr(y, 3),
                       "ratio_to_eps": mp.nstr(r, 3)} for s, x, y, r in onestep]

    print("\n  3. the rate law  s * q_s -> (2-b)/(b-1),  q_s = lam_s**(b-1)")
    print(f"     {'s':>3}  {'s*q_s (ladder)':>15}  {'s*q_s (reduced orbit)':>21}")
    s0 = levels[2].s
    marks = set(l.s for l in levels) | {10**k for k in range(2, 8)} | \
        {3 * 10**k for k in range(2, 7)}
    orbit = reduced_orbit(b, levels[2].p - b, levels[2].lam, s0, 10**7, marks)
    law = []
    for lev in levels:
        sq = lev.s * mp.power(lev.lam, beta)
        so = lev.s * mp.power(orbit[lev.s][1], beta) if lev.s in orbit else None
        law.append((lev.s, sq, so))
        if lev.s in (8, 12, 16, 24, 32, 40, 48, 64, 80, 96) or lev.s == top:
            print(f"     {lev.s:>3}  {mp.nstr(sq, 8):>15}  "
                  f"{(mp.nstr(so, 8) if so is not None else ''):>21}")
    print("     reduced orbit continued (same start), against the two-term law")
    print("     a + 1/log s + (1 + log a)/log^2 s,  a = (2-b)/(b-1):")
    far = []
    for s in sorted(k for k in orbit if k > top):
        sq = s * mp.power(orbit[s][1], beta)
        pred = rate_prediction(b, s)
        far.append((s, sq, pred))
        print(f"     {s:>9}  s*q_s = {mp.nstr(sq, 8):>11}   law = {mp.nstr(pred, 8):>11}"
              f"   diff*log^3 s = {mp.nstr((sq - pred) * mp.log(s) ** 3, 4)}")
    res["rate_law"] = {"target": mp.nstr(target, 10),
                       "ladder": [{"s": s, "sq": mp.nstr(a, 10)} for s, a, _ in law],
                       "reduced": [{"s": s, "sq": mp.nstr(a, 10),
                                    "law": mp.nstr(p, 10)} for s, a, p in far]}
    return res


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--bases", default="1.3")
    ap.add_argument("--top", type=int, default=48)
    ap.add_argument("--dps", type=int, default=40)
    ap.add_argument("--terms", type=int, default=50)
    ap.add_argument("--json", default=None)
    args = ap.parse_args(argv)
    mp.mp.dps = args.dps
    out = [analyse(b, args.top, args.terms) for b in args.bases.split(",")]
    if args.json:
        with open(args.json, "w") as fh:
            json.dump(out, fh, indent=1)
        print(f"\nwrote {args.json}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
