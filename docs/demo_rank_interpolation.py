"""Rank-continuation screen: the s = 1..6 anchors, and what they do to Bennett.

The open direction of `essay-rank-1000-zh.md` is to make the RANK s of
`a[s]b` a continuous (ideally complex) variable.  Five criteria were listed
there for an acceptable `a[s]b`:

    C1  s = 1,2,3,4 give +, *, ^, tetration (Kneser solution at s = 4)
    C2  2[s]2 = 4 for every s >= 1
    C3  analytic in s
    C4  compatible with a[s](b+1) = a[s-1](a[s]b)
    C5  NOT the Bennett family, i.e. non-commutative for s >= 3

The only classical family that is analytic in the rank is Bennett (1915),

    B_s(a,b) = exp^[s-1]( log^[s-1] a + log^[s-1] b ).

"Bennett is commutative, hence wrong from rank 3 on" is the textbook
objection (C5).  This script runs the *numerical* screen instead, on the
anchors this repository actually owns, and finds that C5 is not even the
binding constraint: Bennett fails C1/C2 quantitatively, and on the anchor
point it fails a prior test -- it is not DEFINED there.

Two things here are new relative to the textbook objection:

1.  The iterated logarithm is implemented with this repository's continuous
    `exp^[t]` (Kneser), i.e. Bennett is given its most generous possible
    reading -- real rank, not just integer rank.  Even so its domain is
    `min(a,b) > sexp(s-3)`: the region where rank s is defined at all runs
    away like a tower.  At s = 6 it needs `min(a,b) > 3814279.1`, at
    s = 7 `min(a,b) > 10^1656520`.
2.  Where Bennett IS defined, its rank-4 member undershoots tetration by a
    whole level of the ladder: `slog B_4(a,a) ~ 3` while the true
    `slog(a[4]a) ~ a`.

Anchor column: `(a,b) = (e, 1/2)`, the one point where all six ranks are
computable in this repository.

    s=1,2,3   closed form
    s=4       kneser (Kneser tetration, 30 digits)
    s=5       regular/Koenigs pentation, docs/demo_upper_half_pen.py (~4 s)
    s=6       hexation, docs/demo_hexation_build.py (~70 s, --build6)

Run:  PYTHONPATH=src python3 docs/demo_rank_interpolation.py
      PYTHONPATH=src python3 docs/demo_rank_interpolation.py --build6
      PYTHONPATH=src python3 docs/demo_rank_interpolation.py --json out.json
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys

import mpmath as mp

import kneser

sys.path.insert(0, "docs")

# docs/demo_hexation_build.py, --loops 7 --nt 24 --nf 32 --ncirc 96 --modes 10
# --dps 35 (66 s); the higher-resolution run of section 4.14 gives
# 1.6194230799080.  The spread, 8.2e-9, is the honest error bar.
HEXATION_HALF = "1.61942307168215529"
HEXATION_ERR = "8.2e-9"


# --------------------------------------------------------------------------
# A.  the anchors
# --------------------------------------------------------------------------
def anchors(dps, build6):
    """A(s) = e[s](1/2) for s = 1..6, with an error bar on each."""
    a, b = mp.e, mp.mpf(1) / 2
    rows = [
        (1, "a + b", a + b, mp.mpf(10) ** (-dps + 2)),
        (2, "a * b", a * b, mp.mpf(10) ** (-dps + 2)),
        (3, "a ** b", a ** b, mp.mpf(10) ** (-dps + 2)),
        (4, "e^^(1/2)  Kneser", mp.mpf(kneser.hp.sexp("0.5", dps=dps)),
         mp.mpf(10) ** (-dps + 4)),
    ]

    from demo_upper_half_pen import PentationUpper          # noqa: E402
    pen = PentationUpper(base="e", dps=max(25, dps))
    p_half = mp.mpc(pen(mp.mpf("0.5"))).real
    rows.append((5, "e^^^(1/2)  regular", p_half, mp.mpf("1e-14")))

    if build6:
        out = subprocess.run(
            [sys.executable, "docs/demo_hexation_build.py", "--loops", "7",
             "--nt", "24", "--nf", "32", "--ncirc", "96", "--modes", "10",
             "--dps", "35"],
            capture_output=True, text=True, check=True).stdout
        line = [l for l in out.splitlines() if "e^^^^(1/2)" in l][0]
        h_half = mp.mpf(line.split("=")[1].strip())
    else:
        h_half = mp.mpf(HEXATION_HALF)
    rows.append((6, "e^^^^(1/2)  theta", h_half, mp.mpf(HEXATION_ERR)))
    return rows


# --------------------------------------------------------------------------
# B.  Bennett, with real rank
# --------------------------------------------------------------------------
def bennett(s, a, b):
    """B_s(a,b) = exp^[s-1](log^[s-1] a + log^[s-1] b), Kneser exp^[t].

    Raises ValueError when either iterated logarithm leaves the domain.
    """
    t = float(s) - 1.0
    la = kneser.exp_iter(float(a), -t)
    lb = kneser.exp_iter(float(b), -t)
    return kneser.exp_iter(la + lb, t)


def rank_ceiling(x):
    """Largest s with log^[s-1] x defined:  s < slog(x) + 3.

    exp^[t](x) = sexp(slog(x)+t) needs slog(x)+t > -2, and t = -(s-1).
    """
    return kneser.slog(float(x)) + 3.0


def ceiling_check(x):
    """Bisect the true failure point of exp_iter, to confirm the formula."""
    lo, hi = 1.0, 40.0                      # s known good / known bad
    for _ in range(60):
        mid = (lo + hi) / 2
        try:
            bennett(mid, x, x)
            lo = mid
        except (ValueError, ZeroDivisionError, OverflowError):
            hi = mid
    return lo


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=30)
    ap.add_argument("--build6", action="store_true",
                    help="re-run demo_hexation_build.py (~70 s)")
    ap.add_argument("--json", default=None)
    args = ap.parse_args(argv)
    mp.mp.dps = args.dps + 10

    print("=" * 72)
    print("A.  anchors   A(s) = e[s](1/2),  s = 1..6")
    print("=" * 72)
    rows = anchors(args.dps, args.build6)
    print(f"  {'s':>2}  {'A(s)':<26} {'+/-':<10}  source")
    for s, name, v, err in rows:
        print(f"  {s:>2}  {mp.nstr(v, 17):<26} {mp.nstr(err, 2):<10}  {name}")

    print("\n  finite differences A(s+1) - A(s)   [the shape any candidate")
    print("  interpolation must reproduce; note the sign change at s=2]")
    for i in range(len(rows) - 1):
        d = rows[i + 1][2] - rows[i][2]
        print(f"    A({rows[i+1][0]}) - A({rows[i][0]})  = {mp.nstr(d, 12):>18}")
    print("\n  s >= 3 is monotone DECREASING, but the differences are not")
    print("  geometric (-2.4e-3, -1.4e-2, -1.3e-2): the s=3 -> 4 step is the")
    print("  SMALLEST, so no naive extrapolation to s = infinity is available")
    print("  from these six points.  The s=1 -> 2 -> 3 stretch is not monotone.")

    print("\n" + "=" * 72)
    print("B.  Bennett B_s(a,b) = exp^[s-1](log^[s-1]a + log^[s-1]b)")
    print("    with Kneser exp^[t]: real rank, the most generous reading")
    print("=" * 72)
    print("  sanity, the two ranks Bennett is supposed to own:")
    for s, a, b, want, lab in ((1, mp.e, mp.mpf("0.5"), mp.e + mp.mpf("0.5"), "a+b"),
                               (2, mp.e, mp.mpf("0.5"), mp.e / 2, "a*b")):
        got = bennett(s, a, b)
        print(f"    B_{s}(e,1/2) = {got!r:<22} {lab}   |err| = "
              f"{mp.nstr(abs(mp.mpf(got) - want), 3)}")

    print("\n  domain.  exp^[t](x) needs slog(x) + t > -2, t = -(s-1), so")
    print("           B_s(a,b) exists  <=>  s < slog(min(a,b)) + 3.")
    print(f"    {'x':>12}  {'slog(x)':>12}  {'formula':>10}  {'bisected':>10}")
    for x in ("0.5", "2", "e", "15.154", "3814279.1"):
        xv = mp.e if x == "e" else mp.mpf(x)
        print(f"    {x:>12}  {kneser.slog(float(xv)):>12.6f}"
              f"  {rank_ceiling(xv):>10.6f}  {ceiling_check(xv):>10.6f}")

    print("\n  so to reach rank s at all, Bennett needs min(a,b) > sexp(s-3):")
    for s in (4, 5, 6, 7):
        need = mp.mpf(kneser.hp.sexp(str(s - 3), dps=20))
        if need > mp.mpf("1e15"):
            print(f"    s = {s}:  min(a,b) > 10^{mp.nstr(mp.log10(need), 8)}")
        else:
            print(f"    s = {s}:  min(a,b) > {mp.nstr(need, 12)}")
    print("    s = 1000: min(a,b) > sexp(997), a tower of 997 exponentials.")
    print("    The domain runs away up the ladder it is supposed to climb.")

    print("\n" + "=" * 72)
    print("C.  Bennett against the anchors")
    print("=" * 72)
    ceil_anchor = rank_ceiling(mp.mpf("0.5"))
    print(f"  anchor point (a,b) = (e, 1/2): min = 1/2, ceiling s < "
          f"{ceil_anchor:.6f}")
    verdict_c = {}
    for s, name, v, _err in rows:
        try:
            got = bennett(s, mp.e, mp.mpf("0.5"))
            rel = abs(mp.mpf(got) - v) / abs(v)
            verdict_c[s] = mp.nstr(mp.mpf(got), 12)
            print(f"    s = {s}:  B_s = {got!r:<22} anchor {mp.nstr(v,12):<16}"
                  f" rel.err {mp.nstr(rel, 3)}")
        except (ValueError, ZeroDivisionError, OverflowError) as exc:
            verdict_c[s] = "undefined"
            print(f"    s = {s}:  UNDEFINED  ({str(exc).split(':')[-1].strip()})")
    print("  4 of the 6 anchors are outside Bennett's domain -- it is not")
    print("  wrong there, it does not exist there.  C1 fails before C5.")

    print("\n  where it does exist, rank 3 (a point with min > 1):")
    for a, b in ((2, 3), (3, 2), (3, 3), (10, 10)):
        got = bennett(3, a, b)
        true = mp.mpf(a) ** b
        print(f"    B_3({a},{b}) = {got!r:<22} a^b = {mp.nstr(true,12):<14}"
              f" ratio {mp.nstr(mp.mpf(got)/true, 6)}")
    print("    B_3(2,3) = B_3(3,2) by construction; 2^3 = 8 != 9 = 3^2.  C5 fails.")

    print("\n" + "=" * 72)
    print("D.  C2:  2[s]2 = 4 ?")
    print("=" * 72)
    print("  true ladder: a[s]2 = a[s-1]a forces 2[s]2 = 2[s-1]2 = ... = 4,")
    print("  an identity, no numerics needed.  Bennett:")
    dev, c2 = mp.mpf(0), {}
    for s in ("1", "1.5", "2", "2.5", "3", "3.5", "3.7"):
        sv = mp.mpf(s)
        try:
            got = mp.mpf(bennett(sv, 2, 2))
            dev = max(dev, abs(got - 4))
            c2[s] = mp.nstr(got, 12)
            print(f"    B_{s:<4}(2,2) = {mp.nstr(got, 15):<20} 4 - B = "
                  f"{mp.nstr(4 - got, 6)}")
        except (ValueError, ZeroDivisionError, OverflowError):
            c2[s] = "undefined"
            print(f"    B_{s:<4}(2,2) = UNDEFINED   (ceiling "
                  f"{rank_ceiling(2):.4f})")
    print(f"  max deviation from 4 on the defined range: {mp.nstr(dev, 6)}")
    print("  It touches 4 only at s = 1, 2.  C2 fails on (1,2) as well as above 2.")

    print("\n" + "=" * 72)
    print("E.  C1 at rank 4:  how far below tetration is B_4?")
    print("=" * 72)
    print("  B_4(a,a) itself overflows a float, so measure its HEIGHT: the")
    print("  exact identity slog(exp^[t]x) = slog(x) + t gives")
    print("      height B_4(a,a) = slog(2 * log^[3] a) + 3,")
    print("  no evaluation of the huge value needed.  a[4]a = a^a^...^a is a")
    print("  tower of height a (base a; height counting is base-independent")
    print("  up to O(1) for a > e).")
    print(f"    {'a':>12}  {'height B_4(a,a)':>17}  {'height a[4]a':>14}")
    for a in ("3814280", "1e10", "1e100"):
        av = mp.mpf(a)
        inner = 2 * mp.mpf(kneser.exp_iter(float(av), -3.0))
        h_b = kneser.slog(float(inner)) + 3.0
        print(f"    {a:>12}  {h_b:>17.6f}  {a:>14}")
    print("  B_4's height stays below 4.2 even for a = 1e100, while the true")
    print("  rank-4 value is a")
    print("  tower of height a.  Bennett's 'rank 4' is not tetration's size")
    print("  class at all -- it is exp of a rank-3-ish quantity.")

    print("\n" + "=" * 72)
    print("VERDICT on Bennett (1915) against the five criteria")
    print("=" * 72)
    print("""  C1  s=1,2 exact; s=3 wrong (ratio 0.12 at (3,3)); s=4 wrong by a
      whole level of the ladder; s>=3 UNDEFINED at the anchor point.  FAIL
  C2  2[s]2 = 4 only at s = 1 and s = 2.                             FAIL
  C3  analytic in s where defined (Kneser exp^[t] is).               PASS
  C4  no recursion a[s](b+1) = a[s-1](a[s]b) -- Bennett is built by
      conjugation, not by iteration.                                 FAIL
  C5  commutative by construction.                                   FAIL

  Bennett is screened out 4-1.  Note WHICH failure is binding: the usual
  objection is C5, but the domain result (min(a,b) > sexp(s-3)) kills it
  earlier and more decisively -- a rank-continuous operation whose domain
  escapes up the ladder cannot be evaluated where the anchors live.

  Consequence for the search: any candidate must be tested for DOMAIN
  first.  A conjugation-by-exp^[s] construction inherits this defect
  generically, because log^[s] of a bounded argument dies at s ~ slog + 3.
  That is a structural hint, not just a fact about Bennett.""")

    if args.json:
        payload = {
            "anchor_point": {"a": "e", "b": "1/2"},
            "anchors": [{"s": s, "value": mp.nstr(v, 17),
                         "error": mp.nstr(e, 3), "source": n}
                        for s, n, v, e in rows],
            "bennett_at_anchor": verdict_c,
            "bennett_2_2": c2,
            "bennett_domain": "s < slog(min(a,b)) + 3",
            "verdict": {"C1": "fail", "C2": "fail", "C3": "pass",
                        "C4": "fail", "C5": "fail"},
        }
        with open(args.json, "w") as fh:
            json.dump(payload, fh, indent=2)
        print(f"\nwrote {args.json}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
