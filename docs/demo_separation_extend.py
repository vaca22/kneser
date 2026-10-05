"""Extend the separation ladders to Re b = 1.20, 1.25, 1.30 (towards eta).

The existing post-fix data covers Re b in {1.05, 1.10, 1.15}.  The invariant

    c1hat(b) = lim_{y->0+} D(b+iy) / (-2 R'(1/2) Lambda(b+iy)),
    Lambda = exp(4 pi^2 / log lambda_up),

needs the other end of (1, eta) to be mapped: Lambda collapses like
exp(-4 pi^2 / sqrt(2 e (log eta - log b))) as b -> eta, so each further step
costs digits.  Budget (|D| ~ 0.09 * 2 * R'(1/2) * |Lambda|):

    Re b   |Lambda|     |D| approx   digits needed for snr ~ 1e6
    1.20   2.2e-12      7e-14        20
    1.25   7.9e-15      2.6e-16      24
    1.30   2.7e-18      1.0e-19      32

Seeds: chain horizontally at y = 0.1 from the existing 1.15+0.1j seed, then
descend each vertical ladder as run_decay does.

Run on galic only:
  cd /data/kneser-exp/separation
  PYTHONPATH=/data/kneser-verify/src KNESER_CACHE=/data/kneser-verify/.cache \\
  nohup python3 demo_separation_extend.py --re 1.20 --digits 20 --out out4 &
"""

from __future__ import annotations

import argparse
import json
import os
import sys

import mpmath as mp

import demo_base_separation as S

IMS = [0.08, 0.05, 0.03, 0.02, 0.015, 0.01, 0.007, 0.005]


def step_to(re_b, seed, digits, outdir, n_loops, re0=1.15, tag=None, log=print, step=0.05):
    """Walk re0 -> re_b at y = 0.1 in steps of `step` (the last one lands exactly)."""
    y0 = 0.1
    re = re0
    tag = tag or f"seed:{re0}+0.1j.json"
    while re < re_b - 1e-9:
        re = round(min(re + step, re_b), 10)
        b = complex(re, y0)
        path = os.path.join(outdir, f"{S.bname(b)}.json")
        if os.path.exists(path):
            d = json.load(open(path))
            seed, tag = S.coeffs_of(d), S.bname(b)
            log(f"  walk {S.bname(b)}: cached")
            continue
        d, seed = S.build_point(b, seed, digits, n_loops=n_loops)
        d["seed_from"] = tag
        S.save(d, path)
        tag = S.bname(b)
        log(f"  walk {S.bname(b)}: residual {d['residual']} loops {d['loops']} {d['seconds']}s "
            f"|D(1/2)| {d.get('absD', {}).get('0.5')}")
    return seed, tag


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--re", type=float, required=True)
    ap.add_argument("--digits", type=int, default=20)
    ap.add_argument("--idelta", type=float, default=0.10)
    ap.add_argument("--loops", type=int, default=200)
    ap.add_argument("--dps", type=int, default=0, help="value-extraction precision (default 2*digits+20)")
    ap.add_argument("--ims", default=",".join(str(v) for v in IMS))
    ap.add_argument("--out", default="out4")
    ap.add_argument("--seed", default="seeds/1.15+0.1j.json")
    args = ap.parse_args()

    S.IDELTA = args.idelta
    S.DPS = args.dps or (2 * args.digits + 20)
    outdir = os.path.join(args.out, f"re{args.re}_d{args.digits}_i{args.idelta:.2f}")
    os.makedirs(outdir, exist_ok=True)
    print(f"# extend: Re b = {args.re} digits {args.digits} idelta {args.idelta} DPS {S.DPS}", flush=True)

    seed = S.load_seed(args.seed)
    with open(args.seed) as fh:
        re0 = json.load(fh).get("b", [1.15, 0.1])[0]
    print(f"# walk starts at Re b = {re0} (seed {args.seed})", flush=True)
    seed, tag = step_to(args.re, seed, args.digits, outdir, args.loops,
                        re0=re0, tag=f"seed:{os.path.basename(args.seed)}")

    for y in [float(v) for v in args.ims.split(",")]:
        b = complex(args.re, y)
        path = os.path.join(outdir, f"{S.bname(b)}.json")
        if os.path.exists(path):
            d = json.load(open(path))
            seed, tag = S.coeffs_of(d), S.bname(b)
            print(f"  {S.bname(b)}: cached |D(1/2)| {d.get('absD', {}).get('0.5')}", flush=True)
            continue
        try:
            d, seed = S.build_point(b, seed, args.digits, n_loops=args.loops)
        except Exception as exc:     # noqa: BLE001
            print(f"  {S.bname(b)}: FAILED {exc}", flush=True)
            break
        d["seed_from"] = tag
        S.save(d, path)
        tag = S.bname(b)
        print(f"  {S.bname(b)}: residual {d['residual']} check {d['residual_check']} "
              f"loops {d['loops']} {d['seconds']}s "
              + " ".join(f"|D({z})| {d['absD'][z]:.3e}" for z in S.ZS if "absD" in d), flush=True)


if __name__ == "__main__":
    sys.exit(main())
