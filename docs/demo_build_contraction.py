"""Measure the per-loop contraction of the theta-mapping build (问题 4.4).

The Kneser builder (kneser.build) reports ~1.4 decimal digits of accuracy
gained per theta-iteration loop.  This demo treats that rate as an
experimental quantity: rerun the build at modest precision, varying one
parameter at a time -- the theta sampling height ``idelta``, the
linearization ``depth``, the target digit count -- record the
functional-equation residual after every loop, and fit the geometric
contraction rate in the clean regime between the seed transient and the
precision floor.

Candidate explanations compared against the measurement:

  e^-pi   per loop = 1.364 digits/loop   (lowest theta mode at height 1/2)
  e^-2pi*idelta    = 0.273 digits/loop at idelta = 0.1  (sampling height)
  band fraction 2*asin(idelta)/pi = 1.196 digits at idelta = 0.1

If the measured rate moves with idelta, the sampling height drives the
contraction; if it stays put, the rate is intrinsic to the construction.

Run:  PYTHONPATH=src python3 docs/demo_build_contraction.py [--digits 24] [--fast]
(full matrix takes a few minutes; --fast runs the two cheapest configs)
"""

import argparse
import dataclasses
import math

import mpmath as mp

import kneser.build as kb


def run_config(digits, label, **overrides):
    """Run the builder with selected BuildParams fields overridden."""
    p = kb.plan(digits)
    if "idelta" in overrides and "n_modes" not in overrides:
        # keep the mode count consistent with the new sampling height,
        # mirroring the formula in kneser.build.plan
        d = overrides["idelta"]
        overrides["n_modes"] = math.ceil(digits * math.log(10) / (2 * math.pi * d)) + 8
        overrides["nf"] = 2 * overrides["n_modes"] + 20
    p = dataclasses.replace(p, **overrides)
    orig_plan = kb.plan
    kb.plan = lambda d, **kwargs: p
    try:
        result = kb.build(digits, seed="carleman", verbose=False)
    finally:
        kb.plan = orig_plan
    return p, result


def fit_rate(residuals):
    """Mean digits/loop over the clean geometric regime, with spread."""
    logs = [float(mp.log10(r)) for r in residuals if r > 0]
    drops = [logs[i] - logs[i + 1] for i in range(len(logs) - 1)
             if -20.0 < logs[i + 1] and logs[i] < -8.0]
    if not drops:
        return None, None, 0
    mean = sum(drops) / len(drops)
    var = sum((d - mean) ** 2 for d in drops) / len(drops)
    return mean, math.sqrt(var), len(drops)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--digits", type=int, default=24)
    ap.add_argument("--fast", action="store_true", help="only the two cheapest configs")
    args = ap.parse_args()
    D = args.digits

    configs = [
        ("idelta=0.10 (default)", D, {}),
        ("idelta=0.20", D, {"idelta": 0.2}),
    ]
    if not args.fast:
        configs += [
            ("idelta=0.05", D, {"idelta": 0.05}),
            ("idelta=0.30", D, {"idelta": 0.3}),
            ("depth x2", D, {"depth": 2 * kb.plan(D).depth}),
            (f"digits={D + 12}", D + 12, {}),
        ]

    print(f"theta-iteration contraction rate, base digits={D} (carleman seed)\n")
    rows = []
    for label, digits, overrides in configs:
        p, result = run_config(digits, label, **overrides)
        rate, spread, n = fit_rate(result.residuals)
        logs = " ".join(f"{float(mp.log10(r)):.1f}" for r in result.residuals)
        print(f"[{label}]  loops={len(result.residuals) - 1}  "
              f"floor={mp.nstr(result.residual, 3)}  ({result.seconds:.0f}s)")
        print(f"  log10 residuals: {logs}")
        rows.append((label, p.idelta, rate, spread, n))
    print()

    print(f"{'config':<22} {'idelta':>6} {'digits/loop':>12} {'+-':>6} {'#ratios':>8}")
    for label, idelta, rate, spread, n in rows:
        r = "n/a" if rate is None else f"{rate:.3f}"
        s = "" if spread is None else f"{spread:.3f}"
        print(f"{label:<22} {idelta:>6.2f} {r:>12} {s:>6} {n:>8}")

    print()
    print("references:  e^-pi = {:.3f} digits/loop ; ".format(math.pi / math.log(10))
          + "e^-2pi*0.1 = {:.3f} ; ".format(2 * math.pi * 0.1 / math.log(10))
          + "band 2*asin(0.1)/pi = {:.3f}".format(-math.log10(2 * math.asin(0.1) / math.pi)))


if __name__ == "__main__":
    main()
