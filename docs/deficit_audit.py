"""Reproducible sensitivity audit of the *conjectural* quadratic deficit law.

The bundled snapshot contains inputs to the first-mode estimator, not rebuilt
Kneser coefficients or certified error bounds. No remote machine is required.

    python docs/deficit_audit.py --output docs/data/deficit-audit.json
    python docs/deficit_audit.py --export-inputs /path/to/raw/separation

Fits are diagnostics for deterministic numerical data. Their residuals and
leave-one-out errors are neither confidence intervals nor asymptotic proofs.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import sys

import mpmath as mp
import numpy as np

DOCS = Path(__file__).resolve().parent
sys.path.insert(0, str(DOCS))
from c1_invariant import c1_of, richardson  # noqa: E402
from deficit_law import ALTERNATE, PRIMARY, lam_att, paulsen_point  # noqa: E402

DEFAULT_INPUT = DOCS / "data" / "separation-first-mode-inputs.json"
# Keep decimal strings until entering the working precision context.
B1_ABS = "0.089058436412213331563"
FIELDS = ("base", "b", "digits", "D", "absD", "residual", "residual_check",
          "loop_limit_reached")


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def export_inputs(root, target):
    """Extract the exact fields used, retaining each original file's digest."""
    root = Path(root)
    ladders = dict((directory, base) for base, directory in PRIMARY)
    ladders.update((directory, base) for base, dirs in ALTERNATE.items()
                   for directory in dirs)
    records = []
    for directory, base in sorted(ladders.items()):
        for path in sorted((root / directory).glob("*.json")):
            raw = json.loads(path.read_text())
            if "D" not in raw or raw["b"][1] <= 0:
                continue
            if abs(raw["b"][0] - float(base)) > 1e-9:
                continue
            records.append({"path": path.relative_to(root).as_posix(),
                            "original_sha256": digest(path),
                            "data": {key: raw[key] for key in FIELDS if key in raw}})
    snapshot = {"schema_version": 1,
                "description": "Extracted first-mode inputs from saved numerical runs; "
                "original_sha256 identifies the full local record. Coefficients are "
                "omitted. This snapshot reproduces the analysis, not the original solve.",
                "records": records}
    # Refuse to replace the useful snapshot with an incomplete extraction.
    validate_snapshot(snapshot)
    write_json(target, snapshot)
    return snapshot


def validate_snapshot(snapshot):
    if snapshot.get("schema_version") != 1:
        raise ValueError("unsupported input snapshot schema")
    records = snapshot.get("records", [])
    paths = [item["path"] for item in records]
    if len(set(paths)) != len(paths):
        raise ValueError("duplicate record paths")
    present = {str(Path(path).parent) for path in paths}
    missing = [directory for _, directory in PRIMARY if directory not in present]
    if missing:
        raise ValueError("missing primary ladders: " + ", ".join(missing))


def estimate_ladder(records, directory):
    accepted, rejected = [], []
    for item in records:
        if str(Path(item["path"]).parent) != directory:
            continue
        rec = item["data"]
        y = mp.mpf(str(rec["b"][1]))
        noise = max(mp.mpf(rec[key]) for key in ("residual", "residual_check"))
        signal = abs(mp.mpc(*rec["D"]["0.5"]))
        if not (mp.isfinite(y) and y > 0 and mp.isfinite(noise) and noise >= 0
                and mp.isfinite(signal)):
            raise ValueError("invalid numerical record: " + item["path"])
        if rec.get("loop_limit_reached") or signal <= 100 * noise:
            rejected.append(item["path"])
        else:
            accepted.append((y, item))
    if len(accepted) < 2:
        raise ValueError("fewer than two usable rungs: " + directory)
    accepted.sort(key=lambda pair: pair[0], reverse=True)
    ys = [y for y, _ in accepted]
    if len(set(ys)) != len(ys):
        raise ValueError("duplicate heights: " + directory)
    # Richardson uses only the smallest two/three heights.
    selected = accepted[-3:]
    hats = [c1_of(item["data"], digits=32)[2] for _, item in selected]
    linear, quadratic = richardson([y for y, _ in selected], hats)
    best = linear if quadratic is None else quadratic
    return {"value": best, "linear": linear, "rungs": len(accepted),
            "used_records": [item["path"] for _, item in selected],
            "rejected_records": rejected}


def collect_rows(snapshot):
    """Recompute values from recorded D(1/2), never from rounded paper tables."""
    validate_snapshot(snapshot)
    rows = []
    with mp.workdps(60):
        eta = mp.exp(1 / mp.e)
        b1 = mp.mpf(B1_ABS)
        for base, directory in PRIMARY:
            estimate = estimate_ladder(snapshot["records"], directory)
            value, linear = estimate["value"], estimate["linear"]
            alternate = []
            present = {str(Path(item["path"]).parent) for item in snapshot["records"]}
            for other in ALTERNATE.get(base, []):
                if other in present:
                    alt = estimate_ladder(snapshot["records"], other)
                    alternate.append({"directory": other, "abs_c1hat": float(abs(alt["value"]))})
            variations = [abs(value - linear)]
            variations.extend(abs(abs(value) - item["abs_c1hat"]) for item in alternate)
            deficit = 1 - abs(value) / b1
            if not 0 < deficit < 1:
                raise ValueError("nonpositive or invalid deficit at base " + base)
            rows.append({"base": base, "kind": "computed_ladder",
                         "epsilon": float(abs(mp.log(lam_att(base)))),
                         "gap": float(eta - mp.mpf(base)),
                         "abs_c1hat": float(abs(value)), "arg_c1hat": float(mp.arg(value)),
                         "delta1": float(deficit),
                         "sensitivity_scale": float(max(variations) / b1),
                         "linear_quadratic_complex_difference": float(abs(value - linear)),
                         "alternates": alternate,
                         **{key: estimate[key] for key in ("rungs", "used_records", "rejected_records")}})
        # The external point depends on a phase extrapolation. Keep it separate.
        nearest = sorted(rows, key=lambda row: row["gap"])[:2]
        x1, x2 = [row["gap"] for row in nearest]
        a1, a2 = [row["arg_c1hat"] for row in nearest]
        gap = float(eta - mp.sqrt(2))
        phase = a1 + (a2 - a1) * (gap - x1) / (x2 - x1)
        naive, corrected, multiplier = paulsen_point(mp.mpf(phase))
        external = {"base": "sqrt2", "kind": "external_phase_estimate",
                    "epsilon": float(abs(mp.log(multiplier))), "gap": gap,
                    "abs_c1hat": float(corrected), "arg_c1hat": phase,
                    "delta1": float(1 - corrected / b1),
                    "uncorrected_delta1": float(1 - naive / b1),
                    "sensitivity_scale": float(abs(corrected - naive) / b1),
                    "phase_source_bases": [row["base"] for row in nearest]}
    return rows, external


def fit_model(xs, deficits, degree=0, fixed_p=None):
    """Fit log(delta)=log(C)+p log(eps)+sum a_j eps^j with full diagnostics."""
    xs, deficits = np.asarray(xs, dtype=float), np.asarray(deficits, dtype=float)
    if (xs.ndim != 1 or deficits.shape != xs.shape or not np.all(np.isfinite(xs))
            or not np.all(np.isfinite(deficits)) or np.any(xs <= 0)
            or np.any(deficits <= 0)):
        raise ValueError("fit inputs must be matching finite positive vectors")
    if not isinstance(degree, int) or degree < 0:
        raise ValueError("degree must be a nonnegative integer")
    if fixed_p is not None and not math.isfinite(fixed_p):
        raise ValueError("fixed exponent must be finite")
    cols = [np.ones(len(xs))]
    if fixed_p is None:
        cols.append(np.log(xs))
    cols.extend(xs ** power for power in range(1, degree + 1))
    X = np.column_stack(cols)
    n, k = X.shape
    if n <= k:
        raise ValueError("fit needs more observations than parameters")
    y = np.log(deficits) - (0 if fixed_p is None else fixed_p * np.log(xs))
    coef, _, rank, singular = np.linalg.lstsq(X, y, rcond=None)
    if rank != k:
        raise ValueError("rank-deficient fit")
    residual = y - X @ coef
    loo = []
    for i in range(n):
        keep = np.arange(n) != i
        subcoef, _, subrank, _ = np.linalg.lstsq(X[keep], y[keep], rcond=None)
        if subrank != k:
            raise ValueError("rank-deficient leave-one-out fit")
        loo.append(float(y[i] - X[i] @ subcoef))
    return {"degree": degree, "fixed_p": fixed_p, "n": n, "parameters": k,
            "p": float(coef[1]) if fixed_p is None else float(fixed_p),
            "C": math.exp(float(coef[0])),
            "corrections": coef[2 if fixed_p is None else 1:].tolist(),
            "log_rms": float(np.sqrt(np.mean(residual ** 2))),
            "loo_log_rms": float(np.sqrt(np.mean(np.square(loo)))),
            "closest_point_prediction_log_error": loo[int(np.argmin(xs))],
            "design_condition_number": float(singular[0] / singular[-1])}


def audit_models(rows):
    xs = [row["epsilon"] for row in rows]
    ds = [row["delta1"] for row in rows]
    fits = []
    for degree in range(4):
        # Identical correction families for both candidate exponents.
        for exponent in (None, 2.0, 1.75):
            fit = fit_model(xs, ds, degree, exponent)
            if exponent is None:
                perturbed = [fit["p"]]
                for i, row in enumerate(rows):
                    for sign in (-1, 1):
                        trial = list(ds)
                        trial[i] += sign * row["sensitivity_scale"]
                        if trial[i] > 0:
                            perturbed.append(fit_model(xs, trial, degree)["p"])
                fit["one_point_sensitivity_p_range"] = [min(perturbed), max(perturbed)]
            fits.append(fit)
    windows = []
    nearest = sorted(rows, key=lambda row: row["epsilon"])
    for count in range(6, len(rows) + 1):
        window = nearest[:count]
        for degree in (1, 2, 3):
            windows.append({"bases": [row["base"] for row in window],
                            **fit_model([row["epsilon"] for row in window],
                                        [row["delta1"] for row in window], degree)})
    return {"bases": [row["base"] for row in rows], "fits": fits, "nearest_windows": windows}


def write_json(path, data):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False, allow_nan=False) + "\n")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--export-inputs", type=Path, metavar="RAW_ROOT")
    args = parser.parse_args(argv)
    if args.export_inputs:
        snapshot = export_inputs(args.export_inputs, args.input)
    else:
        snapshot = json.loads(args.input.read_text())
    rows, external = collect_rows(snapshot)
    naive = {**external, "delta1": external["uncorrected_delta1"]}
    scenarios = {"own_only": audit_models(rows),
                 "with_phase_corrected_external": audit_models(rows + [external]),
                 "with_uncorrected_external": audit_models(rows + [naive])}
    report = {"schema_version": 1, "claim_status": "numerical_conjecture",
              "limitations": [
                  "Finite epsilon range cannot establish the asymptotic exponent.",
                  "First-mode extraction and y-to-zero extrapolation have no certified error bound.",
                  "Sensitivity scales are observed numerical variations, not confidence intervals.",
                  "The external point uses an extrapolated phase and is not independent of our ladders.",
                  "The snapshot reproduces analysis of saved runs, not a fresh Kneser construction."],
              "input_sha256": digest(args.input),
              "implementation_sha256": {
                  path.relative_to(DOCS.parent).as_posix(): digest(path)
                  for path in [*(DOCS / name for name in
                                ("deficit_audit.py", "deficit_law.py", "c1_invariant.py")),
                               *sorted((DOCS.parent / "src" / "kneser").glob("*.py"))]},
              "versions": {"python": sys.version.split()[0], "numpy": np.__version__,
                           "mpmath": mp.__version__},
              "horn_abs_B1": B1_ABS, "rows": rows, "external_row": external,
              "scenarios": scenarios}
    for name, scenario in scenarios.items():
        print(f"\n{name}: {len(scenario['bases'])} points")
        print(" degree   p             log-RMS     leave-one-out log-RMS")
        for fit in scenario["fits"]:
            label = "free" if fit["fixed_p"] is None else "fixed"
            print(f" {fit['degree']:4d}    {fit['p']:.6f} {label:5}  "
                  f"{fit['log_rms']:.3e}       {fit['loo_log_rms']:.3e}")
    print("\nStatus: numerical conjecture. Sensitivity ranges are not error bars.")
    if args.output:
        write_json(args.output, report)
        print(f"Report: {args.output}")
    return report


if __name__ == "__main__":
    main()
