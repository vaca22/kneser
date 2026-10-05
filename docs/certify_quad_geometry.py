"""Outward-rounded checks for proofs/quadratic-continuation.tex.

Certifies the rational constants in the cusp estimates over the ENTIRE
interval 0 <= |eps| <= 1/128. The all-upper-plane crescent theorem and
outer critical-value marking are exact algebra, not a finite-grid claim.
This is not a certificate for the unproved marked versions of F and G.

Run: python3 docs/certify_quad_geometry.py [--output FILE]
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from flint import arb, ctx, fmpq


def certify():
    ctx.dps = 60
    radius = arb(fmpq(1, 128))
    rho = arb(fmpq(1, 256), fmpq(1, 256))
    denominator = 1 - arb(fmpq(13, 2)) * rho
    step_error = arb(fmpq(13, 2)) / denominator
    # Squaring a wide ball introduces avoidable dependency loss. This bound
    # is increasing in rho on the certified interval; evaluate its endpoint.
    derivative = 36 / (1 - arb(fmpq(13, 2)) * radius)**2
    log_error = rho / (2 * (1 - rho))
    a_delta_error = (step_error + 1 / (2 * (1 - rho))) / (1 - log_error)
    basis_sine = (arb(fmpq(1, 2)) - log_error) / (1 + log_error)
    qc_limit = 25 * radius / (1 - 25 * radius)
    checks = {
        "log_denominator_positive": denominator > 0,
        "step_error_scaled_lt_7": step_error < 7,
        "step_derivative_scaled_lt_40": derivative < 40,
        "normal_lower_gt_two_fifths": arb(fmpq(1, 2)) - 7 * rho > arb(fmpq(2, 5)),
        "normal_upper_lt_six_fifths": 1 + 7 * rho < arb(fmpq(6, 5)),
        "tangential_derivative_positive": 1 - 40 * rho**2 > 0,
        "interpolation_jacobian_scaled_positive": arb(fmpq(2, 5)) - 40 * rho**2 * (1 + 7 * rho) > 0,
        "A_Delta_error_scaled_lt_8": a_delta_error < 8,
        "basis_sine_gt_49_over_100": basis_sine > arb(fmpq(49, 100)),
        "inverse_basis_frobenius_lt_3": arb(2).sqrt() / arb(fmpq(49, 100)) < 3,
        "derivative_error_scaled_le_25": 3 * (8 + 40 * rho) < 25,
        "qc_dilatation_lt_1": qc_limit < 1,
        "line_distance_gt_1_48": 3 * arb.pi() / 5 - arb(fmpq(2, 5)) > arb(fmpq(148, 100)),
        "crescent_width_lt_quarter": arb(fmpq(6, 5)) * radius < arb(fmpq(1, 4)),
    }
    checks = {name: bool(value) for name, value in checks.items()}
    result = {
        "scope": "quadratic cusp geometric constants only; not marked F/G",
        "arithmetic": "python-flint Arb, 60 decimal digits, outward-rounded balls",
        "rho_domain": "[0, 1/128]",
        "bounds": {
            "step_error_scaled": str(step_error),
            "step_derivative_scaled": str(derivative),
            "A_Delta_error_scaled": str(a_delta_error),
            "basis_sine": str(basis_sine),
            "max_qc_dilatation": str(qc_limit),
        },
        "checks": checks,
        "passed": all(checks.values()),
    }
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = certify()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result["passed"] else 1)
