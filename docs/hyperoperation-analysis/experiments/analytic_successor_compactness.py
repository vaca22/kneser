"""R008 actual directional derivatives and boundary-peak attenuation.

Finite samples do not certify compactness or the full Banach ball; the note
proves those facts with a restriction factorization and an explicit sequence.
"""
from __future__ import annotations

from fractions import Fraction as F
import hashlib
import json
import math
from pathlib import Path
import platform

import mpmath as mp

from polynomial_successor import FactoredDirection, PeakDirection, PolynomialSuccessor
from regular_parameter_family import RegularParameterFamily

ROOT = Path(__file__).resolve().parent
REPOSITORY = ROOT.parents[2]


def exact_constants():
    def exp_bounds(x, k=14):
        lower = sum(x ** j / math.factorial(j) for j in range(k + 1))
        upper = lower + x ** (k + 1) / (math.factorial(k + 1) * (1 - x / (k + 2)))
        return lower, upper
    assert exp_bounds(F(3, 4))[0] > F(211, 100)
    assert exp_bounds(F(1, 4))[0] > F(100, 79)
    assert F(11, 15) + 2000 * F(1, 1000000) < F(3, 4)
    assert F(41, 100) + F(1, 900) < F(1, 2)
    return 4


def run(dps):
    with mp.workdps(dps + 50):
        directions = [FactoredDirection([1]), FactoredDirection([0, 1]),
                      FactoredDirection([1, mp.j])]
        threshold = mp.power(10, -(dps - 5))
        eta = mp.mpf("1e-12")
        heights = (mp.mpf("0.3"), mp.mpf("0.8"), mp.mpf("1.3"), mp.mpc("0.7", "0.0000002"))
        normalization, successor, response_residual, reference_error, coordinate_error = (mp.mpf(0),) * 5
        fd_records = []
        base_responses = []
        reference = RegularParameterFamily(mp.log(mp.mpf(13) / 10), coordinate_steps=500)
        for direction in directions:
            engine = PolynomialSuccessor(direction, requested_dps=dps)
            refined = PolynomialSuccessor(direction, requested_dps=dps, extra_steps=16)
            base_responses.append([engine.value(z, response=True)[2] for z in heights])
            fd_errors = []
            for scale in (eta, eta / 2):
                plus = PolynomialSuccessor(direction, parameter=scale, requested_dps=dps)
                minus = PolynomialSuccessor(direction, parameter=-scale, requested_dps=dps)
                error = mp.mpf(0)
                for z in heights:
                    value, derivative, b = engine.value(z, response=True)
                    next_value, next_derivative, next_b = engine.value(z + 1, response=True)
                    h, _ = direction.pair(value)
                    response_residual = max(response_residual,
                        abs(next_b - h - engine.ell * next_value * b),
                        abs(next_derivative - engine.ell * next_value * derivative))
                    error = max(error, abs((plus.value(z) - minus.value(z)) / (2 * scale) - b))
                    coordinate_error = max(coordinate_error, abs(refined.value(z, response=True)[2] - b))
                    reference_error = max(reference_error, abs(value - reference.value(z)))
                    for perturbed in (plus, minus):
                        successor = max(successor, abs(perturbed.value(z + 1)
                                        - perturbed.map_pair(perturbed.value(z))[0]))
                fd_errors.append(error)
                for perturbed in (plus, minus):
                    normalization = max(normalization, abs(perturbed.value(0) - 1),
                                        abs(perturbed.value(1) - perturbed.a))
            ratio = fd_errors[0] / fd_errors[1]
            assert mp.mpf("3.99") < ratio < mp.mpf("4.01"), ratio
            fd_records.append({"q_coefficients": [str(c) for c in direction.coefficients],
                               "error_eta_1e_12": mp.nstr(fd_errors[0], 24),
                               "error_eta_5e_13": mp.nstr(fd_errors[1], 24),
                               "error_ratio": mp.nstr(ratio, 24)})
            normalization = max(normalization, abs(engine.value(0, response=True)[2]),
                                abs(engine.value(1, response=True)[2]))
        combined = PolynomialSuccessor(FactoredDirection([1, 1]), requested_dps=dps)
        linearity = max(abs(combined.value(z, response=True)[2] - base_responses[0][j] - base_responses[1][j])
                        for j, z in enumerate(heights))
        for value in (normalization, successor, response_residual, reference_error, coordinate_error, linearity):
            assert value < threshold, mp.nstr(value, 12)

        peak_records = []
        radius = mp.mpf("1e-6")
        previous = mp.inf
        for degree in (0, 4, 8, 16, 24):
            direction = PeakDirection(reference.p, radius, degree)
            engine = PolynomialSuccessor(direction, requested_dps=dps)
            observed = max(abs(engine.value(z, response=True)[2]) for z in heights)
            assert observed < previous
            previous = observed
            boundary_samples = [abs(direction.pair(-radius * (1 - mp.mpf("1e-8")))[0])]
            assert mp.mpf("0.99999") < boundary_samples[0] < mp.mpf("1.00001")
            peak_records.append({"degree": degree, "sample_response_max": mp.nstr(observed, 24),
                                 "near_left_boundary_input_abs": mp.nstr(boundary_samples[0], 24)})
        invalid = 0
        for action in (lambda: PeakDirection(reference.p, radius, -1),
                       lambda: PeakDirection(reference.p, 0, 2),
                       lambda: FactoredDirection([]),
                       lambda: combined.value(-1)):
            try:
                action()
            except ValueError:
                invalid += 1
            else:
                raise AssertionError("invalid argument accepted")
        fmt = lambda x: mp.nstr(x, 24)
        record = {"requested_dps": dps, "actual_working_dps": dps + 50,
                  "actual_polynomial_perturbation_successor_error_max": fmt(successor),
                  "normalization_and_response_endpoint_error_max": fmt(normalization),
                  "actual_directional_response_equation_error_max": fmt(response_residual),
                  "independent_exponential_family_reference_error_max": fmt(reference_error),
                  "sixteen_extra_steps_response_change_max": fmt(coordinate_error),
                  "linearity_error_max": fmt(linearity), "finite_difference_checks": fd_records,
                  "boundary_peak_directions": peak_records, "invalid_input_checks_passed": invalid,
                  "final_Banach_ball_radius_certified_numerically": False,
                  "full_operator_norm_certified_numerically": False}
        print(f"Checked dps={dps}: actual response equation error={fmt(response_residual)}", flush=True)
        return record


def main():
    checks = exact_constants()
    records = [run(dps) for dps in (35, 55)]
    inputs = [Path(__file__), ROOT / "polynomial_successor.py", ROOT / "regular_parameter_family.py"]
    result = {"experiment": "R008-v1", "status": "PASS", "date": "2026-10-05",
              "python": platform.python_version(), "mpmath": mp.__version__,
              "input_sha256": {str(p.relative_to(REPOSITORY)): hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in inputs}, "exact_rational_inequalities_checked": checks,
              "records": records,
              "scope": "Actual polynomial perturbations and derivatives of the regular exponential successor "
                       "near base 1.3. Banach compactness and flow obstruction are paper proofs; finite samples "
                       "do not certify the full ball, operator norm or a global fractional-rank family."}
    target = ROOT / "analytic-successor-compactness.json"
    target.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(f"PASS: {target}")


if __name__ == "__main__":
    main()
