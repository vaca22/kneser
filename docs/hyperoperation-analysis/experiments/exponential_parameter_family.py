"""R006 diagnostics against inverse power series and actual exponential sources."""
from __future__ import annotations

from fractions import Fraction as Fraction
import hashlib
import json
from math import factorial
from pathlib import Path
import platform
import sys

import mpmath as mp

REPOSITORY = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPOSITORY / "src"))
from kneser._koenigs import inverse_schroeder, series_eval, tau_of_exponential
from regular_parameter_family import RegularParameterFamily
from translation_resolvent import exponential_particular

OUT = Path(__file__).with_name("exponential-parameter-family.json")


def exact_rational_checks():
    F = Fraction

    def exponential_bounds(x, k):
        total = sum((x ** n / factorial(n) for n in range(k + 1)), F(0))
        tail = x ** (k + 1) / factorial(k + 1) / (1 - x / (k + 2))
        return total, total + tail

    assert exponential_bounds(F(262, 1000), 4)[1] < F(13, 10)
    assert exponential_bounds(F(263, 1000), 4)[0] > F(13, 10)
    assert exponential_bounds(F(2, 5), 5)[1] < F(3, 2)
    assert F(13, 10) ** 7 > F(7, 5) ** 5
    assert F(13, 10) ** 3 < F(3, 2) ** 2
    assert F(151, 100) * F(264, 1000) ** 2 * F(6, 5) / 2 < F(8, 125)
    assert F(599, 1000) - F(32, 55) * F(599, 1000) ** 2 > F(39, 100)
    assert F(51, 100) + F(32, 55) * F(51, 100) ** 2 < F(2, 3)
    assert F(51, 100) ** 4 > F(2, 5) ** 3
    assert F(17, 49) < F(39, 100)
    return 10


def run(dps):
    with mp.workdps(dps + 25):
        ell0 = mp.log(mp.mpf(13) / 10)
        steps = int(mp.ceil((dps + 20) / (-mp.log10(mp.mpf(25) / 36)))) + 10
        center = RegularParameterFamily(ell0, coordinate_steps=steps)
        # Independent inverse Schroder coefficient method from the repository.
        coeffs = inverse_schroeder(tau_of_exponential(mp.mpf("1.3"), center.p, 32))

        def coordinate_reference(w):
            state = mp.mpc(w)
            reduction = 16
            for _ in range(reduction):
                state = center.p * mp.expm1(ell0 * state)
            inverse_argument = mp.findroot(lambda s: series_eval(coeffs, s) - state, state,
                                           tol=mp.power(10, -(dps + 15)))
            return inverse_argument / center.lam ** reduction

        sigma_grid = [mp.mpc("0.2", "0.1"), mp.mpc("-0.4", "0.05"), 1 - center.p]
        coordinate_records = []
        for n in (32, 64, 128):
            errors, bounds = [], []
            for w in sigma_grid:
                observed = center.sigma_details(w, steps=n)[0]
                error = abs(observed - coordinate_reference(w))
                bound = center.sigma_tail_bound(w, steps=n)
                assert error < bound
                errors.append(error)
                bounds.append(bound)
            coordinate_records.append({"iterations": n, "coordinate_error_max": mp.nstr(max(errors), 25),
                                       "paper_coordinate_tail_bound_max": mp.nstr(max(bounds), 25)})
        assert abs(center.C - coordinate_reference(1 - center.p)) < mp.power(10, -(dps - 5))

        parameter_offsets = [mp.mpc(0), mp.mpc("0.0004", "0.0003"), mp.mpc("-0.0005", "0.0002")]
        heights = [mp.mpf("-1.5"), mp.mpf("-1"), mp.mpf("-0.5"), mp.mpf("0"),
                   mp.mpc("0.5", "0.2"), mp.mpf("1"), mp.mpc("2.5", "-0.3")]
        successor, endpoints, seam, response_residual, domain_constants = [], [], [], [], []
        for offset in parameter_offsets:
            model = RegularParameterFamily(ell0 + offset, coordinate_steps=steps)
            endpoints.extend((abs(model.value(0) - 1), abs(model.value(1) - mp.exp(model.ell)),
                              abs(model.value(-1))))
            domain_constants.append({"parameter_offset": str(offset), "fixed_point": mp.nstr(model.p, 25),
                                     "multiplier_abs": mp.nstr(abs(model.lam), 25),
                                     "multiplier_arg_abs": mp.nstr(abs(mp.arg(model.lam)), 25)})
            for z in heights:
                value, derivative, parameter_derivative = model.value(z, derivatives=True)
                next_value, next_derivative, next_parameter_derivative = model.value(z + 1, derivatives=True)
                successor.append(abs(next_value - mp.exp(model.ell * value)))
                seam.append(abs(model.value(z, extra=2) - value))
                response_residual.append(abs(next_parameter_derivative
                                             - next_value * (value + model.ell * parameter_derivative)))
                response_residual.append(abs(next_derivative - model.ell * next_value * derivative))
        threshold = mp.power(10, -(dps - 5))
        assert max(successor + endpoints + seam + response_residual) < threshold

        # Real height response is independently differenced in the actual base parameter.
        fd_errors = []
        fd_grid = [mp.mpf("0.3"), mp.mpc("0.7", "0.1"), mp.mpf("1.5")]
        for h in (mp.mpf("1e-5"), mp.mpf("5e-6")):
            plus = RegularParameterFamily(ell0 + h, coordinate_steps=steps)
            minus = RegularParameterFamily(ell0 - h, coordinate_steps=steps)
            errors = []
            for z in fd_grid:
                numerical = (plus.value(z) - minus.value(z)) / (2 * h)
                predicted = center.value(z, derivatives=True)[2]
                errors.append(abs(numerical - predicted))
            fd_errors.append(max(errors))
        ratio = fd_errors[0] / fd_errors[1]
        assert mp.mpf("3.9") < ratio < mp.mpf("4.1")

        period = 2j * mp.pi / center.loglam
        period_prime = -2j * mp.pi * center.lam_prime / (center.lam * center.loglam ** 2)
        periodic_errors, affine_period_errors = [], []
        for z in (mp.mpc("0.5", "0.2"), mp.mpf("1.5"), mp.mpc("3", "-0.1")):
            value, derivative, parameter_derivative = center.value(z, derivatives=True)
            shifted, shifted_d, shifted_b = center.value(z + period, derivatives=True)
            periodic_errors.append(abs(value - shifted))
            affine_period_errors.append(abs(shifted_b / shifted_d - parameter_derivative / derivative + period_prime))
        assert max(periodic_errors + affine_period_errors) < threshold

        rejected = 0
        for callback in (lambda: center.value(-2),
                         lambda: RegularParameterFamily(ell0 + mp.mpf("0.002"), coordinate_steps=steps),
                         lambda: center.sigma_details(mp.mpf("0.6"))):
            try:
                callback()
            except ValueError:
                rejected += 1
        assert rejected == 3

        return {
            "requested_dps": dps, "actual_working_dps": dps + 25, "coordinate_steps": steps,
            "coordinate_reference_method": "32-term inverse Schroder series with 16 forward reductions",
            "coordinate_convergence": coordinate_records, "parameters": domain_constants,
            "actual_exponential_successor_residual_max": mp.nstr(max(successor), 25),
            "normalization_and_minus_one_error_max": mp.nstr(max(endpoints), 25),
            "extra_logarithm_seam_error_max": mp.nstr(max(seam), 25),
            "actual_parameter_and_height_response_residual_max": mp.nstr(max(response_residual), 25),
            "parameter_fd_error_h_1e_5": mp.nstr(fd_errors[0], 25),
            "parameter_fd_error_h_5e_6": mp.nstr(fd_errors[1], 25),
            "fd_error_ratio_when_h_halved": mp.nstr(ratio, 25),
            "virtual_period": mp.nstr(period, 25),
            "periodicity_error_max": mp.nstr(max(periodic_errors), 25),
            "affine_response_period_increment_error_max": mp.nstr(max(affine_period_errors), 25),
            "invalid_input_checks_passed": rejected,
        }


def green_bridge(dps=60):
    # Enough extra precision to separate the growing source from its tiny
    # remainder at all listed finite summation indices.
    with mp.workdps(dps + 90):
        ell = mp.log(mp.mpf(13) / 10)
        model = RegularParameterFamily(ell, coordinate_steps=600)
        L, C, p, lam = model.loglam, model.C, model.p, model.lam
        exp_coefficient = p / (ell * L * C)
        constant_coefficient = 1 / (ell * L * (1 - lam))

        def W(z):
            _, derivative, parameter_derivative = model.value(z, derivatives=True)
            return parameter_derivative / derivative

        def source_remainder(z):
            value, derivative, _ = model.value(z, derivatives=True)
            return value / (ell * derivative) - exp_coefficient * mp.exp(-L * z) - constant_coefficient

        records = []
        grid = [mp.mpc("0.3", "0.2"), mp.mpf("1.5")]
        origin_response = W(1)
        for n in (8, 16, 32):
            errors = []
            for v in grid:
                secular = (exp_coefficient * mp.exp(-L) * exponential_particular(-L, v)
                           + constant_coefficient * v)
                decaying = mp.fsum(source_remainder(1 + k) - source_remainder(1 + v + k)
                                  for k in range(n))
                errors.append(abs(W(1 + v) - origin_response - secular - decaying))
            records.append({"terms": n, "selected_actual_response_error_max": mp.nstr(max(errors), 25)})
        assert mp.mpf(records[1]["selected_actual_response_error_max"]) < mp.mpf(records[0]["selected_actual_response_error_max"])
        assert mp.mpf(records[2]["selected_actual_response_error_max"]) < mp.mpf(records[1]["selected_actual_response_error_max"])
        return {"requested_dps": dps, "actual_working_dps": dps + 90,
                "paper_global_remainder_norm_certified_numerically": False,
                "finite_sum_comparison": records}


def main():
    rational_count = exact_rational_checks()
    records = []
    for dps in (40, 70):
        records.append(run(dps))
        print(f'Checked dps={dps}: actual exponent residual={records[-1]["actual_exponential_successor_residual_max"]}', flush=True)
    bridge = green_bridge()
    inputs = [Path(__file__), Path(__file__).with_name("regular_parameter_family.py"),
              Path(__file__).with_name("translation_resolvent.py"), REPOSITORY / "src/kneser/_koenigs.py"]
    result = {
        "experiment": "R006-v1", "status": "PASS", "date": "2026-10-05",
        "python": platform.python_version(), "mpmath": mp.__version__,
        "input_sha256": {str(path.relative_to(REPOSITORY)): hashlib.sha256(path.read_bytes()).hexdigest()
                         for path in inputs},
        "exact_rational_inequalities_checked": rational_count,
        "records": records, "actual_source_green_bridge": bridge,
        "scope": "Actual regular exponential parameter family near base 1.3. "
                 "Finite-precision diagnostics and exact rational checks; no interval inversion certificate, "
                 "no Kneser-base-e parameter theorem, no fractional rank.",
    }
    OUT.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(f"PASS: {OUT}", flush=True)


if __name__ == "__main__":
    main()
