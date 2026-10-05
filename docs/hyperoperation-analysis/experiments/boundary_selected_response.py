"""Independent R005 checks: zeta tail, critical limit and nonlinear conjugacy."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import platform

import mpmath as mp

from translation_resolvent import (TranslationResolvent, exponential_particular,
                                  polynomial_particular, resonant_particular)

OUT = Path(__file__).with_name("boundary-selected-response.json")
REPOSITORY = Path(__file__).resolve().parents[3]


def run(dps):
    with mp.workdps(dps):
        def Q(z):
            z = mp.mpc(z)
            return z / (z + 2) ** 3

        def U(z):
            return -mp.zeta(2, z + 2) + 2 * mp.zeta(3, z + 2)

        def exact(z):
            return U(z) - U(0)

        resolver = TranslationResolvent(Q, b="0.25", epsilon=1,
                                       source_norm_bound=mp.mpf(15) / 7)
        grid = [mp.mpf("0"), mp.mpc("-0.2", "0.6"), mp.mpc("0.7", "-0.4"),
                mp.mpc("2.5", "1.2")]
        tail_records = []
        threshold = mp.power(10, -(dps - 8))
        for n in (16, 64, 256):
            errors, bounds, residual_errors = [], [], []
            for z in grid:
                value = resolver.evaluate(z, terms=n)
                error = abs(value.value - exact(z))
                assert error <= value.analytic_truncation_bound
                errors.append(error)
                bounds.append(value.analytic_truncation_bound)
                observed_residual = resolver.evaluate(z + 1, terms=n).value - value.value - Q(z)
                residual_errors.append(abs(observed_residual + Q(z + n)))
                assert abs(observed_residual) <= value.analytic_difference_residual_bound
            assert max(residual_errors) < threshold
            assert abs(resolver.evaluate(0, terms=n).value) < threshold
            endpoint = resolver.evaluate(1, terms=n).value
            assert abs(endpoint + Q(n)) < threshold
            tail_records.append({"terms": n,
                                 "error_max": mp.nstr(max(errors), 25),
                                 "analytic_truncation_bound_max": mp.nstr(max(bounds), 25),
                                 "finite_difference_residual_identity_error_max": mp.nstr(max(residual_errors), 25),
                                 "finite_endpoint_at_1_NONZERO": mp.nstr(endpoint, 25)})
        assert abs(exact(0)) < threshold and abs(exact(1)) < threshold
        assert mp.mpf(tail_records[-1]["error_max"]) < mp.mpf(tail_records[0]["error_max"])

        # A source-bound perturbation has an independently known zeta solution.
        delta = mp.mpf("0.002")
        pointwise_stability_ratios = []
        for z in grid:
            u = 1 + mp.mpf("0.25") + mp.re(z)
            # |constant| + weighted decaying part is bounded pointwise here.
            observed = abs(-delta * U(0)) + u * abs(delta * U(z))
            allowed = 2 * (1 + 1) * delta * (mp.mpf(15) / 7)
            pointwise_stability_ratios.append(observed / allowed)
            assert observed <= allowed

        c = mp.mpf("0.3")

        def S(lam, z):
            if lam == 1:
                return 1 + c * z
            return 1 + c * mp.expm1(z * mp.log(lam)) / (lam - 1)

        def D(lam, z):
            if lam == 1:
                return c
            return c * mp.exp(z * mp.log(lam)) * mp.log(lam) / (lam - 1)

        spectral_errors = []
        spectral_grid = [mp.mpc("0.3", "0.2"), mp.mpf("1"), mp.mpc("1.5", "-0.1")]
        for lam in (mp.mpf("0.4"), mp.mpf("0.8"), mp.mpf("1"), mp.mpf("1.4"),
                    mp.mpc("1.2", "0.1"), 1 + mp.mpf("1e-8")):
            for z in spectral_grid:
                # Guard against cancellation in the coalescing secular terms.
                with mp.workdps(dps + 25):
                    if lam == 1:
                        spectral = polynomial_particular(1, z)
                    else:
                        mu = mp.log(lam)
                        spectral = (z - exponential_particular(-mu, z)) / (lam * mu)
                    observed = mp.diff(lambda ll: S(ll, z), lam) / D(lam, z)
                    spectral_errors.append(abs(spectral - observed))
        assert max(spectral_errors) < threshold

        mode_errors = []
        for mode in (-2, 0, 3):
            for z in spectral_grid:
                mode_errors.append(abs(resonant_particular(mode, z + 1)
                                       - resonant_particular(mode, z)
                                       - mp.exp(2j * mp.pi * mode * z)))
        for degree in range(5):
            for z in spectral_grid:
                mode_errors.append(abs(polynomial_particular(degree, z + 1)
                                       - polynomial_particular(degree, z) - z ** degree))
        assert max(mode_errors) < threshold

        a, lam = 1 + c, mp.mpf("1.4")

        def h(x):
            return (x - 1) * (x - a)

        def phi(eta, x):
            return x + eta * h(x)

        def inverse(eta, y):
            if eta == 0:
                return y
            coefficient = 1 - eta * (1 + a)
            discriminant = coefficient ** 2 + 4 * eta * (y - eta * a)
            return 2 * (y - eta * a) / (coefficient + mp.sqrt(discriminant))

        def deformed(eta, z):
            return inverse(eta, S(lam, z))

        def f(eta, x):
            return inverse(eta, a + lam * (phi(eta, x) - 1))

        nonlinear_grid = [mp.mpf("0"), mp.mpf("0.3"), mp.mpc("0.7", "0.2"),
                          mp.mpf("1"), mp.mpc("1.5", "-0.1")]
        nonlinear_residuals, endpoint_errors, inverse_errors = [], [], []
        for eta in (mp.mpf("0"), mp.mpf("0.01"), mp.mpc("0.006", "0.002")):
            assert abs(eta) < mp.mpf(1) / 27
            endpoint_errors.extend((abs(deformed(eta, 0) - 1), abs(deformed(eta, 1) - a)))
            for z in nonlinear_grid:
                assert abs(S(lam, z)) < 3 and abs(S(lam, z + 1)) < 3
                nonlinear_residuals.append(abs(deformed(eta, z + 1) - f(eta, deformed(eta, z))))
                inverse_errors.append(abs(phi(eta, deformed(eta, z)) - S(lam, z)))
        assert max(nonlinear_residuals + endpoint_errors + inverse_errors) < threshold

        response_errors = []
        for step in (mp.mpf("1e-4"), mp.mpf("5e-5")):
            response_errors.append(max(abs((deformed(step, z) - deformed(-step, z)) / (2 * step)
                                           + h(S(lam, z))) for z in nonlinear_grid))
        ratio = response_errors[0] / response_errors[1]
        assert mp.mpf("3.9") < ratio < mp.mpf("4.1")

        # This response comes from the actual nonlinear family above.
        selected_response_errors = []
        for z in nonlinear_grid:
            mu = mp.log(lam)
            selected = c / mu * (exponential_particular(-mu, z) - exponential_particular(mu, z))
            selected_response_errors.append(abs(selected + h(S(lam, z)) / D(lam, z)))
        assert max(selected_response_errors) < threshold

        invalid_input_checks = 0
        for call in (lambda: resolver.evaluate(-mp.mpf("0.25"), terms=16),
                     lambda: resolver.evaluate(0, terms=0),
                     lambda: TranslationResolvent(Q, b="0.25", epsilon=0, source_norm_bound=1)):
            try:
                call()
            except ValueError:
                invalid_input_checks += 1
        assert invalid_input_checks == 3

        return {
            "working_dps": dps, "tail_checks": tail_records,
            "sample_stability_bound_ratio_max": mp.nstr(max(pointwise_stability_ratios), 25),
            "affine_spectral_response_error_max": mp.nstr(max(spectral_errors), 25),
            "polynomial_and_exact_resonance_error_max": mp.nstr(max(mode_errors), 25),
            "actual_nonlinear_successor_residual_max": mp.nstr(max(nonlinear_residuals), 25),
            "actual_nonlinear_endpoint_error_max": mp.nstr(max(endpoint_errors), 25),
            "conjugacy_inverse_error_max": mp.nstr(max(inverse_errors), 25),
            "nonlinear_response_fd_error_h_1e_4": mp.nstr(response_errors[0], 25),
            "nonlinear_response_fd_error_h_5e_5": mp.nstr(response_errors[1], 25),
            "fd_error_ratio_when_h_halved": mp.nstr(ratio, 25),
            "selected_nonlinear_response_error_max": mp.nstr(max(selected_response_errors), 25),
            "invalid_input_checks_passed": invalid_input_checks,
        }


def main():
    records = [run(dps) for dps in (40, 70)]
    inputs = [Path(__file__), Path(__file__).with_name("translation_resolvent.py")]
    result = {
        "experiment": "R005-v1", "status": "PASS", "date": "2026-10-05",
        "python": platform.python_version(), "mpmath": mp.__version__,
        "input_sha256": {str(path.relative_to(REPOSITORY)): hashlib.sha256(path.read_bytes()).hexdigest()
                         for path in inputs},
        "parameters": {"b": "0.25", "epsilon": "1", "M": "15/7",
                       "truncations": [16, 64, 256], "nonlinear_base": "1.3", "nonlinear_lambda": "1.4"},
        "scope": "Analytic bounds are proved in R005. Floating-point diagnostics are not interval certificates. "
                 "The nonlinear family is a local superfunction deformation, not fractional rank.",
        "records": records,
    }
    OUT.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    for row in records:
        print(f'dps={row["working_dps"]}: nonlinear residual={row["actual_nonlinear_successor_residual_max"]}, '
              f'FD ratio={row["fd_error_ratio_when_h_halved"]}')
    print(f"PASS: {OUT}")


if __name__ == "__main__":
    main()
