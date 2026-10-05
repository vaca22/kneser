"""Finite-point diagnostics for R004; the trial family is not a hierarchy."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import platform

import mpmath as mp

OUT = Path(__file__).with_name("complex-rank-geometry.json")


def run(dps):
    with mp.workdps(dps):
        c = mp.mpf("0.3")
        epsilon = mp.mpf("0.0005")
        q, m = 12, 2

        def b(r):
            return mp.mpf("0.03") * mp.exp(-r / 5) + mp.mpf("0.01") * mp.sin(r)

        def S(r, z):
            return 1 + c * z + b(r) * z * (z - 1)

        def D(r, z):
            return c + b(r) * (2 * z - 1)

        def B(r, z):
            return mp.diff(b, r) * z * (z - 1)

        def W(r, z):
            return B(r, z) / D(r, z)

        def C(r, z):
            return mp.diff(b, r, 2) * z * (z - 1)

        def g(r):
            return r + epsilon * mp.sin(mp.pi * q * r) ** (2 * m)

        def transformed(r, z):
            return S(g(r), z)

        def residual(f, r, z):
            return f(r, z + 1) - f(r - 1, f(r, z))

        rank_grid = [mp.mpf("3.4"), mp.mpc("4.2", "0.02"), mp.mpc("5.1", "-0.03")]
        height_grid = [mp.mpf("0.3"), mp.mpc("0.7", "0.1"), mp.mpc("1.2", "-0.2")]
        covariance, closedness, brackets, second_order, actual_residual = [], [], [], [], []
        derivative_magnitudes = []
        for r in rank_grid:
            for z in height_grid:
                covariance.append(abs(residual(transformed, r, z) - residual(S, g(r), z)))
                closedness.append(abs(mp.diff(lambda rr: D(rr, z), r)
                                      - mp.diff(lambda zz: D(r, zz) * W(r, zz), z)))
                # Direct coefficient formula for the Lie bracket [X,Y].
                coefficient = (mp.diff(lambda rr: 1 / D(rr, z), r)
                               - W(r, z) * mp.diff(lambda zz: 1 / D(r, zz), z)
                               + mp.diff(lambda zz: W(r, zz), z) / D(r, z))
                brackets.append(abs(coefficient))
                state = S(r, z)
                predicted = (C(r, z + 1) - C(r - 1, state)
                             - 2 * mp.diff(lambda xx: B(r - 1, xx), state) * B(r, z)
                             - 2 * b(r - 1) * B(r, z) ** 2
                             - D(r - 1, state) * C(r, z))
                observed = mp.diff(lambda rr: residual(S, rr, z), r, 2)
                second_order.append(abs(predicted - observed))
                actual_residual.append(abs(residual(S, r, z)))
                derivative_magnitudes.append(abs(D(r, z)))

        rational_ranks = [3 + mp.mpf(n) / q for n in (0, 2, 3, 4, 6, 12, 24)]
        rational_error = max(abs(transformed(r, height_grid[1]) - S(r, height_grid[1]))
                             for r in rational_ranks)
        jet_error = max(abs(mp.diff(lambda rr: transformed(rr, height_grid[1]), n, k)
                            - mp.diff(lambda rr: S(rr, height_grid[1]), n, k))
                        for n in (3, 4, 5) for k in range(2 * m))
        witness_rank = 3 + mp.mpf(1) / (4 * q)
        witness = abs(transformed(witness_rank, height_grid[1]) - S(witness_rank, height_grid[1]))
        assert 2 * m * mp.pi * q * epsilon < 1

        # Independent local inversion at perturbed ranks holds x, not z, fixed.
        r0, z0 = mp.mpf("3.4"), mp.mpc("0.3", "0.1")
        x0 = S(r0, z0)
        predicted_velocity_response = D(r0, z0) * mp.diff(lambda zz: W(r0, zz), z0)

        def velocity_at_fixed_state(r):
            inverse_height = mp.findroot(lambda zz: S(r, zz) - x0, z0,
                                         tol=mp.power(10, -(dps - 5)))
            return D(r, inverse_height)

        fd_errors = []
        for h in (mp.mpf("1e-4"), mp.mpf("5e-5")):
            numerical = (velocity_at_fixed_state(r0 + h) - velocity_at_fixed_state(r0 - h)) / (2 * h)
            fd_errors.append(abs(numerical - predicted_velocity_response))

        threshold = mp.power(10, -(dps - 10))
        for values in (covariance, closedness, brackets, second_order):
            assert max(values) < threshold
        assert rational_error < threshold and jet_error < threshold
        assert witness > mp.mpf("1e-8")
        assert max(actual_residual) > mp.mpf("0.01")
        assert min(derivative_magnitudes) > mp.mpf("0.1")
        assert fd_errors[0] < mp.mpf("1e-8")
        assert mp.mpf("3.9") < fd_errors[0] / fd_errors[1] < mp.mpf("4.1")

        def fmt(value):
            return mp.nstr(value, 28)

        return {
            "working_dps": dps,
            "rank_grid": [str(r) for r in rank_grid],
            "height_grid": [str(z) for z in height_grid],
            "covariance_error_max": fmt(max(covariance)),
            "closedness_error_max": fmt(max(closedness)),
            "lie_bracket_coefficient_max": fmt(max(brackets)),
            "second_order_residual_identity_error_max": fmt(max(second_order)),
            "rational_anchor_error_max": fmt(rational_error),
            "integer_jet_error_max_order_3": fmt(jet_error),
            "trial_successor_residual_max_NONZERO": fmt(max(actual_residual)),
            "sample_height_derivative_min": fmt(min(derivative_magnitudes)),
            "noninteger_gauge_witness_difference": fmt(witness),
            "velocity_response_fd_error_h_1e_4": fmt(fd_errors[0]),
            "velocity_response_fd_error_h_5e_5": fmt(fd_errors[1]),
            "fd_error_ratio_when_h_halved": fmt(fd_errors[0] / fd_errors[1]),
        }


def main():
    records = [run(dps) for dps in (40, 70)]
    result = {
        "experiment": "R004-v1", "status": "PASS", "date": "2026-10-05",
        "python": platform.python_version(), "mpmath": mp.__version__,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "parameters": {"a": "1.3", "q": 12, "m": 2, "epsilon": "0.0005"},
        "model": "S(r,z)=1+0.3*z+(0.03*exp(-r/5)+0.01*sin(r))*z*(z-1)",
        "scope": "Finite-point diagnostics of identities on an entire trial family. "
                 "Its successor residual is nonzero. No fractional-rank construction or global certificate.",
        "records": records,
    }
    OUT.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    for row in records:
        print(f'dps={row["working_dps"]}: covariance={row["covariance_error_max"]}, '
              f'FD ratio={row["fd_error_ratio_when_h_halved"]}, '
              f'nonzero successor residual={row["trial_successor_residual_max_NONZERO"]}')
    print(f"PASS: {OUT}")


if __name__ == "__main__":
    main()
