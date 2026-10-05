"""Finite Fourier quadrature checks and near-resonance witnesses for R003."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import platform

import mpmath as mp

OUT = Path(__file__).with_name("quantitative-rigidity.json")


def run(dps):
    with mp.workdps(dps):
        alpha = (mp.sqrt(5) - 1) / 2
        eps = mp.mpf("0.2")
        records = []
        for N in (4, 12, 32):
            denoms = {k: 2 * abs(mp.sin(mp.pi * k * alpha)) for k in range(1, N + 1)}
            kmin = min(denoms, key=denoms.get)
            kderiv = max(denoms, key=lambda k: 2 * mp.pi * k / denoms[k])
            dmin = denoms[kmin]
            C = mp.sqrt(2 * sum(d ** -2 for d in denoms.values()))
            M = 2 * mp.pi * kderiv / denoms[kderiv]
            coeffs = {k: eps / (4 * mp.pi * N * k) for k in range(1, N + 1)}

            def p(u):
                return sum(c * mp.sin(2 * mp.pi * k * u) for k, c in coeffs.items())

            def dp(u):
                return sum(2 * mp.pi * k * c * mp.cos(2 * mp.pi * k * u)
                           for k, c in coeffs.items())

            # More than 2N nodes integrate squared degree-N polynomials exactly.
            grid = [mp.mpf(j) / (4 * N + 1) for j in range(4 * N + 1)]
            delta = mp.sqrt(sum(abs(p(u + alpha) - p(u)) ** 2 for u in grid) / len(grid))
            norm = mp.sqrt(sum(abs(p(u)) ** 2 for u in grid) / len(grid))
            derivative_norm = mp.sqrt(sum(abs(dp(u)) ** 2 for u in grid) / len(grid))
            assert norm <= delta / dmin
            assert derivative_norm <= M * delta
            assert max(abs(p(u)) for u in grid) <= C * delta
            exact_norm = mp.sqrt(sum(c ** 2 / 2 for c in coeffs.values()))
            quad_error = abs(norm - exact_norm)
            assert quad_error < mp.power(10, -(dps - 5))

            def single_ratio(k, derivative=False):
                values = [mp.sin(2 * mp.pi * k * u) for u in grid]
                shifts = [mp.sin(2 * mp.pi * k * (u + alpha)) - v
                          for u, v in zip(grid, values)]
                residual = mp.sqrt(sum(x ** 2 for x in shifts) / len(grid))
                if derivative:
                    values = [2 * mp.pi * k * mp.cos(2 * mp.pi * k * u) for u in grid]
                target = mp.sqrt(sum(x ** 2 for x in values) / len(grid))
                return target / residual

            sharp_value = abs(single_ratio(kmin) - 1 / dmin)
            sharp_derivative = abs(single_ratio(kderiv, True) - M)
            assert max(sharp_value, sharp_derivative) < mp.power(10, -(dps - 8))
            records.append({"bandwidth": N, "working_dps": dps, "min_denominator_frequency": kmin,
                            "d_min": mp.nstr(dmin, 25), "C_N": mp.nstr(C, 25),
                            "M_N": mp.nstr(M, 25), "shift_residual_l2": mp.nstr(delta, 25),
                            "value_l2": mp.nstr(norm, 25),
                            "derivative_l2": mp.nstr(derivative_norm, 25),
                            "quadrature_error": mp.nstr(quad_error, 25),
                            "sharp_value_constant_error": mp.nstr(sharp_value, 25),
                            "sharp_derivative_constant_error": mp.nstr(sharp_derivative, 25)})
        resonance = []
        for q in (5, 13, 34, 89, 233):
            residual = eps * abs(mp.sin(mp.pi * q * alpha)) / (mp.pi * q)
            assert residual < eps / q ** 2
            resonance.append({"q": q, "shift_residual_sup": mp.nstr(residual, 25),
                              "q_squared_times_residual": mp.nstr(q ** 2 * residual, 25),
                              "generator_ratio_at_normalisation": "1.2",
                              "derivative_l2": mp.nstr(eps / mp.sqrt(2), 25)})
        return records, resonance


def main():
    lo, _ = run(40)
    hi, resonance = run(65)
    with mp.workdps(50):
        for x, y in zip(lo, hi):
            assert abs(mp.mpf(x["M_N"]) - mp.mpf(y["M_N"])) < mp.mpf("1e-22")
    result = {"experiment": "R003-v1", "status": "PASS", "book_date": "2026-10-04",
              "python": platform.python_version(), "mpmath": mp.__version__,
              "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "parameters": {"alpha": "(sqrt(5)-1)/2", "epsilon": "0.2",
                             "bandwidths": [4, 12, 32], "resonant_frequencies": [5, 13, 34, 89, 233]},
              "scope": "Finite Fourier exact models, sampled quadrature, not interval certification.",
              "records": lo + hi, "near_resonances": resonance}
    OUT.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    for row in resonance:
        print(f'q={row["q"]}: residual={row["shift_residual_sup"]}, generator_ratio=1.2')
    print(f"PASS: {OUT}")


if __name__ == "__main__":
    main()
