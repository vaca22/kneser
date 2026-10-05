"""Independent central-difference checks of the fixed-endpoint model in R002."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import platform

import mpmath as mp

OUT = Path(__file__).with_name("linear-response.json")


def run(dps):
    with mp.workdps(dps):
        a = mp.mpf("1.3")
        c = a - 1

        def S(lam, t):
            if lam == 1:
                return 1 + c * t
            return 1 + c * mp.expm1(t * mp.log(lam)) / (lam - 1)

        def D(lam, t):
            if lam == 1:
                return c
            return c * mp.power(lam, t) * mp.log(lam) / (lam - 1)

        def B(lam, t):
            if lam == 1:
                return c * t * (t - 1) / 2
            return c * (t * mp.power(lam, t - 1) * (lam - 1)
                        - mp.expm1(t * mp.log(lam))) / (lam - 1) ** 2

        def W(lam, t):
            return B(lam, t) / D(lam, t)

        grid = [mp.mpf(s) for s in ("-0.5", "0", "0.25", "0.7", "1", "1.5", "2.2")]
        records = []
        for lam_text in ("0.4", "0.8", "1", "1.4"):
            lam = mp.mpf(lam_text)
            fe, linear, reduced, flow = [], [], [], []
            fd_errors = [[], []]
            for t in grid:
                fe.append(abs(S(lam, t + 1) - (a + lam * (S(lam, t) - 1))))
                linear.append(abs(B(lam, t + 1) - lam * B(lam, t) - (S(lam, t) - 1)))
                reduced.append(abs(W(lam, t + 1) - W(lam, t)
                                   - (S(lam, t) - 1) / D(lam, t + 1)))
                for index, h_text in enumerate(("0.0001", "0.00005")):
                    h = mp.mpf(h_text)
                    fd = (S(lam + h, t) - S(lam - h, t)) / (2 * h)
                    fd_errors[index].append(abs(fd - B(lam, t)))
            # Actual affine flow at fixed x; inverse S is closed form here.
            def A(lam_value, x):
                if lam_value == 1:
                    return (x - 1) / c
                return mp.log1p((lam_value - 1) * (x - 1) / c) / mp.log(lam_value)

            for x_text in ("1", "1.1", "1.2"):
                x = mp.mpf(x_text)
                for t_text in ("0.25", "0.6"):
                    t = mp.mpf(t_text)
                    u = A(lam, x)
                    predicted = D(lam, u + t) * (W(lam, u + t) - W(lam, u))
                    h = mp.mpf("0.00001")
                    exact_fd = (S(lam + h, A(lam + h, x) + t)
                                - S(lam - h, A(lam - h, x) + t)) / (2 * h)
                    flow.append(abs(exact_fd - predicted))
            threshold = mp.power(10, -(dps - 8))
            assert max(fe) < threshold
            assert max(linear) < threshold
            assert max(reduced) < threshold
            assert abs(B(lam, 0)) < threshold and abs(B(lam, 1)) < threshold
            assert max(fd_errors[1]) < max(fd_errors[0]) / mp.mpf("3.9")
            assert max(fd_errors[0]) < mp.mpf("1e-6")
            assert max(flow) < mp.mpf("1e-8")
            records.append({
                "lambda": lam_text, "working_dps": dps,
                "superfunction_residual_max": mp.nstr(max(fe), 25),
                "linear_response_residual_max": mp.nstr(max(linear), 25),
                "reduced_difference_residual_max": mp.nstr(max(reduced), 25),
                "endpoint_response_max": mp.nstr(max(abs(B(lam, 0)), abs(B(lam, 1))), 25),
                "central_difference_error_h_1e_4": mp.nstr(max(fd_errors[0]), 25),
                "central_difference_error_h_5e_5": mp.nstr(max(fd_errors[1]), 25),
                "error_ratio_when_h_halved": mp.nstr(max(fd_errors[0]) / max(fd_errors[1]), 20),
                "flow_response_central_difference_error_max": mp.nstr(max(flow), 25),
                "response_at_t_0_7": mp.nstr(B(lam, mp.mpf("0.7")), 30),
            })
        return records


def main():
    records = run(40) + run(65)
    with mp.workdps(50):
        for lo, hi in zip(records[:4], records[4:]):
            assert abs(mp.mpf(lo["response_at_t_0_7"])
                       - mp.mpf(hi["response_at_t_0_7"])) < mp.mpf("1e-28")
    result = {
        "experiment": "R002-v1", "status": "PASS", "book_date": "2026-10-04",
        "python": platform.python_version(), "mpmath": mp.__version__,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "parameters": {"base_anchor": "1.3", "lambdas": ["0.4", "0.8", "1", "1.4"],
                       "height_grid": ["-0.5", "0", "0.25", "0.7", "1", "1.5", "2.2"],
                       "central_difference_steps": ["0.0001", "0.00005"]},
        "scope": "Exact affine model plus finite precision diagnostics. Does not construct fractional rank.",
        "records": records,
    }
    OUT.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    for item in records:
        print(f'lambda={item["lambda"]} dps={item["working_dps"]}: '
              f'linear residual={item["linear_response_residual_max"]}, '
              f'FD ratio={item["error_ratio_when_h_halved"]}')
    print(f"PASS: {OUT}")


if __name__ == "__main__":
    main()
