"""Reproduce R001 using analytic and repository Kneser superfunctions.

No claim of interval certification or canonical uniqueness is made.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import platform
import sys

import mpmath as mp

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "src"))
from kneser import hp  # noqa: E402

OUT = Path(__file__).with_name("rational-time.json")


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run(dps):
    with mp.workdps(dps + 15):
        eps, q = mp.mpf("0.2"), 12
        times = [mp.mpf(1) / k for k in (2, 3, 4, 6)]
        other_times = [mp.mpf(1) / 5, mp.sqrt(2) / 10]
        heights = [mp.mpf(s) for s in ("-0.4", "0", "0.35", "1")]

        def P(u):
            return u + eps * mp.sin(2 * mp.pi * q * u) / (2 * mp.pi * q)

        def invP(y):
            # Global bracket follows from |P(u)-u| <= amplitude.
            amplitude = abs(eps) / (2 * mp.pi * q)
            lo, hi = y - 2 * amplitude, y + 2 * amplitude
            for _ in range(int((dps + 15) * 3.5) + 30):
                mid = (lo + hi) / 2
                if P(mid) < y:
                    lo = mid
                else:
                    hi = mid
            return (lo + hi) / 2

        models = [
            ("analytic_exp_superfunction", mp.exp, lambda x: mp.e * x),
            ("repository_kneser_e", lambda z: hp.sexp(z, dps=dps), mp.exp),
        ]
        records = []
        for name, S, f in models:
            inverse_errors, retained, fe = [], [], []
            witnesses, samples = [], []
            for u in heights:
                v = invP(u)
                inverse_errors.append(abs(P(v) - u))
                for t in times:
                    ref, changed = S(u + t), S(P(v + t))
                    retained.append(abs(ref - changed))
                    samples.append({"abel_coordinate": mp.nstr(u, 18),
                                    "x": mp.nstr(S(u), 25),
                                    "time": mp.nstr(t, 25),
                                    "difference": mp.nstr(changed - ref, 18)})
                for t in other_times:
                    witnesses.append({"abel_coordinate": mp.nstr(u, 18),
                                      "time": mp.nstr(t, 25),
                                      "difference": mp.nstr(S(P(v + t)) - S(u + t), 25)})
                fe.append(abs(S(P(u + 1)) - f(S(P(u)))))
            # A witness at the normalised point must be observably different.
            witness_at_zero = abs(S(P(other_times[0])) - S(other_times[0]))
            slope_step = mp.mpf("1e-10")
            measured_ratio = ((S(P(slope_step)) - S(P(-slope_step)))
                              / (S(slope_step) - S(-slope_step)))
            assert max(inverse_errors) < mp.mpf(10) ** (-(dps + 5))
            assert max(retained) < mp.mpf("1e-29")
            assert max(fe) < mp.mpf("1e-29")
            assert witness_at_zero > mp.mpf("1e-5")
            assert abs(measured_ratio - (1 + eps)) < mp.mpf("1e-14")
            records.append({
                "model": name, "working_dps": dps,
                "inverse_residual_max": mp.nstr(max(inverse_errors), 25),
                "retained_time_difference_max": mp.nstr(max(retained), 25),
                "superfunction_residual_max": mp.nstr(max(fe), 25),
                "witness_at_zero_time_one_fifth": mp.nstr(witness_at_zero, 30),
                "generator_ratio_at_normalisation": "1.2",
                "central_difference_generator_ratio": mp.nstr(measured_ratio, 30),
                "central_difference_generator_step": "1e-10",
                "samples": samples, "other_time_witnesses": witnesses,
            })

        # A compact C0 comparison as q rises, while exact slope ratio stays 1.2.
        sequence = []
        for freq in (1, 4, 12, 48, 192):
            amp = eps / (2 * mp.pi * freq)
            grid = [mp.mpf(k) / 997 for k in range(998)]
            max_error = max(abs(mp.exp(t + amp * mp.sin(2 * mp.pi * freq * t))
                                - mp.exp(t)) for t in grid)
            rigorous_bound = mp.exp(1 + abs(amp)) * abs(amp)
            assert max_error <= rigorous_bound
            sequence.append({"q": freq, "grid_max_value_difference": mp.nstr(max_error, 20),
                             "analytic_compact_bound": mp.nstr(rigorous_bound, 20),
                             "generator_ratio_at_one": "1.2"})
        return records, sequence


def main():
    all_records, sequence = [], None
    for dps in (35, 50):
        records, sequence = run(dps)
        all_records.extend(records)
    stable = []
    with mp.workdps(50):
        for lo, hi in zip(all_records[:2], all_records[2:]):
            diff = abs(mp.mpf(lo["witness_at_zero_time_one_fifth"])
                       - mp.mpf(hi["witness_at_zero_time_one_fifth"]))
            assert diff < mp.mpf("1e-28")
            stable.append({"model": lo["model"], "witness_precision_difference": mp.nstr(diff, 20)})
    input_paths = [Path(__file__), ROOT / "src/kneser/hp.py", ROOT / "src/kneser/_coeffs.py",
                   ROOT / "src/kneser/_bases.py", ROOT / "src/kneser/__init__.py"]
    result = {
        "experiment": "R001-v1", "status": "PASS", "book_date": "2026-10-04",
        "python": platform.python_version(), "mpmath": mp.__version__,
        "parameters": {"epsilon": "0.2", "q": 12,
                       "retained_times": ["1/2", "1/3", "1/4", "1/6"],
                       "witness_times": ["1/5", "sqrt(2)/10"]},
        "scope": "Finite sample diagnostics, not certified global error bounds. Kneser coefficients: 50 digits.",
        "input_sha256": {str(p.relative_to(ROOT)): digest(p) for p in input_paths},
        "records": all_records, "precision_comparison": stable,
        "high_frequency_sequence": sequence,
    }
    OUT.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    for item in all_records:
        print(f'{item["model"]} dps={item["working_dps"]}: '
              f'retained={item["retained_time_difference_max"]}, '
              f'witness={item["witness_at_zero_time_one_fifth"]}')
    print(f"PASS: {OUT}")


if __name__ == "__main__":
    main()
