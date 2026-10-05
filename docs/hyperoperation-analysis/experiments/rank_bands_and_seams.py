"""Check actual real-rank bands and exact analytic seam obstructions (R007)."""
from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path
import platform

import mpmath as mp

from rank_band_family import RankBands, RegularSuccessor, profile
from regular_parameter_family import RegularParameterFamily

ROOT = Path(__file__).resolve().parent
REPOSITORY = ROOT.parents[2]


def exact_constant_checks():
    from fractions import Fraction as F

    def exponential_bounds(x, k=12):
        lower = sum(x ** j / math.factorial(j) for j in range(k + 1))
        upper = lower + x ** (k + 1) / (math.factorial(k + 1) * (1 - x / (k + 2)))
        return lower, upper

    assert exponential_bounds(F(263, 1000))[1] < F(4, 3)
    assert exponential_bounds(F(11, 10))[0] > F(25, 9)
    assert exponential_bounds(F(13, 10) * F(262, 1000))[0] > F(14, 10)
    assert exponential_bounds(F(13, 10) * F(263, 1000))[1] < F(141, 100)
    return 4


def run(dps):
    with mp.workdps(dps + 30):
        bands = RankBands(requested_dps=dps)
        seed = bands.seed
        threshold = mp.power(10, -(dps - 4))
        independent_tet = RegularParameterFamily(seed.ell, coordinate_steps=400)
        reference_difference = max(abs(seed.tetration(z) - independent_tet.value(z))
                                   for z in (mp.mpf("0.3"), mp.mpc("0.7", "0.02"), mp.mpf(2)))
        assert reference_difference < threshold

        heights = (mp.mpf("0.25"), mp.mpf("0.8"), mp.mpf("1.6"), mp.mpc("0.7", "0.02"))
        successor_error, endpoint_error, extra_inverse_error, coordinate_shift_error = (mp.mpf(0),) * 4
        states = []
        for fraction in (mp.mpf("0.2"), mp.mpf("0.6"), mp.mpf("0.8")):
            theta = bands.parameter(fraction)
            upper = bands.successor(theta)
            refined = RegularSuccessor(seed, theta, requested_dps=dps, extra_coordinate_steps=16)
            for z in heights:
                lhs = bands.value(4 + fraction, z + 1)
                rhs = bands.value(3 + fraction, bands.value(4 + fraction, z))
                successor_error = max(successor_error, abs(lhs - rhs))
                extra_inverse_error = max(extra_inverse_error, abs(upper.value(z, extra=2) - upper.value(z)))
                coordinate_shift_error = max(coordinate_shift_error, abs(refined.value(z) - upper.value(z)))
            for rank in (3 + fraction, 4 + fraction):
                endpoint_error = max(endpoint_error, abs(bands.value(rank, 0) - 1),
                                     abs(bands.value(rank, 1) - seed.a))
            states.append({"real_rank": mp.nstr(4 + fraction, 8), "seed_parameter": mp.nstr(theta, 18),
                           "fixed_point": mp.nstr(upper.p, 22), "multiplier": mp.nstr(upper.lam, 22),
                           "coordinate_steps": upper.steps,
                           "sample_S_rank_at_half_height": mp.nstr(upper.value(mp.mpf("0.5")), 24)})
        for err in (successor_error, endpoint_error, extra_inverse_error, coordinate_shift_error):
            assert err < threshold, mp.nstr(err, 12)

        anchor_error = mp.mpf(0)
        for z in heights:
            anchor_error = max(anchor_error, abs(bands.value(3, z) - mp.exp(seed.ell * z)),
                               abs(bands.value(4, z) - independent_tet.value(z)),
                               abs(bands.successor(0).value(z) - independent_tet.value(z)))
        anchor_error = max(anchor_error, abs(bands.value(5, 0) - 1), abs(bands.value(5, 1) - seed.a),
                           abs(bands.value(5, 2) - seed.tetration(seed.a)))
        assert anchor_error < threshold

        h2 = mp.power(seed.a, seed.a) - seed.a ** 2
        ha = seed.tetration(seed.a) - mp.power(seed.a, seed.a)
        jump_records = []
        for k in range(5):
            amplitude = mp.mpf(math.factorial(2 * k + 1)) / math.factorial(k)
            # Analytic beta extension permits the exterior probes used by mp.diff;
            # the public profile deliberately restricts real inputs to [0,1].
            beta = lambda s: mp.betainc(k + 1, k + 1, 0, s, regularized=True)
            for s in (mp.mpf("0.2"), mp.mpf("0.5"), mp.mpf("0.8")):
                assert abs(beta(s) - profile(s, order=k)) < threshold
            left = mp.diff(lambda s: seed.a ** 2 + beta(s) * h2, 1, k + 1)
            right = mp.diff(lambda s: mp.power(seed.a, seed.a) + beta(s) * ha, 0, k + 1)
            expected = amplitude * (ha - (-1) ** k * h2)
            assert abs((right - left) - expected) < threshold
            for j in range(1, k + 1):
                assert abs(mp.diff(beta, 0, j)) < threshold
                assert abs(mp.diff(beta, 1, j)) < threshold
            assert abs(expected) > mp.mpf("0.1")
            jump_records.append({"matched_derivatives": k, "next_derivative_jump": mp.nstr(expected, 24)})

        # Different smooth rank clocks have identical integer anchors and flat jets.
        t = mp.mpf(1) / 3
        witness = (profile(t, flat_speed=1) - profile(t, flat_speed=2)) * h2
        assert abs(witness) > mp.mpf("0.01")
        flat_offsets = []
        for h in (mp.mpf("0.1"), mp.mpf("0.05"), mp.mpf("0.025")):
            flat_offsets.append({"distance_to_rank_4": str(h),
                                 "height_2_left_value_offset": mp.nstr((profile(1 - h) - 1) * h2, 24),
                                 "height_2_right_value_offset": mp.nstr(profile(h) * ha, 24)})

        invalid = 0
        for action in (lambda: bands.value(mp.mpc(4, "0.01"), 1), lambda: bands.value(6, 1),
                       lambda: profile(mp.mpf("0.3"), order=-1),
                       lambda: profile(mp.mpf("0.3"), flat_speed=0)):
            try:
                action()
            except ValueError:
                invalid += 1
            else:
                raise AssertionError("invalid family input accepted")
        fmt = lambda x: mp.nstr(x, 24)
        record = {"requested_dps": dps, "outer_working_dps": dps + 30,
                  "seed_engine_working_dps": seed.tet.dps,
                  "independent_tetration_difference_max": fmt(reference_difference),
                  "actual_noninteger_rank_successor_error_max": fmt(successor_error),
                  "normalization_error_max": fmt(endpoint_error), "integer_anchor_error_max": fmt(anchor_error),
                  "extra_inverse_map_seam_error_max": fmt(extra_inverse_error),
                  "sixteen_extra_coordinate_steps_error_max": fmt(coordinate_shift_error),
                  "fractional_rank_states": states, "analytic_join_derivative_jumps": jump_records,
                  "different_flat_rank_clocks_height_2_witness": fmt(witness),
                  "flat_join_value_offsets": flat_offsets, "invalid_input_checks_passed": invalid}
        print(f"Checked dps={dps}: actual fractional real-rank successor error={fmt(successor_error)}", flush=True)
        return record


def main():
    checks = exact_constant_checks()
    records = [run(dps) for dps in (30, 50)]
    inputs = [Path(__file__), ROOT / "rank_band_family.py", ROOT / "regular_parameter_family.py",
              REPOSITORY / "src/kneser/_regular.py", REPOSITORY / "src/kneser/_koenigs.py"]
    result = {"experiment": "R007-v1", "status": "PASS", "date": "2026-10-05",
              "python": platform.python_version(), "mpmath": mp.__version__,
              "input_sha256": {str(p.relative_to(REPOSITORY)): hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in inputs}, "exact_rational_inequalities_checked": checks,
              "records": records,
              "scope": "Actual smooth real ranks 3 through 5 at base 1.3, regular successors. "
                       "Complex height samples are finite-precision diagnostics. No certified complex tube, "
                       "no holomorphic rank join, no all-rank or all-base construction."}
    target = ROOT / "rank-bands-and-seams.json"
    target.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(f"PASS: {target}")


if __name__ == "__main__":
    main()
