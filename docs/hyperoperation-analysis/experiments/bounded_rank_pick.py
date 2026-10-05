"""R009: exact two-anchor obstruction and finite complex-rank diagnostics."""
from __future__ import annotations

from fractions import Fraction as F
import hashlib
import json
import math
from pathlib import Path
import platform

import mpmath as mp

from bounded_rank_interpolation import FiniteSchur, blaschke_bound, minimum_bound, pick_matrix
from rank_band_family import SeedBand
from regular_parameter_family import RegularParameterFamily

ROOT = Path(__file__).resolve().parent
REPOSITORY = ROOT.parents[2]


def exact_obstruction():
    a, q, n = F(13, 10), F(3, 23), 12
    log_lower = 2*sum(q**(2*j+1)/F(2*j+1) for j in range(n))
    log_upper = log_lower + 2*q**(2*n+1)/(F(2*n+1)*(1-q*q))

    def exp_bounds(x, k=24):
        low = sum(x**j/F(math.factorial(j)) for j in range(k+1))
        high = low + x**(k+1)/(F(math.factorial(k+1))*(1-x/F(k+2)))
        return low, high

    b_lower, b_upper = F(1406456, 1000000), F(1406457, 1000000)
    assert exp_bounds(a*log_lower)[0] > b_lower
    assert exp_bounds(a*log_upper)[1] < b_upper
    m, anchor, t = F(185, 100), F(169, 100), F(1086, 1000)
    derivative_at_upper = t*anchor-2*t*t*b_upper/3
    quadratic_at_upper = m*m-anchor*anchor-t*(m*m-anchor*b_upper)+t*t*(m*m-b_upper*b_upper)/3
    assert derivative_at_upper > 0
    assert quadratic_at_upper == F(-319179930078267, 250000000000000000) < 0

    # Constants for the paper's actual E,T common self-map disk lemma.
    assert log_lower > F(262, 1000) and log_upper < F(263, 1000)
    assert exp_bounds(F(263, 1000)*F(5, 2))[1]*F(263, 1000) < F(51, 100)
    assert exp_bounds(F(263, 1000)*F(6, 5))[1] < F(7, 5)
    assert F(44, 100)**10 > F(4, 10)**9
    assert F(26, 100)-F(32, 55)*F(26, 100)**2 > F(22, 100)
    assert exp_bounds(F(21, 100))[0] > F(70, 57)
    assert F(3, 10)+F(21, 100)/F(262, 1000) < F(111, 100)
    return {"certified": True, "arithmetic": "Python fractions.Fraction; rational series bounds",
            "sigma": "5/2", "nodes": [3, 4], "height": 2, "base": "13/10",
            "excluded_supremum_bound": str(m), "second_anchor_strict_lower": str(b_lower),
            "second_anchor_strict_upper": str(b_upper), "test_vector": ["1", str(-t)],
            "quadratic_form_upper_bound": str(quadratic_at_upper),
            "quadratic_form_derivative_lower_bound": str(derivative_at_upper),
            "scope": "No bounded holomorphic scalar rank slice on Re r>5/2 with these two anchors "
                     "has supremum norm <=37/20. Does not exclude larger bounds or other domains."}


def run(dps):
    with mp.workdps(dps+50):
        sigma, a = mp.mpf("2.5"), mp.mpf(13)/10
        family = RegularParameterFamily(mp.log(a), coordinate_steps=700)
        seed = SeedBand(requested_dps=dps+15)
        values = [a*a, a**a, family.value(a)]
        reference_error = abs(values[2]-seed.tetration(a))
        threshold = mp.power(10, -(dps-5))
        assert reference_error < threshold
        minima = [minimum_bound(range(3, last+1), values[:last-2], sigma=sigma) for last in (3, 4, 5)]
        assert minima[0] < minima[1] < minima[2] < 2
        eig_good = mp.eighe(pick_matrix((3, 4, 5), values, sigma=sigma, bound=2), eigvals_only=True)[0]
        eig_bad = mp.eighe(pick_matrix((3, 4), values[:2], sigma=sigma, bound="1.85"), eigvals_only=True)[0]
        assert eig_good > 0 > eig_bad
        f0 = FiniteSchur((3, 4, 5), values, sigma=sigma, bound=2)
        f1 = FiniteSchur((3, 4, 5), values, sigma=sigma, bound=2, free=mp.mpc("0.6", "0.1"))
        anchor_error = max(abs(f.value(n)-v) for f in (f0, f1) for n, v in zip((3, 4, 5), values))
        assert anchor_error < threshold
        records = []
        for rank in (mp.mpc("3.5"), mp.mpc("4.2", "0.4"), mp.mpc("2.8", "0.3")):
            v0, v1 = f0.value(rank), f1.value(rank)
            bound = 4*blaschke_bound(rank, sigma=sigma, last=5)
            assert abs(v0) <= 2 and abs(v1) <= 2 and abs(v0-v1) <= bound
            product = blaschke_bound(rank, sigma=sigma, last=5)
            gamma_value = abs(mp.gamma(6-rank)*mp.gamma(3+rank-2*sigma)
                              /(mp.gamma(3-rank)*mp.gamma(6+rank-2*sigma)))
            assert abs(product-gamma_value) < threshold
            records.append({"rank": str(rank), "free_zero_value": mp.nstr(v0, 24),
                            "free_complex_value": mp.nstr(v1, 24), "difference": mp.nstr(abs(v0-v1), 24),
                            "analytic_diameter_bound": mp.nstr(bound, 24)})
        assert abs(f0.value(mp.mpf("3.5"))-f1.value(mp.mpf("3.5"))) > mp.mpf("1e-5")
        assert abs(blaschke_bound(mp.mpf("3.5"), sigma=sigma, last=5)-mp.mpf(1)/35) < threshold

        # Known complete bounded function to independently check truncation bounds.
        model = lambda rank: (rank-sigma)/(rank-sigma+1)
        calibration = []
        for last in (4, 8, 16, 32):
            nodes = tuple(range(3, last+1))
            f = FiniteSchur(nodes, tuple(model(n) for n in nodes), sigma=sigma,
                            bound="1.2", free=mp.mpc("0.5", "0.1"))
            for rank in (mp.mpc("3.5"), mp.mpc("4.2", "0.4")):
                error = abs(f.value(rank)-model(rank))
                bound = mp.mpf("2.4")*blaschke_bound(rank, sigma=sigma, last=last)
                assert error <= bound
                calibration.append({"last_integer_node": last, "rank": str(rank),
                                    "actual_error": mp.nstr(error, 24), "analytic_error_bound": mp.nstr(bound, 24)})
        exact_model = lambda rank: (rank-sigma-1)/(rank-sigma+1)
        assert abs(minimum_bound((3, 4), [exact_model(3), exact_model(4)], sigma=sigma)-1) < threshold

        invalid = 0
        actions = (lambda: FiniteSchur((3, 3), (1, 1), sigma=sigma, bound=2),
                   lambda: FiniteSchur((2, 3), (1, 1), sigma=sigma, bound=2),
                   lambda: FiniteSchur((3,), (1,), sigma=sigma, bound=2, free=2),
                   lambda: FiniteSchur((3, 4), values[:2], sigma=sigma, bound="1.85"),
                   lambda: f0.value(sigma), lambda: blaschke_bound(4, sigma=sigma, last=True))
        for action in actions:
            try:
                action()
            except ValueError:
                invalid += 1
            else:
                raise AssertionError("invalid input accepted")
        fmt = lambda x: mp.nstr(x, 24)
        print(f"Checked dps={dps}: three-anchor minimum={fmt(minima[2])}", flush=True)
        return {"requested_dps": dps, "actual_working_dps": dps+50,
                "actual_height_two_anchors": [fmt(v) for v in values],
                "finite_minimum_bounds_one_two_three_anchors": [fmt(v) for v in minima],
                "smallest_three_point_pick_eigenvalue_at_bound_two": fmt(eig_good),
                "smallest_two_point_pick_eigenvalue_at_bound_1_85": fmt(eig_bad),
                "independent_tetration_reference_error": fmt(reference_error),
                "finite_interpolant_anchor_error_max": fmt(anchor_error),
                "actual_data_finite_interpolants": records, "known_model_truncation_checks": calibration,
                "invalid_input_checks_passed": invalid,
                "three_anchor_minimum_interval_certified": False,
                "all_integer_all_height_pick_positivity_established": False,
                "actual_global_complex_rank_constructed": False}


def main():
    certificate = exact_obstruction()
    records = [run(dps) for dps in (40, 60)]
    inputs = [Path(__file__), ROOT / "bounded_rank_interpolation.py", ROOT / "rank_band_family.py",
              ROOT / "regular_parameter_family.py", REPOSITORY / "src/kneser/_regular.py",
              REPOSITORY / "src/kneser/_koenigs.py", REPOSITORY / "src/kneser/_bases.py"]
    result = {"experiment": "R009-v1", "status": "PASS", "date": "2026-10-05",
              "python": platform.python_version(), "mpmath": mp.__version__,
              "input_sha256": {str(p.relative_to(REPOSITORY)): hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in inputs}, "exact_two_anchor_certificate": certificate,
              "records": records,
              "scope": "Exact rational two-anchor norm obstruction; finite Schur and Pick diagnostics. "
                       "Infinite bounded interpolation and automatic successor are conditional paper theorems; "
                       "the complete actual integer chain on a common height disk has not been verified."}
    target = ROOT / "bounded-rank-pick.json"
    target.write_text(json.dumps(result, ensure_ascii=False, indent=2)+"\n")
    print(f"PASS: {target}")


if __name__ == "__main__":
    main()
