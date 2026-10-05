"""Interval certificates for the shipped series.

phi'' > 0 and the strong-B sign chart are theorems about the coefficients
in src/kneser/_coeffs.py.  They need python-flint, and they are not part
of the default test job.
"""

import pytest

pytest.importorskip("flint")

pytestmark = pytest.mark.research


def test_phi_log_convex():
    from docs.certify_phi_log_convex import certify

    report = certify(verbose=False)
    assert report["x_star_upper"] < 0.5


def test_strong_b_sign_chart():
    from docs.certify_strong_b import certify

    report = certify(verbose=False)
    assert report["small_q"]["q_rho_lower"] > 1
    assert report["positive_gap_cells"] > 0
    assert report["mid_left_cells"] > 0
    assert float(report["past_minus_40_upper"]) < 0
    assert float(report["q24_near_zero_upper"]) < 0
    assert report["rectangle_cells"] > 0
    assert report["complement_cells"] > 0
    assert float(report["large_return"]["rho_right_lower"]) > 0
