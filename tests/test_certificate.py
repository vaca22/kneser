"""Re-check the cheap parts of docs/error-certificate.md (interval arithmetic).

Runs docs/demo_certificate.py in --quick mode for the shipped tables and
asserts the certified bounds quoted in the markdown, with a safety margin.
Everything here is rigorous interval arithmetic (mpmath.iv); nothing is a
floating-point spot check.
"""

from __future__ import annotations

import importlib.util
import pathlib

import mpmath as mp
import pytest

HERE = pathlib.Path(__file__).resolve().parent
SCRIPT = HERE.parent / "docs" / "demo_certificate.py"


def _load():
    spec = importlib.util.spec_from_file_location("demo_certificate", SCRIPT)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture(scope="module")
def cert():
    mod = _load()
    from kneser import _coeffs, _coeffs_2
    return mod, mod.certify(_coeffs, name="e", quick=True), mod.certify(_coeffs_2, name="2", quick=True)


def _agrees(mod, interval, decimal, tol="1e-52"):
    """The decimal (a rounded print-out) agrees with the enclosure to within tol."""
    t = mp.mpf(tol)
    return mod.lo(interval) - t <= mp.mpf(decimal) <= mod.hi(interval) + t


def test_rung1_polynomial_e(cert):
    mod, e, _ = cert
    assert e["C_env"] < 2.2                       # |c_k| <= 2.2 * 2^-k
    assert e["C_log"] < 7.8                       # |c_k| <= 7.8 * 2^-k / k
    assert e["S1"] < 1.6464
    assert e["f64_bound"] < mp.mpf("5.5e-14")     # float64 Horner on |z| <= 1/2
    assert e["mp_bound_50"] < mp.mpf("4e-59")     # mpmath Horner at dps=50


def test_rung2_seam_defect_e(cert):
    mod, e, _ = cert
    assert mod.hi(abs(e["seam"])) < mp.mpf("2.62e-52")
    assert e["profile"]["1/8"] < mp.mpf("4e-52")
    assert e["profile"]["1/4"] < mp.mpf("7.1e-52")
    assert e["profile"]["1/2"] < mp.mpf("1e-47")
    # C^m mismatch at the seam z = 1/2
    assert mod.hi(abs(e["Dm"][1])) < mp.mpf("6e-52")
    assert mod.hi(abs(e["Dm"][2])) < mp.mpf("7e-51")
    assert e["convex"] and e["increasing"]
    assert mod.lo(e["Pd_range"]) > 0.95 and mod.hi(e["Pd_range"]) < 1.58


def test_rung3_seam_jumps_e(cert):
    mod, e, _ = cert
    J = e["J"]
    assert J[0] < mp.mpf("2.62e-52")
    assert J[1] < mp.mpf("1.36e-51")
    assert J[2] < mp.mpf("2.44e-49")
    assert e["Jm"][0] < mp.mpf("1.6e-52")
    assert e["Jm"][1] < mp.mpf("3.2e-52")
    assert e["Lambda"][1] < 5.19 and e["Lambda"][2] < 930


def test_rung4_table_constants_e(cert):
    mod, e, _ = cert
    with mp.workdps(80):
        assert _agrees(mod, e["sexp_half"], "1.6463542337511945809719240315921145182053116489690416")
        assert _agrees(mod, e["sexp_mhalf_lib"], "0.49856328794111443467961909249313329400247186492241935")
        assert _agrees(mod, e["fprime0_left"], "0.87633613222481309394808927154811959614628509947979705")
        assert _agrees(mod, e["half_exp_half"], "1.0016400378866631889882297295807994303276834552788148")
        assert _agrees(mod, e["asymptote"], "-0.69602474088608417173296092502920405275724683287608229")
        # the README's float64 quotes are consistent with the table
        assert abs(float(mod.lo(e["sexp_half"])) - 1.6463542337511945) < 1e-15
        assert abs(float(mod.lo(e["fprime0_left"])) - 0.8763361322248131) < 1e-15
        # width of every enclosure is far below the seam residual
        for key in ("sexp_half", "sexp_mhalf_lib", "fprime0_left", "half_exp_half"):
            assert mod.hi(e[key]) - mod.lo(e[key]) < mp.mpf("1e-65")


def test_base2_table(cert):
    mod, _, t2 = cert
    assert t2["f64_bound"] < mp.mpf("1e-13")
    assert mod.hi(abs(t2["seam"])) < mp.mpf("8e-53")
    assert t2["profile"]["1/8"] < mp.mpf("1e-50")
    assert t2["increasing"] and not t2["convex"]   # base-2 P has an inflection point
    assert t2["J"][0] < mp.mpf("8e-53")
    with mp.workdps(80):
        assert _agrees(mod, t2["sexp_half"], "1.4587818160364217006839716610385871352966066053309071")
        assert _agrees(mod, t2["fprime0_left"], "0.74798531300884998942109549476750834455376111423689544")
