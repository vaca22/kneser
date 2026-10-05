"""High-precision path: 50-digit identities and cross-implementation checks.

The REF_* strings were computed by the *independent* implementation in the
sibling research repo (semi_exp, theta-mapping at DEPTH=370/dps=110, residual
~8e-51).  Agreement here is two implementations agreeing on Kneser's
function, not a tautology.
"""

import mpmath as mp
import pytest

import kneser
import kneser.hp as hp

REF = {
    # sexp values (semi_exp/NOTES_half_iterate_exp.md, section 8)
    "sexp(-0.5)": "0.49856328794111443467961909249313329400247186491429",
    "sexp(0.5)": "1.64635423375119458097192403159211451820531164896904",
    # half_exp values (same source)
    "f(0)": "0.49856328794111443467961909249313329400247186491429",
    "f(0.1)": "0.58869690223430341457982046155216196551491273297182",
    "f(0.5)": "1.00164003788666318898822972958079943032768345527882",
    "f(0.9)": "1.50523832100338443762092933325652736664618437988210",
    "f(1.0)": "1.64635423375119458097192403159211451820531164896904",
    # sexp Taylor coefficients at 0 (same source)
    "a1": "1.0917673512583209918013845500271516443847311771937",
    "a2": "0.27148321290169459533170668362354900617398721619906",
    "a3": "0.21245324817625628430896763774094826856663057675559",
}

TOL = mp.mpf("1e-47")  # leaves margin over the ~1e-50 build residuals


def _close(a, b, tol=TOL):
    return abs(mp.mpf(a) - mp.mpf(b)) < tol


def test_cross_implementation_sexp():
    with mp.workdps(60):
        assert _close(hp.sexp("-0.5", dps=55), REF["sexp(-0.5)"])
        assert _close(hp.sexp("0.5", dps=55), REF["sexp(0.5)"])


def test_cross_implementation_half_exp():
    with mp.workdps(60):
        for x, key in [("0", "f(0)"), ("0.1", "f(0.1)"), ("0.5", "f(0.5)"),
                       ("0.9", "f(0.9)"), ("1.0", "f(1.0)")]:
            assert _close(hp.half_exp(x, dps=55), REF[key]), key


def test_cross_implementation_taylor_coefficients():
    from kneser import _coeffs
    with mp.workdps(60):
        for k, key in [(1, "a1"), (2, "a2"), (3, "a3")]:
            assert _close(mp.mpf(_coeffs.COEFFS[k]), REF[key]), key


def test_functional_equation_50_digits():
    with mp.workdps(60):
        worst = mp.mpf(0)
        for i in range(-15, 16):
            x = mp.mpf(i) / 10
            err = abs(hp.half_exp(hp.half_exp(x, dps=55), dps=55) - mp.exp(x))
            worst = max(worst, err)
        assert worst < mp.mpf("1e-46"), mp.nstr(worst, 5)


def test_sexp_functional_equation_50_digits():
    with mp.workdps(60):
        for i in range(-14, 21):
            z = mp.mpf(i) / 10
            err = abs(hp.sexp(z + 1, dps=55) - mp.exp(hp.sexp(z, dps=55)))
            assert err < mp.mpf("1e-46"), f"z={z}: {mp.nstr(err, 5)}"


def test_exp_iter_recovers_exp_and_log():
    with mp.workdps(60):
        # third-iterates composed three times = exp, at full precision
        for xs in ["0", "0.7", "1.3"]:
            v = mp.mpf(xs)
            for _ in range(3):
                v = hp.exp_iter(v, mp.mpf(1) / 3, dps=55)
            assert abs(v - mp.exp(mp.mpf(xs))) < mp.mpf("1e-46")
        # fractional split of -1: exp^[-0.5] twice = log
        v = hp.exp_iter(hp.exp_iter("2", "-0.5", dps=55), "-0.5", dps=55)
        assert abs(v - mp.log(2)) < mp.mpf("1e-46")


def test_slog_roundtrip_hp():
    with mp.workdps(60):
        for zs in ["-1.5", "-0.7", "0", "0.9", "2.2"]:
            z = mp.mpf(zs)
            assert abs(hp.slog(hp.sexp(z, dps=55), dps=55) - z) < mp.mpf("1e-46")


def test_float_path_agrees_with_hp():
    with mp.workdps(30):
        for x in [-2.0, -0.3, 0.0, 0.4, 1.0, 2.3]:
            a = kneser.half_exp(x)
            b = hp.half_exp(x, dps=25)
            assert abs(mp.mpf(a) - b) < mp.mpf("1e-12"), f"x={x}"
