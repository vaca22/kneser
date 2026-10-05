"""Independent small-loop checks of the exploratory analytic bracket."""

import importlib.util
from pathlib import Path

import mpmath as mp


_path = Path(__file__).resolve().parents[1] / "docs" / "demo_mixed_base_bracket.py"
_spec = importlib.util.spec_from_file_location("mixed_base_demo", _path)
demo = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(demo)


def test_commutator_sign_and_quadratic_extrapolation():
    with mp.workdps(50):
        f, g = demo.Flow("e", 50), demo.Flow("2", 50)
        x = mp.mpf(1)
        b = demo.bracket(f, g, x)
        assert b < 0
        errors = []
        for h in [mp.mpf("0.01"), mp.mpf("0.005")]:
            measured = (demo.loop(f, g, x, h)+demo.loop(f, g, x, -h)-2*x)/(2*h*h)
            errors.append(abs(measured-b))
        assert mp.mpf("3.9") < errors[0]/errors[1] < mp.mpf("4.1")
        assert errors[1] < mp.mpf("1e-5")
        assert abs(demo.loop(f, f, x, mp.mpf("0.01"))-x) < mp.mpf("1e-40")


def test_bracket_zero_still_has_cubic_drift():
    with mp.workdps(50):
        f, g = demo.Flow("e", 50), demo.Flow("2", 50)
        root = mp.findroot(lambda x: demo.bracket(f, g, x), (mp.mpf("2.6"), mp.mpf("2.65")))
        delta = mp.mpf("1e-10")
        bp = (demo.bracket(f, g, root+delta)-demo.bracket(f, g, root-delta))/(2*delta)
        prediction = (f.velocity(root)[0]+g.velocity(root)[0])*bp/2
        h = mp.mpf("1e-5")
        measured = (demo.loop(f, g, root, h)-root)/h**3
        assert prediction > mp.mpf("0.9")
        assert abs(measured-prediction) < mp.mpf("3e-6")


def test_nested_bracket_asymptotic_low_orders():
    result = demo.nested_probe(50)
    for row in result["rows"]:
        ratios = [mp.mpf(p["ratio"]) for p in row["measured_over_leading_term"]]
        assert abs(ratios[-1]-1) < mp.mpf("3e-6")
        assert abs(ratios[-1]-1) < abs(ratios[0]-1)/1000
