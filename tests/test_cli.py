"""CLI smoke tests (run in-process via kneser.__main__.main)."""

import math

import pytest

from kneser.__main__ import main


def test_half_exp_default(capsys):
    assert main(["0.5"]) == 0
    out = capsys.readouterr().out.strip()
    assert float(out) == pytest.approx(1.0016400378866632, rel=1e-12)


def test_sexp_slog_iter(capsys):
    assert main(["--sexp", "0.5"]) == 0
    assert main(["--slog", "2.0"]) == 0
    assert main(["--iter", "0.25", "2.0"]) == 0
    lines = capsys.readouterr().out.strip().splitlines()
    assert len(lines) == 3
    assert float(lines[0]) == pytest.approx(1.6463542337511946, rel=1e-12)


def test_digits_mode(capsys):
    assert main(["--digits", "40", "0.5"]) == 0
    out = capsys.readouterr().out.strip()
    assert out.startswith("1.00164003788666318898822972958079943")


def test_table_and_verify(capsys):
    assert main(["--table"]) == 0
    assert main(["--verify"]) == 0
    out = capsys.readouterr().out
    assert "f(x)" in out and "max |f(f(x)) - e^x|" in out
    assert "[-2, 2]" in out and "(float64)" in out


def test_no_args_prints_help(capsys):
    assert main([]) == 2
    assert "half-exponential" in capsys.readouterr().out
