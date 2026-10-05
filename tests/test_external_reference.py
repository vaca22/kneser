"""Cross-check this library against an *independent* implementation.

Every other test in this suite is self-referential: it checks the residual
|f(f(x)) - e^x|, the seam defect, or the interval-arithmetic certificate of
our own tables.  A small residual bounds how well the table solves the
functional equation; it does **not** bound the distance to Kneser's solution,
because the Abel function still has the theta degree of freedom
(docs/error-certificate.md, last section).

This file closes that gap from the outside.  ``tests/data/external_reference.json``
holds values computed with PARI/GP by an optimised fork of sheldonison's
``fatou.gp`` -- a completely different construction, language, and author --
published on the Tetration Forum (see ``_source`` in that file and
docs/external-validation.md).  Agreeing with it to 52 digits is evidence
about the *solution*, not just about the residual.

The complex-base tests at the bottom record a real disagreement; read
docs/external-validation.md before "fixing" them.
"""

from __future__ import annotations

import json
import pathlib

import mpmath as mp
import pytest

import kneser
from kneser import hp

DATA = pathlib.Path(__file__).resolve().parent / "data" / "external_reference.json"


@pytest.fixture(scope="module")
def ref():
    with open(DATA) as fh:
        return json.load(fh)["values"]


def _value(entry):
    """mpf/mpc at the current precision (the strings carry 80+ digits)."""
    re_, im = mp.mpf(entry["real"]), mp.mpf(entry["imag"])
    return mp.mpc(re_, im) if im != 0 else re_


def _grid(ref, family, base, dps="80"):
    prefix = f"{family}|{base}|"
    suffix = f"|{dps}"
    for key, entry in ref.items():
        if key.startswith(prefix) and key.endswith(suffix):
            yield key.split("|")[2], _value(entry)


def _worst(pairs):
    worst, where = mp.mpf(0), None
    for height, theirs, ours in pairs:
        if theirs == 0:
            err = abs(ours)
        else:
            err = abs(ours - theirs) / abs(theirs)
        if err > worst:
            worst, where = err, height
    return worst, where


# --------------------------------------------------------------------------
# baked 50-digit tables: bases e and 2
# --------------------------------------------------------------------------

@pytest.mark.parametrize("family,base,kw", [
    ("sexp", "e", {}),
    ("slog", "e", {}),
    ("sexp", "2", {"base": 2}),
    ("slog", "2", {"base": 2}),
])
def test_baked_tables_match_fatou_gp_to_50_digits(ref, family, base, kw):
    """Our 50-digit tables reproduce fatou.gp's 80-digit values to ~52 digits."""
    with mp.workdps(100):
        fn = hp.sexp if family == "sexp" else hp.slog
        pairs = [(h, theirs, fn(h, dps=50, **kw))
                 for h, theirs in _grid(ref, family, base)]
        assert len(pairs) == 16
        worst, where = _worst(pairs)
        assert worst < mp.mpf("1e-50"), f"{family} base {base} at {where}: {mp.nstr(worst, 3)}"


@pytest.mark.parametrize("base,kw", [("e", {}), ("2", {"base": 2})])
def test_half_height_matches_the_deep_reference(ref, base, kw):
    """sexp_b(1/2) against the 200-digit entries (upstream: >=194 proven digits)."""
    with mp.workdps(260):
        theirs = _value(ref[f"sexp|{base}|0.5|200"])
        ours = hp.sexp("0.5", dps=50, **kw)
        assert abs(ours - theirs) / theirs < mp.mpf("1e-50")


def test_deep_base_e_entries_are_mutually_consistent(ref):
    """The 200/500/700/1000-digit sexp_e(1/2) entries all extend our 50 digits."""
    with mp.workdps(1100):
        ours = hp.sexp("0.5", dps=50)
        for dps in ("200", "500", "700", "1000"):
            theirs = _value(ref[f"sexp|e|0.5|{dps}"])
            assert abs(ours - theirs) / theirs < mp.mpf("1e-50"), dps


def test_known_bad_upstream_entry_is_still_bad(ref):
    """sexp|2|0.5|1000 upstream is wrong from digit ~44; see _known_bad in the JSON.

    Its own 200- and 500-digit entries agree with each other in full and with
    this library to 53 digits, so the 1000-digit entry is the outlier.  The
    assertion is inverted on purpose: if it ever starts passing, upstream has
    republished the value and the note in docs/external-validation.md (and the
    forum report) can be retired.
    """
    with mp.workdps(1100):
        ours = hp.sexp("0.5", dps=50, base=2)
        bad = _value(ref["sexp|2|0.5|1000"])
        rel = abs(ours - bad) / bad
        assert mp.mpf("1e-43") < rel < mp.mpf("1e-41"), mp.nstr(rel, 3)


# --------------------------------------------------------------------------
# on-demand table: base 10 (built by kneser.build, not baked)
# --------------------------------------------------------------------------

@pytest.mark.parametrize("family", ["sexp", "slog"])
def test_on_demand_base_10_table_matches_fatou_gp(ref, family):
    """The table kneser.build makes on first use is right to its nominal digits."""
    kneser.prepare(10, 17)
    with mp.workdps(100):
        fn = hp.sexp if family == "sexp" else hp.slog
        pairs = [(h, theirs, fn(h, dps=17, base=10))
                 for h, theirs in _grid(ref, family, "10")]
        assert len(pairs) == 16
        worst, where = _worst(pairs)
        assert worst < mp.mpf("1e-17"), f"{family} base 10 at {where}: {mp.nstr(worst, 3)}"


# --------------------------------------------------------------------------
# complex bases: a documented disagreement, not a bug
# --------------------------------------------------------------------------

# base -> (our engine's answer differs from fatou.gp by roughly this much).
# All three bases are *inside* the Shell-Thron region, where we return the
# regular Koenigs superfunction at the attracting fixed point and fatou.gp
# returns the merged two-fixed-point solution.  Both solve sexp(z+1) = b^sexp(z)
# with sexp(0) = 1; they differ by a non-trivial 1-periodic function, and the
# gap grows as |lambda| -> 1 (the Shell-Thron boundary).
INSIDE_SHELL_THRON = {
    "0.8+0.4*I": ("0.8+0.4j", "1e-4"),
    "1+I": ("1+1j", "4e-3"),
    "2+I": ("2+1j", "2e-1"),
}


@pytest.mark.parametrize("key,pair", sorted(INSIDE_SHELL_THRON.items()))
def test_complex_bases_inside_shell_thron_are_regular_not_merged(ref, key, pair):
    """We give the regular solution there; fatou.gp gives the merged one.

    See docs/external-validation.md section 3.  This test pins the size of the
    gap so that a future merged-solution engine shows up here as a change.
    """
    base_repr, tol = pair
    with mp.workdps(100):
        theirs = _value(ref[f"sexp|{key}|0.5|80"])
        ours = hp.sexp("0.5", dps=15, base=base_repr)
        rel = abs(ours - theirs) / abs(theirs)
        assert rel > mp.mpf("1e-8"), "the two constructions are supposed to differ"
        assert rel < mp.mpf(tol), f"gap grew unexpectedly: {mp.nstr(rel, 3)}"


@pytest.mark.parametrize("key,base", [
    ("sexp|3+2*I|0.5|40", "3+2j"),
    ("sexp|2+2*I|0.5|30", "2+2j"),
    ("sexp|-1+1*I|0.5|30", "-1+1j"),
])
def test_cbuild_outside_shell_thron_matches_fatou_gp(key, base):
    """Both fixed points repelling: our default path here *is* the merged one.

    The published reference set has no base outside the Shell-Thron region, so
    these values come from our own fatou.gp runs (``_local_runs`` in the JSON).
    They are the only external check of ``kneser._cbuild``'s main path -- and
    for -1+1i also of the sheet it picks, which docs/base-plane-zh.md could
    only pin down by conjugation symmetry until now.

    Each builds an 8-digit table on first use (10-40 s, then cached).
    """
    with open(DATA) as fh:
        entry = json.load(fh)["local"][key]
    with mp.workdps(60):
        theirs = _value(entry)
        ours = hp.sexp("0.5", dps=8, base=base)
        rel = abs(ours - theirs) / abs(theirs)
        assert rel < mp.mpf("1e-9"), mp.nstr(rel, 3)   # table residuals are 4e-10 .. 9e-10


def test_solution_kneser_reproduces_fatou_gp_inside_shell_thron():
    """`solution="kneser"` is the merged construction and it *does* agree.

    Base 1+i, |lambda| = 0.711, inside the Shell-Thron region: the merged
    two-fixed-point table (kneser._cbuild with allow_attracting) lands on
    fatou.gp's value to its own residual floor, while the default regular
    solution is 3.3e-3 away.  This is the only external check of the
    allow_attracting path.

    Builds an 8-digit table on first use (~20 s, then cached).
    """
    with open(DATA) as fh:
        entry = json.load(fh)["values"]["sexp|1+I|0.5|80"]
    with mp.workdps(100):
        theirs = _value(entry)
        merged = hp.sexp("0.5", dps=10, base="1+1j", solution="kneser")
        regular = hp.sexp("0.5", dps=10, base="1+1j", solution="regular")
        assert abs(merged - theirs) / abs(theirs) < mp.mpf("1e-10")
        assert abs(regular - theirs) / abs(theirs) > mp.mpf("1e-3")


@pytest.mark.parametrize("base_repr", ["0.8+0.4j", "1+1j", "2+1j"])
def test_our_complex_base_answer_solves_the_functional_equation(base_repr):
    """The disagreement above is a different solution, not a wrong one."""
    from kneser._bases import base_value, normalize_base

    with mp.workdps(60):
        # pass the base as text: complex(0.8, 0.4) as a float64 pair is 4e-17
        # away from the exact decimal the engine uses, which would swamp the
        # residual below.
        name = normalize_base(base_repr)
        b = base_value(name)
        lo = hp.sexp("0.5", dps=30, base=base_repr)
        hi = hp.sexp("1.5", dps=30, base=base_repr)
        assert abs(hi - mp.power(b, lo)) < mp.mpf("1e-25")
        assert abs(hp.sexp("0", dps=30, base=base_repr) - 1) < mp.mpf("1e-25")
