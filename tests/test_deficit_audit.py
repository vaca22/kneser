"""Independent recovery and failure checks for the research fit machinery."""

import json
from pathlib import Path
import shutil
import subprocess
import sys

import mpmath as mp
import pytest

np = pytest.importorskip("numpy")
from docs.deficit_audit import (  # noqa: E402
    DEFAULT_INPUT, collect_rows, estimate_ladder, fit_model, validate_snapshot,
)


def test_known_exponent_recovered_with_unseen_point_predictions():
    # A nonquadratic exponent ensures the analysis does not bake in p=2.
    xs = np.geomspace(0.1, 3, 12)
    ds = 0.037 * xs ** 1.37 * np.exp(-0.2 * xs + 0.013 * xs ** 2)
    fitted = fit_model(xs, ds, degree=2)
    assert fitted["p"] == pytest.approx(1.37, abs=1e-11)
    assert fitted["C"] == pytest.approx(0.037, abs=1e-12)
    assert fitted["loo_log_rms"] < 1e-11
    wrong = fit_model(xs, ds, degree=2, fixed_p=2)
    assert wrong["loo_log_rms"] > 0.05


@pytest.mark.parametrize("xs, ds", [
    ([1, 2, 3], [1, -1, 2]), ([0, 2, 3], [1, 2, 3]),
    ([1, 2, float("nan")], [1, 2, 3]), ([1, 2, 3], [1, 2]),
    ([1, 1, 1, 1], [1, 2, 3, 4]),
])
def test_invalid_or_unidentifiable_fit_fails(xs, ds):
    with pytest.raises(ValueError):
        fit_model(xs, ds)


def test_saturated_fit_is_not_reported_as_evidence():
    with pytest.raises(ValueError, match="more observations"):
        fit_model([0.1, 0.2, 0.3, 0.4], [1, 2, 3, 4], degree=2)


def test_bundle_has_all_ladders_and_duplicate_paths_are_rejected():
    snapshot = json.loads(DEFAULT_INPUT.read_text())
    validate_snapshot(snapshot)
    with pytest.raises(ValueError, match="missing primary"):
        validate_snapshot({"schema_version": 1, "records": []})
    snapshot["records"].append(snapshot["records"][0])
    with pytest.raises(ValueError, match="duplicate record paths"):
        validate_snapshot(snapshot)


def test_bad_ladder_is_not_silently_accepted():
    def record(y, noise="0", limited=False):
        return {"path": f"ladder/{y}.json", "data": {
            "b": [1.1, y], "D": {"0.5": ["1e-10", "0"]},
            "residual": noise, "residual_check": noise,
            "loop_limit_reached": limited}}
    with pytest.raises(ValueError, match="duplicate heights"):
        estimate_ladder([record(0.1), record(0.1)], "ladder")
    with pytest.raises(ValueError, match="fewer than two"):
        estimate_ladder([record(0.1), record(0.2, limited=True)], "ladder")
    with pytest.raises(ValueError, match="fewer than two"):
        estimate_ladder([record(0.1), record(0.2, noise="1e-8")], "ladder")


def test_recomputed_snapshot_and_phase_dependency_are_explicit():
    snapshot = json.loads(DEFAULT_INPUT.read_text())
    before = mp.mp.dps
    rows, external = collect_rows(snapshot)
    assert mp.mp.dps == before
    assert len(rows) == 8
    assert all(left["delta1"] > right["delta1"] > 0
               for left, right in zip(rows, rows[1:]))
    # Loose compared with stored digits: this checks the published signal scale,
    # not a claim that the original extrapolation has rigorously bounded error.
    assert rows[-1]["delta1"] == pytest.approx(0.0018301, abs=1e-6)
    assert external["kind"] == "external_phase_estimate"
    assert external["phase_source_bases"] == ["1.40", "1.35"]
    assert external["uncorrected_delta1"] > external["delta1"]


def test_scripts_import_from_another_checkout_without_local_absolute_paths(tmp_path):
    root = Path(__file__).resolve().parents[1]
    (tmp_path / "docs").mkdir()
    shutil.copytree(root / "src" / "kneser", tmp_path / "src" / "kneser",
                    ignore=shutil.ignore_patterns("__pycache__"))
    for name in ("deficit_audit.py", "deficit_law.py", "c1_invariant.py"):
        shutil.copy(root / "docs" / name, tmp_path / "docs" / name)
    # Import outside both checkouts, then verify the copied sibling src was
    # actually loaded (the original checkout still exists on this machine).
    import os
    env = {key: value for key, value in os.environ.items() if key != "PYTHONPATH"}
    script = (
        "import runpy, sys; from pathlib import Path; "
        "module = runpy.run_path(sys.argv[1]); import kneser; "
        "assert Path(kneser.__file__).resolve().is_relative_to(Path(sys.argv[2]).resolve()); "
        "module['main'](['--help'])"
    )
    result = subprocess.run([sys.executable, "-c", script,
                             str(tmp_path / "docs" / "deficit_audit.py"), str(tmp_path)],
                            cwd=tmp_path.parent, env=env,
                            text=True, capture_output=True, timeout=30)
    assert result.returncode == 0, result.stderr
    assert "--export-inputs" in result.stdout
