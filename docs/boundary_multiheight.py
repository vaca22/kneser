"""Finite two-sided Shell--Thron comparison at five noninteger heights.

Run with PARI/GP and the unmodified Sheldonison fatou.gp file:

    python3 docs/boundary_multiheight.py --fatou /path/to/fatou.gp

The file's SHA-256 is checked. The six sampled bases are the same as in the
paper's boundary test. This is numerical evidence, not a proof of (P2).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path

import mpmath as mp


EXPECTED_SHA256 = "70559dafad8630543b09a2f0843e9e8e041c6b4968ae3546bfe549ced3adfdba"
RADII = ("0.98", "0.99", "0.995", "1.005", "1.01", "1.02")
HEIGHTS = ("1/6", "1/3", "1/2", "2/3", "5/6")
CHECK_RADII = ("0.995", "1.005")


def gp_values(fatou: Path, radius: str, precision: int) -> dict:
    source = str(fatou).replace("\\", "\\\\").replace('"', '\\"')
    lines = [
        f'read("{source}");',
        f"default(realprecision,{precision});",
        "quietmode=1;",
        "phi=2*Pi*(sqrt(2)-1)/5;",
        f"r={radius};",
        "lam=r*exp(I*phi);",
        "b=exp(lam*exp(-lam));",
        "sexpinit(b);",
    ]
    for z in HEIGHTS:
        lines += [
            f"z={z};",
            "v=sexp(z);",
            f'print("DATA|{radius}|{z}|",real(b),"|",imag(b),"|",real(v),"|",imag(v));',
        ]
    lines.append("quit;")
    with tempfile.TemporaryDirectory(prefix="kneser-boundary-") as directory:
        script = Path(directory) / "run.gp"
        script.write_text("\n".join(lines) + "\n")
        result = subprocess.run(
            ["gp", "-q", str(script)], capture_output=True, text=True, timeout=300
        )
    data = [line.split("|") for line in result.stdout.splitlines() if line.startswith("DATA|")]
    if result.returncode or result.stderr or len(data) != len(HEIGHTS):
        raise RuntimeError(
            f"GP failed at r={radius}, precision={precision}: "
            f"returncode={result.returncode}, rows={len(data)}, stderr={result.stderr[-1000:]}"
        )
    first = data[0]
    if any(row[1] != radius or row[3:5] != first[3:5] for row in data):
        raise RuntimeError(f"Inconsistent GP rows at r={radius}")
    return {
        "r": radius,
        "b": [first[3], first[4]],
        "values": {row[2]: [row[5], row[6]] for row in data},
    }


def complex_value(pair: list[str]) -> mp.mpc:
    return mp.mpc(mp.mpf(pair[0]), mp.mpf(pair[1]))


def interpolate(nodes: list[tuple[mp.mpc, mp.mpc]], x: mp.mpc) -> mp.mpc:
    total = mp.mpc(0)
    for i, (xi, yi) in enumerate(nodes):
        term = yi
        for j, (xj, _) in enumerate(nodes):
            if j != i:
                term *= (x - xj) / (xi - xj)
        total += term
    return total


def diagnostics(samples: list[dict], checks: list[dict]) -> dict:
    mp.mp.dps = 100
    lambda_c = mp.exp(2j * mp.pi * (mp.sqrt(2) - 1) / 5)
    b_c = mp.exp(lambda_c * mp.exp(-lambda_c))
    by_r = {sample["r"]: sample for sample in samples}
    by_r_check = {sample["r"]: sample for sample in checks}
    details = {}
    for z in HEIGHTS:
        nodes = [
            (complex_value(by_r[r]["b"]), complex_value(by_r[r]["values"][z]))
            for r in RADII
        ]
        errors = [
            abs(interpolate(nodes[:i] + nodes[i + 1 :], nodes[i][0]) - nodes[i][1])
            for i in range(len(nodes))
        ]
        inside = interpolate(nodes[:3], b_c)
        outside = interpolate(nodes[3:], b_c)
        precision_difference = max(
            abs(complex_value(by_r[r]["values"][z])
                - complex_value(by_r_check[r]["values"][z]))
            for r in CHECK_RADII
        )
        details[z] = {
            "max_degree4_leave_one_out_error": mp.nstr(max(errors), 12),
            "quadratic_two_side_gap_at_boundary": mp.nstr(abs(inside - outside), 12),
            "max_precision_50_vs_70_difference": mp.nstr(precision_difference, 12),
        }
    return {"boundary_base": [mp.nstr(b_c.real, 55), mp.nstr(b_c.imag, 55)],
            "by_height": details}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fatou", type=Path, required=True)
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).parent / "data" / "boundary-multiheight.json",
    )
    args = parser.parse_args()
    fatou = args.fatou.expanduser().resolve()
    digest = hashlib.sha256(fatou.read_bytes()).hexdigest()
    if digest != EXPECTED_SHA256:
        raise ValueError(f"fatou.gp SHA-256 mismatch: {digest}")
    samples = [gp_values(fatou, r, 50) for r in RADII]
    checks = [gp_values(fatou, r, 70) for r in CHECK_RADII]
    report = {
        "purpose": "Finite numerical comparison only; it does not establish (P2).",
        "alpha": "(sqrt(2)-1)/5",
        "fatou_gp_sha256": digest,
        "radii": RADII,
        "heights": HEIGHTS,
        "precision_50_samples": samples,
        "precision_70_checks": checks,
        "diagnostics": diagnostics(samples, checks),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    for z, row in report["diagnostics"]["by_height"].items():
        print(z, row)
    print(f"Wrote {args.output}")


if __name__ == "__main__":
    main()
