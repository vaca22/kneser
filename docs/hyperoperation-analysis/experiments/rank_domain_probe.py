"""R010: diagnose common-height-disk Pick failure in the actual regular ladder.

The rational witness certifies the explicitly recorded decimal Pick data.
It excludes the exact analytic ladder only CONDITIONAL on a separately proved
value enclosure; high-precision residuals do not supply that enclosure.
"""
from __future__ import annotations

from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import platform
import sys

import mpmath as mp

ROOT = Path(__file__).resolve().parent
REPOSITORY = ROOT.parents[2]
sys.path.insert(0, str(REPOSITORY / "src"))
sys.path.insert(0, str(REPOSITORY / "docs"))
from demo_rank_regular import Level
from bounded_rank_interpolation import minimum_bound, pick_matrix
from rank_band_family import SeedBand, RegularSuccessor
from regular_parameter_family import RegularParameterFamily


class AuditedLevel(Level):
    """Record margins from the principal logarithms the evaluator actually uses."""
    margins = []

    def Sinv(self, y):
        argument = self.sigma(y)/self.C
        self.margins.append(mp.pi-abs(mp.arg(argument)))
        return mp.log(argument)/self.loglam

    def Tinv(self, y):
        if self.prev is None:
            self.margins.append(mp.pi-abs(mp.arg(y)))
            return mp.log(y)/mp.log(self.b)
        return self.prev.Sinv(y)


def rational_witness(values, eigenvector, *, first_node=3, sigma=F(5, 2)):
    # Complex numbers represented as pairs of exact fractions.
    to_pair = lambda z: (F(mp.nstr(mp.re(z), 35)), F(mp.nstr(mp.im(z), 35)))
    add = lambda a, b: (a[0]+b[0], a[1]+b[1])
    mul = lambda a, b: (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
    conj = lambda a: (a[0], -a[1])
    scale = lambda a, t: (a[0]*t, a[1]*t)
    w = [to_pair(z) for z in values]
    eigenvector = eigenvector/max(abs(z) for z in eigenvector)
    u = [to_pair(z) for z in eigenvector]
    assert all(x*x+y*y < 1 for x, y in w)
    assert all(x*x+y*y < 4 for x, y in u)
    total = (F(0), F(0))
    for i, wi in enumerate(w):
        for j, wj in enumerate(w):
            product = mul(wi, conj(wj))
            entry = scale((1-product[0], -product[1]), 1/(F(2*first_node+i+j)-2*sigma))
            total = add(total, mul(mul(conj(u[i]), entry), u[j]))
    assert total[1] == 0
    eta = F(1, 10**20)
    perturbation = 4*len(w)**2*(2*eta+eta*eta)
    assert total[0] + perturbation < 0
    pair_text = lambda pair: [str(x) for x in pair]
    return {"arithmetic": "exact fractions.Fraction complex matrix arithmetic",
            "first_integer_node": first_node, "sigma": str(sigma),
            "certified_object": "explicit decimal surrogate data, not the exact analytic ladder",
            "surrogate_values_normalized": [pair_text(z) for z in w],
            "witness_vector": [pair_text(z) for z in u],
            "quadratic_form": str(total[0]), "quadratic_form_approx": mp.nstr(mp.mpf(total[0].numerator)/total[0].denominator, 24),
            "assumed_max_normalized_value_error_for_actual_exclusion": str(eta),
            "perturbation_bound": str(perturbation),
            "surrogate_negative_certified": True,
            "actual_value_error_enclosure_certified": False,
            "actual_analytic_chain_exclusion_certified": False}


def run(dps, terms):
    with mp.workdps(dps+50):
        a, c, radius, sigma = mp.mpf(13)/10, mp.mpf(6)/5, mp.mpf(13)/10, mp.mpf(5)/2
        levels, prev = [], None
        for rank in range(4, 13):
            lev = AuditedLevel(a, prev, terms)
            levels.append(lev)
            prev = lev
        threshold = mp.power(10, -(dps-5))
        fmt = lambda x: mp.nstr(x, 24)
        family = RegularParameterFamily(mp.log(a), coordinate_steps=700)
        seed = SeedBand(requested_dps=dps+10)
        fifth = RegularSuccessor(seed, 1, requested_dps=dps+15)
        reference_error, shift_error, successor_error, largest_increment = (mp.mpf(0),)*4
        AuditedLevel.margins = []
        path = [mp.mpc("0.3", mp.mpf(j)/50) for j in range(21)]
        path_values = []
        for lev in levels:
            previous = None
            for z in path:
                observed = lev.S(z)
                shift_error = max(shift_error, abs(observed-lev.S(z, extra=3)))
                successor_error = max(successor_error, abs(lev.S(z+1)-lev.T(observed)))
                if previous is not None:
                    largest_increment = max(largest_increment, abs(observed-previous))
                previous = observed
                if lev.s == 4:
                    reference_error = max(reference_error, abs(observed-family.value(z)))
                if lev.s == 5 and z in (path[0], path[-1]):
                    reference_error = max(reference_error, abs(observed-fifth.value(z)))
            path_values.append(previous)
        assert all(x < threshold for x in (shift_error, successor_error, reference_error))
        assert largest_increment < mp.mpf("0.1")
        minimum_margin = min(AuditedLevel.margins)
        assert minimum_margin > mp.mpf("0.1")
        raw = [a**path[-1]]+path_values
        centered = [(v-c)/radius for v in raw]
        p = pick_matrix(range(3, 13), centered, sigma=sigma, bound=1)
        eigenvalues, eigenvectors = mp.eighe(p)
        assert eigenvalues[0] < 0
        certificate = rational_witness(centered, eigenvectors[:, 0])

        samples = []
        for z in [mp.mpf("0.1"), mp.mpf("0.3"), mp.mpf("0.5"), mp.mpf(2),
                  mp.mpc("0.3", "0.1"), mp.mpc("0.3", "0.2"),
                  mp.mpc("0.3", "0.3"), path[-1]]:
            values = [a**z]+[lev.S(z) for lev in levels]
            centered_values = [(v-c)/radius for v in values]
            norms = [minimum_bound(range(3, last+1), centered_values[:last-2], sigma=sigma)
                     for last in (5, 8, 12)]
            samples.append({"height": str(z), "minimum_bounds_last_5_8_12": [fmt(m) for m in norms],
                            "maximum_anchor_radius_ratio": fmt(max(abs(w) for w in centered_values))})
        assert samples[0]["height"] == "0.1"
        norm = minimum_bound(range(3, 13), centered, sigma=sigma)
        assert norm > mp.mpf("1.20")
        # Relaxed scalar polynomial growth is a different construction class.
        growth = []
        for degree in (0, 1, 2):
            weighted = [v/(n-sigma+1)**degree for n, v in zip(range(3, 13), centered)]
            growth.append({"polynomial_weight_degree": degree,
                           "finite_weighted_minimum_bound": fmt(minimum_bound(range(3, 13), weighted, sigma=sigma))})
        record = {"requested_dps": dps, "actual_working_dps": dps+50, "series_terms": terms,
                  "height_disk_center": "6/5", "height_disk_radius": "13/10", "rank_half_plane_sigma": "5/2",
                  "witness_height": str(path[-1]), "path_step": "i/50", "path_points": len(path),
                  "raw_witness_values_rank_3_to_12": [fmt(v) for v in raw],
                  "witness_minimum_normalized_bound": fmt(norm),
                  "witness_pick_smallest_eigenvalue": fmt(eigenvalues[0]),
                  "additional_three_inverse_steps_difference_max": fmt(shift_error),
                  "sampled_successor_residual_max": fmt(successor_error),
                  "independent_first_two_successors_reference_difference_max": fmt(reference_error),
                  "largest_adjacent_path_value_increment": fmt(largest_increment),
                  "minimum_sampled_principal_log_cut_angle_margin": fmt(minimum_margin),
                  "samples": samples, "finite_polynomial_growth_probes": growth,
                  "exact_surrogate_witness": certificate,
                  "scope": "Actual regular-ladder finite precision diagnostics; path margins and residuals "
                           "do not certify analytic continuation or interval error. The exact rational witness "
                           "is for the recorded surrogate matrix; actual exclusion needs the stated enclosure."}
        print(f"Checked dps={dps}, terms={terms}: witness norm={fmt(norm)}, residual={fmt(successor_error)}", flush=True)
        return record


def add_halfplane_probe(record):
    """A separate probe using the exact 35-digit surrogate already recorded.

    This does not recompute or improve the accuracy of the analytic ladder.
    """
    with mp.workdps(100):
        pairs = record["exact_surrogate_witness"]["surrogate_values_normalized"]
        values = []
        for pair in pairs:
            real, imag = (F(x) for x in pair)
            w = mp.mpc(mp.mpf(real.numerator)/real.denominator,
                       mp.mpf(imag.numerator)/imag.denominator)
            values.append(mp.mpf(6)/5+mp.mpf(13)/10*w)
        schur = [(v-1)/(v+1) for v in values]
        profiles = []
        for last in (5, 8, 10, 11, 12):
            part = values[:last-2]
            k = mp.matrix([[(x+mp.conj(y))/(i+j+1) for j, y in enumerate(part)]
                           for i, x in enumerate(part)])
            smallest = mp.eighe(k, eigvals_only=True)[0]
            norm = minimum_bound(range(3, last+1), schur[:last-2], sigma="2.5")
            profiles.append({"last_integer_node": last, "cayley_minimum_bound": mp.nstr(norm, 24),
                             "positive_real_kernel_smallest_eigenvalue": mp.nstr(smallest, 24)})
        record["unbounded_height_halfplane_probe"] = {
            "input": "the exact 35-significant-digit rational surrogate, evaluated at 100 working digits",
            "profiles": profiles, "actual_positive_real_chain_exclusion_certified": False}
        return record


def higher_halfplane_probe():
    """Extend the new unbounded self-map route beyond the twelve-point screen."""
    with mp.workdps(110):
        a, z = mp.mpf(13)/10, mp.mpc("0.3", "0.4")
        values, prev, shift_error, successor_error, increment = [a**z], None, mp.mpf(0), mp.mpf(0), mp.mpf(0)
        AuditedLevel.margins = []
        profiles = []
        for rank in range(4, 17):
            lev = AuditedLevel(a, prev, 100)
            observed = lev.S(z)
            values.append(observed)
            shift_error = max(shift_error, abs(observed-lev.S(z, extra=3)))
            successor_error = max(successor_error, abs(lev.S(z+1)-lev.T(observed)))
            if rank > 12:
                path = [lev.S(mp.mpc("0.3", mp.mpf(j)/10)) for j in range(5)]
                increment = max(increment, max(abs(y-x) for x, y in zip(path, path[1:])))
            if rank >= 12:
                schur = [(v-1)/(v+1) for v in values]
                matrix = pick_matrix(range(3, rank+1), schur, sigma="2.5", bound=1)
                eigenvalues, eigenvectors = mp.eighe(matrix)
                norm = minimum_bound(range(3, rank+1), schur, sigma="2.5")
                profiles.append({"last_integer_node": rank, "cayley_minimum_bound": mp.nstr(norm, 24),
                                 "cayley_pick_smallest_eigenvalue": mp.nstr(eigenvalues[0], 24)})
            prev = lev
            print(f"Extended half-plane probe rank {rank}", flush=True)
        assert max(shift_error, successor_error) < mp.mpf("1e-55")
        assert increment < mp.mpf("0.3") and min(AuditedLevel.margins) > mp.mpf("0.1")
        witness = rational_witness(schur, eigenvectors[:, 0]) if eigenvalues[0] < 0 else None
        return {"actual_working_dps": 110, "series_terms": 100, "height": str(z),
                "raw_values_rank_3_to_16": [mp.nstr(v, 40) for v in values], "profiles": profiles,
                "additional_three_inverse_steps_difference_max": mp.nstr(shift_error, 24),
                "sampled_successor_residual_max": mp.nstr(successor_error, 24),
                "minimum_sampled_principal_log_cut_angle_margin": mp.nstr(min(AuditedLevel.margins), 24),
                "largest_new_coarse_path_increment": mp.nstr(increment, 24),
                "exact_cayley_surrogate_witness": witness,
                "actual_positive_real_chain_exclusion_certified": False}


def add_boundary_probe(record):
    """Discard rank 3 and restrict to Re r>3: this tests every sigma<3 route."""
    with mp.workdps(100):
        pairs = record["exact_cayley_surrogate_witness"]["surrogate_values_normalized"]
        values = []
        for pair in pairs[1:]:
            real, imag = (F(x) for x in pair)
            values.append(mp.mpc(mp.mpf(real.numerator)/real.denominator,
                                 mp.mpf(imag.numerator)/imag.denominator))
        matrix = pick_matrix(range(4, 17), values, sigma=3, bound=1)
        eigenvalues, eigenvectors = mp.eighe(matrix)
        assert eigenvalues[0] < 0
        witness = rational_witness(values, eigenvectors[:, 0], first_node=4, sigma=F(3))
        record["boundary_halfplane_probe"] = {
            "sigma": "3", "integer_nodes": list(range(4, 17)),
            "finite_cayley_minimum_bound": mp.nstr(minimum_bound(range(4, 17), values, sigma=3), 24),
            "smallest_surrogate_pick_eigenvalue": mp.nstr(eigenvalues[0], 24),
            "exact_surrogate_witness": witness,
            "scope": "Negative surrogate data on Re r>3. If actual values are enclosed, restriction "
                     "excludes self-map interpolation on every half-plane Re r>sigma with sigma<3.",
            "actual_chain_exclusion_certified": False}
        return record


def main():
    records = [add_halfplane_probe(run(40, 75)), add_halfplane_probe(run(60, 100))]
    higher = add_boundary_probe(higher_halfplane_probe())
    inputs = [Path(__file__), ROOT / "bounded_rank_interpolation.py", ROOT / "regular_parameter_family.py",
              ROOT / "rank_band_family.py", REPOSITORY / "docs/demo_rank_regular.py",
              REPOSITORY / "src/kneser/_koenigs.py", REPOSITORY / "src/kneser/_regular.py",
              REPOSITORY / "src/kneser/_bases.py"]
    payload = {"experiment": "R010-v1", "status": "PASS", "date": "2026-10-05",
               "python": platform.python_version(), "mpmath": mp.__version__,
               "input_sha256": {str(p.relative_to(REPOSITORY)): hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in inputs}, "records": records, "higher_halfplane_probe": higher,
               "scope": "Tests pass by detecting a finite Pick failure. This is not a positive global "
                        "existence result, nor a certified exclusion of the exact analytic integer chain."}
    target = ROOT / "rank-domain-probe.json"
    target.write_text(json.dumps(payload, ensure_ascii=False, indent=2)+"\n")
    print(f"PASS: {target}")


if __name__ == "__main__":
    main()
