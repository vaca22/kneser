"""Mixed base-e/base-2 Kneser flows: analytic jets and commutator probes.

Run from kneser/: PYTHONPATH=src python3 docs/demo_mixed_base_bracket.py
Only the shipped e/2 tables are used. Working precision is not a certified
error bound; numerical root counts refer only to the declared sample grid.
"""

import argparse
import json
from pathlib import Path

import mpmath as mp

from kneser import _coeffs, _coeffs_2, hp


class Flow:
    def __init__(self, base, dps=55):
        self.base, self.dps = base, dps
        data = _coeffs if base == "e" else _coeffs_2
        with mp.workdps(dps + 10):
            self.c = tuple(mp.mpf(c) for c in data.COEFFS)
            self.logb = mp.mpf(1) if base == "e" else mp.log(2)

    def jet(self, z):
        """Return S, S', S'' using differentiated shift identities."""
        z = mp.mpf(z)
        if z <= -2:
            raise ValueError("real tetration requires height > -2")
        k = int(mp.ceil(z - mp.mpf("0.5")))
        z -= k
        s = d = dd = mp.mpf(0)
        for c in reversed(self.c):
            dd, d, s = dd * z + 2 * d, d * z + s, s * z + c
        a = self.logb
        for _ in range(k):
            v = mp.exp(a * s)
            s, d, dd = v, a * v * d, v * (a * dd + a * a * d * d)
        for _ in range(-k):
            s, d, dd = mp.log(s) / a, d / (a * s), (dd / s - (d / s)**2) / a
        return s, d, dd

    def velocity(self, x):
        _, d, dd = self.jet(hp.slog(x, dps=self.dps, base=self.base))
        return d, dd / d

    def __call__(self, x, t):
        return hp.exp_iter(x, t, dps=self.dps, base=self.base)


def bracket(f, g, x):
    v, dv = f.velocity(x)
    w, dw = g.velocity(x)
    return v * dw - w * dv


def loop(f, g, x, h):
    """Apply f_h, g_h, f_-h, g_-h in that chronological order."""
    return g(f(g(f(x, h), h), -h), -h)


def nested_bracket(f, g, x, n):
    """Low-order numerical check only; the independence proof is analytic.

    Fixed explicit differencing step avoids differentiating an hp function
    with infinitesimal steps below its fixed working precision.
    """
    if n == 0:
        return g.velocity(x)[0]
    if n == 1:
        return bracket(f, g, x)
    h = mp.mpf("1e-6")
    prev = nested_bracket(f, g, x, n-1)
    deriv = (nested_bracket(f, g, x+h, n-1)-nested_bracket(f, g, x-h, n-1))/(2*h)
    v, dv = f.velocity(x)
    return v*deriv-dv*prev


def run(dps=55):
    with mp.workdps(dps):
        f, g = Flow("e", dps), Flow("2", dps)
        fmt = lambda x: mp.nstr(x, 30)
        grid = [mp.mpf(i) / 20 for i in range(-80, 241)]
        values = [bracket(f, g, x) for x in grid]
        roots = []
        for left, right, bl, br in zip(grid, grid[1:], values, values[1:]):
            if bl * br < 0:
                root = mp.findroot(lambda x: bracket(f, g, x), (left, right),
                                   solver="anderson")
                delta = mp.mpf("1e-12")
                bp = (bracket(f, g, root+delta)-bracket(f, g, root-delta))/(2*delta)
                cubic = (f.velocity(root)[0]+g.velocity(root)[0])*bp/2
                roots.append({"bracket_interval": [fmt(left), fmt(right)],
                              "x": fmt(root), "residual": fmt(abs(bracket(f, g, root))),
                              "cubic_prediction": fmt(cubic),
                              "loop_over_h3": [
                                  {"h": hs, "value": fmt((loop(f, g, root, mp.mpf(hs))-root)/mp.mpf(hs)**3)}
                                  for hs in ["0.001", "0.0001", "0.00001"]]})
        probes = []
        for xs in ["-1", "0", "0.5", "1", "2", "5"]:
            x = mp.mpf(xs)
            b = bracket(f, g, x)
            rows = []
            for hs in ["0.01", "0.005", "0.0025", "0.00125"]:
                h = mp.mpf(hs)
                q = (loop(f, g, x, h) - x) / h**2
                # Symmetrizing h cancels the cubic term in the loop.
                sym = (loop(f, g, x, h) + loop(f, g, x, -h) - 2*x) / (2*h**2)
                rows.append({"h": hs, "loop_over_h2": fmt(q),
                             "error": fmt(abs(q-b)), "symmetric_error": fmt(abs(sym-b))})
            probes.append({"x": xs, "B": fmt(b), "convergence": rows})
        # Independent functional identity for the analytically propagated jets.
        residuals = []
        for flow in [f, g]:
            for xs in ["-1", "0", "0.5", "1"]:
                x = mp.mpf(xs)
                y = mp.exp(flow.logb*x)
                v, dv = flow.velocity(x)
                w, dw = flow.velocity(y)
                residuals.extend([abs(w/(flow.logb*y*v)-1),
                                  abs(dw-(flow.logb*v+dv))/(1+abs(dw))])
        same = abs(loop(f, f, mp.mpf(1), mp.mpf("0.01"))-1)
        tail = []
        for xs in ["-20", "-10", "100", "1e3", "1e6", "1e10", "1e30", "1e100"]:
            x = mp.mpf(xs)
            v, dv = f.velocity(x)
            w, dw = g.velocity(x)
            tail.append({"x": xs, "W_over_V": fmt(w/v), "B_over_VW": fmt(dw/w-dv/v)})
        half_ab = g(f(mp.mpf(1), mp.mpf("0.5")), mp.mpf("0.5"))
        half_ba = f(g(mp.mpf(1), mp.mpf("0.5")), mp.mpf("0.5"))
        return {"working_dps": dps, "coefficient_digits": 50,
                "scan": {"interval": [-4, 12], "step": "0.05", "points": len(grid),
                         "sign_change_roots": roots,
                         "samples": [[fmt(x), fmt(b)] for x, b in zip(grid, values)]},
                "max_generator_identity_relative_residual": fmt(max(residuals)),
                "same_base_loop_residual": fmt(same),
                "tail_samples": tail,
                "half_step_at_1": {"e_then_2": fmt(half_ab), "2_then_e": fmt(half_ba),
                                   "difference": fmt(half_ab-half_ba)},
                "probes": probes}


def nested_probe(dps):
    with mp.workdps(dps):
        f, g = Flow("e", dps), Flow("2", dps)
        a = mp.log(2)
        c, d = f.velocity(0)[0], g.velocity(0)[0]/a
        rows = []
        for n in range(1, 4):
            cn = d*c**n*mp.fprod(1-a-j for j in range(n))
            rows.append({"order": n, "exponent": mp.nstr(a+n, 25),
                         "predicted_coefficient": mp.nstr(cn, 25),
                         "measured_over_leading_term": [
                             {"x": xs, "ratio": mp.nstr(nested_bracket(f, g, mp.mpf(xs), n)
                                                        /(cn*mp.exp(-(a+n)*mp.mpf(xs))), 20)}
                             for xs in ["-5", "-10", "-20"]]})
        return {"finite_difference_step": "1e-6", "rows": rows}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dps", type=int, default=55)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--plot", type=Path, help="Optional standalone figure (requires matplotlib)")
    args = parser.parse_args()
    data = run(args.dps)
    data["nested_brackets"] = nested_probe(args.dps)
    result = json.dumps(data, ensure_ascii=False, indent=2)
    if args.output:
        args.output.write_text(result + "\n")
    if args.plot:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        points = [(float(x), float(b)) for x, b in data["scan"]["samples"] if -1 <= float(x) <= 5]
        fig, ax = plt.subplots(figsize=(8, 4.5), layout="constrained")
        ax.plot(*zip(*points), color="#176b87", linewidth=2.5)
        ax.axhline(0, color="#777777", linewidth=0.8)
        for root in data["scan"]["sign_change_roots"]:
            x = float(root["x"])
            ax.scatter([x], [0], color="#bd4738", zorder=3)
            ax.annotate(f"{x:.6f}", (x, 0), xytext=(8, 15), textcoords="offset points")
        ax.set(xlabel="Initial value x", ylabel="B(x) = V(x) W'(x) - W(x) V'(x)",
               title="Base e and base 2: the direction of commutator drift changes")
        ax.text(0.35, 0.83, "Loop: e(+h), 2(+h), e(-h), 2(-h)\nDisplacement = h² B(x) + O(h³)",
                transform=ax.transAxes, fontsize=10)
        ax.grid(alpha=0.18)
        fig.savefig(args.plot, dpi=180)
        plt.close(fig)
    print(result)
