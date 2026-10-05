"""Sewing solution K^W at a COMPLEX base inside the Shell-Thron region, compared with
an independent Kneser-type implementation (fatou.gp / gp-tetration, PARI/GP).

R = regular superfunction at the attracting fixed point L_up (arg lambda_up > 0),
S = regular superfunction at the repelling fixed point L_dn, S(z)=tau^{-1}(-lambda_dn^z).
T = R^{-1} o S.  Sewing: Q = -Pi_<0[T(x+Q)-(x+Q)-t0] on a seam line in S-time,
phi_+ = id + t0 + P', normalising root phi_+(z0) in varpi*Z, K(z) = R(phi_+(z+z0)).
K(1/2) = R(1/2 + delta), delta = P'(1/2+z0) - P'(z0).

Usage: python3 docs/weld_complex.py "0.8+0.4j" [dps] [N] [seam_y]
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(ROOT / "docs"))
from kneser._cbuild import choose_fixed_points  # noqa: E402
from kneser._bases import base_value, normalize_base  # noqa: E402
from kneser._general import GeneralRegularEngine  # noqa: E402
from transition_map import schroeder, peval  # noqa: E402


class CSetup:
    def __init__(self, base, N=60):
        _, Lu, lu, _, Ld, ld = choose_fixed_points(base, dps=mp.mp.dps + 10)
        self.b = mp.mpc(base_value(normalize_base(base.replace("I", "j"))))  # exact decimal base
        self.lb = mp.log(self.b)
        for _ in range(8):  # Newton polish at working precision: L = b^L
            Lu = Lu - (mp.exp(self.lb * Lu) - Lu) / (self.lb * mp.exp(self.lb * Lu) - 1)
            Ld = Ld - (mp.exp(self.lb * Ld) - Ld) / (self.lb * mp.exp(self.lb * Ld) - 1)
        lu, ld = Lu * self.lb, Ld * self.lb
        self.L, self.lam, self.L2, self.lam2 = Lu, lu, Ld, ld
        g1 = [mp.mpc(0)] + [Lu * self.lb**k / mp.factorial(k) for k in range(1, N + 1)]
        g2 = [mp.mpc(0)] + [Ld * self.lb**k / mp.factorial(k) for k in range(1, N + 1)]
        self.s = schroeder(lu, g1, N)
        self.t = schroeder(ld, g2, N)
        self.varpi = 2j * mp.pi / mp.log(lu)
        self.Lam = mp.exp(4 * mp.pi**2 / mp.log(lu))
        self.r = mp.mpf(10) ** (-mp.mp.dps / 30.0)
        self.logsig1, self.n1 = self._logsig(mp.mpc(1))

    def E(self, w):
        return mp.exp(self.lb * w)

    def _logsig(self, w):
        n = 0
        while abs(w - self.L) > self.r:
            w = self.E(w)
            n += 1
            if abs(w) > 1e8:
                raise RuntimeError("orbit escapes (not in basin)")
            if n > 200000:
                raise RuntimeError("no convergence to L_up")
        return mp.log(peval(self.s, w - self.L)), n

    def Rinv(self, w):
        ls, n = self._logsig(w)
        return self.n1 - n + (ls - self.logsig1) / mp.log(self.lam)

    def tau_inv(self, y):
        x = y
        for _ in range(80):
            fx = peval(self.t, x) - y
            d = sum(k * self.t[k] * x ** (k - 1) for k in range(1, len(self.t)))
            dx = fx / d
            x -= dx
            if abs(dx) < mp.mpf(10) ** (-mp.mp.dps + 5) * (abs(x) + mp.mpf(10) ** -mp.mp.dps):
                break
        return x

    def S(self, z):
        ll2 = mp.log(self.lam2)
        m = int(mp.ceil((mp.re(z * ll2) - mp.log(self.r)) / mp.re(ll2))) + 1  # |lambda2^(z-m)| < r
        m = max(m, 0)
        w = self.L2 + self.tau_inv(-mp.exp((z - m) * ll2))
        for _ in range(m):
            w = self.E(w)
            if abs(w) > 1e8:
                raise RuntimeError("S overflow")
        return w


def line_values(st, y, N, ref=None):
    """T(x+iy)-(x+iy) on N points, unwrapped by multiples of varpi."""
    vals, prev = [], ref
    for k in range(N):
        z = mp.mpf(k) / N + 1j * y
        v = st.Rinv(st.S(z)) - z
        if prev is not None:
            j = mp.nint(mp.re((prev - v) / st.varpi))
            v += j * st.varpi
        vals.append(v)
        prev = v
    return vals


def dft(vals, xs, n, y=0):
    N = len(vals)
    return sum(vals[k] * mp.exp(-2j * mp.pi * n * (xs[k] + 1j * y)) for k in range(N)) / N


def scan(st, ys, N=24):
    out = []
    for y in ys:
        try:
            vals = line_values(st, mp.mpf(y), N)
            xs = [mp.mpf(k) / N for k in range(N)]
            t = {n: dft(vals, xs, n, mp.mpf(y)) for n in (-1, 0, 1)}
            out.append((y, t))
            print(f"y={y:+.2f}  t0={mp.nstr(t[0], 10)}  t1={mp.nstr(t[1], 8)}  t-1={mp.nstr(t[-1], 8)}", flush=True)
        except Exception as exc:  # noqa: BLE001
            print(f"y={y:+.2f}  failed: {exc}")
    return out


def weld(st, ys, N=32, iters=40):
    """Contraction on the seam line Im z = ys of S-time; returns (pp modes, t0, z0 candidates)."""
    xs = [mp.mpf(k) / N for k in range(N)]
    base_vals = line_values(st, mp.mpf(ys), N)
    t0 = dft(base_vals, xs, 0, mp.mpf(ys)) + 1j * ys   # T(x+i ys) - x has mean t0

    def Tshift(w):  # T(w + i ys) in true R-time, branch nearest to w + t0
        v = st.Rinv(st.S(w + 1j * ys))
        j = mp.nint(mp.re((w + t0 - v) / st.varpi))
        return v + j * st.varpi

    Q = [mp.mpc(0)] * N
    modes = None
    for it in range(iters):
        r = [Tshift(xs[k] + Q[k]) - (xs[k] + Q[k]) - t0 for k in range(N)]
        modes = {n: dft(r, xs, n) for n in range(-N // 2 + 1, N // 2)}
        Qn = [-sum(modes[n] * mp.exp(2j * mp.pi * n * x) for n in modes if n < 0) for x in xs]
        dQ = max(abs(Qn[k] - Q[k]) for k in range(N))
        Q = Qn
        if dQ < mp.mpf(10) ** (-mp.mp.dps + 6):
            break
    print(f"  weld: {it + 1} iterations, last |dQ|={mp.nstr(dQ, 3)}, |Q|max={mp.nstr(max(abs(q) for q in Q), 3)}")
    pp = {n: modes[n] for n in modes if n >= 0}
    return pp, t0


def main():
    base = sys.argv[1]
    mp.mp.dps = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    N = int(sys.argv[3]) if len(sys.argv) > 3 else 32
    st = CSetup(base, N=70)
    print(f"base {base}: lam_up={mp.nstr(st.lam, 8)} lam_dn={mp.nstr(st.lam2, 8)} "
          f"varpi={mp.nstr(st.varpi, 8)} |Lambda|={mp.nstr(abs(st.Lam), 5)}")
    if len(sys.argv) <= 4:
        scan(st, [-3, -2, -1.5, -1, -0.5, 0, 0.5, 1, 1.5, 2, 3])
        return
    ys = mp.mpf(sys.argv[4])
    pp, t0 = weld(st, ys, N)
    Pp = lambda z: sum(pp[n] * mp.exp(2j * mp.pi * n * z) for n in pp)  # noqa: E731
    eng = GeneralRegularEngine(base.replace("I", "j"), mp.mp.dps)
    ref = json.load(open(ROOT / "tests" / "data" / "external_reference.json"))["values"]
    key = [k for k in ref if k.split("|")[1] == base.replace("j", "*I").replace("1*I", "I")
           or k.split("|")[1] == base.replace("j", "I")]
    Kref = mp.mpc(mp.mpf(ref[key[0]]["real"]), mp.mpf(ref[key[0]]["imag"])) if key else None
    import os
    if os.environ.get("KREF"):
        re_, im_ = os.environ["KREF"].split(",")
        Kref = mp.mpc(mp.mpf(re_), mp.mpf(im_))
    R_half = eng.sexp(mp.mpf("0.5"))
    for k in range(-3, 4):
        target = k * st.varpi
        try:
            z0 = mp.findroot(lambda z: z + t0 + Pp(z) - target, target - t0)
        except Exception:  # noqa: BLE001
            continue
        delta = Pp(mp.mpf("0.5") + z0) - Pp(z0)
        Kw = eng.sexp(mp.mpf("0.5") + delta)
        c1 = pp[1] * mp.exp(2j * mp.pi * z0)
        line = (f"k={k:+d} Im z0={mp.nstr(mp.im(z0), 6)} |c1/Lam|={mp.nstr(abs(c1 / st.Lam), 10)} "
                f"K^W(1/2)={mp.nstr(Kw, 25)}")
        if Kref is not None:
            err = abs(Kw - Kref)
            line += f"  |K^W-K_fatou|={mp.nstr(err, 3)}  |R(1/2)-K_fatou|={mp.nstr(abs(R_half - Kref), 3)}"
        print(line, flush=True)


if __name__ == "__main__":
    main()
