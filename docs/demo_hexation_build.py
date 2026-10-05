"""Rank-6 theta iteration: hexation, the input the rank-7 constant needs.

Mirrors `demo_pentation_build.py` one more rung up.  Rank 5 solved for
pentation with the map sexp and sexp's complex fixed point; rank 6 solves for
hexation H with the map PENTATION and pentation's complex fixed point

    z*_5 = -2.2597543772948619217694227344490 + 1.3844243840414798988939409459371 i
    mu_5 = 1.775236647758065 + 2.945803451058312 i,   |mu_5| = 3.4394   REPELLING

    H(z+1) = pen(H(z)),   H(0) = 1,   H(z) -> z*_5 as Im z -> +inf

Three things are different from rank 5, and two of them are easier:

1.  mu_5 is REPELLING, so Q_6(w) = z*_5 + u(mu_5**w) is walked outward with the
    FORWARD map -- no complex slog (that was the wall at rank 5, section 4.7).
    The cost moves to Q_6^{-1}, which now needs pen^{-1} iterated; that is a
    Newton on pen, seeded by the local linearisation z*_5 + (y-z*_5)/mu_5.
2.  There is NO regular hexation to seed with.  For b > b_c6 = 1.7374 pentation
    has no real fixed point at all (that is the definition of b_c6), so the
    Koenigs route does not exist here.  Seeded with 1 + z instead, as
    `kneser.build` does with its "linear" seed.
3.  The magnitudes stay tame on the unit circle, contrary to first fears:
    H(1) = pen(H(0)) = pen(1) = e.  The anchors are the same at every rank --
    H(-2) = -1, H(-1) = 0, H(0) = 1, H(1) = e -- and none of them is large.
    The blow-up only starts at H(2) = pen(e), outside the disc.

Which pentation: the REGULAR / Koenigs one (`demo_upper_half_pen.py`).  The
Kneser-type pentation would give a different hexation; see
docs/hyperoperation-program-zh.md section 4.12.

Run:  PYTHONPATH=src python3 docs/demo_hexation_build.py [--loops N]
"""

from __future__ import annotations

import argparse
import sys
import time

import mpmath as mp

from kneser._koenigs import Superfunction, series_eval

sys.path.insert(0, "docs")
from demo_upper_half_pen import PentationUpper, ZSTAR5          # noqa: E402


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=35)
    ap.add_argument("--base", default="e")
    ap.add_argument("--nt", type=int, default=20)
    ap.add_argument("--modes", type=int, default=8)
    ap.add_argument("--nf", type=int, default=24)
    ap.add_argument("--ncirc", type=int, default=64)
    ap.add_argument("--radius", default="1.0")
    ap.add_argument("--delta", default="0.5")
    ap.add_argument("--loops", type=int, default=6)
    args = ap.parse_args(argv)

    mp.mp.dps = args.dps
    t0 = time.time()
    E = PentationUpper(base=args.base, dps=args.dps)
    pen = lambda z: E(z)                                        # noqa: E731

    z5 = mp.findroot(lambda w: E(w) - w, mp.mpc(*ZSTAR5))
    d6 = E.taylor(z5, mp.mpf("0.20"), 24, N=288)
    Q6 = Superfunction(z5, [mp.mpc(0)] + d6[1:], forward=pen)
    Q6.C = mp.mpc(1)
    mu5, logmu = Q6.lam, mp.log(Q6.lam)
    qper = 2 * mp.pi * mp.mpc(0, 1) / logmu
    Ru = 1 / max(abs(Q6.u[k + 1] / Q6.u[k]) for k in range(12, 24)
                 if Q6.u[k] != 0)
    print(f"pen: x*={mp.nstr(E.xs,18)}  lam={mp.nstr(E.lam,14)}")
    print(f"z*_5 = {mp.nstr(z5,22)}")
    print(f"mu_5 = {mp.nstr(mu5,18)}  |mu_5| = {mp.nstr(abs(mu5),12)}  (repelling)")
    print(f"Q6 period = {mp.nstr(qper,14)}   u-radius = {mp.nstr(Ru,6)}")

    inv_stats = [0, 0]

    def pen_inv(y, guess):
        """x with pen(x) = y, Newton; the branch is whatever `guess` picks."""
        v, g = mp.mpc(guess), mp.mpc(guess)
        tol = mp.mpf(10) ** (-mp.mp.dps + 6)
        for it in range(40):
            try:
                f = pen(v) - y
            except Exception:
                v = (v + g) / 2
                continue
            if f == 0:
                break
            h = mp.mpf(10) ** (-mp.mp.dps // 3) * max(mp.mpf(1), abs(v))
            try:
                df = (pen(v + h) - pen(v - h)) / (2 * h)
            except Exception:
                df = 0
            if df == 0:
                v = (v + g) / 2
                continue
            step = f / df
            cap = mp.mpf("0.3") * max(mp.mpf(1), abs(v))
            if abs(step) > cap:
                step *= cap / abs(step)
            v -= step
            if abs(step) < tol:
                break
        inv_stats[0] += 1
        inv_stats[1] += it + 1
        return v

    def Q6inv(y):
        """z*_5 is repelling for pen, so pen^{-1} drives y into its disc."""
        n, v = 0, mp.mpc(y)
        while abs(v - z5) > Q6.smax and n < 60:
            v = pen_inv(v, z5 + (v - z5) / mu5)
            n += 1
            if abs(v) > 100:
                raise ValueError("left the neighbourhood of z*_5")
        if n >= 60:
            raise ValueError("did not reach the disc of z*_5")
        return mp.log(Q6.sigma(v) * mp.power(mu5, n)) / logmu

    # ---- seed: 1 + z (no regular hexation exists above b_c6) --------------
    R, delta, nt = mp.mpf(args.radius), mp.mpf(args.delta), args.nt
    NC, NF, NM = args.ncirc, args.nf, args.modes
    circle = [mp.e ** (mp.mpc(0, 1) * 2 * mp.pi * mp.mpf(j) / NC)
              for j in range(NC)]
    coeffs = [mp.mpf(1), mp.mpf(1)] + [mp.mpf(0)] * (nt - 2)
    H = lambda z: series_eval(coeffs, z)                        # noqa: E731

    def cauchy(vals):
        out = []
        for k in range(nt):
            acc = mp.mpc(0)
            for j, v in enumerate(vals):
                acc += v * mp.e ** (-mp.mpc(0, 1) * 2 * mp.pi * k
                                    * mp.mpf(j) / NC)
            out.append(acc.real / (NC * mp.power(R, k)))
        out[0] = mp.mpf(1)
        return out

    def residual():
        return abs(H(mp.mpf("0.5")) - pen(H(mp.mpf("-0.5"))))

    print(f"\nseed = 1 + z,  nt={nt} R={R} delta={delta} modes={NM} "
          f"nf={NF} ncirc={NC}")
    print("  seed residual =", mp.nstr(residual(), 5))

    ts = [mp.mpf(j) / NF - mp.mpf("0.5") for j in range(NF)]
    for loop in range(args.loops):
        # (A) theta on Im z = delta, unwrapped by Q6's period
        raw = []
        for t in ts:
            z = mp.mpc(t, delta)
            raw.append(Q6inv(H(z)) - z)
        th = [raw[0]]
        for v in raw[1:]:
            k = mp.nint(((th[-1] - v) / qper).real)
            th.append(v + k * qper)

        # (B) non-negative modes only -- the Kneser condition
        fa = []
        for m in range(NM):
            acc = mp.mpc(0)
            for j, tv in enumerate(th):
                acc += tv * mp.e ** (-2 * mp.pi * mp.mpc(0, 1) * m * ts[j])
            fa.append(acc / NF)

        def theta(z):
            zs = z - mp.mpc(0, 1) * delta
            acc, w = mp.mpc(0), mp.mpc(1)
            b = mp.e ** (2 * mp.pi * mp.mpc(0, 1) * zs)
            for m in range(NM):
                acc += fa[m] * w
                w *= b
            return acc

        # (C) resample on the circle
        vals = []
        for cz in circle:
            lower = cz.imag < 0
            z = R * (mp.conj(cz) if lower else cz)
            if z.imag >= delta:
                v = Q6.value(z + theta(z))       # repelling: walks with pen
            elif z.real > 0:
                v = pen(H(z - 1))
            else:
                v = pen_inv(H(z + 1), H(z))
            vals.append(mp.conj(v) if lower else v)

        new = cauchy(vals)
        move = max(abs(new[k] - coeffs[k]) for k in range(nt))
        coeffs = new
        avg = inv_stats[1] / max(1, inv_stats[0])
        inv_stats[0] = inv_stats[1] = 0
        print(f"  loop {loop:2d}: max|dc| = {mp.nstr(move,5):>12}"
              f"   residual = {mp.nstr(residual(),5):>12}"
              f"   <newton> = {avg:.1f}  [{time.time()-t0:.0f}s]")

    print("\nanchors forced by H(0)=1 and H(z+1)=pen(H(z)):")
    for zt, want in (("-2", "-1"), ("-1", "0"), ("0", "1"), ("1", "e")):
        v = H(mp.mpf(zt))
        tgt = mp.e if want == "e" else mp.mpf(want)
        print(f"  H({zt:>2}) = {mp.nstr(v,18):>22}   target {want:>2}"
              f"   |diff| = {mp.nstr(abs(v-tgt),5)}")
    print("\nhexation values:")
    for zt in ("1/4", "1/2", "3/4"):
        a, b = zt.split("/")
        z = mp.mpf(a) / mp.mpf(b)
        print(f"  e^^^^({zt}) = {mp.nstr(H(z), 18)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
