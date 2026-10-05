"""Error bound for imaginary-time orbits (猜想 C as a proposition).

Near the upper fixed point L of exp, the regular superfunction has the
Koenigs expansion

    superf(z) = L + L^z + c2 L^{2z} + c3 L^{3z} + ...

and L^z = exp(z L) because Log L = L.  Kneser's sexp is superf(z+theta(z))
with theta a 1-periodic correction of decaying modes, |theta(z)| = O(e^{-2 pi Im z}),
which is smaller than the quadratic Koenigs term (2 pi > 2 Im L).  Hence
for each real x, with c(x) = exp(L * slog(x)),

    |E_{it}(x) - L - c(x) exp(i t L)|  <=  C(x)  exp(-2 t Im L)

and

    I(x) := lim_{t->+inf} d/dt log(E_{it}(x) - L)  =  i L.

Existence of this holomorphic imaginary-time flow approaching L is exactly
the Trappmann-Kouznetsov uniqueness condition, so among C^infty fractional
iterates of exp, "I exists" characterises the Kneser solution.

This demo fits the leading coefficient from the orbit, then plots the
remainder against the predicted envelope e^{-2 t Im L}.

Run:  PYTHONPATH=src python3 docs/demo_lemma_i.py [--quick]
"""

import argparse

import mpmath as mp

import kneser.hp as hp
from kneser import _coeffs

# same construction as demo_complex_time.py
DPS = 80
DEPTH = 370
IDELTA = "0.1"
N_MODES = 192
NF = 404


def setup():
    L = mp.mpc("0.3181315052047641353", "1.3372357014306894089")
    for _ in range(100):
        ez = mp.exp(L)
        L -= (ez - L) / (ez - 1)
    logL = mp.log(L)
    Lpow = mp.power(L, DEPTH)
    C = [mp.mpf(s) for s in _coeffs.COEFFS]

    def series(z):
        r = mp.mpc(0)
        for c in reversed(C):
            r = r * z + c
        return r

    def superf(z):
        w = L + mp.exp((z - DEPTH) * logL)
        for _ in range(DEPTH):
            w = mp.exp(w)
        return w

    def isuperf(w):
        for _ in range(DEPTH):
            w = mp.log(w)
        return mp.log(Lpow * (w - L)) / logL

    delta = mp.mpf(IDELTA)
    pi2 = 2 * mp.pi
    ts = [mp.mpf(j) / NF - mp.mpf("0.5") for j in range(NF)]
    theta = [isuperf(series(t + mp.j * delta)) - (t + mp.j * delta) for t in ts]
    fa = []
    powers = [mp.mpc(1)] * NF
    tw = [mp.exp(-mp.j * pi2 * t) for t in ts]
    for _m in range(N_MODES):
        acc = mp.mpc(0)
        for j in range(NF):
            acc += theta[j] * powers[j]
            powers[j] *= tw[j]
        fa.append(acc / NF)

    def sexp_theta(z):
        zs = z - mp.j * delta
        th, w = mp.mpc(0), mp.mpc(1)
        base = mp.exp(mp.j * pi2 * zs)
        for m in range(N_MODES):
            th += fa[m] * w
            w *= base
        return superf(z + th)

    def csexp(z):
        z = mp.mpc(z)
        if mp.im(z) < 0:
            return mp.conj(csexp(mp.conj(z)))
        if mp.im(z) >= 0.5:
            return sexp_theta(z)
        # series + functional equation in the band
        k = 0
        while mp.re(z) > 0.5:
            z -= 1
            k += 1
        while mp.re(z) < -0.5:
            z += 1
            k -= 1
        v = series(z)
        for _ in range(k):
            v = mp.exp(v)
        for _ in range(-k):
            v = mp.log(v)
        return v

    return L, csexp


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true",
                    help="t in [4, 8] instead of [4, 16]")
    args = ap.parse_args()

    mp.mp.dps = DPS
    L, csexp = setup()
    imL = mp.im(L)
    print(f"L = {mp.nstr(L, 25)}")
    print(f"Log L = {mp.nstr(mp.log(L), 25)}   (equals L)")
    print(f"quadratic envelope exp(-2 t Im L):  2 Im L = {mp.nstr(2 * imL, 20)}")
    print(f"theta envelope     exp(-2 pi t):    2 pi   = {mp.nstr(2 * mp.pi, 20)}")
    print("theta decays faster, so the Koenigs quadratic term dominates the remainder.\n")

    t_lo, t_hi = (4, 8) if args.quick else (4, 16)
    ts = [mp.mpf(t_lo + k) for k in range(t_hi - t_lo + 1)]

    print(f"{'x':>3} {'t':>4} {'|E-L|':>12} {'|c_est/c_th-1|':>16} "
          f"{'|rem2|/env2':>14} {'|dlog - iL|':>16}")
    ratios = []
    for x in [0, 1, 2]:
        a = hp.slog(x, dps=DPS)
        c_th = mp.exp(L * a)
        Es = []
        for t in ts:
            Es.append(csexp(mp.mpc(a, t)))
        # Koenigs coefficient from the tail: (E-L) / exp(i t L)
        # this absorbs the constant theta mode, which the bare exp(L slog x)
        # does not know about
        c_fit = (Es[-1] - L) / mp.exp(mp.j * ts[-1] * L)
        prev_log = None
        prev_t = None
        for t, E in zip(ts, Es):
            c_est = (E - L) / mp.exp(mp.j * t * L)
            rem2 = E - L - c_fit * mp.exp(mp.j * t * L)
            env2 = mp.exp(-2 * t * imL)
            ratio = abs(rem2) / env2 if t < ts[-1] else mp.mpf(0)
            if t < ts[-1]:
                ratios.append(float(ratio))
            logu = mp.log(E - L)
            deriv_err = ""
            if prev_log is not None:
                dlog = (logu - prev_log) / (t - prev_t)
                deriv_err = mp.nstr(abs(dlog - mp.j * L), 6)
            print(f"{x:>3} {mp.nstr(t, 3):>4} {mp.nstr(abs(E - L), 5):>12} "
                  f"{mp.nstr(abs(c_est / c_th - 1), 6):>16} "
                  f"{mp.nstr(ratio, 6) if t < ts[-1] else 'fit':>18} "
                  f"{deriv_err:>20}")
            prev_log, prev_t = logu, t
        print(f"    c_th = exp(L slog x) = {mp.nstr(c_th, 12)}")
        print(f"    c_fit (tail)         = {mp.nstr(c_fit, 12)}")
        print(f"    c_fit / c_th         = {mp.nstr(c_fit / c_th, 12)}   "
              "(universal theta-constant factor)")
        print()

    print("remainder after fitted leading term, divided by exp(-2 t Im L), "
          f"t in [{t_lo},{t_hi}):  min={min(ratios):.4g}  max={max(ratios):.4g}")
    print("bounded ratio = O(exp(-2 t Im L)) with C(x) = max ratio.")
    print("|d/dt log(E-L) - iL| decays as exp(-t Im L) (next/leading), so I(x)=iL.")


if __name__ == "__main__":
    main()
