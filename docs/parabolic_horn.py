"""Ecalle-Voronin horn map of the parabolic germ at b = eta, upper end.

At b = eta the map w -> b^w has a parabolic fixed point at w = e.  In the
coordinate w = e(1+u) the germ is

    f(u) = e^u - 1 = u + u^2/2 + u^3/6 + ...

with the (divergent, asymptotic) Abel function already implemented in
kneser._general.ParabolicEngine:

    alpha(u) = -2/u + log(-u)/3 + sum_k c_k u^k,      alpha(f(u)) = alpha(u) + 1.

The attracting petal is on the side Re u < 0, the repelling petal on Re u > 0.
Both Fatou coordinates are normalised by the SAME alpha:

    Phi_att(u) = lim_{n->inf} [ alpha(f^n(u)) - n ],
    Phi_rep(u) = lim_{n->inf} [ alpha(f^{-n}(u)) + n ],   f^{-1}(u) = log(1+u).

On the upper gate the transition map h = Phi_rep o Phi_att^{-1} commutes with
z -> z+1, so

    h(z) - z = A_0 + A_1 e^{2 pi i z} + A_2 e^{4 pi i z} + ...

and |A_1| is the first horn-map invariant (|A_1| does not depend on the additive
normalisation of the Fatou coordinates, which is why it is the quantity to
compare with lim_{b->eta^-} |c1hat| from the hyperbolic side).

Usage: python3 docs/parabolic_horn.py [Y ...]
"""

from __future__ import annotations

import sys

import mpmath as mp

sys.path.insert(0, "/Volumes/dream/halfexp/kneser/src")

from kneser._general import parabolic_engine  # noqa: E402

TWOPI = None  # set inside workdps


class Alpha:
    """alpha(u) with the branch of log(-u) continued along a path."""

    def __init__(self, coeffs):
        self.coeffs = coeffs
        self.prev = None

    def reset(self, value=None):
        self.prev = value

    def log_cont(self, u):
        L = mp.log(-u)
        if self.prev is not None:
            k = mp.nint((mp.im(self.prev) - mp.im(L)) / (2 * mp.pi))
            L += 2j * mp.pi * k
        self.prev = L
        return L

    def __call__(self, u, cont=True):
        L = self.log_cont(u) if cont else mp.log(-u)
        p = mp.mpc(0)
        for c in reversed(self.coeffs):
            p = p * u + c
        return -2 / u + L / 3 + p * u

    def deriv(self, u):
        p = dp = mp.mpc(0)
        for c in reversed(self.coeffs):
            p = p * u + c
        for k in range(len(self.coeffs), 1, -1):
            dp = dp * u + (k - 1) * self.coeffs[k - 1]
        return 2 / u**2 + 1 / (3 * u) + p + dp * u


def phi_att_inverse(al, z, umax, nextra=4):
    """u with Phi_att(u) = z: solve alpha(u0) = z + n in the attracting petal,
    then pull back n times with f^{-1}(u) = log(1+u)."""
    n = int(mp.ceil(2 / umax - mp.re(z))) + nextra
    n = max(n, 1)
    t = z + n
    u = -2 / t
    al.reset()
    for _ in range(80):
        step = (al(u, cont=False) - t) / al.deriv(u)
        u -= step
        if abs(step) < mp.mpf(10) ** (-(mp.mp.dps - 5)):
            break
    us = [u]
    for _ in range(n):
        u = mp.log(1 + u)
        us.append(u)
    return u, us


def phi_rep(al, u, umax, maxit=20000, nextra=6):
    """Phi_rep(u) = lim [alpha(f^{-k}(u)) + k], f^{-1} = log(1+u)."""
    al.reset()
    al(u)                      # seed the branch at the starting point
    k = 0
    while abs(u) > umax and k < maxit:
        u = mp.log(1 + u)
        k += 1
        al(u)                  # keep the branch continuous
    if k >= maxit:
        raise ValueError("backward orbit did not enter the repelling petal")
    for _ in range(nextra):
        u = mp.log(1 + u)
        k += 1
        al(u)
    al.prev = None
    # recompute with a continuous branch from the start, in one sweep
    return u, k


def transition(Y, N=16, digits=40, terms=60, umax="0.01"):
    """h(z) - z sampled at z = j/N + iY, and its Fourier coefficients."""
    with mp.workdps(digits + 20):
        eng = parabolic_engine(digits)
        coeffs = list(eng.coeffs) if terms is None else list(eng.coeffs)
        al = Alpha(coeffs)
        umax = mp.mpf(umax)
        vals = []
        for j in range(N):
            z = mp.mpc(mp.mpf(j) / N, Y)
            u, _ = phi_att_inverse(al, z, umax)
            # walk backwards, tracking the branch, until the repelling petal
            al.reset()
            al(u)
            k = 0
            uu = u
            while abs(uu) > umax and k < 100000:
                uu = mp.log(1 + uu)
                k += 1
                al(uu)
            if k >= 100000:
                raise ValueError(f"no convergence at z={z}")
            for _ in range(6):
                uu = mp.log(1 + uu)
                k += 1
            hz = al(uu) + k
            vals.append(hz - z)
        cs = []
        for n in range(4):
            acc = mp.mpc(0)
            for j in range(N):
                z = mp.mpc(mp.mpf(j) / N, Y)
                acc += vals[j] * mp.exp(-2j * mp.pi * n * z)
            cs.append(acc / N)
        return cs, vals


def main(Ys):
    for Y in Ys:
        try:
            cs, vals = transition(mp.mpf(Y))
        except Exception as exc:     # noqa: BLE001
            print(f"Y={Y}: FAILED {exc}")
            continue
        print(f"Y={float(Y):.2f}  A0={mp.nstr(cs[0], 12)}")
        for n in (1, 2, 3):
            print(f"        |A{n}|={float(abs(cs[n])):.10f}  arg={float(mp.arg(cs[n])):+.6f}")


if __name__ == "__main__":
    args = [float(a) for a in sys.argv[1:]] or [1.0, 1.5, 2.0]
    main(args)
