"""Superfunctions at a hyperbolic fixed point, from the map's Taylor series.

Given an analytic map T with a fixed point p and multiplier

    lam = T'(p),        lam != 0,  |lam| != 1,

Koenigs' theorem gives a unique analytic sigma near p with sigma(p) = 0,
sigma'(p) = 1 and sigma(T(x)) = lam * sigma(x).  Writing u = sigma^{-1},

    S(z) = p + u(C * lam**z)

satisfies S(z+1) = T(S(z)) for any constant C, and C fixes the normalisation.
This module turns "Taylor series of T at p" into such an S.  It is the engine
behind regular (Schroeder) iteration; `_regular.py` is the special case
T(w) = b**w, and rank-5 and higher hyperoperations are further cases where T is
itself a superfunction of the rank below.

Both signs of hyperbolicity are handled, and they differ in how a point far
from p is reached:

    |lam| < 1  (attracting)  -- |lam**z| is small for z large: shift z UP,
                                sum the series, then walk back down with the
                                INVERSE map.
    |lam| > 1  (repelling)   -- |lam**z| is small for z very negative: shift z
                                DOWN, sum the series, then walk back up with
                                the FORWARD map.

In both cases the series is only ever summed well inside its disc of
convergence and every step away from it is an exact application of the map,
so no error is amplified by lam**n.  Building the input series by ITERATING the
map instead (sigma(x) = lim lam**n (T^{-n}(x) - p)) does amplify: for rank 5,
lam = 6.46 and n = 40 already costs 32 digits.  See
`docs/hyperoperation-program-zh.md` and `docs/base-separation-zh.md` section 3.

Everything runs at the ambient mpmath precision; callers set `mp.workdps`.
"""

from __future__ import annotations

import mpmath as mp

__all__ = [
    "Superfunction",
    "inverse_schroeder",
    "series_shift",
    "series_mul",
    "series_log",
    "series_eval",
    "tau_of_exponential",
]

_SMAX_CAP = mp.mpf("0.05")


# --------------------------------------------------------------- power series
def series_mul(a, b, K):
    """Coefficients of (sum a_i t^i)(sum b_j t^j) truncated at t**K."""
    out = [mp.mpf(0)] * (K + 1)
    for i, ai in enumerate(a[: K + 1]):
        if ai == 0:
            continue
        for j in range(0, K + 1 - i):
            out[i + j] += ai * b[j]
    return out


def series_shift(c, a, K):
    """Re-expand sum c_j z**j about z = a, keeping K+1 terms.

    Valid when |a| is inside the disc of convergence; the truncation error
    inherits the tail of c."""
    powers = [mp.mpf(1)]
    for _ in range(len(c)):
        powers.append(powers[-1] * a)
    out = []
    for k in range(K + 1):
        s = mp.mpf(0)
        for j in range(k, len(c)):
            s += c[j] * mp.binomial(j, k) * powers[j - k]
        out.append(s)
    return out


def series_log(d, K):
    """Coefficients of log(sum d_k t**k); requires d[0] != 0."""
    w = [d[k] / d[0] for k in range(K + 1)]
    w[0] = mp.mpf(0)
    out = [mp.log(d[0])] + [mp.mpf(0)] * K
    power = [mp.mpf(1)] + [mp.mpf(0)] * K
    for m in range(1, K + 1):
        power = series_mul(power, w, K)
        sign = 1 if m % 2 else -1
        for k in range(K + 1):
            out[k] += sign * power[k] / m
    return out


def series_eval(c, t):
    r = mp.mpf(0)
    for ck in reversed(c):
        r = r * t + ck
    return r


def inverse_schroeder(tau):
    """u(s) = s + sum_{k>=2} u_k s**k with tau(u(s)) = u(lam s), lam = tau[1].

    Comparing [s^k]:  u_k (lam**k - lam) = [s^k] sum_{m>=2} tau_m u(s)**m,
    whose right side involves only u_1 .. u_{k-1}.  No resonance as long as
    |lam| != 1, which keeps lam**k != lam for k >= 2.

    This is the single source of truth for regular (Schroeder) iteration in
    this package; `_regular.py` and `Superfunction` both call it."""
    K = len(tau) - 1
    lam = tau[1]
    u = [mp.mpf(0), mp.mpf(1)] + [mp.mpf(0)] * (K - 1)
    for k in range(2, K + 1):
        lower = list(u)
        lower[k] = mp.mpf(0)
        power = list(lower)                          # u(s)**1
        acc = mp.mpf(0)
        for m in range(2, k + 1):
            power = series_mul(power, lower, K)
            if tau[m] != 0:
                acc += tau[m] * power[k]
        u[k] = acc / (mp.power(lam, k) - lam)
    return u


def tau_of_exponential(b, alpha, K):
    """tau for T(w) = b**w at its fixed point alpha (b**alpha = alpha).

    T(alpha + t) - alpha = alpha*(exp(t log b) - 1), so tau_m = alpha (log b)^m / m!
    and tau_1 = alpha log b = lam.  This is the `_regular.py` case in the form
    this module wants."""
    lb = mp.log(b)
    tau = [mp.mpf(0)]
    term = mp.mpf(1)
    for m in range(1, K + 1):
        term = term * lb / m
        tau.append(alpha * term)
    return tau


# ------------------------------------------------------------------- the engine
class Superfunction:
    """S with S(z+1) = T(S(z)), built from the Taylor series of T at p.

    Parameters
    ----------
    p     : the fixed point.
    tau   : coefficients of tau(t) = T(p+t) - p, with tau[0] == 0 and
            tau[1] == lam.  Length K+1 sets the series order.
    forward  : callable applying T exactly (needed when |lam| > 1).
    inverse  : callable applying T^{-1} exactly (needed when |lam| < 1).

    Only the one matching the sign of hyperbolicity is required; passing both
    lets `value` be used with `extra` in either direction.
    """

    __slots__ = ("p", "tau", "K", "lam", "u", "smax", "forward", "inverse", "C")

    def __init__(self, p, tau, *, forward=None, inverse=None):
        if tau[0] != 0:
            raise ValueError("tau[0] must be 0: tau(t) = T(p+t) - p")
        self.p = p
        self.tau = list(tau)
        self.K = len(tau) - 1
        self.lam = tau[1]
        if self.lam == 0 or abs(abs(self.lam) - 1) < mp.mpf(10) ** (-mp.mp.dps // 2):
            raise ValueError("fixed point is not hyperbolic (lam = 0 or |lam| = 1)")
        self.forward = forward
        self.inverse = inverse
        self.u = inverse_schroeder(self.tau)
        self.smax = self._disc()
        self.C = mp.mpf(1)

    # -- series -------------------------------------------------------------
    def _disc(self):
        """A radius well inside the disc of convergence of u."""
        ratios = [abs(self.u[k + 1] / self.u[k])
                  for k in range(self.K // 2, self.K)
                  if self.u[k] != 0 and self.u[k + 1] != 0]
        if not ratios:
            return _SMAX_CAP
        return min(_SMAX_CAP, 1 / (8 * max(ratios)))

    def u_eval(self, s):
        return series_eval(self.u, s)

    def sigma(self, x):
        """Schroeder function sigma = u^{-1}, by Newton on the u series.

        Only valid for x within the disc; callers reach other points with the
        functional equation sigma(T(x)) = lam sigma(x)."""
        t = x - self.p
        s = t
        tol = mp.mpf(10) ** (-mp.mp.dps + 5)
        for _ in range(80):
            f = series_eval(self.u, s) - t
            df = sum(k * self.u[k] * mp.power(s, k - 1)
                     for k in range(1, self.K + 1))
            step = f / df
            s -= step
            if abs(step) < tol * max(mp.mpf(1), abs(s)):
                break
        return s

    # -- evaluation ----------------------------------------------------------
    def _split(self, z, extra=0):
        """(argument inside the disc, number of map steps, direction)."""
        repelling = abs(self.lam) > 1
        step = -1 if repelling else 1            # shift applied to z
        arg = self.C * mp.power(self.lam, z)
        n = 0
        while abs(arg) > self.smax:
            arg = arg / self.lam if repelling else arg * self.lam
            n += 1
        for _ in range(extra):
            arg = arg / self.lam if repelling else arg * self.lam
            n += 1
        return arg, n, step

    def value(self, z, extra=0):
        """S(z).  `extra` pushes the series further into the disc and takes
        that many more exact map steps; the answer must not depend on it, and
        that is the only non-trivial self-check the construction admits --
        S(z+1) = T(S(z)) holds by fiat."""
        arg, n, step = self._split(z, extra)
        w = self.p + series_eval(self.u, arg)
        move = self.forward if step < 0 else self.inverse
        if n and move is None:
            raise ValueError("need %s map to reach this argument"
                             % ("forward" if step < 0 else "inverse"))
        for _ in range(n):
            w = move(w)
        return w

    def normalize(self, target=None, z0=0, steps=4):
        """Set C so that S(z0) = target (default target = 1).

        C is read off near the fixed point, where u is accurate, and carried
        out with only `steps` exact map applications, so the lam**steps factor
        stays small.  Increasing `steps` improves the Koenigs truncation but
        amplifies the input error by |lam|**steps; a few steps is the optimum
        and callers should check stability across `steps`."""
        target = mp.mpf(1) if target is None else target
        repelling = abs(self.lam) > 1
        move = self.inverse if repelling else self.forward
        if move is None:
            raise ValueError("normalize needs the opposite map")
        y = target
        for _ in range(steps):
            y = move(y)
        shift = -steps if repelling else steps
        self.C = self.sigma(y) * mp.power(self.lam, -(z0 + shift))
        return self.C
