"""Regular (Schroeder) iteration for bases 1 < b < eta = e^(1/e).

For such b the map E(w) = b**w has an attracting real fixed point

    alpha = -W(-log b) / log b,      lambda = E'(alpha) = alpha * log b  in (0, 1),

and the tower 1, b, b^b, ... increases to alpha.  The regular superfunction
is the analytic F with F(z+1) = E(F(z)) and F(z) = alpha + u(-lambda**z),
where u is the inverse Schroeder series, u(s) = s + c_2 s^2 + c_3 s^3 + ...,
determined by E(alpha + u(s)) = alpha + u(lambda s).  Tetration is
sexp(z) = F(z + z0) with F(z0) = 1.

Evaluation: pick n with lambda**(z+n) small, sum the series there, then
apply log_b n times.  This is the classical construction (Koenigs 1884,
Szekeres 1958); unlike the Kneser regime no theta correction is needed and
the function is real-analytic on z > -2 with the same logarithmic
singularity at z = -2.  The values fill (-inf, alpha); the upper repelling
fixed point is never reached.  The engine works in mpmath and is shared by
the float64 and hp APIs.
"""

from __future__ import annotations

from functools import lru_cache

import mpmath as mp

from ._bases import normalize_base, regime

_GUARD = 10
_TERMS = 64
_SMAX = mp.mpf("0.05")  # |s| at which the series is summed


class RegularEngine:
    __slots__ = ("BASE", "DIGITS", "dps", "b", "logb", "alpha", "lam", "loglam",
                 "coeffs", "smax", "z0", "RESIDUAL", "COEFFS", "_hi", "_lo")

    def __init__(self, name: str, digits: int):
        self.BASE = name
        self.DIGITS = digits
        self.dps = digits + _GUARD
        with mp.workdps(self.dps):
            b = mp.e if name == "e" else mp.mpf(name)
            self.b = b
            self.logb = mp.log(b)
            self.alpha = mp.re(-mp.lambertw(-self.logb) / self.logb)
            self.lam = self.alpha * self.logb
            self.loglam = mp.log(self.lam)
            self.coeffs = self._schroeder_inverse(_TERMS)
            # sum the series only well inside its disc: radius ~ 1/max|c_{k+1}/c_k|
            c = self.coeffs
            ratio = max(abs(c[k + 1] / c[k]) for k in range(_TERMS // 2, _TERMS))
            self.smax = min(_SMAX, 1 / (8 * ratio))
            self.z0 = mp.mpf(0)
            self.z0 = self._normalize()
            self.COEFFS = tuple(mp.nstr(c, digits + 6) for c in self.coeffs)
            self._hi = self.sexp(mp.mpf("0.5"))
            self._lo = self.sexp(mp.mpf("-0.5"))
            # functional-equation residual across the seam, as in the tables
            self.RESIDUAL = mp.nstr(abs(self._hi - mp.power(b, self._lo)), 4)

    # -- series ------------------------------------------------------------
    def _schroeder_inverse(self, K: int):
        """c_k of u(s) = sum c_k s^k with E(alpha + u(s)) = alpha + u(lam s)."""
        lb, alpha, lam = self.logb, self.alpha, self.lam
        c = [mp.mpf(0), mp.mpf(1)]
        g = [mp.mpf(1), lb]          # g = exp(lb * u(s)) power series
        for k in range(2, K + 1):
            # g_k = lb*c_k + P_k with P_k from lower orders (exp recurrence)
            P = sum(j * lb * c[j] * g[k - j] for j in range(1, k)) / k
            ck = alpha * P / (mp.power(lam, k) - lam)
            c.append(ck)
            g.append(lb * ck + P)
        return c

    def _u(self, s):
        r = 0
        for ck in reversed(self.coeffs[1:]):
            r = r * s + ck
        return r * s

    def _du(self, s):
        r = 0
        for k in range(len(self.coeffs) - 1, 0, -1):
            r = r * s + k * self.coeffs[k]
        return r

    # -- superfunction -------------------------------------------------------
    def _F(self, z, derivative=False):
        """F(z) = alpha + u(-lam**z) continued by log_b; optionally (F, F')."""
        lam, lb, loglam = self.lam, self.logb, self.loglam
        re = mp.re(z)
        # lam**(z+n) <= smax  <=>  z + n >= log(smax)/log(lam)
        n = int(mp.ceil(mp.log(self.smax) / loglam - re))
        if n < 0:
            n = 0
        s = -mp.exp((z + n) * loglam)
        w = self.alpha + self._u(s)
        if derivative:
            dw = self._du(s) * s * loglam
        for _ in range(n):
            if isinstance(w, mp.mpf) and w <= 0:
                raise ValueError("below the z = -2 singularity of tetration")
            if derivative:
                dw = dw / (w * lb)
            w = mp.log(w) / lb
        return (w, dw) if derivative else w

    def _normalize(self):
        """z0 with F(z0) = 1."""
        one = mp.mpf(1)

        def f(z):
            try:
                return self._F(z) - one
            except ValueError:
                return mp.mpf(-1)

        hi = mp.mpf(0)
        while f(hi) < 0:
            hi += 1
        lo = hi - 1
        while f(lo) > 0:
            lo -= 1
        for _ in range(8):
            mid = (lo + hi) / 2
            if f(mid) < 0:
                lo = mid
            else:
                hi = mid
        z = (lo + hi) / 2
        for _ in range(100):
            v, d = self._F(z, derivative=True)
            step = (v - one) / d
            z -= step
            if abs(step) < mp.mpf(10) ** (-(self.dps - 2)):
                break
        return z

    # -- public --------------------------------------------------------------
    def sexp(self, z, derivative=False):
        if mp.re(z) <= -2:
            raise ValueError(f"sexp is defined for z > -2 (got {z})")
        with mp.workdps(self.dps):
            return self._F(z + self.z0, derivative)

    def slog(self, x):
        with mp.workdps(self.dps):
            return self._slog(mp.mpf(x))

    def _slog(self, x):
        if x >= self.alpha * (1 - mp.mpf(10) ** (-(self.DIGITS + 1))):
            if x <= self.alpha * (1 + mp.mpf(10) ** (-(self.DIGITS + 1))):
                return mp.inf
            raise ValueError(
                f"slog({x}) is undefined for base {self.BASE}: the tower converges to "
                f"alpha = {mp.nstr(self.alpha, 12)} and never exceeds it")
        # reduce into (sexp(-1/2), sexp(1/2)] with the functional equation
        k = 0
        while x > self._hi:
            x = mp.log(x) / self.logb
            k += 1
        while x <= self._lo:
            x = mp.power(self.b, x)
            k -= 1
        # Newton, safeguarded by the bracket [-1/2, 1/2]
        lo, hi = mp.mpf("-0.5"), mp.mpf("0.5")
        z = (x - 1) / self.sexp(mp.mpf(0), derivative=True)[1]
        tol = mp.mpf(10) ** (-(self.dps - 2))
        for _ in range(200):
            v, d = self.sexp(z, derivative=True)
            if v > x:
                hi = z
            else:
                lo = z
            step = (v - x) / d
            zn = z - step
            if not (lo < zn < hi):
                zn = (lo + hi) / 2
            done = abs(zn - z) <= tol * max(1, abs(z))
            z = zn
            if done:
                break
        return z + k


@lru_cache(maxsize=16)
def engine(name: str, digits: int = 17) -> RegularEngine:
    name = normalize_base(name)
    if regime(name) != "regular":
        raise ValueError(f"base {name} > eta is in the Kneser regime, not the regular one")
    return RegularEngine(name, digits)
