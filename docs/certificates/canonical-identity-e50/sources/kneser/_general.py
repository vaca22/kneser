"""Tetration for every other base: complex a, 0 < a < 1, a < 0, and a = eta.

Two engines, both mpmath-based and used by the float64 and hp APIs.

``GeneralRegularEngine`` -- regular (Koenigs/Schroeder) iteration of
E(w) = a**w = exp(w * log a) at a fixed point L = -W_k(-log a)/log a with
multiplier lambda = L * log a, for any complex a not in {0, 1} whose fixed
point is hyperbolic (|lambda| != 1).  With u the inverse Schroeder series
(u(s) = s + c_2 s^2 + ..., E(L + u(s)) = L + u(lambda s)):

    |lambda| < 1:  F(z) = E^{-n}(L + u(lambda**(z+n)))     (inverse iteration)
    |lambda| > 1:  F(z) = E^{ n}(L + u(lambda**(z-n)))     (forward iteration)

with n chosen so |lambda**(z +- n)| is small.  sexp(z) = F(z + z0), F(z0) = 1.
For real a in (1, eta) this is exactly ``_regular`` (kept separately for its
real arithmetic).  For every other base the multiplier is negative or
complex, lambda**z is complex for non-integer z, and sexp is complex-valued
except at integer heights: no real-analytic tetration exists for such bases,
and this regular solution is the canonical holomorphic one at that fixed
point.  In the attracting case the backward orbit passes through 0
(sexp(-1) = 0, logarithmic singularity at -2); in the repelling case the
superfunction is entire and never vanishes, so sexp(-1) = 2*pi*i*k/log a
for some integer k -- the tower cannot be continued backwards through 0.

``ParabolicEngine`` -- base eta = e^(1/e), where E has the parabolic fixed
point e (multiplier 1).  With w = e*(1 + u) the map is u -> exp(u) - 1.  The
Abel function on the attracting petal (u < 0) has the asymptotic expansion

    alpha(u) = -2/u + (1/3) log(-u) + sum_{k>=1} c_k u^k

whose c_k are determined here formally from alpha(f(u)) = alpha(u) + 1.
F(z) is evaluated by inverting alpha at z + n (|u| ~ 0.02, Newton) and then
applying f^{-1}(u) = log(1 + u) n times.  This is the classical lower
(Szekeres/Ecalle) solution: real-analytic, increasing, sexp(z) -> e as z ->
+inf, and the limit of the regular solutions for a -> eta- (see
docs/base-plane-zh.md for the numerical check against the Kneser side).
"""

from __future__ import annotations

from functools import lru_cache

import mpmath as mp

_GUARD = 10
_TERMS = 64
_SMAX = mp.mpf("0.05")


class GeneralRegularEngine:
    def __init__(self, name: str, digits: int, branch: int = 0):
        from ._bases import base_value
        self.BASE = name
        self.DIGITS = digits
        self.branch = branch
        self.dps = digits + _GUARD
        with mp.workdps(self.dps):
            b = base_value(name)
            self.b = b
            self.logb = mp.log(b)
            self.L = -mp.lambertw(-self.logb, branch) / self.logb
            self.lam = self.L * self.logb
            self.loglam = mp.log(self.lam)
            r = abs(self.lam)
            if abs(r - 1) < mp.mpf(10) ** (-(digits // 2)):
                raise ValueError(f"base {name}: fixed point {mp.nstr(self.L, 8)} is neutral "
                                 f"(|lambda| = {mp.nstr(r, 8)}); no hyperbolic regular iteration")
            self.attracting = r < 1
            self.canonical = False   # set by _normalize: orbit-based normalization succeeded
            self.coeffs = self._schroeder_inverse(_TERMS)
            c = self.coeffs
            ratio = max(abs(c[k + 1] / c[k]) for k in range(_TERMS // 2, _TERMS) if c[k] != 0)
            self.smax = min(_SMAX, 1 / (8 * ratio))
            self.z0 = mp.mpc(0)
            self.z0 = self._normalize()
            self.COEFFS = tuple(mp.nstr(x, digits + 6) for x in c)
            half, mhalf = self.sexp(mp.mpf("0.5")), self.sexp(mp.mpf("-0.5"))
            self.RESIDUAL = mp.nstr(abs(half - mp.exp(self.logb * mhalf)), 4)

    def _schroeder_inverse(self, K):
        lb, L, lam = self.logb, self.L, self.lam
        c = [mp.mpc(0), mp.mpc(1)]
        g = [mp.mpc(1), lb]
        for k in range(2, K + 1):
            P = sum(j * lb * c[j] * g[k - j] for j in range(1, k)) / k
            ck = L * P / (mp.power(lam, k) - lam)
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

    def _F(self, z, derivative=False):
        lb, loglam = self.logb, self.loglam
        z = mp.mpc(z)
        # |lambda**w| = exp(Re(w * loglam)); want it <= smax
        if self.attracting:
            nn = mp.ceil((mp.log(self.smax) - mp.re(z * loglam)) / mp.re(loglam))
        else:
            nn = mp.ceil((mp.re(z * loglam) - mp.log(self.smax)) / mp.re(loglam))
        if not nn < 100000:
            raise ValueError(f"height {z} is too far from the fixed point for base {self.BASE}")
        n = max(int(nn), 0)
        s = mp.exp((z + n) * loglam) if self.attracting else mp.exp((z - n) * loglam)
        w = self.L + self._u(s)
        dw = self._du(s) * s * loglam if derivative else None
        for _ in range(n):
            if self.attracting:
                if w == 0:
                    raise ValueError("tetration singularity (iterated logarithm of 0)")
                if derivative:
                    dw = dw / (w * lb)
                w = mp.log(w) / lb
            else:
                try:
                    w = mp.exp(lb * w)
                except OverflowError:
                    raise ValueError(f"tower overflow at height {z} for base {self.BASE}") from None
                if derivative:
                    dw = lb * w * dw
        return (w, dw) if derivative else w

    def _inverse_u(self, w):
        """s with u(s) = w (Newton on the series; w small)."""
        s = w
        for _ in range(100):
            step = (self._u(s) - w) / self._du(s)
            s -= step
            if abs(step) < mp.mpf(10) ** (-(self.dps + 2)) * max(1, abs(s)):
                break
        return s

    def _normalize(self):
        """z0 with F(z0) = 1, from the orbit of 1 that converges to L.

        attracting: the forward orbit 1, a, a^a, ... -> L;
        repelling:  the backward orbit under the branch of log_a nearest L.
        Newton on F(z) = 1 is the fallback (a < e^-e: the backward orbit hits 0).
        """
        L, lb, loglam = self.L, self.logb, self.loglam
        tol = self.smax / 4
        w = mp.mpc(1)
        m = 0
        z0 = None
        try:
            while abs(w - L) > tol and m < 20000 and mp.isfinite(w):
                if self.attracting:
                    w = mp.exp(lb * w)
                else:
                    if w == 0:
                        raise ValueError("backward orbit of 1 reaches 0")
                    lw = mp.log(w)
                    k = int(mp.nint(-mp.im(lw - L * lb) / (2 * mp.pi)))
                    w = (lw + 2j * mp.pi * k) / lb
                m += 1
            if abs(w - L) <= tol:
                sv = self._inverse_u(w - L)
                z0 = mp.log(sv) / loglam + (-m if self.attracting else m)
                v = self._F(z0)
                if abs(v - 1) > mp.mpf(10) ** (-(self.dps - 6)):
                    z0 = self._newton_root(z0)          # polish (branch mismatch)
                self.canonical = True
        except (ValueError, ZeroDivisionError, OverflowError):
            z0 = None
        if z0 is None:
            # repelling principal fixed point whose backward orbit from 1 dies
            # (typically at 0): F(z) = 1 has clustering roots and no canonical
            # choice; the engine stays usable for research via _newton_root.
            self.canonical = False
            return mp.mpc(0)
        return z0

    def _newton_root(self, z):
        for _ in range(200):
            try:
                v, d = self._F(z, derivative=True)
            except (ValueError, ZeroDivisionError, OverflowError):
                raise ValueError("newton left the domain")
            step = (v - 1) / d
            if abs(step) > 1:
                step = step / abs(step)
            z -= step
            if abs(z) > 40:
                raise ValueError("newton diverged")
            if abs(step) < mp.mpf(10) ** (-(self.dps - 2)):
                return z
        raise ValueError("newton did not converge")

    def sexp(self, z, derivative=False):
        with mp.workdps(self.dps):
            return self._F(mp.mpc(z) + self.z0, derivative)

    def slog(self, x):
        """A height z with sexp(z) = x.

        Attracting case: iterate E forward from x until the orbit is inside
        the series disc, invert the Schroeder series there, and read off the
        Abel time (the same construction as the normalization, so
        slog(sexp(z)) = z exactly up to the period 2*pi*i/log(lambda), which
        is removed by taking the branch nearest z = 0 when needed).
        """
        with mp.workdps(self.dps):
            x = mp.mpc(x)
            L, lb, loglam = self.L, self.logb, self.loglam
            if not self.attracting:
                raise ValueError(f"slog is not available for base {self.BASE} (repelling fixed point)")
            tol = self.smax / 4
            w = x
            m = 0
            while abs(w - L) > tol and m < 20000 and mp.isfinite(w):
                w = mp.exp(lb * w)
                m += 1
            if not abs(w - L) <= tol:
                raise ValueError(f"slog({x}) for base {self.BASE}: the orbit of x does not converge "
                                 f"to the fixed point {mp.nstr(L, 8)}")
            sv = self._inverse_u(w - L)
            z = mp.log(sv) / loglam - m - self.z0
            # the branch of log(sv) is free: choose the one nearest the real axis
            period = 2j * mp.pi / loglam
            k = mp.nint(-mp.im(z) / mp.im(period)) if mp.im(period) != 0 else 0
            z += k * period
            if abs(mp.im(z)) < mp.mpf(10) ** (-(self.dps - 4)):
                z = mp.mpc(mp.re(z))
            return z


class ParabolicEngine:
    BASE = "eta"

    def __init__(self, digits: int, terms: int = 40):
        self.DIGITS = digits
        self.dps = digits + _GUARD
        with mp.workdps(self.dps + 10):
            self.coeffs = self._abel_coefficients(terms)   # c_1 .. c_terms
            self.terms = terms
            # summation point: the asymptotic series is used at |u| <= umax
            self.umax = mp.mpf("0.02")
            self.z0 = mp.mpf(0)
            self.z0 = self._normalize()
            half, mhalf = self.sexp(mp.mpf("0.5")), self.sexp(mp.mpf("-0.5"))
            self.RESIDUAL = mp.nstr(abs(half - mp.exp(mhalf / mp.e)), 4)
            self.COEFFS = tuple(mp.nstr(c, digits + 6) for c in self.coeffs)

    @staticmethod
    def _abel_coefficients(K):
        """c_k in alpha(u) = -2/u + log(-u)/3 + sum c_k u^k for f(u) = e^u - 1."""
        N = K + 2
        f = [mp.mpf(0)] + [1 / mp.factorial(k) for k in range(1, N + 1)]   # e^u - 1
        # known part: R(u) = 1 - (-2/f + 2/u) - (1/3) log(f/u)
        g1 = mp.taylor(lambda u: -2 / (mp.exp(u) - 1) + 2 / u if u != 0 else mp.mpf(1), 0, N)
        g2 = mp.taylor(lambda u: mp.log((mp.exp(u) - 1) / u) / 3 if u != 0 else mp.mpf(0), 0, N)
        R = [mp.re(1 - g1[m] - g2[m] if m == 0 else -g1[m] - g2[m]) for m in range(N + 1)]

        def mul(p, q):
            out = [mp.mpf(0)] * (N + 1)
            for i, pi in enumerate(p):
                if pi == 0:
                    continue
                for j, qj in enumerate(q):
                    if i + j > N:
                        break
                    out[i + j] += pi * qj
            return out
        powers = [None, f]
        for j in range(2, K + 1):
            powers.append(mul(powers[-1], f))
        c = [mp.mpf(0)] * (K + 1)
        for k in range(1, K + 1):
            m = k + 1
            acc = R[m]
            for j in range(1, k):
                acc -= c[j] * powers[j][m]          # [u^m](f^j - u^j), m > j
            c[k] = acc / powers[k][m]              # [u^{k+1}] f^k = k/2
        return [mp.re(x) for x in c[1:]]

    def _alpha(self, u, derivative=False):
        a = -2 / u + mp.log(-u) / 3
        p, dp = 0, 0
        for k in range(len(self.coeffs), 0, -1):
            p = p * u + self.coeffs[k - 1]
        for k in range(len(self.coeffs), 1, -1):
            dp = dp * u + (k - 1) * self.coeffs[k - 1]
        val = a + p * u
        if not derivative:
            return val
        return val, 2 / u ** 2 + 1 / (3 * u) + p + dp * u

    def _F(self, z, derivative=False):
        """u-coordinate at Abel time z: F -> 0- as z -> +inf; log(1+u) chain otherwise."""
        target_re = 2 / self.umax
        n = int(mp.ceil(target_re - mp.re(z)))
        n = max(n, 0)
        t = z + n
        u = -2 / t
        for _ in range(60):
            a, da = self._alpha(u, derivative=True)
            step = (a - t) / da
            u -= step
            if abs(step) < mp.mpf(10) ** (-(self.dps + 5)):
                break
        du = 1 / da if derivative else None
        for _ in range(n):
            if u == -1:
                raise ValueError("tetration singularity at height -2")
            if derivative:
                du = du / (1 + u)
            u = mp.log(1 + u)
        return (u, du) if derivative else u

    def _normalize(self):
        target = 1 / mp.e - 1          # sexp = e(1+u) = 1
        z = -2 / target + mp.log(-target) / 3   # leading terms of alpha(target)
        for _ in range(100):
            v, d = self._F(z, derivative=True)
            step = mp.re((v - target) / d)
            z -= step
            if abs(step) < mp.mpf(10) ** (-(self.dps - 2)):
                break
        return z

    def sexp(self, z, derivative=False):
        with mp.workdps(self.dps):
            if isinstance(z, mp.mpf) or (isinstance(z, mp.mpc) and z.imag == 0):
                z = mp.mpf(mp.re(z))
                if z <= -2:
                    raise ValueError(f"sexp is defined for z > -2 (got {z})")
            r = self._F(z + self.z0, derivative)
            fix = (lambda v: mp.re(v)) if isinstance(z, mp.mpf) else (lambda v: v)
            if derivative:
                return fix(mp.e * (1 + r[0])), fix(mp.e * r[1])
            return fix(mp.e * (1 + r))

    def slog(self, x):
        with mp.workdps(self.dps):
            x = mp.mpf(mp.re(x))
            if x >= mp.e:
                if abs(x - mp.e) < mp.mpf(10) ** (-(self.DIGITS + 1)):
                    return mp.inf
                raise ValueError(f"slog({x}) is undefined for base eta: the tower converges to e")
            # bracket on the real line then Newton
            lo, hi = mp.mpf(-2) + mp.mpf(10) ** (-self.dps), mp.mpf(1)
            while self.sexp(hi) < x:
                hi *= 2
            z = mp.mpf(0) if x > 0 else -1
            for _ in range(300):
                v, d = self.sexp(z, derivative=True)
                if v > x:
                    hi = z
                else:
                    lo = z
                zn = z - (v - x) / d
                if not (lo < zn < hi):
                    zn = (lo + hi) / 2
                done = abs(zn - z) < mp.mpf(10) ** (-(self.dps - 2)) * max(1, abs(z))
                z = zn
                if done:
                    break
            return z


@lru_cache(maxsize=32)
def general_engine(name: str, digits: int = 17, branch: int = 0) -> GeneralRegularEngine:
    return GeneralRegularEngine(name, digits, branch)


@lru_cache(maxsize=8)
def parabolic_engine(digits: int = 17) -> ParabolicEngine:
    return ParabolicEngine(digits)


class ComplexKneserEngine:
    """Evaluate the two-fixed-point Kneser tetration of a complex base from its table.

    Only ``sexp`` is provided.  Heights are reduced to Re z in [-1/2, 1/2]
    with the functional equation; backward steps (Re z < -1/2) choose the
    branch of log_b consistent with the Taylor series, which limits the
    domain to Re z > -1.5 (|z| inside the disc of convergence).
    """

    def __init__(self, name: str, digits: int):
        from ._registry import ctable
        from ._bases import base_value
        t = ctable(name, digits)
        self.BASE, self.DIGITS, self.RESIDUAL = name, t.DIGITS, t.RESIDUAL
        self.K_UP, self.K_DN = t.K_UP, t.K_DN
        self.dps = digits + _GUARD
        with mp.workdps(self.dps + 10):
            self.coeffs = tuple(mp.mpc(*(mp.mpf(p) for p in s.split(","))) for s in t.COEFFS)
            self.logb = mp.log(base_value(name))
        self.canonical = True

    def _series(self, z):
        r = mp.mpc(0)
        for c in reversed(self.coeffs):
            r = r * z + c
        return r

    def sexp(self, z):
        with mp.workdps(self.dps):
            z = mp.mpc(z)
            if mp.re(z) <= -1.5:
                raise ValueError(f"sexp for complex base {self.BASE}: Re z > -1.5 only")
            if abs(mp.im(z)) > 1.3:
                raise ValueError(f"sexp for complex base {self.BASE}: |Im z| <= 1.3 only")
            k = int(mp.ceil(mp.re(z) - mp.mpf("0.5")))
            zr = z - k
            v = self._series(zr)
            for _ in range(k):
                v = mp.exp(self.logb * v)
            if k == -1:
                # one backward step: branch of log_b nearest the series value at z
                lw = mp.log(v)
                cur = self._series(z)
                kk = int(mp.nint(mp.re((cur * self.logb - lw) / (2j * mp.pi))))
                v = (lw + 2j * mp.pi * kk) / self.logb
            return v

    def slog(self, x):
        raise ValueError(f"slog is not available for complex base {self.BASE} (Kneser continuation)")


@lru_cache(maxsize=32)
def complex_kneser_engine(name: str, digits: int = 8) -> ComplexKneserEngine:
    return ComplexKneserEngine(name, digits)
