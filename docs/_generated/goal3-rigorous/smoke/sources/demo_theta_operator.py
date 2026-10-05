"""Linearisation DT of one theta-mapping pass of ``kneser.build`` (goal 3).

One pass of ``kneser.build.build`` is a map  T : c -> c'  on real Taylor
coefficient vectors of sexp at 0 (length nt, c_0 = 1):

  (A) theta_j = isuperf(P_c(z_j)) - z_j           z_j = t_j + i*delta, nf samples
  (B) fa_m    = (1/nf) sum_j theta_j e^{-2 pi i m t_j}      m = 0..n_modes-1
  (C) circle values on |z| = 1 (upper half, conjugate below):
        Im z >= delta :  v = superf(z + sum_m fa_m e^{2 pi i m (z - i delta)})
        band, Re z > 0:  v = exp(l * P_c(z-1))        (l = log base)
        band, Re z <= 0: v = log(P_c(z+1)) / l
  (D) c'_k = (1/n_circ) Re sum_j v_j e^{-i k a_j},  c'_0 := 1.

This script builds the Jacobian DT(c) *exactly* (chain rule through the
depth exp/log chains; no finite-difference noise), at the shipped table c
(the numerical fixed point), assembled as a product of the linear pieces

    DT = (1/n_circ) Re( E . [ C_theta . B . A  ;  C_band ] )     (rows for
    lower-half circle points are evaluated at the conjugate point and
    complex-conjugated, exactly as build.py does)

with A[j,k] = isuperf'(P(z_j)) z_j^k,  B = DFT/nf,
C_theta[i,m] = superf'(z_i + theta_i) e^{2 pi i m (z_i - i delta)},
C_band[i,k] = l e^{l P(z_i-1)} (z_i-1)^k  or  (z_i+1)^k / (l P(z_i+1)),
E[k,j] = e^{-i k a_j}.

It then reports: the spectrum (spectral radius rho), induced operator
norms in weighted norms (max |c_k| 2^k; sum |c_k| r^k, r in {1/2, 1, 3/2};
2-norm), the arc/band block split, the norm of (I - DT)^{-1}, the
contraction on the theta-family tangent directions P'(z) cos/sin(2 pi m z),
the size of T(c) - c, a finite-difference cross-check of a few columns, an
optional one-pass comparison with ``kneser.build`` itself, and -- with
--interval -- a candidate enclosure of the norm bounds (not an audited certificate;
see docs/theta-contraction.md §6) (mpmath interval
arithmetic for every scalar factor, Rump-style midpoint/radius products
with Higham's gamma_n rounding bound for the matrix products).

Everything numerical is meant to run on the galic box:

  PYTHONPATH=/data/kneser-verify/src KNESER_CACHE=/data/kneser-verify/.cache \\
  python3 demo_theta_operator.py --base e --digits 50 --delta 0.1 --fd 1,5,20,60 \\
      --build-check --interval --lipschitz --out /data/kneser-exp/goal3/out

Outputs a JSON file (<out>/dt_<base>_d<digits>_delta<delta>.json), the
float64 matrix (.npy) and a human-readable log on stdout.
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import math
import os
import time

import mpmath as mp
from mpmath import mp as MP     # the global context object (mp.dps = ... on the module is a no-op)
import numpy as np

import kneser.build as kb
from kneser._bases import normalize_base, coefficients


# ---------------------------------------------------------------------------
# parameters and fixed point
# ---------------------------------------------------------------------------

def make_params(base: str, digits: int, delta: float | None):
    p = kb.plan(digits, base=base)
    if delta is not None and abs(delta - p.idelta) > 1e-12:
        n_modes = math.ceil(digits * math.log(10) / (2 * math.pi * delta)) + 8
        p = dataclasses.replace(p, idelta=delta, n_modes=n_modes, nf=2 * n_modes + 20)
    return p


def fixed_point_strings(base: str, digits: int, nt: int):
    """Shipped/cached coefficient table as decimal strings (built on demand
    for bases other than e and 2)."""
    data = coefficients(base, digits)
    strs = list(data.COEFFS)[:nt] + ["0"] * max(0, nt - len(data.COEFFS))
    return strs, getattr(data, "DIGITS", digits), getattr(data, "RESIDUAL", "?")



# ---------------------------------------------------------------------------
# circular complex interval arithmetic (centre + radius): no wrapping effect
# ---------------------------------------------------------------------------

class Disc:
    """Closed disc {w : |w - c| <= r} in C.  c is an mpmath mpc, r an mpf >= 0.

    The formulas target enclosures of the images of the operand discs;
    rounding and branch audits are incomplete (see theta-contraction.md §6).
    Transcendental centers use interval point evaluations; basic arithmetic
    uses ordinary mpmath operations with heuristic inflation.
    """
    __slots__ = ("c", "r", "ctx")

    def __init__(self, ctx, c, r):
        self.ctx, self.c, self.r = ctx, c, r

    # arithmetic -----------------------------------------------------------
    def _coerce(self, other):
        if isinstance(other, Disc):
            return other
        return self.ctx.mpf(other) if not isinstance(other, complex) else self.ctx.mpc(other.real, other.imag)

    def __add__(self, o):
        o = self._coerce(o)
        c = self.c + o.c
        return Disc(self.ctx, c, self.ctx._infl(self.r + o.r, c))
    __radd__ = __add__

    def __neg__(self):
        return Disc(self.ctx, -self.c, self.r)

    def __sub__(self, o):
        return self + (-self._coerce(o))

    def __rsub__(self, o):
        return (-self) + o

    def __mul__(self, o):
        o = self._coerce(o)
        X = self.ctx
        c = self.c * o.c
        r = X._absup(self.c) * o.r + X._absup(o.c) * self.r + self.r * o.r
        return Disc(X, c, X._infl(r, c))
    __rmul__ = __mul__

    def inverse(self):
        X = self.ctx
        a_lo = X._abslow(self.c)
        if not (self.r < a_lo):
            raise ZeroDivisionError("disc contains 0")
        c = 1 / self.c
        r = self.r / (a_lo * (a_lo - self.r))
        return Disc(X, c, X._infl(r, c))

    def __truediv__(self, o):
        return self * self._coerce(o).inverse()

    def __rtruediv__(self, o):
        return self._coerce(o) * self.inverse()

    @property
    def real(self):
        return Disc(self.ctx, mp.mpc(mp.re(self.c), 0), self.r)

    @property
    def imag(self):
        return Disc(self.ctx, mp.mpc(mp.im(self.c), 0), self.r)

    def absup(self):
        return self.ctx._absup(self.c) + self.r


class DiscCtx:
    """Context object with the subset of the mpmath API used by Pass."""

    def __init__(self, dps):
        self.dps = dps
        mp.iv.dps = dps
        MP.dps = dps                                   # centres are computed at the same precision
        assert MP.prec == mp.iv.prec
        self.u = mp.mpf(2) ** (-(MP.prec) + 8)         # generous ulp multiple

    def _infl(self, r, c):
        """Inflate a radius to cover the roundings of the centre and the radius."""
        mag = abs(mp.re(c)) + abs(mp.im(c))
        return r * (1 + 16 * self.u) + mag * 16 * self.u + mp.mpf(10) ** (-(self.dps * 3))

    def _absup(self, c):
        return mp.sqrt(mp.re(c) ** 2 + mp.im(c) ** 2) * (1 + 8 * self.u)

    def _abslow(self, c):
        return mp.sqrt(mp.re(c) ** 2 + mp.im(c) ** 2) * (1 - 8 * self.u)

    def _from_box(self, box):
        """iv point-evaluation result (ivmpc/ivmpf) -> Disc(mid, half-diagonal)."""
        if hasattr(box, "real") and not isinstance(box, mp.iv.mpf):
            re, im = box.real, box.imag
        else:
            re, im = box, None
        cre = (mp.mpf(re.a) + mp.mpf(re.b)) / 2
        hre = (mp.mpf(re.b) - mp.mpf(re.a)) / 2
        if im is None:
            return Disc(self, mp.mpc(cre, 0), self._infl(hre, mp.mpc(cre, 0)))
        cim = (mp.mpf(im.a) + mp.mpf(im.b)) / 2
        him = (mp.mpf(im.b) - mp.mpf(im.a)) / 2
        c = mp.mpc(cre, cim)
        return Disc(self, c, self._infl(hre + him, c))

    def mpf(self, x):
        if isinstance(x, Disc):
            return x
        if isinstance(x, (list, tuple)):
            lo, hi = mp.mpf(x[0]), mp.mpf(x[1])
            c = mp.mpc((lo + hi) / 2, 0)
            return Disc(self, c, self._infl((hi - lo) / 2, c))
        if isinstance(x, int):
            return Disc(self, mp.mpc(x, 0), mp.mpf(0))
        v = mp.mpf(x)
        c = mp.mpc(v, 0)
        return Disc(self, c, self._infl(mp.mpf(0), c))

    def mpc(self, a, b=0):
        da, db = self.mpf(a), self.mpf(b)
        c = mp.mpc(mp.re(da.c), mp.re(db.c))
        return Disc(self, c, self._infl(da.r + db.r, c))

    @property
    def pi(self):
        return self._from_box(mp.iv.pi)

    def exp(self, d):
        d = self.mpf(d) if not isinstance(d, Disc) else d
        base = self._from_box(mp.iv.exp(mp.iv.mpc(mp.re(d.c), mp.im(d.c))))
        growth = mp.expm1(d.r) * (1 + 8 * self.u) if d.r > 0 else mp.mpf(0)
        r = base.r + base.absup() * growth
        return Disc(self, base.c, self._infl(r, base.c))

    def log(self, d):
        d = self.mpf(d) if not isinstance(d, Disc) else d
        a_lo = self._abslow(d.c)
        if not (d.r < a_lo):
            raise ValueError("disc contains 0: log undefined")
        # A zero-free disc can still cross the principal logarithm cut.
        # In that case the analytic continuation radius formula is invalid
        # for the principal branch used by the builder. Fail conservatively.
        if mp.re(d.c) <= 0 and abs(mp.im(d.c)) <= d.r:
            raise ValueError("disc intersects principal log branch cut")
        base = self._from_box(mp.iv.log(mp.iv.mpc(mp.re(d.c), mp.im(d.c))))
        extra = -mp.log1p(-d.r / a_lo) * (1 + 8 * self.u) if d.r > 0 else mp.mpf(0)
        return Disc(self, base.c, self._infl(base.r + extra, base.c))

    def conj(self, d):
        return Disc(self, mp.conj(d.c), d.r)


def is_disc_ctx(X):
    return isinstance(X, DiscCtx) or getattr(X, "is_verified_disc_context", False)

# ---------------------------------------------------------------------------
# one pass of T with all the derivative factors (mp, iv or disc context)
# ---------------------------------------------------------------------------

class Pass:
    """Evaluate one pass T(c) and the scalar factors of DT(c).

    ctx is mpmath.mp (floating) or mpmath.iv (interval).  All formulas are
    those of kneser.build.build, step by step.  Branch decisions (which
    circle point is arc / band / lower) are combinatorial and are taken once
    from the floating geometry exactly as build.py takes them.
    """

    def __init__(self, p, base: str, ctx=mp):
        self.p, self.base, self.ctx = p, base, ctx
        X = ctx
        self.I = X.mpc(0, 1)
        self.logb = X.mpf(1) if base == "e" else X.log(X.mpf(base))
        wd = (p.dps if X is mp else X.dps) + 20
        with mp.workdps(wd):
            Lf = kb._fixed_point(base=base)
            Lre, Lim = mp.nstr(mp.re(Lf), wd), mp.nstr(mp.im(Lf), wd)
        if X is mp:
            self.L = mp.mpc(Lre, Lim)
        elif is_disc_ctx(X):
            mp.iv.dps = X.dps
            box = self._enclose_fixed_point(Lre, Lim, mp.iv)
            self.L = X._from_box(box)
        else:
            self.L = self._enclose_fixed_point(Lre, Lim, X)
        self.mult = self.logb * self.L
        self.logL = X.log(self.mult)
        self.Lpow = X.exp(p.depth * self.logL)
        self.pi2 = 2 * X.pi
        self.idelta = X.mpf(p.idelta)
        self.ts = [X.mpf(j) / p.nf - X.mpf(1) / 2 for j in range(p.nf)]
        self.zs = [t + self.I * self.idelta for t in self.ts]
        self.tw_theta = [X.exp(-self.I * self.pi2 * t) for t in self.ts]
        self.circle = [X.exp(self.I * self.pi2 * X.mpf(k) / p.n_circ) for k in range(p.n_circ)]
        self.tw_circ = [self.conj(c) for c in self.circle]
        # branch decisions, as in build.py (floating, at the working precision)
        kinds, lower = [], []
        with mp.workdps(p.dps):
            for k in range(p.n_circ):
                cz = mp.exp(1j * 2 * mp.pi * mp.mpf(k) / p.n_circ)
                lo = mp.im(cz) < 0
                z = mp.conj(cz) if lo else cz
                lower.append(lo)
                if mp.im(z) >= p.idelta:
                    kinds.append("arc")
                elif mp.re(z) > 0:
                    kinds.append("band+")
                else:
                    kinds.append("band-")
        self.kinds, self.lower = kinds, lower
        self.zpt = [self.conj(c) if lower[j] else c for j, c in enumerate(self.circle)]

    def conj(self, z):
        if self.ctx is mp:
            return mp.conj(z)
        if is_disc_ctx(self.ctx):
            return self.ctx.conj(z)
        return self.ctx.mpc(z.real, -z.imag)

    def re(self, z):
        if self.ctx is mp:
            return mp.re(z)
        return z.real

    def _enclose_fixed_point(self, Lre, Lim, X):
        """Interval box proved (Krawczyk test) to contain exactly one zero of
        f(w) = E(w) - w, i.e. the fixed point L the floating code uses.

        Real 2-D Krawczyk operator (Moore/Krawczyk): with m the box centre,
        Y = J(m)^-1 (floating), [J] the interval Jacobian over the box,
        K = m - Y f(m) + (I - Y [J]) (box - m); K inside the interior of the
        box implies a unique zero in the box.  The Jacobian of w -> E(w) - w
        as a map of R^2 is [[Re g, -Im g], [Im g, Re g]] with g = l E(w) - 1;
        the two rows may use different mean-value points, which is why the
        test is done with a real 2x2 interval matrix and not with complex
        interval multiplication.
        """
        dps = X.dps
        logb = X.mpf(1) if self.base == "e" else X.log(X.mpf(self.base))
        for k in (dps - 8, dps - 16, dps // 2):
            widen = mp.mpf(10) ** (-k)
            with mp.workdps(dps + 20):
                mr, mi = mp.mpf(Lre), mp.mpf(Lim)
                lo_r, hi_r = mp.nstr(mr - widen, dps + 15), mp.nstr(mr + widen, dps + 15)
                lo_i, hi_i = mp.nstr(mi - widen, dps + 15), mp.nstr(mi + widen, dps + 15)
            box = X.mpc(X.mpf([lo_r, hi_r]), X.mpf([lo_i, hi_i]))
            m = X.mpc(X.mpf(Lre), X.mpf(Lim))
            fm = X.exp(logb * m) - m                     # f(m), interval point value
            gm = logb * X.exp(logb * m) - 1         # f'(m)
            gX = logb * X.exp(logb * box) - 1       # f'(box)
            # Y = J(m)^-1 as floating 2x2 (midpoints): J = [[a,-b],[b,a]] -> inverse = [[a,b],[-b,a]]/(a^2+b^2)
            a, b = X.mpf(gm.real.mid), X.mpf(gm.imag.mid)
            det = a * a + b * b
            Y = ((a / det, b / det), (-b / det, a / det))
            J = ((gX.real, -gX.imag), (gX.imag, gX.real))
            # I - Y J (real 2x2 interval matrix)
            IYJ = [[(1 if i == j else 0) - sum(Y[i][t] * J[t][j] for t in range(2)) for j in range(2)]
                   for i in range(2)]
            dx = (box.real - m.real, box.imag - m.imag)
            fv = (fm.real, fm.imag)
            K = [m_c - sum(Y[i][t] * fv[t] for t in range(2)) + sum(IYJ[i][t] * dx[t] for t in range(2))
                 for i, m_c in enumerate((m.real, m.imag))]
            inside = (K[0].a > box.real.a and K[0].b < box.real.b and
                      K[1].a > box.imag.a and K[1].b < box.imag.b)
            if inside:
                return box
        raise RuntimeError("Krawczyk test failed: could not verify the fixed-point enclosure")

    # --- primitives -------------------------------------------------------
    def poly(self, coeffs, z):
        r = 0
        for c in reversed(coeffs):
            r = r * z + c
        return r

    def superf_and_deriv(self, z):
        X, p = self.ctx, self.p
        e = X.exp((z - p.depth) * self.logL)
        w = self.L + e
        d = self.logL * e
        for _ in range(p.depth):
            w = X.exp(self.logb * w)
            d = d * (self.logb * w)
        return w, d

    def isuperf_and_deriv(self, w):
        X, p = self.ctx, self.p
        d = 1
        for _ in range(p.depth):
            d = d / (self.logb * w)
            w = X.log(w) / self.logb
        dw = w - self.L
        return X.log(self.Lpow * dw) / self.logL, d / (dw * self.logL)

    def absmax(self, seq):
        if self.ctx is mp:
            return max(abs(x) for x in seq)
        return max(absup(x) for x in seq)

    # --- the pass ---------------------------------------------------------
    def run(self, coeffs, log=print):
        X, p = self.ctx, self.p
        t0 = time.time()
        # (A)
        theta, dis, Pz = [], [], []
        for z in self.zs:
            w = self.poly(coeffs, z)
            th, d = self.isuperf_and_deriv(w)
            theta.append(th - z)
            dis.append(d)
            Pz.append(w)
        if X is mp:  # unwrap: locally constant, no derivative
            period = 2j * mp.pi / self.logL
            out = [theta[0]]
            for th in theta[1:]:
                k = int(mp.nint(mp.re((th - out[-1]) / period)))
                out.append(th - k * period)
            theta = out
        elif getattr(X, "is_verified_disc_context", False):
            from theta_branch import audited_unwrap
            theta, self.unwrap_audit = audited_unwrap(
                theta, X.mpc(0, 2) * X.pi / self.logL,
                shifts=getattr(self, "required_unwrap_shifts", None))
        log(f"    (A) theta samples: {time.time()-t0:.0f}s  max|theta| = "
            f"{mp.nstr(self.absmax(theta), 4)}")
        # (B)
        fa = []
        powers = [X.mpc(1)] * p.nf
        for m in range(p.n_modes):
            acc = X.mpc(0)
            for j in range(p.nf):
                acc += theta[j] * powers[j]
                powers[j] *= self.tw_theta[j]
            fa.append(acc / p.nf)
        # (C)
        n = p.n_circ
        vals, dsup, dband, zpts, thetac = [None] * n, [None] * n, [None] * n, [None] * n, [None] * n
        for j in range(n):
            kd = self.kinds[j]
            z = self.zpt[j]
            if kd == "arc":
                zs = z - self.I * self.idelta
                th, w = X.mpc(0), X.mpc(1)
                b = X.exp(self.I * self.pi2 * zs)
                for m in range(p.n_modes):
                    th += fa[m] * w
                    w *= b
                v, d = self.superf_and_deriv(z + th)
                vals[j], dsup[j], zpts[j], thetac[j] = v, d, z, th
            elif kd == "band+":
                v = X.exp(self.logb * self.poly(coeffs, z - 1))
                vals[j], dband[j], zpts[j] = v, self.logb * v, z - 1
            else:
                pw = self.poly(coeffs, z + 1)
                vals[j], dband[j], zpts[j] = X.log(pw) / self.logb, 1 / (self.logb * pw), z + 1
        for j in range(n):
            if self.lower[j]:
                vals[j] = self.conj(vals[j])
        log(f"    (C) circle values: {time.time()-t0:.0f}s  "
            f"arc points {self.kinds.count('arc')}, band "
            f"{self.kinds.count('band+') + self.kinds.count('band-')} (both half-planes)")
        # (D)
        new = []
        powers = [X.mpc(1)] * n
        for k in range(p.nt):
            acc = X.mpc(0)
            for j in range(n):
                acc += vals[j] * powers[j]
                powers[j] *= self.tw_circ[j]
            new.append(self.re(acc) / n)
        new[0] = X.mpf(1)
        log(f"    (D) Cauchy: {time.time()-t0:.0f}s")
        return dict(theta=theta, dis=dis, Pz=Pz, fa=fa, vals=vals, dsup=dsup,
                    dband=dband, zpts=zpts, thetac=thetac, new=new)


# ---------------------------------------------------------------------------
# DT as a float64 matrix (from an mp pass)
# ---------------------------------------------------------------------------

def build_dt_float(ps: Pass, run):
    p = ps.p
    nt, nf, nm, n = p.nt, p.nf, p.n_modes, p.n_circ
    A = np.empty((nf, nt), dtype=complex)
    for j, z in enumerate(ps.zs):
        zc, d = complex(z), complex(run["dis"][j])
        A[j, :] = d * (zc ** np.arange(nt))
    tw = np.array([complex(t) for t in ps.tw_theta])
    B = np.empty((nm, nf), dtype=complex)
    pw = np.ones(nf, dtype=complex)
    for m in range(nm):
        B[m, :] = pw / nf
        pw = pw * tw
    BA = B @ A
    Marc = np.zeros((n, nt), dtype=complex)
    Mband = np.zeros((n, nt), dtype=complex)
    for j in range(n):
        kd = ps.kinds[j]
        if kd == "arc":
            z = complex(ps.zpt[j]) - 1j * p.idelta
            row = complex(run["dsup"][j]) * (np.exp(2j * np.pi * z) ** np.arange(nm))
            Marc[j, :] = row @ BA
        else:
            Mband[j, :] = complex(run["dband"][j]) * (complex(run["zpts"][j]) ** np.arange(nt))
        if ps.lower[j]:          # real perturbations: conjugate the row
            Marc[j, :] = np.conj(Marc[j, :])
            Mband[j, :] = np.conj(Mband[j, :])
    E = np.exp(-2j * np.pi * np.outer(np.arange(nt), np.arange(n)) / n)
    DT_arc = np.real(E @ Marc) / n
    DT_band = np.real(E @ Mband) / n
    DT_arc[0, :] = 0
    DT_band[0, :] = 0
    return DT_arc + DT_band, DT_arc, DT_band


# ---------------------------------------------------------------------------
# norms and spectra
# ---------------------------------------------------------------------------

def weighted_norms(DT, nt):
    out = {}
    k = np.arange(nt)
    for name, w in (("inf_2^k", 2.0 ** k), ("inf_1", np.ones(nt)), ("inf_2^-k", 2.0 ** -k)):
        Bm = (w[:, None] * DT) / w[None, :]
        out[name] = float(np.max(np.sum(np.abs(Bm), axis=1)))
    for r in (0.5, 0.51, 0.55, 0.7, 1.0, 1.5):
        w = r ** k
        Bm = (w[:, None] * DT) / w[None, :]
        out[f"one_r{r}"] = float(np.max(np.sum(np.abs(Bm), axis=0)))
    for r in (0.5, 1.0):
        w = r ** k
        Bm = (w[:, None] * DT) / w[None, :]
        out[f"two_r{r}"] = float(np.linalg.norm(Bm, 2))
    return out


def spectrum(DT, nt):
    k = np.arange(nt)
    res = {}
    for r in (0.5, 1.0, 2.0):
        w = r ** k
        Bm = (w[:, None] * DT) / w[None, :]
        ev = np.linalg.eigvals(Bm)
        ev = ev[np.argsort(-np.abs(ev))]
        res[f"balance_r{r}"] = [(float(e.real), float(e.imag)) for e in ev[:12]]
    ev = np.linalg.eigvals(DT)
    ev = ev[np.argsort(-np.abs(ev))]
    res["raw"] = [(float(e.real), float(e.imag)) for e in ev[:12]]
    return float(np.abs(ev[0])), res


def resolvent_norms(DT, nt):
    R = np.linalg.inv(np.eye(nt) - DT)
    k = np.arange(nt)
    out = {}
    for r in (0.5, 1.0):
        w = r ** k
        Bm = (w[:, None] * R) / w[None, :]
        out[f"one_r{r}"] = float(np.max(np.sum(np.abs(Bm), axis=0)))
        out[f"two_r{r}"] = float(np.linalg.norm(Bm, 2))
    return out


def power_norms(DT, nt, nmax=12, r=0.5):
    k = np.arange(nt)
    w = r ** k
    Bm = (w[:, None] * DT) / w[None, :]
    P = np.eye(nt)
    out = []
    for _ in range(nmax):
        P = P @ Bm
        out.append(float(np.max(np.sum(np.abs(P), axis=0))))
    return out


def theta_tangent_ratios(DT, coeffs, nt, mmax=4):
    """Contraction on h = P'(z) cos(2 pi m z), P'(z) sin(2 pi m z)
    (tangents to the theta-family F(z + theta(z)); m <= 4 keeps the
    float64 cancellation in the trigonometric coefficients under 1e-5)."""
    c = np.array([float(x) for x in coeffs])
    dP = np.array([(k + 1) * c[k + 1] for k in range(nt - 1)] + [0.0])
    k = np.arange(nt)
    out = {}
    for m in range(mmax + 1):
        a = 2 * np.pi * m
        pw = [1.0]                                   # a^j / j! by recursion (no factorial overflow)
        for j in range(1, nt):
            pw.append(pw[-1] * a / j)
        cosc = np.array([((-1) ** (j // 2)) * pw[j] if j % 2 == 0 else 0.0 for j in range(nt)])
        sinc = np.array([((-1) ** ((j - 1) // 2)) * pw[j] if j % 2 == 1 else 0.0 for j in range(nt)])
        for nm_, trig in (("cos", cosc), ("sin", sinc)):
            if m == 0 and nm_ == "sin":
                continue
            h = np.convolve(dP, trig)[:nt]
            g = DT @ h
            for r in (0.5, 1.0):
                w = r ** k
                nh, ng = np.sum(np.abs(h) * w), np.sum(np.abs(g) * w)
                out[f"m{m}_{nm_}_r{r}"] = float(ng / nh) if nh > 0 else None
            out[f"m{m}_{nm_}_two"] = float(np.linalg.norm(g) / np.linalg.norm(h))
    return out


# ---------------------------------------------------------------------------
# semi-analytic bounds (section 4 of theta-contraction.md)
# ---------------------------------------------------------------------------

def analytic_bounds(ps: Pass, sup_dsup, sup_dis, sup_dband):
    """Upper bounds for ||DT_arc|| and ||DT_band|| in the (1, rho)-norm,
    rho = max_j |z_j| = sqrt(1/4 + delta^2), from sup-bounds of the scalar
    factors, Parseval for the DFT and the trivial bound |c'_k| <= max |v_j|.
    Rigorous when the sups are verified upper bounds."""
    p = ps.p
    rho = math.sqrt(0.25 + p.idelta ** 2)
    n = p.n_circ
    ys = [math.sin(2 * math.pi * j / n) for j in range(n)]
    ksum = 0.0
    for j in range(n):
        if ps.kinds[j] == "arc":
            y = abs(ys[j])
            x = 4 * math.pi * (y - p.idelta)
            g = p.n_modes if x <= 0 else min(p.n_modes, 1.0 / (1.0 - math.exp(-x)))
            ksum += math.sqrt(g)
    arc = sup_dsup * sup_dis * ksum / n / (1 - rho)
    nb = sum(1 for j in range(n) if ps.kinds[j] != "arc")
    band = sup_dband * nb / n / (1 - rho)
    return {"rho_norm": rho, "arc_bound": arc, "band_bound": band, "total_bound": arc + band,
            "kernel_average": ksum / n, "band_fraction": nb / n}


# ---------------------------------------------------------------------------
# verified (interval) evaluation
# ---------------------------------------------------------------------------

EPS = 2.0 ** -53


def gamma(n):
    return n * EPS / (1 - n * EPS)


def to_midrad_real(x):
    """mpmath interval (ivmpf) -> (mid, rad) floats, outward rounded."""
    a, b = float(x.a), float(x.b)          # nearest-rounded end points
    mid = 0.5 * (a + b)
    rad = (max(b - mid, mid - a) + EPS * (abs(a) + abs(b))) * (1 + 4 * EPS) + 2 * EPS * abs(mid) + 1e-300
    return mid, rad


def to_midrad_cplx(z):
    if isinstance(z, Disc):
        mr, mi = float(mp.re(z.c)), float(mp.im(z.c))
        rr = float(z.r) * (1 + 4 * EPS) + 2 * EPS * (abs(mr) + abs(mi)) + 1e-300
        return mr, mi, rr, rr
    mr, rr = to_midrad_real(z.real)
    mi, ri = to_midrad_real(z.imag)
    return mr, mi, rr, ri


def absup(x):
    """Upper bound of |x| for an iv or disc value."""
    if isinstance(x, Disc) or (hasattr(x, "c") and hasattr(x, "r")):
        return float(x.absup()) * (1 + 4 * EPS)
    return float(abs(x).b) * (1 + 4 * EPS)


def width_of(x):
    if isinstance(x, Disc):
        return float(2 * x.r)
    return float(x.delta)


def iv_matmul(Am, Ar, Bm, Br):
    """Rigorous product of real midpoint/radius matrices (Rump 1999).

    |fl(A B) - A B| <= gamma_n |A||B| elementwise (Higham, Accuracy and
    Stability, eq. 3.5) for any summation order, with or without FMA; the
    radius sums are themselves floating point and are inflated by
    (1 + 4 gamma_{n+2}) to cover their own rounding.
    """
    n = Am.shape[1]
    Cm = Am @ Bm
    absA, absB = np.abs(Am), np.abs(Bm)
    Cr = absA @ Br + Ar @ absB + Ar @ Br + gamma(n + 1) * (absA @ absB)
    Cr = Cr * (1 + 4 * gamma(n + 2)) + 1e-290
    return Cm, Cr


def cplx_block(Mre_m, Mim_m, Mre_r, Mim_r):
    """Complex mid/rad -> real block form [[Re,-Im],[Im,Re]]."""
    top = np.hstack([Mre_m, -Mim_m]); bot = np.hstack([Mim_m, Mre_m])
    topr = np.hstack([Mre_r, Mim_r]); botr = np.hstack([Mim_r, Mre_r])
    return np.vstack([top, bot]), np.vstack([topr, botr])


def block_to_cplx(Bm, Br):
    r, c = Bm.shape[0] // 2, Bm.shape[1] // 2
    return Bm[:r, :c], Bm[r:, :c], Br[:r, :c], Br[r:, :c]


def verified_dt(ps_iv: Pass, coeffs_iv, log=print):
    """Interval-verified DT as real mid/rad matrices (DT_m, DT_r)."""
    p = ps_iv.p
    X = ps_iv.ctx
    nt, nf, nm, n = p.nt, p.nf, p.n_modes, p.n_circ
    t0 = time.time()
    run = ps_iv.run(coeffs_iv, log=log)
    log(f"  [iv] pass done {time.time()-t0:.0f}s")

    def mat_cplx(rows, cols, entry):
        Mre_m = np.empty((rows, cols)); Mim_m = np.empty((rows, cols))
        Mre_r = np.empty((rows, cols)); Mim_r = np.empty((rows, cols))
        for i in range(rows):
            for j, val in enumerate(entry(i)):
                Mre_m[i, j], Mim_m[i, j], Mre_r[i, j], Mim_r[i, j] = to_midrad_cplx(val)
        return Mre_m, Mim_m, Mre_r, Mim_r

    def geometric(d, ratio, count):
        out, pw = [], X.mpc(1)
        for _ in range(count):
            out.append(d * pw); pw = pw * ratio
        return out

    A = mat_cplx(nf, nt, lambda j: geometric(run["dis"][j], ps_iv.zs[j], nt))
    # B rows: (1/nf) tw_theta[j]^m; build columnwise with running powers
    Bcols = [geometric(X.mpf(1) / nf, ps_iv.tw_theta[j], nm) for j in range(nf)]
    Bmat = mat_cplx(nm, nf, lambda m: [Bcols[j][m] for j in range(nf)])
    log(f"  [iv] A, B built {time.time()-t0:.0f}s")
    arc = [j for j in range(n) if ps_iv.kinds[j] == "arc"]
    band = [j for j in range(n) if ps_iv.kinds[j].startswith("band")]
    Cth = mat_cplx(len(arc), nm, lambda ii: geometric(
        run["dsup"][arc[ii]], X.exp(ps_iv.I * ps_iv.pi2 * (ps_iv.zpt[arc[ii]] - ps_iv.I * ps_iv.idelta)), nm))
    Cb = mat_cplx(len(band), nt, lambda ii: geometric(run["dband"][band[ii]], run["zpts"][band[ii]], nt))
    Ecols = [geometric(X.mpf(1), ps_iv.tw_circ[j], nt) for j in range(n)]
    E = mat_cplx(nt, n, lambda k: [Ecols[j][k] for j in range(n)])
    log(f"  [iv] C, E built {time.time()-t0:.0f}s")

    BA = iv_matmul(*cplx_block(*Bmat), *cplx_block(*A))
    CBA = iv_matmul(*cplx_block(*Cth), *BA)
    CBA_re_m, CBA_im_m, CBA_re_r, CBA_im_r = block_to_cplx(*CBA)
    Cb_re_m, Cb_im_m, Cb_re_r, Cb_im_r = Cb
    Z = lambda: np.zeros((n, nt))
    Are_m, Aim_m, Are_r, Aim_r = Z(), Z(), Z(), Z()
    Mre_m, Mim_m, Mre_r, Mim_r = Z(), Z(), Z(), Z()
    for ii, j in enumerate(arc):
        Are_m[j], Aim_m[j], Are_r[j], Aim_r[j] = CBA_re_m[ii], CBA_im_m[ii], CBA_re_r[ii], CBA_im_r[ii]
    for ii, j in enumerate(band):
        Mre_m[j], Mim_m[j], Mre_r[j], Mim_r[j] = Cb_re_m[ii], Cb_im_m[ii], Cb_re_r[ii], Cb_im_r[ii]
    for j in range(n):
        if ps_iv.lower[j]:       # real perturbations: conjugate the row
            Aim_m[j] = -Aim_m[j]
            Mim_m[j] = -Mim_m[j]
    Eb = cplx_block(*E)
    parts = {}
    for name, blocks in (("arc", (Are_m, Aim_m, Are_r, Aim_r)), ("band", (Mre_m, Mim_m, Mre_r, Mim_r))):
        prod = iv_matmul(*Eb, *cplx_block(*blocks))
        re_m, _, re_r, _ = block_to_cplx(*prod)
        dm = re_m / n
        dr = re_r / n * (1 + 2 * EPS) + np.abs(dm) * 2 * EPS
        dm[0, :] = 0; dr[0, :] = 0
        parts[name] = (dm, dr)
    DTm = parts["arc"][0] + parts["band"][0]
    DTr = (parts["arc"][1] + parts["band"][1]) * (1 + 2 * EPS) + np.abs(DTm) * 2 * EPS
    log(f"  [iv] DT enclosure done {time.time()-t0:.0f}s; max radius {DTr.max():.3e}, "
        f"max |entry| {np.abs(DTm).max():.3e}")
    return DTm, DTr, run


def verified_norms(DTm, DTr, nt, log=print):
    """Rigorous upper bounds: weighted 1-norms of DT, of (I-DT)^{-1}, and
    the norm of DT in the (approximate) eigenbasis."""
    k = np.arange(nt)
    res = {}
    I = np.eye(nt)
    for r in (0.5, 0.51, 1.0):
        w = r ** k                      # 0.5, 1 exact in binary; 0.51 covered by the (1+4 EPS) inflation
        Bm = (w[:, None] * DTm) / w[None, :]
        Br = ((w[:, None] * DTr) / w[None, :]) * (1 + 4 * EPS) + np.abs(Bm) * 4 * EPS
        norm1 = float(np.max(np.sum(np.abs(Bm) + Br, axis=0)) * (1 + gamma(nt + 1)))
        res[f"norm_one_r{r}"] = norm1
        # ||(I-B)^-1|| <= ||R|| / (1 - ||I - R(I-B)||), R a floating approximate inverse
        R = np.linalg.inv(I - Bm)
        RB_m, RB_r = iv_matmul(R, np.zeros_like(R), Bm, Br)
        Dm = (I - R) + RB_m
        Dr = RB_r * (1 + 2 * EPS) + np.abs(I - R) * 2 * EPS + np.abs(Dm) * 2 * EPS
        defect = float(np.max(np.sum(np.abs(Dm) + Dr, axis=0)) * (1 + gamma(nt + 2)))
        normR = float(np.max(np.sum(np.abs(R), axis=0)) * (1 + gamma(nt + 1)))
        res[f"resolvent_defect_r{r}"] = defect
        res[f"resolvent_one_r{r}"] = normR / (1 - defect) if defect < 1 else None
        # eigenbasis norm ||x||_G := ||G x||_inf:  ||B||_G <= ||G B V||_inf / (1 - ||I - G V||_inf)
        ev, V = np.linalg.eig(Bm)
        G = np.linalg.inv(V)
        z0 = np.zeros_like(V.real)
        Vb = cplx_block(V.real, V.imag, z0, z0)
        Gb = cplx_block(G.real, G.imag, z0, z0)
        Bb = cplx_block(Bm, np.zeros_like(Bm), Br, np.zeros_like(Bm))
        GBV = iv_matmul(*Gb, *iv_matmul(*Bb, *Vb))
        gre_m, gim_m, gre_r, gim_r = block_to_cplx(*GBV)
        mod = np.sqrt((np.abs(gre_m) + gre_r) ** 2 + (np.abs(gim_m) + gim_r) ** 2) * (1 + 4 * EPS)
        normGBV = float(np.max(np.sum(mod, axis=1)) * (1 + gamma(nt + 2)))
        gvre_m, gvim_m, gvre_r, gvim_r = block_to_cplx(*iv_matmul(*Gb, *Vb))
        Dm2 = gvre_m - I
        mod2 = np.sqrt((np.abs(Dm2) + gvre_r + 2 * EPS) ** 2 + (np.abs(gvim_m) + gvim_r) ** 2) * (1 + 4 * EPS)
        defect2 = float(np.max(np.sum(mod2, axis=1)) * (1 + gamma(nt + 2)))
        res[f"eig_defect_r{r}"] = defect2
        res[f"eig_norm_r{r}"] = normGBV / (1 - defect2) if defect2 < 1 else None
        res[f"eig_condV_r{r}"] = float(np.linalg.cond(V, np.inf))
        res[f"eig_rho_float_r{r}"] = float(np.max(np.abs(ev)))
        log(f"  [iv] r={r}: ||DT||_1 <= {norm1:.4e}; resolvent defect {defect:.2e} -> "
            f"||(I-DT)^-1||_1 <= {res[f'resolvent_one_r{r}']}; eig-norm <= {res[f'eig_norm_r{r}']} "
            f"(defect {defect2:.2e}, cond V {res[f'eig_condV_r{r}']:.2e})")
    return res


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def norms_of_vector(v, nt):
    v = np.array([float(x) for x in v])
    k = np.arange(nt)
    return {"one_r0.5": float(np.sum(np.abs(v) * 0.5 ** k)),
            "one_r1.0": float(np.sum(np.abs(v))),
            "inf_2^k": float(np.max(np.abs(v) * 2.0 ** k)),
            "two": float(np.linalg.norm(v)),
            "max": float(np.max(np.abs(v)))}


def certify_stored_matrix(path):
    """Exact rational certificate for the stored binary64 *linear model*.

    This does not enclose the exact Jacobian of the nonlinear pass. Fraction
    removes rounding uncertainty in the norm of the explicitly stored matrix.
    """
    from fractions import Fraction
    from hashlib import sha256
    A = np.load(path, allow_pickle=False)
    if A.ndim != 2 or A.shape[0] != A.shape[1] or not np.isfinite(A).all():
        raise ValueError("expected a finite square matrix")
    n = A.shape[0]
    cols = [sum((abs(Fraction.from_float(float(A[i, j]))) *
                 Fraction(2) ** (j - i) for i in range(n)), Fraction(0))
            for j in range(n)]
    q = max(cols)
    result = {"object": "exact rational linear map represented by stored binary64 matrix",
              "nonlinear_jacobian_certified": False,
              "sha256": sha256(open(path, "rb").read()).hexdigest(),
              "shape": list(A.shape), "norm": "weighted induced l1, weights 2^-k",
              "exact_norm_numerator": str(q.numerator),
              "exact_norm_denominator": str(q.denominator),
              "contractive": q < 1,
              "norm_less_than_0.426": q < Fraction(426, 1000),
              "norm_less_than_0.098": q < Fraction(98, 1000)}
    if q < 1:
        bound = 1 / (1 - q)
        result["resolvent_neumann_bound_numerator"] = str(bound.numerator)
        result["resolvent_neumann_bound_denominator"] = str(bound.denominator)
    return result


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--certify-stored-matrix", help="exact rational norm certificate for a saved .npy linear model only")
    ap.add_argument("--base", default="e")
    ap.add_argument("--digits", type=int, default=50)
    ap.add_argument("--delta", type=float, default=None)
    ap.add_argument("--fd", default="", help="comma list of columns to cross-check by finite differences")
    ap.add_argument("--build-check", action="store_true", help="compare T(c) with one pass of kneser.build")
    ap.add_argument("--interval", action="store_true", help="candidate interval bounds; certification audit remains incomplete")
    ap.add_argument("--lipschitz", action="store_true", help="estimate the Lipschitz constant of DT")
    ap.add_argument("--iv-dps", type=int, default=None,
                    help="interval working precision (default: dps + depth*log10(sqrt 2) + digits + 10, "
                         "which absorbs the rectangular wrapping growth of the exp/log chains and the "
                         "(w - L) cancellation)")
    ap.add_argument("--ball", type=float, default=None,
                    help="with --interval: enclose DT over the whole (1,1/2)-ball of this radius around c "
                         "(coefficient boxes |x_k - c_k| <= R 2^k), giving sup over the ball of the norm bounds")
    ap.add_argument("--disc", action="store_true",
                    help="with --interval: use circular complex intervals (centre+radius, no wrapping) instead of "
                         "mpmath.iv boxes; required for --ball, optional cross-check for the point enclosure")
    ap.add_argument("--perturb", type=float, default=1e-30, help="size of the c_1 kick for --iterate")
    ap.add_argument("--iterate", type=int, default=0,
                    help="iterate the nonlinear T this many times from c + 1e-30 e_1 and print the contraction ratios")
    ap.add_argument("--out", default=".")
    args = ap.parse_args(argv)
    if args.certify_stored_matrix:
        print(json.dumps(certify_stored_matrix(args.certify_stored_matrix), indent=2))
        return

    base = normalize_base(args.base)
    p = make_params(base, args.digits, args.delta)
    os.makedirs(args.out, exist_ok=True)
    tag = f"{base}_d{args.digits}_delta{p.idelta}"
    log = lambda *a: print(*a, flush=True)
    log(f"[theta-operator] base={base} digits={args.digits} params={p}")

    strs, tab_digits, tab_res = fixed_point_strings(base, args.digits, p.nt)
    log(f"  fixed point: table digits={tab_digits} residual={tab_res} nt={p.nt}")
    result = {"base": base, "digits": args.digits, "params": dataclasses.asdict(p),
              "table_digits": tab_digits, "table_residual": str(tab_res),
              "certificate_status": "not_certified",
              "certificate_audit": {
                  "report": "docs/theta-contraction.md#6-certification-gaps-and-reproduction",
                  "open_gaps": ["directed rounding audit", "uniform unwrap stability",
                                "finite-dimensional to Kneser consistency"],
                  "principal_log_disc_guard": True}}

    with mp.workdps(p.dps):
        coeffs = [mp.mpf(s) for s in strs]
        ps = Pass(p, base, mp)
        t0 = time.time()
        run = ps.run(coeffs, log=log)
        log(f"  pass T(c) in {time.time()-t0:.0f}s")
        diff = [run["new"][k] - coeffs[k] for k in range(p.nt)]
        result["Tc_minus_c"] = norms_of_vector(diff, p.nt)
        result["Tc_minus_c_first"] = [mp.nstr(d, 5) for d in diff[:8]]
        log(f"  ||T(c)-c||: {result['Tc_minus_c']}")
        arc = [j for j in range(p.n_circ) if ps.kinds[j] == "arc"]
        band = [j for j in range(p.n_circ) if ps.kinds[j] != "arc"]
        dsup = [abs(run["dsup"][j]) for j in arc]
        dband = [abs(run["dband"][j]) for j in band]
        dis = [abs(d) for d in run["dis"]]
        result["factors"] = {
            "sup_superf_prime_arc": float(max(dsup)), "inf_superf_prime_arc": float(min(dsup)),
            "sup_band_factor": float(max(dband)), "inf_band_factor": float(min(dband)),
            "sup_isuperf_prime_line": float(max(dis)), "inf_isuperf_prime_line": float(min(dis)),
            "max_theta_sample": float(ps.absmax(run["theta"])),
            "max_fa": float(ps.absmax(run["fa"])),
            "n_arc": len(arc), "n_band": len(band),
            "harmonic_measure_band": 2 * math.asin(p.idelta) / math.pi,
            "L_linearisation_floor": float(abs(ps.mult) ** (-p.depth)),
            "abs_multiplier": float(abs(ps.mult)),
        }
        log(f"  factors: {result['factors']}")

        DT, DT_arc, DT_band = build_dt_float(ps, run)
        rho, spec = spectrum(DT, p.nt)
        result["rho"] = rho
        result["spectrum"] = spec
        result["norms"] = weighted_norms(DT, p.nt)
        result["norms_arc_block"] = weighted_norms(DT_arc, p.nt)
        result["norms_band_block"] = weighted_norms(DT_band, p.nt)
        result["rho_arc_block"] = float(np.max(np.abs(np.linalg.eigvals(DT_arc))))
        result["rho_band_block"] = float(np.max(np.abs(np.linalg.eigvals(DT_band))))
        result["resolvent"] = resolvent_norms(DT, p.nt)
        result["power_norms_r0.5"] = power_norms(DT, p.nt)
        result["power_norms_r1.0"] = power_norms(DT, p.nt, r=1.0)
        result["theta_tangent"] = theta_tangent_ratios(DT, coeffs, p.nt)
        for frac in (0.5, 0.75):
            m = int(p.nt * frac)
            result[f"rho_trunc_{frac}"] = float(np.max(np.abs(np.linalg.eigvals(DT[:m, :m]))))
        result["law_0.017+delta/2pi"] = 0.017 + p.idelta / (2 * math.pi)
        ev, V = np.linalg.eig(DT)
        top = np.argsort(-np.abs(ev))[:3]
        result["eigvecs_top"] = [[float(x) for x in np.real(V[:, i]) / np.real(V[1, i])] for i in top]
        result["analytic_bounds_float"] = analytic_bounds(
            ps, result["factors"]["sup_superf_prime_arc"], result["factors"]["sup_isuperf_prime_line"],
            result["factors"]["sup_band_factor"])
        log(f"  analytic bounds (float sups): {result['analytic_bounds_float']}")
        log(f"  rho(DT) = {rho:.6f}   leading eigenvalues {spec['raw'][:6]}")
        log(f"  empirical law 0.017 + delta/2pi = {result['law_0.017+delta/2pi']:.4f}")
        log(f"  norms {result['norms']}")
        log(f"  arc block: rho {result['rho_arc_block']:.4f} norms {result['norms_arc_block']}")
        log(f"  band block: rho {result['rho_band_block']:.4f} norms {result['norms_band_block']}")
        log(f"  resolvent {result['resolvent']}")
        log(f"  power norms r=1/2: {['%.3e' % x for x in result['power_norms_r0.5']]}")
        log(f"  power norms r=1:   {['%.3e' % x for x in result['power_norms_r1.0']]}")
        log(f"  theta-tangent ratios: {result['theta_tangent']}")
        log(f"  rho truncated to nt/2, 3nt/4: {result['rho_trunc_0.5']:.5f} {result['rho_trunc_0.75']:.5f}")
        np.save(os.path.join(args.out, f"dt_{tag}.npy"), DT)

        if args.fd:
            cols = [int(s) for s in args.fd.split(",") if s]
            eps = mp.mpf(10) ** (-(p.dps // 3))
            fd = {}
            for kcol in cols:
                if kcol >= p.nt:
                    continue
                c2 = list(coeffs); c2[kcol] += eps
                r2 = ps.run(c2, log=lambda *a: None)
                col = np.array([float((r2["new"][k] - run["new"][k]) / eps) for k in range(p.nt)])
                ref = DT[:, kcol]
                err = float(np.max(np.abs(col - ref)) / max(np.max(np.abs(ref)), 1e-300))
                fd[kcol] = err
                log(f"  FD column {kcol}: max rel diff {err:.3e}  (|col|max {np.max(np.abs(ref)):.3e})")
            result["fd_check"] = fd

        if args.build_check and base in ("e", "2"):
            orig = kb.plan
            p1 = dataclasses.replace(p, n_loops=1)
            kb.plan = lambda *a, **k: p1
            try:
                br = kb.build(args.digits, seed="baked", verbose=False, base=base)
            finally:
                kb.plan = orig
            d = max(abs(br.coeffs[k] - run["new"][k]) for k in range(p.nt))
            result["build_check_max_diff"] = float(d)
            log(f"  kneser.build one pass vs this T(c): max |diff| = {mp.nstr(d, 4)}")

        if args.iterate:
            kk = np.arange(p.nt)
            x = list(coeffs); x[1] += mp.mpf(args.perturb)
            dists, ratios = [], []
            for it in range(args.iterate):
                r2 = ps.run(x, log=lambda *a: None)
                x = r2["new"]
                dist = float(sum(abs(x[k] - coeffs[k]) * mp.mpf(0.5) ** k for k in range(p.nt)))
                dists.append(dist)
                if len(dists) > 1 and dists[-2] > 0:
                    ratios.append(dists[-1] / dists[-2])
                log(f"  iterate {it+1}: ||T^n x - c||_(1,1/2) = {dist:.3e}" +
                    (f"  ratio {ratios[-1]:.5f}" if ratios else ""))
            result["iterate"] = {"dists": dists, "ratios": ratios, "rho": rho}

        if args.lipschitz:
            rng = np.random.default_rng(1)
            kk = np.arange(p.nt)
            v = rng.standard_normal(p.nt) * (0.5 ** kk)
            v /= np.sum(np.abs(v) * 0.5 ** kk)
            eta = 1e-4
            c2 = [coeffs[k] + mp.mpf(eta * v[k]) for k in range(p.nt)]
            r2 = ps.run(c2, log=lambda *a: None)
            DT2, _, _ = build_dt_float(ps, r2)
            w = 0.5 ** kk
            Bd = (w[:, None] * (DT2 - DT)) / w[None, :]
            lip = float(np.max(np.sum(np.abs(Bd), axis=0)) / eta)
            result["lipschitz_estimate_r0.5"] = lip
            w = np.ones(p.nt)
            lip1 = float(np.max(np.sum(np.abs(DT2 - DT), axis=0)) / (eta * np.sum(np.abs(v))))
            result["lipschitz_estimate_r1.0"] = lip1
            log(f"  Lipschitz estimate of DT (one-norms, eta={eta}): r=1/2 {lip:.3e}, r=1 {lip1:.3e}")

    if args.interval:
        if args.disc:
            dps_iv = args.iv_dps or (p.dps + args.digits + 20)
            iv = DiscCtx(dps_iv)
        else:
            iv = mp.iv
            iv.dps = args.iv_dps or (p.dps + math.ceil(p.depth * math.log10(math.sqrt(2))) + args.digits + 10)
        log(f"  [iv] interval precision dps = {iv.dps}  arithmetic = {'disc' if args.disc else 'iv boxes'}")
        result["iv_dps"] = iv.dps
        result["iv_arith"] = "disc" if args.disc else "box"
        if args.ball:
            if not args.disc:
                raise SystemExit("--ball needs --disc (box arithmetic explodes through the exp/log chains)")
            with mp.workdps(iv.dps + 10):
                coeffs_iv = []
                for k, s_ in enumerate(strs):
                    ck, hw = mp.mpf(s_), mp.mpf(args.ball) * mp.mpf(2) ** k
                    coeffs_iv.append(iv.mpf([mp.nstr(ck - hw, iv.dps + 5), mp.nstr(ck + hw, iv.dps + 5)]))
            log(f"  [iv] coefficient boxes for the (1,1/2)-ball of radius {args.ball}")
            result["interval_ball_radius"] = args.ball
        else:
            coeffs_iv = [iv.mpf(s) for s in strs]        # exact decimal strings -> tight boxes
        ps_iv = Pass(p, base, iv)
        DTm, DTr, run_iv = verified_dt(ps_iv, coeffs_iv, log=log)
        result["interval"] = {"max_radius": float(DTr.max()),
                              "max_mid_vs_float": float(np.max(np.abs(DTm - DT)))}
        sup_dsup = max(absup(run_iv["dsup"][j]) for j in range(p.n_circ) if ps_iv.kinds[j] == "arc")
        sup_dband = max(absup(run_iv["dband"][j]) for j in range(p.n_circ) if ps_iv.kinds[j] != "arc")
        sup_dis = max(absup(d) for d in run_iv["dis"])
        result["interval"]["verified_sups"] = {"superf_prime_arc": sup_dsup, "band_factor": sup_dband,
                                               "isuperf_prime_line": sup_dis}
        result["interval"]["analytic_bounds_verified"] = analytic_bounds(ps_iv, sup_dsup, sup_dis, sup_dband)
        log(f"  [iv] verified sups {result['interval']['verified_sups']}")
        log(f"  [iv] analytic bounds (verified sups): {result['interval']['analytic_bounds_verified']}")
        result["interval"].update(verified_norms(DTm, DTr, p.nt, log=log))
        if not args.ball:
            d_up = 0.0
            for k in range(p.nt):
                dk = run_iv["new"][k] - coeffs_iv[k]
                d_up += absup(dk) * 0.5 ** k
            result["interval"]["Tc_minus_c_one_r0.5_upper"] = d_up * (1 + 1e-12)
            log(f"  [iv] ||T(c)-c||_(1,1/2) <= {d_up:.3e}")
            result["interval"]["Tc_minus_c_widths_first"] = [width_of(run_iv["new"][k] - coeffs_iv[k]) for k in range(6)]

    with open(os.path.join(args.out, f"dt_{tag}.json"), "w") as fh:
        json.dump(result, fh, indent=1, default=str)
    log(f"[theta-operator] wrote {os.path.join(args.out, f'dt_{tag}.json')}")


if __name__ == "__main__":
    main()
