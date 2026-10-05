"""Kneser-type tetration for complex bases: the two-fixed-point construction.

For a real base b > eta Kneser's sexp is characterised (Trappmann &
Kouznetsov 2010) by: F(z+1) = b**F(z), F(0) = 1, F holomorphic in the
slit plane, F(z) -> L as Im z -> +inf and F(z) -> conj(L) as Im z -> -inf,
with L the upper fixed point of b**w.  The builder in ``kneser.build``
realises this with one theta-mapping in the upper half-plane and conjugate
symmetry below.

For a complex base the two limits are two different fixed points L_up and
L_dn, no longer conjugate, and this module applies a theta-mapping to each
half-plane separately:

    upper:  sexp(z) ~ superf_up(z + theta_up(z)),  theta_up 1-periodic, decaying upward
    lower:  sexp(z) ~ superf_dn(z + theta_dn(z)),  theta_dn 1-periodic, decaying downward
    band:   functional equation from the current Taylor series

and recovers the Taylor coefficients at 0 (now complex) by a Cauchy integral
over the unit circle.  The fixed points are chosen as the ones of smallest
|lambda| with arg(lambda) > 0 (upper) and arg(lambda) < 0 (lower), which
for real b > eta is exactly the conjugate pair (k = -1, 0 of Lambert W) and
continues analytically off the real axis (k = 0, 1 just above it).  By
default both fixed points must be repelling (|lambda| > 1): this covers
every base outside the Shell-Thron region, including negative reals.  Real
bases in (0, 1) can be forced onto their complex pair (k = -1, 1), which
yields a real-analytic, oscillating tower.

With ``allow_attracting=True`` one side may be attracting (|lambda| < 1,
inside the Shell-Thron region; the neutral band |lambda| within 0.02 of 1
is refused).  The characterisation is unchanged -- with arg lambda_up > 0
the regular superfunction at L_up still tends to L_up as Im z -> +inf --
only the evaluation differs: superf by inverse iteration
E^{-n}(L + u(lambda^{z+n})) with the branch of log_b continued along the
circle, isuperf by branch-free forward iteration, u the inverse Schroeder
series.  This is the continuation of Kneser's tetration in the base
through the Shell-Thron boundary (Paulsen 2019); see
docs/paulsen-continuation-zh.md for what it converges to on (1, eta).

Everything is guarded against the blow-up that a poor seed can cause in
the forward iteration of the superfunction (a single unguarded build ate
60 GB); on overflow the build raises instead of continuing.
"""

from __future__ import annotations

import math
import time
from dataclasses import dataclass, field

import mpmath as mp

from ._bases import normalize_base, base_value

__all__ = ["choose_fixed_points", "build_complex", "CBuildResult"]

_BIG = mp.mpf("1e100")
_U_TERMS = 64            # inverse Schroeder series length (attracting side)
_SMAX = mp.mpf("0.05")   # |s| at which that series is summed
_NEUTRAL_BAND = 0.02     # refuse |lambda| this close to 1


def _fixed_point(logb, k):
    return -mp.lambertw(-logb, k) / logb


def choose_fixed_points(base, *, k_up=None, k_dn=None, dps=30):
    """(k_up, L_up, lambda_up, k_dn, L_dn, lambda_dn) for the given base.

    Default: among Lambert-W branches -6..6, the fixed point of smallest
    |lambda| with arg lambda > 0 (upper) and with arg lambda < 0 (lower).
    A real fixed point (arg lambda in {0, pi}) is never chosen by default.
    """
    name = normalize_base(base)
    with mp.workdps(dps):
        b = base_value(name)
        logb = mp.log(b)
        cands = []
        for k in range(-6, 7):
            L = _fixed_point(logb, k)
            lam = L * logb
            cands.append((k, L, lam))

        def pick(sign):
            best = None
            for k, L, lam in cands:
                a = mp.arg(lam)
                if sign * a > 1e-12 and abs(abs(a) - mp.pi) > 1e-12:
                    if best is None or abs(lam) < abs(best[2]):
                        best = (k, L, lam)
            return best

        if k_up is None:
            up = pick(+1)
        else:
            L = _fixed_point(logb, k_up)
            up = (k_up, L, L * logb)
        if k_dn is None:
            dn = pick(-1)
        else:
            L = _fixed_point(logb, k_dn)
            dn = (k_dn, L, L * logb)
        if up is None or dn is None:
            raise ValueError(f"base {name}: no suitable fixed point pair")
        return (*up, *dn)


@dataclass
class CBuildResult:
    base: str
    digits: int
    k_up: int
    k_dn: int
    coeffs: list                      # complex mpc Taylor coefficients at 0
    residuals: list = field(default_factory=list)
    seconds: float = 0.0
    params: dict = field(default_factory=dict)

    @property
    def residual(self):
        return self.residuals[-1] if self.residuals else None


def _schroeder_inverse(L, lam, logb, K=_U_TERMS):
    """c_k of u(s) = sum c_k s^k with E(L + u(s)) = L + u(lam s) (E = exp(logb * .))."""
    c = [mp.mpc(0), mp.mpc(1)]
    g = [mp.mpc(1), logb]
    for k in range(2, K + 1):
        P = sum(j * logb * c[j] * g[k - j] for j in range(1, k)) / k
        ck = L * P / (mp.power(lam, k) - lam)
        c.append(ck)
        g.append(logb * ck + P)
    return c


def build_complex(digits: int = 10, *, base, k_up=None, k_dn=None, idelta=None,
                  idelta_dn=None, n_loops=None, verbose=True, seed=None,
                  allow_attracting=False) -> CBuildResult:
    """Two-fixed-point Kneser build; see the module docstring.

    ``allow_attracting=True`` admits an attracting fixed point on either side
    (|lambda| < 1, inside the Shell-Thron region).  With arg lambda_up > 0 the
    regular superfunction at L_up still tends to L_up as Im z -> +inf, so the
    characterisation is unchanged; only the evaluation differs: superf by
    inverse iteration E^{-n}(L + u(lambda^{z+n})) with the branch of log_b
    continued analytically along the circle (nearest to the previous sample's
    chain, first sample nearest to L), isuperf by branch-free forward
    iteration.  ``u`` is the inverse Schroeder series.  Bases with |lambda|
    within ``_NEUTRAL_BAND`` of 1 are refused.
    """
    name = normalize_base(base)
    bv = complex(base_value(name))
    if idelta is None:
        # left half of the base plane: the upper theta line must sit at 0.3
        # (at 0.05/0.1 it encircles a branch point of the Abel function and
        # theta is no longer 1-periodic), the lower one at 0.1
        idelta = 0.3 if bv.real < 0 else 0.1
    if idelta_dn is None:
        idelta_dn = 0.1 if bv.real < 0 else idelta
    if n_loops is None and bv.real < 0:
        n_loops = 160
    log = (lambda *a, **k: print(*a, **k, flush=True)) if verbose else (lambda *a, **k: None)
    if digits < 6:
        digits = 6
    ku, Lu, lamu, kd, Ld, lamd = choose_fixed_points(name, k_up=k_up, k_dn=k_dn)
    ru, rd = float(abs(lamu)), float(abs(lamd))
    if not allow_attracting and (ru <= 1.0 or rd <= 1.0):
        raise ValueError(f"base {name}: fixed points must both be repelling for the theta "
                         f"construction (|lambda_up| = {ru:.4f}, |lambda_dn| = {rd:.4f}); "
                         "inside the Shell-Thron region use the regular solution "
                         "(or allow_attracting=True for the Kneser continuation)")
    for r, side in ((ru, "up"), (rd, "dn")):
        if abs(r - 1.0) < _NEUTRAL_BAND:
            raise ValueError(f"base {name}: |lambda_{side}| = {r:.4f} is within {_NEUTRAL_BAND} of 1 "
                             "(Shell-Thron boundary): no hyperbolic superfunction")
    attr_u, attr_d = ru < 1.0, rd < 1.0
    # repelling: forward depth for `digits` digits; attracting: set inside make()
    depth_u = None if attr_u else math.ceil(digits * math.log(10) / math.log(ru)) + 16
    depth_d = None if attr_d else math.ceil(digits * math.log(10) / math.log(rd)) + 16
    dps = 2 * digits + 20
    nt = max(48, math.ceil(4.0 * digits))
    if idelta_dn is None:
        idelta_dn = idelta
    n_modes = math.ceil(digits * math.log(10) / (2 * math.pi * min(idelta, idelta_dn))) + 8
    nf = 2 * n_modes + 20
    n_circ = max(4 * nt, 256)
    if n_loops is None:
        n_loops = 3 * digits + 24
    log(f"[kneser._cbuild] base={name} digits={digits} up: k={ku} L={mp.nstr(Lu, 6)} |lam|={ru:.4f} "
        f"depth={depth_u}; dn: k={kd} L={mp.nstr(Ld, 6)} |lam|={rd:.4f} depth={depth_d}; "
        f"dps={dps} nt={nt} modes={n_modes} loops<={n_loops}")
    t0 = time.time()
    with mp.workdps(dps):
        b = base_value(name)
        logb = mp.log(b)
        two_pi_i = 2j * mp.pi

        def E(w):
            if abs(w) > _BIG:
                raise OverflowError("superfunction overflow")
            return mp.exp(logb * w)

        def logb_near(w, target):
            """The branch of log_b(w) nearest to ``target`` (in the imaginary direction)."""
            if w == 0:
                raise ValueError("inverse iteration hit 0")
            lw = mp.log(w)
            k = int(mp.nint(mp.re((target * logb - lw) / two_pi_i)))
            return (lw + two_pi_i * k) / logb

        def make_attracting(L, lam):
            """superf / isuperf for an attracting fixed point (|lam| < 1).

            superf(z) = E^{-n}(L + u(lam^{z+n})): the n backward steps use the
            branch of log_b nearest to the previous sample's chain value at
            the same step (analytic continuation along the circle); the first
            sample takes the branch nearest to L.  isuperf(w): forward
            iteration until |w - L| <= smax/4 (branch-free), then invert the
            series; the branch of log s is left to ``unwrap`` (period
            2 pi i / log lam).  Returns (superf, theta_line, unwrap, depth).
            """
            logL = mp.log(lam)
            period = two_pi_i / logL
            cu = _schroeder_inverse(L, lam, logb)
            ratio = max(abs(cu[k + 1] / cu[k]) for k in range(_U_TERMS // 2, _U_TERMS) if cu[k] != 0)
            smax = min(_SMAX, 1 / (8 * ratio))
            # |lam^{z+depth}| <= smax for Re z >= -4 and Im z >= 0 (arg lam > 0)
            depth = math.ceil(float(mp.log(smax) / mp.log(abs(lam)))) + 8

            def u(s):
                r = mp.mpc(0)
                for ck in reversed(cu[1:]):
                    r = r * s + ck
                return r * s

            def du(s):
                r = mp.mpc(0)
                for k in range(_U_TERMS, 0, -1):
                    r = r * s + k * cu[k]
                return r

            def inv_u(w):
                s = w
                for _ in range(100):
                    step = (u(s) - w) / du(s)
                    s -= step
                    if abs(step) < mp.mpf(10) ** (-(dps + 2)) * max(1, abs(s)):
                        break
                return s

            def superf(z, prev=None):
                s = mp.exp((z + depth) * logL)
                extra = 0
                while abs(s) > smax:          # further right than planned: more steps near L
                    s *= lam
                    extra += 1
                    if extra > 100000:
                        raise ValueError("superf: point too far from the fixed point")
                w = L + u(s)
                for _ in range(extra):
                    w = logb_near(w, L)
                chain = []
                for i in range(depth):
                    w = logb_near(w, prev[i] if prev is not None else L)
                    chain.append(w)
                return w, chain

            def isuperf(w, prev=None):
                m = 0
                while abs(w - L) > smax / 4:
                    w = E(w)
                    m += 1
                    if m > 100000:
                        raise ValueError("isuperf: forward orbit does not converge to the fixed point")
                s = inv_u(w - L)
                return mp.log(s) / logL - m, None

            def theta_line(points):
                out, prev = [], None
                for z in points:
                    val, prev = isuperf(series(z), prev)
                    out.append(val - z)
                return out

            def unwrap(theta):
                out = [theta[0]]
                for th in theta[1:]:
                    k = int(mp.nint(mp.re((th - out[-1]) / period)))
                    out.append(th - k * period)
                # the Abel value is defined modulo the period and superf is
                # periodic, so theta's constant mode is only defined mod P:
                # take the representative of smallest modulus
                mean = sum(out) / len(out)
                k = int(mp.nint(mp.re(mean * mp.conj(period)) / abs(period) ** 2))
                if k:
                    out = [th - k * period for th in out]
                return out

            return superf, theta_line, unwrap, depth

        def make(L, lam, depth):
            logL = mp.log(lam)
            Lpow = mp.power(lam, depth)
            period = two_pi_i / logL
            def superf(z, prev=None):
                w = L + mp.exp((z - depth) * logL)
                for _ in range(depth):
                    w = E(w)
                return w, None

            def isuperf(w, prev=None):
                """Inverse iteration toward L; returns (Abel value, chain).

                The inverse of E is multivalued and its Abel function has
                infinitely many sheets that are NOT related by the period, so
                the branch must be continued analytically along the sample
                line: at each step take the branch whose value is nearest to
                the previous sample's chain value at the same step (``prev``).
                Without ``prev`` (first sample) take the branch nearest to L.
                Choosing "nearest to L" at every sample instead jumps sheets
                mid-line (base -1+i: theta jumps by 2.0 + 0.9i, not a period).
                """
                chain = []
                for i in range(depth):
                    if w == 0:
                        raise ValueError("isuperf hit 0")
                    lw = mp.log(w)
                    target = prev[i] if prev is not None else L
                    k = int(mp.nint(mp.re((target * logb - lw) / two_pi_i)))
                    w = (lw + two_pi_i * k) / logb
                    chain.append(w)
                if abs(w - L) > mp.mpf("1e-3"):
                    raise ValueError("isuperf chain did not converge to the fixed point")
                return mp.log(Lpow * (w - L)) / logL, chain

            def theta_line(points):
                out, prev = [], None
                for z in points:
                    val, prev = isuperf(series(z), prev)
                    out.append(val - z)
                return out

            def unwrap(theta):
                out = [theta[0]]
                for th in theta[1:]:
                    k = int(mp.nint(mp.re((th - out[-1]) / period)))
                    out.append(th - k * period)
                return out

            return superf, theta_line, unwrap

        if attr_u:
            superf_u, theta_u_line, unwrap_u, depth_u = make_attracting(Lu, lamu)
        else:
            superf_u, theta_u_line, unwrap_u = make(Lu, lamu, depth_u)
        if attr_d:
            superf_d, theta_d_line, unwrap_d, depth_d = make_attracting(Ld, lamd)
        else:
            superf_d, theta_d_line, unwrap_d = make(Ld, lamd, depth_d)
        if attr_u or attr_d:
            log(f"  attracting side(s): {'up ' if attr_u else ''}{'dn' if attr_d else ''} "
                f"-> inverse-iteration superfunction, depth up={depth_u} dn={depth_d}")

        if seed is None:
            coeffs = [mp.mpc(0)] * nt
            coeffs[0] = mp.mpc(1)
            coeffs[1] = mp.mpc(1)
        else:
            coeffs = [mp.mpc(c) for c in seed][:nt] + [mp.mpc(0)] * max(0, nt - len(seed))

        def series(z):
            r = mp.mpc(0)
            for c in reversed(coeffs):
                r = r * z + c
            return r

        def residual():
            return abs(series(mp.mpf("0.5")) - E(series(mp.mpf("-0.5"))))

        delta = mp.mpf(idelta)
        delta_d = mp.mpf(idelta_dn)
        ts = [mp.mpf(j) / nf - mp.mpf("0.5") for j in range(nf)]
        tw_pos = [mp.exp(-two_pi_i * t) for t in ts]     # for positive modes
        tw_neg = [mp.exp(two_pi_i * t) for t in ts]      # for negative modes
        circle = [mp.exp(two_pi_i * mp.mpf(k) / n_circ) for k in range(n_circ)]
        tw_circ = [mp.conj(c) for c in circle]

        res = residual()
        result = CBuildResult(name, digits, ku, kd, list(coeffs), [res],
                              params=dict(depth_u=depth_u, depth_d=depth_d, dps=dps, nt=nt,
                                          n_modes=n_modes, nf=nf, n_circ=n_circ, idelta=idelta,
                                          idelta_dn=idelta_dn, attracting_up=attr_u,
                                          attracting_dn=attr_d, L_up=Lu, L_dn=Ld,
                                          lambda_up=lamu, lambda_dn=lamd))
        log(f"  seed residual = {mp.nstr(res, 4)}")
        target = mp.mpf(10) ** (-(digits + 1))

        def fourier(theta, tw):
            fa = [mp.mpc(0)] * n_modes
            powers = [mp.mpc(1)] * nf
            for m in range(n_modes):
                acc = mp.mpc(0)
                for j in range(nf):
                    acc += theta[j] * powers[j]
                    powers[j] *= tw[j]
                fa[m] = acc / nf
            return fa

        def eval_modes(fa, w, cap=3):
            th, p = mp.mpc(0), mp.mpc(1)
            for m in range(n_modes):
                th += fa[m] * p
                p *= w
            # damp absurd corrections (early passes from a crude seed) so the
            # forward superfunction is never asked for a point far to the right;
            # not needed (and harmful: theta may legitimately be ~|P|/2) on an
            # attracting side, whose superfunction is evaluated by inverse iteration
            a = abs(th)
            if cap is not None and a > cap:
                th = th * (cap / a)
            return th

        def cap_for(theta, attracting):
            # the cap must stay above the genuine |theta| (the lower theta grows
            # to ~3.2 when L_dn moves to the real axis near eta): 1.5x the
            # sampled maximum, at least 3
            if attracting:
                return None
            return max(3, 1.5 * float(max(abs(t) for t in theta)))

        try:
            for loop in range(n_loops):
                theta_u = unwrap_u(theta_u_line([t + 1j * delta for t in ts]))
                theta_d = unwrap_d(theta_d_line([t - 1j * delta_d for t in ts]))
                if verbose and loop < 3:
                    ju = max(abs(theta_u[j + 1] - theta_u[j]) for j in range(nf - 1))
                    jd = max(abs(theta_d[j + 1] - theta_d[j]) for j in range(nf - 1))
                    log(f"  loop {loop}: max theta jump up {mp.nstr(ju, 3)} dn {mp.nstr(jd, 3)}; "
                        f"|theta| up {mp.nstr(max(abs(t) for t in theta_u), 3)} dn {mp.nstr(max(abs(t) for t in theta_d), 3)}; "
                        f"wrap up {mp.nstr(theta_u[0] - theta_u[-1], 3)} dn {mp.nstr(theta_d[0] - theta_d[-1], 3)}")
                fa_u = fourier(theta_u, tw_pos)      # theta_u(z) = sum fa_u[m] e^{+2 pi i m z}
                fa_d = fourier(theta_d, tw_neg)      # theta_d(z) = sum fa_d[m] e^{-2 pi i m z}
                cap_u, cap_d = cap_for(theta_u, attr_u), cap_for(theta_d, attr_d)
                # diagnostics: the theta modes of this pass (a_m, m >= 1, vanish
                # iff sexp is the regular superfunction shifted by a constant)
                result.params["fa_up"], result.params["fa_dn"] = list(fa_u), list(fa_d)
                vals = []
                chain_u = chain_d = None      # branch continuation along the circle
                for cz in circle:
                    y = mp.im(cz)
                    if y >= delta:
                        th = eval_modes(fa_u, mp.exp(two_pi_i * (cz - 1j * delta)), cap_u)
                        v, chain_u = superf_u(cz + th, chain_u)
                    elif y <= -delta_d:
                        th = eval_modes(fa_d, mp.exp(-two_pi_i * (cz + 1j * delta_d)), cap_d)
                        v, chain_d = superf_d(cz + th, chain_d)
                    else:
                        if mp.re(cz) > 0:
                            v = E(series(cz - 1))
                        else:
                            # backward step of the tower: choose the branch of
                            # log_b consistent with the current series value
                            w = series(cz + 1)
                            lw = mp.log(w)
                            cur = series(cz)
                            k = int(mp.nint(mp.re((cur * logb - lw) / two_pi_i)))
                            v = (lw + two_pi_i * k) / logb
                    vals.append(v)
                new = []
                powers = [mp.mpc(1)] * n_circ
                for k in range(nt):
                    acc = mp.mpc(0)
                    for j in range(n_circ):
                        acc += vals[j] * powers[j]
                        powers[j] *= tw_circ[j]
                    new.append(acc / n_circ)
                new[0] = mp.mpc(1)
                coeffs = new
                res = residual()
                result.residuals.append(res)
                if verbose and (loop % 5 == 0 or res < target):
                    log(f"  loop {loop:3d}: residual = {mp.nstr(res, 4)}  [{time.time()-t0:.0f}s]")
                if res < target:
                    break
                if loop >= 6 and res > 10 * min(result.residuals):
                    raise ValueError("theta iteration diverging")
        except (OverflowError, ValueError) as exc:
            raise ValueError(f"kneser._cbuild: build failed for base {name}: {exc}") from exc
        result.coeffs = coeffs
        result.seconds = time.time() - t0
    log(f"[kneser._cbuild] done: residual = {mp.nstr(result.residual, 4)} in {result.seconds:.0f}s")
    return result
