"""Goal 2 (docs/world-class-plan-zh.md): is the two-fixed-point Kneser tetration
K(b; z) analytic in the complex base b inside the Shell-Thron region, and is the
real segment (1, eta) a natural boundary?  Numerical Cauchy tests in the base.

Run on galic only (never on the Mac):

  PYTHONPATH=/data/kneser-verify/src KNESER_CACHE=/data/kneser-verify/.cache \\
  timeout 36000 python3 demo_base_cauchy.py <mode> [options]

Modes
  circle    M2.1 / M2.2: build K(b_j) on the circle |b - b0| = r (N points, chained
            from neighbours; the antipode is built from both directions -> monodromy /
            sheet check), the centre and one interior point b1; then Cauchy sums.
  boundary  M2.4: same on a circle centred ON the Shell-Thron boundary (|lambda_up| = 1),
            with the phase of the samples chosen to avoid the refused neutral band.
  decay     M2.3: vertical ladder Im b -> 0 at fixed Re b; D = K - R at every rung.
  fit       M2.3: fit ln|D| = A - c / y^p over the ladders (and over circles).
  analyse   recompute the Cauchy sums / Taylor coefficients of a finished circle.

Every build uses kneser._cbuild.build_complex(digits, allow_attracting=True) seeded
with the Taylor coefficients of a neighbouring base (keeps the sheet).  R(b; z) is
the regular (Schroeder) solution kneser._general.GeneralRegularEngine, analytic in b
inside the region (control).  Results: <out>/<tag>/*.json.
"""

from __future__ import annotations

import argparse
import contextlib
import io
import json
import math
import os
import re
import sys
import time
from multiprocessing import Pool

import mpmath as mp

from kneser._bases import base_value
from kneser._cbuild import build_complex, choose_fixed_points
from kneser._general import GeneralRegularEngine

ZS = ["0.5", "-0.5", "0.25", "0.5-0.5j"]
FUNCTIONALS = ZS + ["c1", "c2"]          # values at z, plus Taylor coefficients at z = 0
DPS = 40
NEUTRAL = 0.02                            # _cbuild refuses | |lambda| - 1 | < 0.02
IDELTA = None                             # theta sample-line height passed to build_complex (None = default 0.1)
KUP = KDN = None                          # forced Lambert-W branches (real bases: k_up=0 alpha, k_dn=-1 beta)


# ----------------------------------------------------------------------------- helpers

def _log(*a):
    print(*a, flush=True)


def bname(b) -> str:
    b = complex(b)
    return f"{b.real:.17g}{b.imag:+.17g}j"


def nd():
    """significant digits used when writing values out.

    This used to be a hard-coded 24 everywhere.  For the K values and for D
    that is harmless (they are stored as numbers in their own right), but the
    Taylor coefficients of K are O(1), so rounding them to 24 digits put an
    absolute floor of about 1e-25 on anything recomputed from them downstream
    -- in particular on the Fourier mode c_2 of P, which is smaller than that
    from b = 1.25 on.  Two builds at 32 and 44 digits then returned bitwise the
    same wrong c_2, which is how the truncation was found."""
    return max(24, DPS - 4)


def cstr(v):
    v = mp.mpc(v)
    return [mp.nstr(mp.re(v), nd()), mp.nstr(mp.im(v), nd())]


def cval(s):
    return mp.mpc(mp.mpf(s[0]), mp.mpf(s[1]))


def series_at(coeffs, z):
    r = mp.mpc(0)
    for c in reversed(coeffs):
        r = r * z + c
    return r


def sexp_from_coeffs(coeffs, logb, z):
    z = mp.mpc(z)
    k = max(0, int(mp.ceil(mp.re(z) - mp.mpf("0.5"))))
    v = series_at(coeffs, z - k)
    for _ in range(k):
        v = mp.exp(logb * v)
    return v


def lam_abs(b):
    with mp.workdps(20):
        _, _, lu, _, _, ld = choose_fixed_points(bname(b))
        return float(abs(lu)), float(abs(ld))


def diagnostic_noise(d):
    """Heuristic screening only: a functional residual is NOT a value-error bound."""
    return max(10 ** (-(d["digits"] + 0.5)),
               abs(float(d.get("residual", 0))),
               abs(float(d.get("residual_check", 0))))


def fit_eligible(d, key):
    return (d.get("R_c0_minus_1", 1) < 1e-10
            and d["absD"][key] > 100 * diagnostic_noise(d)
            and d["b"][1] > 0)


def load_seed(path):
    with open(path) as fh:
        d = json.load(fh)
    with mp.workdps(DPS):
        return [mp.mpc(*(mp.mpf(p) for p in s.split(","))) for s in d["coeffs"]]


def regular_values(name, digits=20):
    """R(b; z) for z in ZS and its Taylor c0..c2 at 0 (Cauchy integral on |z| = 1/2, 64 pts).
    c0 must be 1: if not, the engine's branch handling is inconsistent inside |z| < 1/2
    (happens next to the Shell-Thron boundary) and R is not usable there."""
    with mp.workdps(digits + 12):
        g = GeneralRegularEngine(name, digits)
        vals = {z: g.sexp(mp.mpc(complex(z))) for z in ZS}
        npts, rad = 64, mp.mpf("0.5")
        pts = [g.sexp(rad * mp.exp(2j * mp.pi * j / npts)) for j in range(npts)]
        tc = []
        for k in range(3):
            acc = mp.mpc(0)
            for j in range(npts):
                acc += pts[j] * mp.exp(-2j * mp.pi * j * k / npts)
            tc.append(acc / npts / rad ** k)
        vals["c1"], vals["c2"] = tc[1], tc[2]
        return vals, g.RESIDUAL, tc[0]


_WRAP = re.compile(r"wrap up (\([^)]*\)|\S+) dn (\([^)]*\)|\S+)")
_JUMP = re.compile(r"max theta jump up (\S+) dn (\S+);")


def _cplx(s):
    return complex(s.replace(" ", ""))


def build_point(b, seed, digits, n_loops=60, want_regular=True):
    """Build K at base b (seeded), one post-check pass for the wrap diagnostic and the
    theta modes of the converged solution, values of K, R, D.  Returns a JSON-able dict."""
    name = bname(b)
    t0 = time.time()
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        r = build_complex(digits, base=name, seed=seed, verbose=True, allow_attracting=True,
                          n_loops=n_loops, idelta=IDELTA, k_up=KUP, k_dn=KDN)
        chk = build_complex(digits, base=name, seed=r.coeffs, verbose=True, allow_attracting=True,
                            n_loops=1, idelta=IDELTA, k_up=KUP, k_dn=KDN)
    log = buf.getvalue()
    wraps = _WRAP.findall(log)
    jumps = _JUMP.findall(log)
    with mp.workdps(DPS):
        logb = mp.log(base_value(name))
        K = {z: sexp_from_coeffs(r.coeffs, logb, mp.mpc(complex(z))) for z in ZS}
        K["c1"], K["c2"] = r.coeffs[1], r.coeffs[2]
        fu, fd = chk.params["fa_up"], chk.params["fa_dn"]
        out = {
            "base": name, "b": [float(complex(b).real), float(complex(b).imag)], "digits": digits, "idelta": IDELTA,
            "residual": mp.nstr(r.residual, 4), "loops": len(r.residuals) - 1,
            "residual_check": mp.nstr(chk.residual, 4),
            "loop_limit_reached": len(r.residuals) - 1 >= n_loops,
            "seconds": round(time.time() - t0, 1), "k_up": r.k_up, "k_dn": r.k_dn,
            "lam_up_abs": float(abs(r.params["lambda_up"])), "lam_up_arg": float(mp.arg(r.params["lambda_up"])),
            "lam_dn_abs": float(abs(r.params["lambda_dn"])),
            "attracting_up": r.params["attracting_up"], "attracting_dn": r.params["attracting_dn"],
            "wrap_up": [wraps[-1][0].strip(), _cplx(wraps[-1][0]).__abs__()] if wraps else None,
            "wrap_dn": [wraps[-1][1].strip(), _cplx(wraps[-1][1]).__abs__()] if wraps else None,
            "wrap_max": max(max(abs(_cplx(a)), abs(_cplx(c))) for a, c in wraps) if wraps else None,
            "jump_up": float(jumps[-1][0]) if jumps else None,
            "jump_dn": float(jumps[-1][1]) if jumps else None,
            "a0_up": cstr(fu[0]), "a1_up": float(abs(fu[1])), "a2_up": float(abs(fu[2])),
            "a1_dn": float(abs(fd[1])),
            "coeffs": [f"{mp.nstr(mp.re(c), nd())},{mp.nstr(mp.im(c), nd())}" for c in r.coeffs],
            "K": {z: cstr(v) for z, v in K.items()},
        }
        if want_regular and out["attracting_up"]:
            try:
                R, rres, c0 = regular_values(name, digits=max(20, digits + 6))
                out["R"] = {z: cstr(v) for z, v in R.items()}
                out["R_residual"] = rres
                out["R_c0_minus_1"] = float(abs(c0 - 1))
                out["D"] = {z: cstr(K[z] - R[z]) for z in FUNCTIONALS}
                out["absD"] = {z: float(abs(K[z] - R[z])) for z in FUNCTIONALS}
            except Exception as exc:      # noqa: BLE001
                out["R_error"] = str(exc)[:200]
    return out, r.coeffs


def save(d, path):
    with open(path, "w") as fh:
        json.dump(d, fh, indent=1)


def coeffs_of(d):
    with mp.workdps(DPS):
        return [mp.mpc(*(mp.mpf(p) for p in s.split(","))) for s in d["coeffs"]]


def _worker(args):
    b, seed_strs, digits, path, tag = args
    with mp.workdps(DPS):
        seed = [mp.mpc(*(mp.mpf(p) for p in s.split(","))) for s in seed_strs]
    try:
        d, _ = build_point(b, seed, digits)
        d["seed_from"] = tag
        save(d, path)
        return (path, d["residual"], d["loops"], d["seconds"], None)
    except Exception as exc:      # noqa: BLE001
        return (path, None, None, None, str(exc)[:300])


# ----------------------------------------------------------------------------- circles

def circle_points(b0, r, N, phase):
    return [complex(b0) + r * complex(math.cos(phase + 2 * math.pi * j / N), math.sin(phase + 2 * math.pi * j / N))
            for j in range(N)]


def run_circle(b0, r, N, digits, seed_path, outdir, phase=0.0, b1=None, log=_log, start_seed_b=None,
               n0=8):
    """Build the centre, the circle (chained, refined by doubling from n0 points), the
    antipode of the start from both directions, and the interior point b1."""
    os.makedirs(outdir, exist_ok=True)
    pts = circle_points(b0, r, N, phase)
    meta = {"b0": [complex(b0).real, complex(b0).imag], "r": r, "N": N, "phase": phase, "digits": digits,
            "points": [[p.real, p.imag] for p in pts],
            "lam_up_abs": [lam_abs(p)[0] for p in pts], "lam_dn_abs": [lam_abs(p)[1] for p in pts]}
    bad = [j for j in range(N) if abs(meta["lam_up_abs"][j] - 1) < NEUTRAL or abs(meta["lam_dn_abs"][j] - 1) < NEUTRAL]
    meta["refused_points"] = bad
    log(f"circle b0={bname(b0)} r={r} N={N} phase={phase:.4f} digits={digits}; |lam_up| on circle "
        f"{min(meta['lam_up_abs']):.3f}..{max(meta['lam_up_abs']):.3f}; refused {bad}")
    save(meta, os.path.join(outdir, "meta.json"))
    seed = load_seed(seed_path)

    def build_named(b, seed, label, tag):
        path = os.path.join(outdir, f"{label}.json")
        if abs(lam_abs(b)[0] - 1) < NEUTRAL or abs(lam_abs(b)[1] - 1) < NEUTRAL:
            log(f"  {label} {bname(b)}: in the neutral band, skipped (seed passed through)")
            return None, seed
        if os.path.exists(path):
            d = json.load(open(path))
            log(f"  {label} {bname(b)}: cached (residual {d['residual']})")
            return d, coeffs_of(d)
        d, c = build_point(b, seed, digits)
        d["seed_from"] = tag
        save(d, path)
        log(f"  {label} {bname(b)}: residual {d['residual']} loops {d['loops']} {d['seconds']}s "
            f"wrap {(d['wrap_max'] or 0):.2e} jump {(d['jump_up'] or 0):.2e}/{(d['jump_dn'] or 0):.2e} a1_up {d['a1_up']:.2e}"
            + (f" |D(1/2)| {d['absD']['0.5']:.2e}" if "absD" in d else ""))
        return d, c

    # centre (may be refused: on the boundary)
    centre_ok = abs(lam_abs(b0)[0] - 1) >= NEUTRAL and abs(lam_abs(b0)[1] - 1) >= NEUTRAL
    if centre_ok:
        dc, cc = build_named(b0, seed, "centre", f"seed:{os.path.basename(seed_path)}")
        chain_seed, chain_tag = cc, "centre"
    else:
        log("  centre is in the neutral band: not built (boundary circle)")
        chain_seed, chain_tag = seed, f"seed:{os.path.basename(seed_path)}"
    # coarse chain: n0 points, both directions, antipode twice
    step = N // n0
    coarse = list(range(0, N, step))
    built = {}
    j0 = coarse[0]
    if start_seed_b is not None:      # start from the sample nearest to a given base
        j0 = min(coarse, key=lambda j: abs(pts[j] - complex(start_seed_b)))
    d, c = build_named(pts[j0], chain_seed, f"p{j0:03d}", chain_tag)
    built[j0] = c
    order = coarse[coarse.index(j0):] + coarse[:coarse.index(j0)]
    half = len(order) // 2
    fwd, bwd = order[1:half + 1], list(reversed(order[half:]))
    c_prev, tag = c, f"p{j0:03d}"
    for j in fwd:
        d, c_prev = build_named(pts[j], c_prev, f"p{j:03d}", tag)
        built[j] = c_prev
        tag = f"p{j:03d}"
    c_prev, tag = built[j0], f"p{j0:03d}"
    for j in bwd:
        label = f"p{j:03d}" if j not in built else f"p{j:03d}_bwd"
        d, c_prev = build_named(pts[j], c_prev, label, tag)
        if j not in built:
            built[j] = c_prev
        tag = f"p{j:03d}"
    # monodromy: antipode from both sides
    ja = order[half]
    pa, pb = os.path.join(outdir, f"p{ja:03d}.json"), os.path.join(outdir, f"p{ja:03d}_bwd.json")
    mono = None
    if os.path.exists(pa) and os.path.exists(pb):
        da, db = json.load(open(pa)), json.load(open(pb))
        ca, cb = coeffs_of(da), coeffs_of(db)
        with mp.workdps(DPS):
            mono = {"antipode": ja, "max_coeff_diff_30": float(max(abs(ca[k] - cb[k]) for k in range(30))),
                    "K_half_diff": float(abs(cval(da["K"]["0.5"]) - cval(db["K"]["0.5"])))}
        log(f"  monodromy at p{ja:03d}: max|dcoeff| {mono['max_coeff_diff_30']:.2e}, |dK(1/2)| {mono['K_half_diff']:.2e}")
    meta["monodromy"] = mono
    save(meta, os.path.join(outdir, "meta.json"))
    # refinement by doubling, parallel
    while step > 1:
        step //= 2
        new = [j for j in range(0, N, step) if j not in built]
        jobs = []
        for j in new:
            if j in bad:
                continue
            cands = [jj for jj in (j - step, j + step, j - 2 * step, j + 2 * step) if jj % N in built]
            if not cands:
                continue
            jn = cands[0] % N
            path = os.path.join(outdir, f"p{j:03d}.json")
            if os.path.exists(path):
                built[j] = coeffs_of(json.load(open(path)))
                continue
            seed_strs = [f"{mp.nstr(mp.re(c), nd())},{mp.nstr(mp.im(c), nd())}" for c in built[jn]]
            jobs.append((pts[j], seed_strs, digits, path, f"p{jn:03d}"))
        if jobs:
            log(f"  refining to {N // step} points: {len(jobs)} builds in parallel")
            with Pool(min(24, len(jobs))) as pool:
                for path, res, loops, sec, err in pool.map(_worker, jobs):
                    if err:
                        log(f"    {os.path.basename(path)}: FAILED {err}")
                    else:
                        log(f"    {os.path.basename(path)}: residual {res} loops {loops} {sec}s")
        for j in new:
            path = os.path.join(outdir, f"p{j:03d}.json")
            if os.path.exists(path) and j not in built:
                built[j] = coeffs_of(json.load(open(path)))
    # interior point b1
    if b1 is not None and abs(lam_abs(b1)[0] - 1) >= NEUTRAL:
        jn = min(built, key=lambda j: abs(pts[j] - complex(b1)))
        build_named(b1, built[jn] if not centre_ok else cc, "b1", "centre" if centre_ok else f"p{jn:03d}")
    return meta


def load_circle(outdir):
    meta = json.load(open(os.path.join(outdir, "meta.json")))
    N = meta["N"]
    pts, data = [], {}
    for j in range(N):
        p = os.path.join(outdir, f"p{j:03d}.json")
        if os.path.exists(p):
            data[j] = json.load(open(p))
    extra = {}
    for lab in ("centre", "b1"):
        p = os.path.join(outdir, f"{lab}.json")
        if os.path.exists(p):
            extra[lab] = json.load(open(p))
    return meta, data, extra


def fval(d, f, key):
    if f == "K":
        return cval(d["K"][key])
    if f == "R":
        return cval(d["R"][key]) if "R" in d else None
    if f == "D":
        return cval(d["D"][key]) if "D" in d else None
    raise KeyError(f)


def analyse_circle(outdir, log=_log, extra_targets=None):
    """Trapezoid Cauchy sums on nested subsets of the circle:
      I0[N]   = sum_j f(b_j) i r e^{i phi_j} 2pi/N                (should be 0)
      C[N](b1)= (1/2pi i) sum_j f(b_j)/(b_j - b1) i r e^{i phi_j} 2pi/N  (should be f(b1))
      a_n r^n = (1/N) sum_j f(b_j) e^{-i n phi_j}                (Taylor coefficients in b about b0)
    and, for D, the fit ln|D| vs 1/Im b on the circle and the sub-mean-value check."""
    meta, data, extra = load_circle(outdir)
    N, r, phase = meta["N"], mp.mpf(meta["r"]), mp.mpf(meta["phase"])
    b0 = mp.mpc(*meta["b0"])
    with mp.workdps(DPS):
        res = {"N": N, "r": float(r), "b0": meta["b0"], "missing": [j for j in range(N) if j not in data],
               "diagnostic_notes": [
                   "wrap is first-minus-last adjacent mesh value, NOT theta(t+1)-theta(t)",
                   "residuals and requested digits are not certified value-error bounds",
                   "old data used 12-significant-digit bases; grid displacement limits Cauchy accuracy",
                   "Taylor radius and submean diagnostics are exploratory, not proofs"],
               "base_grid_displacement_max": max(float(abs(mp.mpc(complex(data[j]["base"])) -
                   (b0 + r * mp.exp(1j * (phase + 2 * mp.pi * j / N))))) for j in data),
               "residual_max": max(float(d["residual"]) for d in data.values()),
               "wrap_max": max((d["wrap_max"] or 0) for d in data.values()),
               "wrap_converged_max": max(max((d["wrap_up"] or [0, 0])[1], (d["wrap_dn"] or [0, 0])[1]) for d in data.values()),
               "jump_max": max(max(d["jump_up"] or 0, d["jump_dn"] or 0) for d in data.values()),
               "a1_up_range": [min(d["a1_up"] for d in data.values()), max(d["a1_up"] for d in data.values())],
               "R_c0_max": max(d.get("R_c0_minus_1", 0) for d in data.values()),
               "loops_range": [min(d["loops"] for d in data.values()), max(d["loops"] for d in data.values())],
               "monodromy": meta.get("monodromy")}
        subsets = []
        n = N
        while n >= 4:
            subsets.append(n)
            n //= 2
        phis = {j: phase + 2 * mp.pi * j / N for j in range(N)}
        bj = {j: b0 + r * mp.exp(1j * phis[j]) for j in range(N)}
        targets = {}
        for lab in ("centre", "b1"):
            if lab in extra:
                targets[lab] = (mp.mpc(*extra[lab]["b"]), extra[lab])
        for lab, (b, d) in (extra_targets or {}).items():
            targets[lab] = (b, d)
        res["I0"], res["cauchy"], res["taylor"], res["scale"] = {}, {}, {}, {}
        for f in ("K", "R", "D"):
            if any(fval(d, f, "0.5") is None for d in data.values()):
                continue
            res["I0"][f], res["cauchy"][f], res["taylor"][f], res["scale"][f] = {}, {}, {}, {}
            for key in FUNCTIONALS:
                vals = {j: fval(data[j], f, key) for j in data}
                res["scale"][f][key] = float(max(abs(v) for v in vals.values()))
                res["I0"][f][key] = {}
                res["cauchy"][f][key] = {}
                for n in subsets:
                    js = [j for j in range(0, N, N // n) if j in vals]
                    if len(js) < n:
                        continue
                    I0 = sum(vals[j] * 1j * r * mp.exp(1j * phis[j]) for j in js) * 2 * mp.pi / n
                    res["I0"][f][key][str(n)] = float(abs(I0))
                    for lab, (b1, d1) in targets.items():
                        C = sum(vals[j] / (bj[j] - b1) * 1j * r * mp.exp(1j * phis[j]) for j in js) * 2 * mp.pi / n / (2j * mp.pi)
                        ref = fval(d1, f, key)
                        if ref is not None:
                            res["cauchy"][f][key].setdefault(lab, {})[str(n)] = float(abs(C - ref))
                # Taylor coefficients in b (full N)
                if len(vals) == N:
                    tay = []
                    for m in range(N // 2 + 1):
                        a = sum(vals[j] * mp.exp(-1j * m * phis[j]) for j in range(N)) / N
                        tay.append(a)
                    if "centre" not in extra:
                        res.setdefault("centre_predicted", {}).setdefault(f, {})[key] = cstr(tay[0])
                    res["taylor"][f][key] = [float(abs(a)) for a in tay]
                    res["taylor"].setdefault(f + "_complex", {})[key] = [[float(mp.re(a)), float(mp.im(a))] for a in tay]
                    # clean range: coefficients well above the build noise
                    noise = 10 ** (-(min(d["digits"] for d in data.values()) + 1))
                    peak = max(range(len(tay)), key=lambda m: abs(tay[m]))
                    clean = [m for m in range(peak, len(tay)) if abs(tay[m]) > 300 * noise]
                    # radius of convergence from the geometric decay over the clean tail
                    # (fit ln|a_n r^n| = alpha + n ln q, rho = r / q), and Domb-Sykes at the
                    # cleanest late index: b_s ~ b0 + r a_m / a_{m+1}
                    ds, rad = [], None
                    if len(clean) >= 4:
                        tail = clean[max(0, len(clean) - 8):]
                        fl = linfit([float(m) for m in tail], [math.log(float(abs(tay[m]))) for m in tail])
                        q = math.exp(fl[1])
                        rad = {"n_range": [tail[0], tail[-1]], "ratio_per_n": q, "radius": float(r) / q, "rms": fl[2]}
                        for m in tail[:-1]:
                            qq = tay[m] / tay[m + 1] * r
                            ds.append([m, float(mp.re(b0 + qq)), float(mp.im(b0 + qq)), float(abs(qq))])
                    res["taylor"].setdefault(f + "_singularity_estimate", {})[key] = ds
                    res["taylor"].setdefault(f + "_radius", {})[key] = rad
        # D on the circle: fit ln|D| = A - c / y and the sub-mean-value check
        if "D" in res["I0"]:
            res["D_circle"] = {}
            for key in FUNCTIONALS:
                ys, ls = [], []
                for j in data:
                    y = float(mp.im(bj[j]))
                    a = data[j]["absD"][key]
                    if fit_eligible(data[j], key):
                        ys.append(1.0 / y)
                        ls.append(math.log(a))
                fit = None
                if len(ys) >= 4:
                    fit = linfit(ys, ls)
                mean_log = sum(math.log(max(data[j]["absD"][key], 10 ** (-(data[j]["digits"] + 1)))) for j in data) / len(data)
                centre_log = math.log(extra["centre"]["absD"][key]) if "centre" in extra and "absD" in extra["centre"] else None
                res["D_circle"][key] = {"fit_c": fit, "n_used": len(ys), "mean_log_abs_on_circle(floor)": mean_log,
                                        "log_abs_at_centre": centre_log}
    save(res, os.path.join(outdir, "analysis.json"))
    # readable summary
    log(f"=== circle {outdir}: b0={meta['b0']} r={meta['r']} N={N} missing={res['missing']}")
    log(f"  build residual max {res['residual_max']:.2e}, wrap max {res['wrap_max']:.2e} (converged {res['wrap_converged_max']:.2e}), jump max {res['jump_max']:.2e}, "
        f"loops {res['loops_range']}, a1_up {res['a1_up_range'][0]:.2e}..{res['a1_up_range'][1]:.2e}, R c0-1 max {res['R_c0_max']:.1e}")
    if res["monodromy"]:
        log(f"  monodromy (antipode from both directions): max|dcoeff| {res['monodromy']['max_coeff_diff_30']:.2e}, "
            f"|dK(1/2)| {res['monodromy']['K_half_diff']:.2e}")
    if "centre_predicted" in res:
        for f, dd in res["centre_predicted"].items():
            log(f"  centre not built; Cauchy-mean prediction of {f}(b0): " + ", ".join(f"{k}: {v[0][:16]}{'+' if not v[1].startswith('-') else ''}{v[1][:16]}i" for k, v in dd.items()))
    for f in res["I0"]:
        for key in FUNCTIONALS:
            i0 = res["I0"][f][key]
            s = "  ".join(f"N={n}: {i0[n]:.2e}" for n in sorted(i0, key=int))
            log(f"  |oint {f}({key}) db| (scale {res['scale'][f][key]:.2e}): {s}")
            for lab, cc in res["cauchy"][f][key].items():
                s = "  ".join(f"N={n}: {cc[n]:.2e}" for n in sorted(cc, key=int))
                log(f"     |Cauchy[{f}]({lab}) - {f}({lab})|: {s}")
            if key in res["taylor"].get(f, {}):
                t = res["taylor"][f][key]
                log(f"     |a_n r^n| n=0..: " + " ".join(f"{x:.1e}" for x in t))
                ds = res["taylor"][f + "_singularity_estimate"][key]
                rad = res["taylor"][f + "_radius"][key]
                if rad:
                    log(f"     geometric tail n={rad['n_range']}: ratio {rad['ratio_per_n']:.3f}/step -> radius of convergence {rad['radius']:.3f} (rms {rad['rms']:.2f})")
                if ds:
                    log("     Domb-Sykes b_s ~ " + "; ".join(f"m={m}: {x:.3f}{y:+.3f}i (d={q:.3f})" for m, x, y, q in ds[-4:]))
    if "D_circle" in res:
        for key in FUNCTIONALS:
            dc = res["D_circle"][key]
            fit = dc["fit_c"]
            log(f"  D({key}) on circle: fit ln|D| = {fit[0]:.2f} - {-fit[1]:.2f}/y (n={dc['n_used']}, rms {fit[2]:.2f})" if fit else
                f"  D({key}) on circle: too few resolved points")
            if dc["log_abs_at_centre"] is not None:
                log(f"     sub-mean-value: mean ln|D| on circle {dc['mean_log_abs_on_circle(floor)']:.2f} vs ln|D(b0)| "
                    f"{dc['log_abs_at_centre']:.2f}  ({'OK' if dc['mean_log_abs_on_circle(floor)'] >= dc['log_abs_at_centre'] else 'VIOLATED'})")
    return res


def linfit(xs, ys):
    n = len(xs)
    mx, my = sum(xs) / n, sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    slope = sxy / sxx if sxx else 0.0
    inter = my - slope * mx
    rms = math.sqrt(sum((y - inter - slope * x) ** 2 for x, y in zip(xs, ys)) / n)
    return [inter, slope, rms]


# ----------------------------------------------------------------------------- M2.4

def boundary_point(bA, bB, tol=1e-9):
    """Point on the segment [bA, bB] with |lambda_up| = 1 (bisection)."""
    bA, bB = complex(bA), complex(bB)
    fa = lam_abs(bA)[0] - 1
    lo, hi = 0.0, 1.0
    for _ in range(60):
        mid = (lo + hi) / 2
        fm = lam_abs(bA + mid * (bB - bA))[0] - 1
        if (fm > 0) == (fa > 0):
            lo, fa = mid, fm
        else:
            hi = mid
        if hi - lo < tol:
            break
    return bA + (lo + hi) / 2 * (bB - bA)


def choose_phase(b0, r, N, margin=0.025):
    best = None
    for k in range(180):
        ph = math.pi * k / 180 / (N / 2)     # phases in [0, 2pi/N)
        pts = circle_points(b0, r, N, ph)
        m = min(min(abs(lam_abs(p)[0] - 1), abs(lam_abs(p)[1] - 1)) for p in pts)
        if best is None or m > best[1]:
            best = (ph, m)
    return best


# ----------------------------------------------------------------------------- M2.3

def run_decay(re_b, ims, digits, seed_path, outdir, log=_log, n_loops=60):
    os.makedirs(outdir, exist_ok=True)
    seed = load_seed(seed_path)
    tag = f"seed:{os.path.basename(seed_path)}"
    for y in ims:
        b = complex(re_b, y)
        path = os.path.join(outdir, f"{bname(b)}.json")
        if os.path.exists(path):
            d = json.load(open(path))
            seed, tag = coeffs_of(d), bname(b)
            log(f"  {bname(b)}: cached |D(1/2)| {d.get('absD', {}).get('0.5')}")
            continue
        try:
            d, seed = build_point(b, seed, digits, n_loops=n_loops)
        except Exception as exc:      # noqa: BLE001
            log(f"  {bname(b)}: FAILED {exc}")
            break
        d["seed_from"] = tag
        save(d, path)
        tag = bname(b)
        log(f"  {bname(b)}: residual {d['residual']} loops {d['loops']} {d['seconds']}s wrap {(d['wrap_max'] or 0):.1e} "
            f"|lam_up| {d['lam_up_abs']:.3f} arg {d['lam_up_arg']:.4f} a1_up {d['a1_up']:.2e} "
            + (" ".join(f"|D({z})| {d['absD'][z]:.2e}" for z in FUNCTIONALS) if "absD" in d else d.get("R_error", "")))


def fit_decay(dirs, log=_log, pgrid=None):
    """ln|D| = A - c / y^p per ladder and per functional; p = 1 forced, and best p on a grid."""
    pgrid = pgrid or [0.5 + 0.05 * k for k in range(41)]
    out = {}
    for dd in dirs:
        rows = []
        for fn in sorted(os.listdir(dd)):
            if fn.endswith(".json") and fn not in ("meta.json", "analysis.json", "fit.json"):
                d = json.load(open(os.path.join(dd, fn)))
                if "absD" in d:
                    rows.append(d)
        rows.sort(key=lambda d: d["b"][1])
        res = {}
        for key in FUNCTIONALS:
            ys, ls, arg = [], [], []
            for d in rows:
                a = d["absD"][key]
                floor = 10 ** (-(d["digits"] + 0.5))
                if fit_eligible(d, key):
                    ys.append(d["b"][1])
                    ls.append(math.log(a))
                    arg.append(d["lam_up_arg"])
            if len(ys) < 3:
                res[key] = {"n": len(ys)}
                continue
            f1 = linfit([1 / y for y in ys], ls)
            best = None
            for p in pgrid:
                f = linfit([y ** (-p) for y in ys], ls)
                if best is None or f[2] < best[1][2]:
                    best = (p, f)
            farg = linfit([1 / a for a in arg], ls)
            res[key] = {"n": len(ys), "y_range": [min(ys), max(ys)],
                        "p1": {"A": f1[0], "c": -f1[1], "rms": f1[2]},
                        "best": {"p": best[0], "A": best[1][0], "c": -best[1][1], "rms": best[1][2]},
                        "vs_arg_lambda": {"A": farg[0], "c": -farg[1], "rms": farg[2]},
                        "screening": "absD > 100*max(requested floor,residual,residual_check), R_c0<1e-10; heuristic only",
                        "points": [[y, l] for y, l in zip(ys, ls)]}
        out[dd] = res
        save(res, os.path.join(dd, "fit.json"))
        log(f"=== ladder {dd}: {len(rows)} rungs, Im b = {[d['b'][1] for d in rows]}")
        log("  " + "  ".join(f"y={d['b'][1]:.3g}:|D|={d['absD']['0.5']:.1e}" for d in rows))
        for key in FUNCTIONALS:
            rr = res[key]
            if "p1" in rr:
                log(f"  D({key}): n={rr['n']} y in [{rr['y_range'][0]:.2f},{rr['y_range'][1]:.2f}]  p=1: c={rr['p1']['c']:.3f} A={rr['p1']['A']:.2f} rms={rr['p1']['rms']:.3f}"
                    f"  | best p={rr['best']['p']:.2f}: c={rr['best']['c']:.3f} rms={rr['best']['rms']:.3f}"
                    f"  | vs 1/arg(lam_up): c={rr['vs_arg_lambda']['c']:.3f} rms={rr['vs_arg_lambda']['rms']:.3f}")
            else:
                log(f"  D({key}): only {rr['n']} resolved rungs")
    return out



# ----------------------------------------------------------------------------- law test

def lam_quantities(d):
    """log lambda_up, P = 2 pi i / log lambda, Lambda = exp(4 pi^2 / log lambda) = e^{-2 pi i P}."""
    with mp.workdps(30):
        lam = mp.mpf(d["lam_up_abs"]) * mp.exp(1j * mp.mpf(d["lam_up_arg"]))
        ll = mp.log(lam)
        P = 2j * mp.pi / ll
        Lam = mp.exp(4 * mp.pi ** 2 / ll)
        return ll, P, Lam


def collect_points(dirs):
    rows = []
    for dd in dirs:
        for fn in sorted(os.listdir(dd)):
            if fn.endswith(".json") and fn not in ("meta.json", "analysis.json", "fit.json", "law.json"):
                d = json.load(open(os.path.join(dd, fn)))
                if "D" in d and d.get("attracting_up"):
                    d["_dir"] = dd
                    rows.append(d)
    return rows


def law_test(dirs, log=_log, key="0.5"):
    """Test |D| = C |Lambda|^kappa, Lambda = exp(4 pi^2 / log lambda_up):
    regress ln|D| on x = Re(4 pi^2 / log lambda_up) (slope kappa should be 1) and on 1/Im b (the
    old law), report rms; and the ratio E = D / Lambda (modulus and phase) per base."""
    rows = collect_points(dirs)
    out = {"n": len(rows), "per_key": {}}
    for key in FUNCTIONALS:
        xs, ys, invy, rec = [], [], [], []
        for d in rows:
            a = d["absD"][key]
            floor = 10 ** (-(d["digits"] + 0.5))
            if not fit_eligible(d, key):
                continue
            ll, P, Lam = lam_quantities(d)
            with mp.workdps(30):
                x = float(mp.re(4 * mp.pi ** 2 / ll))
                Dv = cval(d["D"][key])
                E = Dv / Lam
                rec.append({"base": d["base"], "y": d["b"][1], "x": d["b"][0], "lnD": math.log(a), "Re4pi2_over_loglam": x,
                            "absE": float(abs(E)), "argE": float(mp.arg(E)), "P": [float(mp.re(P)), float(mp.im(P))],
                            "digits": d["digits"]})
            xs.append(x)
            ys.append(math.log(a))
            invy.append(1.0 / d["b"][1])
        if len(xs) < 4:
            out["per_key"][key] = {"n": len(xs)}
            continue
        f_law = linfit(xs, ys)
        f_old = linfit(invy, ys)
        # fixed slope 1: ln|D| - x = const ?
        resid1 = [y - x for x, y in zip(xs, ys)]
        m1 = sum(resid1) / len(resid1)
        rms1 = math.sqrt(sum((r - m1) ** 2 for r in resid1) / len(resid1))
        # prefactor E = D / Lambda against candidate variables: ln|E| = a + s ln v
        pref = {}
        for vname in ("Im b", "|log lam|", "arg lam", "|Im P|", "|P|"):
            vs = []
            for rr, d in zip(rec, [d for d in rows if fit_eligible(d, key)]):
                ll, P, _ = lam_quantities(d)
                v = {"Im b": d["b"][1], "|log lam|": float(abs(ll)), "arg lam": d["lam_up_arg"],
                     "|Im P|": abs(rr["P"][1]), "|P|": math.hypot(*rr["P"])}[vname]
                vs.append(math.log(v))
            fp = linfit(vs, [math.log(rr["absE"]) for rr in rec])
            pref[vname] = {"slope": fp[1], "a": fp[0], "rms": fp[2]}
        out["per_key"][key] = {"n": len(xs), "law_fit": {"kappa": f_law[1], "lnC": f_law[0], "rms": f_law[2]},
                               "law_slope1": {"lnC": m1, "rms": rms1},
                               "old_fit_1_over_y": {"c": -f_old[1], "A": f_old[0], "rms": f_old[2]},
                               "prefactor_fits": pref, "points": rec}
        log(f"=== law test D({key}): {len(xs)} bases from {len(dirs)} dirs")
        log(f"  ln|D| = lnC + kappa * Re(4pi^2/log lam_up):  kappa = {f_law[1]:.4f}, lnC = {f_law[0]:.3f}, rms = {f_law[2]:.3f}")
        log(f"  slope fixed to 1: lnC = {m1:.3f}, rms = {rms1:.3f}")
        log(f"  old law ln|D| = A - c/Im b:  c = {-f_old[1]:.3f}, A = {f_old[0]:.3f}, rms = {f_old[2]:.3f}")
        log("  prefactor |E| = |D/Lambda| ~ v^s: " + "; ".join(f"{v}: s={q['slope']:.3f} (rms {q['rms']:.3f})" for v, q in pref.items()))
        if key == "0.5":
            log("  base | Im b | ln|D| | Re(4pi^2/log lam) | |E| = |D/Lambda| | arg E | P")
            for rr in sorted(rec, key=lambda t: (t["x"], t["y"])):
                log(f"  {rr['base']:>28} | {rr['y']:.3f} | {rr['lnD']:8.2f} | {rr['Re4pi2_over_loglam']:8.2f} | {rr['absE']:9.3e} | {rr['argE']:+.3f} | {rr['P'][0]:.3f}{rr['P'][1]:+.3f}i")
    # first theta-mode picture: D(z) ~ a_1 e^{2 pi i z} R'(z)  =>  D(z) / (e^{2 pi i z} R'(z)) = const (= a_1) in z
    log("=== first-mode check: |D(z) / (e^{2 pi i z} R'(z))| for z in ZS, vs |a_1^up| of the build")
    chk = []
    for d in sorted(rows, key=lambda d: -d["b"][1]):
        if d["absD"]["0.5"] < 1e-9 or d["_dir"] not in dirs[-6:]:
            continue
        with mp.workdps(30):
            g = GeneralRegularEngine(d["base"], 18)
            ratios = []
            for z in ZS:
                zz = mp.mpc(complex(z))
                _, dR = g.sexp(zz, derivative=True)
                ratios.append(cval(d["D"][z]) / (mp.exp(2j * mp.pi * zz) * dR))
            row = {"base": d["base"], "a1_up": d["a1_up"], "ratios": [[float(abs(q)), float(mp.arg(q))] for q in ratios]}
            chk.append(row)
            log(f"  {d['base']:>28}: a1_up {d['a1_up']:.3e}; |ratio| " + " ".join(f"{float(abs(q)):.3e}" for q in ratios) +
                "; arg " + " ".join(f"{float(mp.arg(q)):+.3f}" for q in ratios))
        if len(chk) >= 14:
            break
    out["first_mode_check"] = chk
    return out


def analyse_E(outdir, log=_log):
    """Cauchy / Taylor analysis of E = D / Lambda on a finished circle (essential singularity at
    eta divided out)."""
    meta, data, extra = load_circle(outdir)
    N, r, phase = meta["N"], mp.mpf(meta["r"]), mp.mpf(meta["phase"])
    b0 = mp.mpc(*meta["b0"])
    if any("D" not in d for d in data.values()):
        log("  E analysis: D missing on some points")
        return
    res = {}
    with mp.workdps(DPS):
        phis = {j: phase + 2 * mp.pi * j / N for j in range(N)}
        for key in FUNCTIONALS:
            vals = {}
            for j, d in data.items():
                _, _, Lam = lam_quantities(d)
                vals[j] = cval(d["D"][key]) / Lam
            noiseE = max(10 ** (-(d["digits"] + 1)) / float(abs(lam_quantities(d)[2])) for d in data.values())
            I0 = {}
            n = N
            while n >= 4:
                js = list(range(0, N, N // n))
                I0[str(n)] = float(abs(sum(vals[j] * 1j * r * mp.exp(1j * phis[j]) for j in js) * 2 * mp.pi / n))
                n //= 2
            tay = [sum(vals[j] * mp.exp(-1j * m * phis[j]) for j in range(N)) / N for m in range(N // 2 + 1)]
            mods = [float(abs(a)) for a in tay]
            peak = max(range(len(tay)), key=lambda m: mods[m])
            clean = [m for m in range(peak, len(tay)) if mods[m] > 300 * noiseE]
            rad, ds = None, []
            if len(clean) >= 4:
                tail = clean[max(0, len(clean) - 8):]
                fl = linfit([float(m) for m in tail], [math.log(mods[m]) for m in tail])
                rad = {"n_range": [tail[0], tail[-1]], "ratio_per_n": math.exp(fl[1]), "radius": float(r) / math.exp(fl[1]), "rms": fl[2]}
                for m in tail[:-1]:
                    qq = tay[m] / tay[m + 1] * r
                    ds.append([m, float(mp.re(b0 + qq)), float(mp.im(b0 + qq)), float(abs(qq))])
            cen = None
            if "centre" in extra and "D" in extra["centre"]:
                _, _, Lc = lam_quantities(extra["centre"])
                Ec = cval(extra["centre"]["D"][key]) / Lc
                cen = {"absE_centre": float(abs(Ec)), "cauchy_minus_centre": float(abs(tay[0] - Ec))}
            res[key] = {"scale": float(max(abs(v) for v in vals.values())), "noise": noiseE, "I0": I0, "taylor_abs": mods,
                        "radius": rad, "domb_sykes": ds, "centre": cen}
            log(f"  E({key}) = D/Lambda on circle: scale {res[key]['scale']:.3e} (noise ~{noiseE:.1e}); |oint E db|: "
                + "  ".join(f"N={n}: {v:.2e}" for n, v in sorted(I0.items(), key=lambda t: int(t[0]))))
            if cen:
                log(f"     |mean_circle E - E(b0)| = {cen['cauchy_minus_centre']:.2e}  (|E(b0)| = {cen['absE_centre']:.3e})")
            log("     |a_n r^n|: " + " ".join(f"{x:.1e}" for x in mods[:24]))
            if rad:
                log(f"     geometric tail n={rad['n_range']}: ratio {rad['ratio_per_n']:.3f}/step -> radius {rad['radius']:.3f} (rms {rad['rms']:.2f});  "
                    + "Domb-Sykes " + "; ".join(f"m={m}: {x:.3f}{y:+.3f}i" for m, x, y, q in ds[-3:]))
    save(res, os.path.join(outdir, "analysis_E.json"))
    return res

# ----------------------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["circle", "boundary", "decay", "fit", "analyse", "plan", "law", "analyseE"])
    ap.add_argument("--b0", default="1.3+0.5j")
    ap.add_argument("--r", type=float, default=0.15)
    ap.add_argument("--N", type=int, default=32)
    ap.add_argument("--n0", type=int, default=8)
    ap.add_argument("--phase", type=float, default=None)
    ap.add_argument("--digits", type=int, default=12)
    ap.add_argument("--seed", default=None, help="json of a nearby base (coeffs)")
    ap.add_argument("--seed2", default=None, help="boundary: json for the exterior test point")
    ap.add_argument("--out", default="out")
    ap.add_argument("--tag", default=None)
    ap.add_argument("--b1", default=None, help="interior test point (default b0 - 0.5 r i)")
    ap.add_argument("--re", type=float, default=1.3)
    ap.add_argument("--ims", default="0.8,0.7,0.6,0.5,0.45,0.4,0.35,0.3,0.25,0.2,0.15")
    ap.add_argument("--dirs", default="")
    ap.add_argument("--bA", default="1.9+1.1j")
    ap.add_argument("--bB", default="2.16+1j")
    ap.add_argument("--targets", default="1.9+1.1j,2.16+1j", help="boundary: test points inside/outside")
    ap.add_argument("--idelta", type=float, default=None)
    ap.add_argument("--k_up", type=int, default=None)
    ap.add_argument("--k_dn", type=int, default=None)
    ap.add_argument("--loops", type=int, default=60)
    a = ap.parse_args()
    global IDELTA, KUP, KDN
    IDELTA, KUP, KDN = a.idelta, a.k_up, a.k_dn

    if a.mode == "fit":
        fit_decay([d for d in a.dirs.split(",") if d])
        return
    if a.mode == "analyse":
        analyse_circle(os.path.join(a.out, a.tag) if a.tag else a.out)
        return
    if a.mode == "analyseE":
        analyse_E(os.path.join(a.out, a.tag) if a.tag else a.out)
        return
    if a.mode == "law":
        dirs = [d for d in a.dirs.split(",") if d]
        res = law_test(dirs)
        save(res, os.path.join(a.out, "law.json"))
        return
    if a.mode == "decay":
        tag = a.tag or f"decay_re{a.re}"
        run_decay(a.re, [float(s) for s in a.ims.split(",")], a.digits, a.seed, os.path.join(a.out, tag), n_loops=a.loops)
        return
    if a.mode in ("circle", "plan"):
        b0 = complex(a.b0)
        tag = a.tag or f"circle_{bname(b0)}_r{a.r}_N{a.N}"
        b1 = complex(a.b1) if a.b1 else b0 - 0.5j * a.r
        if a.mode == "plan":
            for p in circle_points(b0, a.r, a.N, a.phase or 0.0):
                print(bname(p), lam_abs(p))
            return
        outdir = os.path.join(a.out, tag)
        run_circle(b0, a.r, a.N, a.digits, a.seed, outdir, phase=a.phase or 0.0, b1=b1, n0=a.n0)
        analyse_circle(outdir)
        return
    if a.mode == "boundary":
        bs = boundary_point(a.bA, a.bB)
        r = a.r
        while True:
            ph, m = choose_phase(bs, r, a.N)
            if m >= NEUTRAL + 0.003 or r >= 0.8:
                break
            print(f"r={r}: best margin {m:.4f} too small, enlarging", flush=True)
            r = round(r + 0.05, 3)
        a.r = r
        if a.phase is not None:
            ph = a.phase
        print(f"boundary point |lambda_up| = 1 on [{a.bA}, {a.bB}]: {bname(bs)}; phase {ph:.4f} "
              f"(min | |lambda|-1 | on samples = {m:.4f})", flush=True)
        for p in circle_points(bs, a.r, a.N, ph):
            print("   ", bname(p), lam_abs(p), flush=True)
        tag = a.tag or f"boundary_{bname(bs)}_r{a.r}_N{a.N}"
        outdir = os.path.join(a.out, tag)
        os.makedirs(outdir, exist_ok=True)
        # test points (inside / outside), built from the given seeds
        targets = {}
        tnames = a.targets.split(",")
        seeds = [a.seed, a.seed2 or a.seed]
        for lab, tn, sp in zip(("t_in", "t_out"), tnames, seeds):
            path = os.path.join(outdir, f"{lab}.json")
            if not os.path.exists(path):
                d, _ = build_point(complex(tn), load_seed(sp), a.digits)
                d["seed_from"] = f"seed:{os.path.basename(sp)}"
                save(d, path)
                print(f"  {lab} {tn}: residual {d['residual']} loops {d['loops']} {d['seconds']}s", flush=True)
            d = json.load(open(path))
            targets[lab] = (mp.mpc(*d["b"]), d)
        run_circle(bs, a.r, a.N, a.digits, os.path.join(outdir, "t_in.json"), outdir, phase=ph, b1=None,
                   start_seed_b=complex(tnames[0]), n0=a.n0)
        analyse_circle(outdir, extra_targets=targets)
        return


if __name__ == "__main__":
    main()
