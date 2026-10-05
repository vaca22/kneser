"""Numerical base-path experiment for two-fixed-point tetration.

Starting at base 3, compute solutions at discrete bases along a path through
the upper half-plane and across the Shell-Thron boundary toward (1, eta).
Compare interior values with the regular (Schroeder) solution.  Finite
sampling and small functional-equation residuals do not prove that these
solutions form a holomorphic base continuation of Kneser's family.

Run on galic only (never on the Mac):

  PYTHONPATH=/data/kneser-verify/src KNESER_CACHE=/data/kneser-verify/.cache \
  timeout 36000 python3 demo_paulsen_continuation.py [outdir] [path-name]

Each base is built with kneser._cbuild.build_complex(8, allow_attracting=True)
seeded with the Taylor coefficients of the previous base; if a step fails
(exception, or residual > 1e-8 within the loop budget) the step is bisected,
avoiding the neutral band |lambda| in (0.98, 1.02).  Results go to
<outdir>/<base>.json (coefficients, residual, values) and a summary table.
"""

import json
import math
import os
import sys
import time

import mpmath as mp

from kneser._cbuild import build_complex, choose_fixed_points
from kneser._bases import normalize_base, base_value
from kneser._general import GeneralRegularEngine

DIGITS = 8
N_LOOPS = 60
TARGET = mp.mpf(10) ** (-(DIGITS))

PATHS = {
    # Discrete path across the Shell-Thron boundary (|lambda_up| = 1
    # near 2+1i) -> 1.3 + i eps.  |lambda_up|: 1.41, 1.31, 1.19, 1.12, 0.94, 0.81,
    # 0.75, 0.68, 0.55, 0.46, 0.40, 0.39, 0.386
    "main": ["3", "3+0.5j", "2.6+0.7j", "2.4+0.9j", "2.16+1j", "1.9+1.1j", "1.8+1.15j", "1.5+1j",
             "1.4+0.9j", "1.3+0.8j", "1.3+0.5j", "1.3+0.3j", "1.3+0.15j", "1.3+0.05j", "1.3+0.01j"],
    # towards real targets nearer eta: 1.42 (|lambda_up| = 0.72) and 1.44 (0.87);
    # a repeated entry re-loads the cached coefficients as the seed
    "eta_side": ["3", "3+0.5j", "2.6+0.7j", "2.4+0.9j", "2.16+1j", "1.9+1.1j", "1.8+1.15j", "1.5+1j",
                 "1.4+0.9j", "1.42+0.6j", "1.42+0.4j", "1.42+0.25j", "1.42+0.15j", "1.42+0.08j",
                 "1.42+0.04j", "1.42+0.02j", "1.42+0.01j",
                 "1.42+0.15j", "1.44+0.15j", "1.44+0.08j", "1.44+0.04j", "1.44+0.02j", "1.44+0.01j"],
}


def load_coeffs(outdir, name, dps=44):
    with open(os.path.join(outdir, f"{name}.json")) as fh:
        d = json.load(fh)
    with mp.workdps(dps):
        return [mp.mpc(*(mp.mpf(p) for p in s.split(","))) for s in d["coeffs"]]


def extras(outdir):
    """(1) 12-digit rebuilds near 1.3 vs the regular engine at 16 digits; (2) the exact real
    base 1.3 with the real fixed points forced (k_up=0, k_dn=-1), seeded from 1.3+0.01i;
    (3) conjugate symmetry: 1.3-0.3i seeded with the conjugate coefficients of 1.3+0.3i."""
    from kneser._regular import RegularEngine
    print("=== extras (1): 12-digit rebuilds vs regular engine (16 digits) ===", flush=True)
    for name in ["1.3+0.3j", "1.3+0.15j", "1.3+0.05j"]:
        seed = load_coeffs(outdir, name)
        r = build_complex(12, base=name, seed=seed, verbose=True, allow_attracting=True, n_loops=60)
        with mp.workdps(44):
            logb = mp.log(base_value(name))
            g = GeneralRegularEngine(name, 16)
            print(f"### {name} @12 digits: residual {mp.nstr(r.residual, 4)}, {len(r.residuals) - 1} loops, "
                  f"{r.seconds:.0f}s", flush=True)
            g24 = GeneralRegularEngine(name, 24)
            print(f"    regular engine: residual {g.RESIDUAL}; |sexp16(0.5) - sexp24(0.5)| = "
                  f"{mp.nstr(abs(g.sexp(mp.mpf('0.5')) - g24.sexp(mp.mpf('0.5'))), 3)}", flush=True)
            D = {}
            for z in ["0.5", "-0.5", "0.25", "0.5+0.5j", "0.5-0.5j", "0.5+1j", "0.5-1j"]:
                zz = mp.mpc(complex(z))
                kv = sexp_from_coeffs(r.coeffs, logb, zz)
                gv = g24.sexp(zz)
                D[z] = kv - gv
                print(f"    z={z:>8}: kneser {mp.nstr(kv, 16)}  regular {mp.nstr(gv, 16)}  |diff| {mp.nstr(abs(kv - gv), 3)}",
                      flush=True)
            # a theta-type discrepancy D ~ F'(z) a_1 e^{2 pi i z} shrinks by e^{-2 pi} per unit height
            print(f"    |D(0.5+0.5i)|/|D(0.5-0.5i)| = {mp.nstr(abs(D['0.5+0.5j']) / abs(D['0.5-0.5j']), 4)}  "
                  f"(e^-2pi = {mp.nstr(mp.exp(-2 * mp.pi), 4)});  "
                  f"|D(0.5+1i)|/|D(0.5-1i)| = {mp.nstr(abs(D['0.5+1j']) / abs(D['0.5-1j']), 4)}", flush=True)
            with open(os.path.join(outdir, f"{name}-d12.json"), "w") as fh:
                json.dump({"base": name, "digits": 12, "residual": mp.nstr(r.residual, 4),
                           "coeffs": [f"{mp.nstr(mp.re(c), 20)},{mp.nstr(mp.im(c), 20)}" for c in r.coeffs]}, fh)
    print("=== extras (2): exact real base 1.3, fixed points alpha (k=0) / beta (k=-1) forced ===", flush=True)
    seed = load_coeffs(outdir, "1.3+0.01j")
    try:
        r = build_complex(8, base="1.3", k_up=0, k_dn=-1, seed=seed, verbose=True, allow_attracting=True,
                          n_loops=60)
        with mp.workdps(36):
            logb = mp.log(mp.mpf("1.3"))
            g = RegularEngine("1.3", 14)
            print(f"### 1.3 (real, alpha/beta): residual {mp.nstr(r.residual, 4)}, {len(r.residuals) - 1} loops",
                  flush=True)
            print("    max |Im coeff| over 48 coefficients:", mp.nstr(max(abs(mp.im(c)) for c in r.coeffs), 3), flush=True)
            for z in ["0.5", "-0.5", "0.25", "2.5", "8.5"]:
                kv = sexp_from_coeffs(r.coeffs, logb, mp.mpf(z))
                gv = g.sexp(mp.mpf(z))
                print(f"    z={z:>5}: kneser {mp.nstr(kv, 14)}  regular {mp.nstr(gv, 14)}  |diff| {mp.nstr(abs(kv - gv), 3)}",
                      flush=True)
    except Exception as exc:      # noqa: BLE001
        print("### 1.3 (real): FAILED:", exc, flush=True)
    print("=== extras (3): conjugate base 1.3-0.3i seeded with conj coefficients ===", flush=True)
    seed = [mp.conj(c) for c in load_coeffs(outdir, "1.3+0.3j")]
    r = build_complex(8, base="1.3-0.3j", seed=seed, verbose=True, allow_attracting=True, n_loops=60)
    with mp.workdps(36):
        ref = load_coeffs(outdir, "1.3+0.3j")
        print(f"### 1.3-0.3j: residual {mp.nstr(r.residual, 4)}, {len(r.residuals) - 1} loops; k_up={r.k_up} k_dn={r.k_dn}",
              flush=True)
        print("    max |coeff - conj(coeff of 1.3+0.3i)| (30 terms):",
              mp.nstr(max(abs(r.coeffs[k] - mp.conj(ref[k])) for k in range(30)), 3), flush=True)
        logb = mp.log(base_value("1.3-0.3j"))
        print("    sexp(0.5) =", mp.nstr(sexp_from_coeffs(r.coeffs, logb, mp.mpf("0.5")), 12), flush=True)


def series_at(coeffs, z):
    r = mp.mpc(0)
    for c in reversed(coeffs):
        r = r * z + c
    return r


def sexp_from_coeffs(coeffs, logb, z):
    """sexp(z) for Re z >= -0.5 from the Taylor series at 0 and the functional equation."""
    z = mp.mpc(z)
    k = max(0, int(mp.ceil(mp.re(z) - mp.mpf("0.5"))))
    v = series_at(coeffs, z - k)
    for _ in range(k):
        if abs(v) > 1e50:
            return mp.mpc(mp.inf)
        v = mp.exp(logb * v)
    return v


def taylor_of_engine(g, n=12, radius="0.5", npts=64):
    """Taylor coefficients at 0 of the regular solution (Cauchy integral)."""
    r = mp.mpf(radius)
    out = []
    pts = [g.sexp(r * mp.exp(2j * mp.pi * j / npts)) for j in range(npts)]
    for k in range(n):
        acc = mp.mpc(0)
        for j in range(npts):
            acc += pts[j] * mp.exp(-2j * mp.pi * j * k / npts)
        out.append(acc / npts / r ** k)
    return out


def analyse(name, coeffs, dps=36):
    """Values of the continued function, and of the regular solution if inside the region."""
    with mp.workdps(dps):
        logb = mp.log(base_value(name))
        ku, Lu, lamu, kd, Ld, lamd = choose_fixed_points(name)
        out = {"L_up": mp.nstr(Lu, 12), "lam_up_abs": float(abs(lamu)), "lam_up_arg": float(mp.arg(lamu)),
               "L_dn": mp.nstr(Ld, 12), "lam_dn_abs": float(abs(lamd)), "lam_dn_arg": float(mp.arg(lamd))}
        HEIGHTS = ["0.5", "-0.5", "0.25", "2.5", "4.5", "8.5", "16.5", "32.5"]
        kv = {z: sexp_from_coeffs(coeffs, logb, mp.mpf(z)) for z in HEIGHTS}
        vals = {z: mp.nstr(v, 12) for z, v in kv.items()}
        out["kneser"] = vals
        out["coeffs_first"] = [mp.nstr(c, 12) for c in coeffs[:8]]
        if abs(lamu) < 1:
            try:
                g = GeneralRegularEngine(name, 12)
                if abs(g.L - Lu) > mp.mpf("1e-6"):
                    out["regular_note"] = f"regular engine fixed point {mp.nstr(g.L, 8)} != L_up"
                gv = {z: g.sexp(mp.mpf(z)) for z in HEIGHTS}
                out["regular"] = {z: mp.nstr(v, 12) for z, v in gv.items()}
                tc = taylor_of_engine(g)
                out["regular_coeffs_first"] = [mp.nstr(c, 12) for c in tc[:8]]
                out["coeff_diff_max8"] = float(max(abs(coeffs[k] - tc[k]) for k in range(8)))
                out["value_diff"] = {z: float(abs(kv[z] - gv[z])) for z in HEIGHTS}
            except Exception as exc:      # noqa: BLE001
                out["regular_error"] = str(exc)
        return out


def build_step(name, seed, log):
    t0 = time.time()
    r = build_complex(DIGITS, base=name, seed=seed, verbose=True, allow_attracting=True,
                      n_loops=N_LOOPS)
    ok = r.residual is not None and r.residual < TARGET
    log(f"### {name}: residual {mp.nstr(r.residual, 4)} after {len(r.residuals) - 1} loops, "
        f"{time.time() - t0:.0f}s  {'OK' if ok else 'NOT CONVERGED'}")
    return r, ok


def cname(b):
    return normalize_base(str(b)) if not isinstance(b, str) else normalize_base(b)


def midpoint_name(a, b):
    za, zb = complex(cname(a).replace(" ", "")), complex(cname(b).replace(" ", ""))
    m = (za + zb) / 2
    # avoid the neutral band
    for shift in (0.0, 0.1, -0.1, 0.2, -0.2, 0.3, -0.3):
        mm = za + (0.5 + shift) * (zb - za)
        with mp.workdps(20):
            _, _, lam, _, _, lamd = choose_fixed_points(f"{mm.real:.6g}{mm.imag:+.6g}j")
            if abs(abs(lam) - 1) > 0.03 and abs(abs(lamd) - 1) > 0.03:
                m = mm
                break
    return f"{m.real:.6g}{m.imag:+.6g}j"


ORDER = ["3", "3+0.5j", "2.6+0.7j", "2.4+0.9j", "2.16+1j", "1.9+1.1j", "1.8+1.15j", "1.5+1j", "1.4+0.9j",
         "1.3+0.8j", "1.3+0.5j", "1.3+0.3j", "1.3+0.15j", "1.3+0.05j", "1.3+0.01j", "1.42+0.6j", "1.42+0.4j",
         "1.42+0.25j", "1.42+0.15j", "1.42+0.08j", "1.42+0.04j", "1.42+0.02j", "1.42+0.01j", "1.44+0.15j",
         "1.44+0.08j", "1.44+0.04j", "1.44+0.02j", "1.44+0.01j"]


def modes(outdir):
    """One extra pass per finished base: the Fourier modes a_m of theta_up (and theta_dn)
    of the converged solution.  a_m = 0 for m >= 1 <=> sexp = F_up(z + a_0) is the regular
    superfunction at L_up.  Also the regular engine's Taylor c_0 (must be 1; if not, its
    branch handling fails inside |z| < 1/2 and |K - R| is not meaningful there)."""
    print("| base | |lam_up| | a_0^up | |a_1^up| | |a_2^up| | max_{m>=3}|a_m^up| | |a_1^dn| | regular c_0 | sexp(-1/2) |",
          flush=True)
    print("|---|---|---|---|---|---|---|---|---|", flush=True)
    for name in ORDER:
        f = os.path.join(outdir, f"{name}.json")
        if not os.path.exists(f):
            continue
        seed = load_coeffs(outdir, name)
        r = build_complex(DIGITS, base=name, seed=seed, verbose=False, allow_attracting=True, n_loops=1)
        with mp.workdps(36):
            fu, fd = r.params["fa_up"], r.params["fa_dn"]
            logb = mp.log(base_value(name))
            c0 = "—"
            if r.params["attracting_up"]:
                try:
                    g = GeneralRegularEngine(name, 12)
                    c0 = mp.nstr(taylor_of_engine(g, n=1)[0], 8)
                except Exception as exc:      # noqa: BLE001
                    c0 = f"error: {exc}"[:40]
            print(f"| {name} | {float(abs(r.params['lambda_up'])):.4f} | {mp.nstr(fu[0], 8)} | {mp.nstr(abs(fu[1]), 3)} | "
                  f"{mp.nstr(abs(fu[2]), 3)} | {mp.nstr(max(abs(x) for x in fu[3:]), 3)} | {mp.nstr(abs(fd[1]), 3)} | {c0} | "
                  f"{mp.nstr(series_at(seed, mp.mpf('-0.5')), 12)} |", flush=True)


def main():
    outdir = sys.argv[1] if len(sys.argv) > 1 else "paulsen_out"
    if len(sys.argv) > 2 and sys.argv[2] == "extras":
        extras(outdir)
        return
    if len(sys.argv) > 2 and sys.argv[2] == "modes":
        modes(outdir)
        return
    path = PATHS[sys.argv[2] if len(sys.argv) > 2 else "main"]
    os.makedirs(outdir, exist_ok=True)
    logf = open(os.path.join(outdir, "walk.log"), "a")

    def log(*a):
        s = " ".join(str(x) for x in a)
        print(s, flush=True)
        logf.write(s + "\n")
        logf.flush()

    summary = []
    seed = None
    prev = None
    for target in path:
        target = cname(target)
        queue = [target]
        while queue:
            name = queue[0]
            f = os.path.join(outdir, f"{name}.json")
            if os.path.exists(f):
                with open(f) as fh:
                    d = json.load(fh)
                with mp.workdps(36):
                    seed = [mp.mpc(*(mp.mpf(p) for p in s.split(","))) for s in d["coeffs"]]
                log(f"### {name}: cached (residual {d['residual']})")
                summary.append(d)
                prev = name
                queue.pop(0)
                continue
            try:
                r, ok = build_step(name, seed, log)
            except Exception as exc:      # noqa: BLE001
                log(f"### {name}: FAILED: {exc}")
                ok, r = False, None
            if not ok:
                if prev is None:
                    log("first base failed; abort")
                    return
                mid = midpoint_name(prev, name)
                if mid == name or len(queue) > 12:
                    log(f"cannot bisect further between {prev} and {name}; abort path")
                    return
                log(f"    bisecting: inserting {mid} between {prev} and {name}")
                queue.insert(0, mid)
                continue
            with mp.workdps(r.params["dps"]):
                d = {"base": name, "residual": mp.nstr(r.residual, 4), "loops": len(r.residuals) - 1,
                     "seconds": round(r.seconds, 1), "k_up": r.k_up, "k_dn": r.k_dn,
                     "coeffs": [f"{mp.nstr(mp.re(c), 16)},{mp.nstr(mp.im(c), 16)}" for c in r.coeffs],
                     "depth_u": r.params["depth_u"], "depth_d": r.params["depth_d"]}
                d.update(analyse(name, r.coeffs))
            with open(f, "w") as fh:
                json.dump(d, fh, indent=1)
            log(f"    L_up={d['L_up']} |lam_up|={d['lam_up_abs']:.4f}  L_dn={d['L_dn']} |lam_dn|={d['lam_dn_abs']:.4f}")
            log(f"    sexp(0.5)={d['kneser']['0.5']}  sexp(-0.5)={d['kneser']['-0.5']}  sexp(0.25)={d['kneser']['0.25']}")
            log(f"    sexp(2.5)={d['kneser']['2.5']} sexp(8.5)={d['kneser']['8.5']} sexp(32.5)={d['kneser']['32.5']}")
            if "regular" in d:
                log(f"    regular(0.5)={d['regular']['0.5']}  regular(-0.5)={d['regular']['-0.5']}  "
                    f"regular(32.5)={d['regular']['32.5']}")
                log(f"    |kneser - regular|: {d.get('value_diff')}  max coeff diff (8) {d.get('coeff_diff_max8')}")
            if "regular_error" in d:
                log(f"    regular comparison failed: {d['regular_error']}")
            summary.append(d)
            seed = r.coeffs
            prev = name
            queue.pop(0)
    log("\n=== summary ===")
    log(f"{'base':>14} {'|lam_up|':>8} {'loops':>5} {'residual':>9} {'sexp(0.5)':>34} {'regular(0.5)':>34} {'|diff|':>9}")
    for d in summary:
        reg = d.get("regular", {}).get("0.5", "-")
        diff = d.get("value_diff", {}).get("0.5", float("nan"))
        log(f"{d['base']:>14} {d['lam_up_abs']:8.4f} {d['loops']:5d} {d['residual']:>9} {d['kneser']['0.5']:>34} "
            f"{reg:>34} {diff:9.2e}")


if __name__ == "__main__":
    main()
