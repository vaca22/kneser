"""Kneser constants and integer-relation null experiments (问题 5.1/5.2, 猜想 D).

The continuous iteration flow distinguishes a small family of constants:

    K1 = sexp(1/2)            the half-tower         = half_exp(1)
    K2 = sexp(-1/2)           identity-path midpoint = half_exp(0)
    K3 = f'(0)                slope of half_exp at 0 = sexp'(-1/2)/sexp'(0)
    K4 = V(0) = sexp'(0)      flow speed at 0 (= speed at 1)
    K5 = V_min                slowest speed of the flow
    K6 = x*                   where the flow is slowest (sexp''(a*) = 0)
    K7 = a* = slog(K6)        the same point in Abel coordinate

This demo prints them to 50 digits (or more with --coeffs, see below) and
runs three families of *null* experiments, reporting every search
parameter so the negative results are reproducible and quantified:

  A. algebraic:      findpoly(K, degree, maxcoeff) -- is K a root of a
                     small integer polynomial?
  B. linear:         PSLQ over a standard constant basis, incl. the
                     components of the exp fixed point Re L, Im L;
  C. multiplicative: PSLQ over logarithms -- is K a product of powers
                     of standard constants?  (log|L| = Re L exactly,
                     so Re L doubles as log |L| here.)
  D. internal:       PSLQ across the K-family itself.

A null result here is *evidence of independence only at the stated
height*, not a proof (research-program-zh.md, 纪律 3).  The cautionary
example is built in: V_min agrees with 22/23 to 7 digits and is killed
at 50.

Run:  PYTHONPATH=src python3 docs/demo_constants_pslq.py
      ... --coeffs /tmp/kneser_coeffs80.py   # use a higher-precision build
"""

import argparse
import importlib.util

import mpmath as mp

DPS_DATA = 50  # digits carried by the shipped coefficients


def load_coeffs(path=None):
    global DPS_DATA
    if path:
        spec = importlib.util.spec_from_file_location("_coeffs_hp", path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        DPS_DATA = module.DIGITS
        return module.COEFFS
    from kneser import _coeffs
    DPS_DATA = _coeffs.DIGITS
    return _coeffs.COEFFS


def make_eval(coeff_strings):
    """sexp, slog and the derivative helpers from a coefficient table."""
    C = [mp.mpf(s) for s in coeff_strings]
    C1 = [k * c for k, c in enumerate(C)][1:]
    C2 = [k * (k - 1) * c for k, c in enumerate(C)][2:]

    def horner(cs, z):
        r = mp.mpf(0)
        for c in reversed(cs):
            r = r * z + c
        return r

    def S012(z):
        z = mp.mpf(z)
        k = 0
        while z > mp.mpf("0.5"):
            z -= 1
            k += 1
        while z < mp.mpf("-0.5"):
            z += 1
            k -= 1
        s, s1, s2 = horner(C, z), horner(C1, z), horner(C2, z)
        for _ in range(k):
            sn = mp.exp(s)
            s2 = sn * (s1 * s1 + s2)
            s1 = sn * s1
            s = sn
        for _ in range(-k):
            s1n = s1 / s
            s2 = s2 / s - s1n * s1n
            s1 = s1n
            s = mp.log(s)
        return s, s1, s2

    return S012


def kneser_constants(S012):
    a_star = mp.findroot(lambda a: S012(a)[2], (mp.mpf(-1), mp.mpf(0)),
                         solver="anderson")
    x_star, v_min, _ = S012(a_star)
    return {
        "K1 = sexp(1/2)": S012(mp.mpf("0.5"))[0],
        "K2 = sexp(-1/2)": S012(mp.mpf("-0.5"))[0],
        "K3 = f'(0)": S012(mp.mpf("-0.5"))[1] / S012(0)[1],
        "K4 = sexp'(0)": S012(0)[1],
        "K5 = V_min": v_min,
        "K6 = x_min": x_star,
        "K7 = a_min": a_star,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--coeffs", default=None, help="alternative _coeffs.py module")
    args = ap.parse_args()

    coeffs = load_coeffs(args.coeffs)
    work = DPS_DATA + 10
    mp.mp.dps = work
    S012 = make_eval(coeffs)
    K = kneser_constants(S012)

    print(f"Kneser constants at {DPS_DATA} digits "
          f"(coefficients: {'shipped' if not args.coeffs else args.coeffs})\n")
    for name, v in K.items():
        print(f"  {name:<16} = {mp.nstr(v, DPS_DATA)}")

    # PSLQ working precision: stay safely inside the data accuracy
    dps_rel = DPS_DATA - 4
    L = mp.mpc("0.3181315052047641353", "1.3372357014306894089")
    for _ in range(60):
        ez = mp.exp(L)
        L -= (ez - L) / (ez - 1)

    def pslq_verified(vec, maxcoeff, label):
        """PSLQ + an independent residual check at full data precision.

        An n-vector at working precision d admits *noise* relations of
        height ~10^(d/(n-1)); any candidate is therefore re-evaluated at
        the full data precision and accepted only if its residual is at
        the data's own noise floor.
        """
        with mp.workdps(dps_rel):
            rel = mp.pslq([+v for v in vec], maxcoeff=maxcoeff,
                          maxsteps=2 * 10**6)
        if rel is None:
            print(f"  {label:<16} -> None  (excluded up to height {maxcoeff:.0e})")
            return
        with mp.workdps(DPS_DATA + 10):
            resid = abs(mp.fsum(r * v for r, v in zip(rel, vec)))
        if resid < mp.mpf(10) ** (-(DPS_DATA - 6)):
            print(f"  {label:<16} -> RELATION {rel}  residual={mp.nstr(resid, 3)}")
        else:
            print(f"  {label:<16} -> None  (PSLQ noise floor: height "
                  f"{max(abs(r) for r in rel):.0e} vector leaves "
                  f"residual {mp.nstr(resid, 3)} at {DPS_DATA} digits)")

    # height caps scale with the available precision: a search over an
    # n-vector is trustworthy while (n-1)*log10(height) << dps.
    def cap(n_vec, hard=12):
        return 10 ** max(3, min(hard, (dps_rel - 10) // (n_vec - 1)))

    # --- A. small algebraic relations ---------------------------------------
    def findpoly_verified(v, deg, mc):
        """findpoly + residual check at full data precision (noise filter)."""
        with mp.workdps(dps_rel):
            p = mp.findpoly(+v, deg, maxcoeff=mc, maxsteps=200000)
        if p is None:
            return f"d<={deg},H<={mc:.0e}: None"
        with mp.workdps(DPS_DATA + 10):
            resid = abs(mp.polyval([mp.mpf(c) for c in p], v))
        if resid < mp.mpf(10) ** (-(DPS_DATA - 6)):
            return f"d<={deg},H<={mc:.0e}: ROOT of {p} (residual {mp.nstr(resid, 3)})"
        return (f"d<={deg},H<={mc:.0e}: None "
                f"(noise, height {max(abs(c) for c in p):.0e})")

    print(f"\n[A] findpoly at dps={dps_rel}: degree/height ladder "
          "(None = no relation found)")
    ladder = [(d, cap(d + 2)) for d in (2, 4, 6, 8)]
    for name, v in K.items():
        hits = [findpoly_verified(v, deg, mc) for deg, mc in ladder]
        print(f"  {name:<16} " + " | ".join(hits))

    # the cautionary near-miss
    with mp.workdps(work):
        print(f"\n  near-miss: |V_min - 22/23| = "
              f"{mp.nstr(abs(K['K5 = V_min'] - mp.mpf(22) / 23), 3)}"
              "   (visible at 7 digits, dead at 50)")

    # --- B. linear relations over a standard basis ---------------------------
    # two regimes: a small basis with a large height cap, and the full
    # basis with a small cap, so that (n-1)*log10(height) stays well
    # below the working precision in both runs.
    basis = {
        "pi": mp.pi, "e": mp.e, "log2": mp.log(2), "gamma": mp.euler,
        "Omega": mp.lambertw(1), "e^(1/e)": mp.exp(mp.exp(-1)),
        "ReL": mp.re(L), "ImL": mp.im(L),
    }
    print(f"\n[B1] PSLQ over [1, K, pi, e], dps={dps_rel}, maxcoeff={cap(4):.0e}")
    for name, v in K.items():
        pslq_verified([mp.mpf(1), v, mp.pi, mp.e], cap(4), name)
    print(f"\n[B2] PSLQ over [1, K, {', '.join(basis)}], "
          f"dps={dps_rel}, maxcoeff={cap(2 + len(basis), hard=7):.0e}")
    for name, v in K.items():
        pslq_verified([mp.mpf(1), v] + list(basis.values()),
                      cap(2 + len(basis), hard=7), name)

    # --- C. multiplicative relations (PSLQ over logs) ------------------------
    log_basis = [mp.mpf(1), mp.log(2), mp.log(mp.pi), mp.log(mp.lambertw(1)),
                 mp.re(L), mp.im(L)]
    print(f"\n[C] PSLQ over [log K, 1, log2, log pi, log Omega, ReL(=log|L|), ImL"
          f"(=arg L)], dps={dps_rel}, maxcoeff={cap(1 + len(log_basis), hard=9):.0e}")
    for name, v in K.items():
        if v <= 0:
            continue
        pslq_verified([mp.log(v)] + log_basis, cap(1 + len(log_basis), hard=9), name)

    # --- D. relations inside the K-family ------------------------------------
    print(f"\n[D] PSLQ across [1, K1..K7], dps={dps_rel}, "
          f"maxcoeff={cap(8, hard=9):.0e}")
    pslq_verified([mp.mpf(1)] + list(K.values()), cap(8, hard=9), "K-family")

    print("\nsummary: every search above that prints None excludes integer")
    print("relations up to the stated degree/height at the stated precision.")


if __name__ == "__main__":
    main()
