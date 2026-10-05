"""Lambda law: exact (1, eta) parametrisation by the multiplier, and the
normalised first Fourier coefficient of the periodic difference.

For 1 < b < eta the attracting fixed point L of E(w) = b^w satisfies L = b^L,
and the multiplier is lam = L log b.  Eliminating b:

    log L = L log b = lam   =>   L = e^lam,   log b = lam * e^(-lam).

So the whole family is parametrised by lam in (0, 1), with lam -> 1 the
parabolic (saddle-node) limit b -> eta.  The strip height available to the
1-periodic difference P is h = 2*pi/|log lam| (the imaginary period of the
regular superfunction), hence the scale

    Lambda = exp(-2*pi*h) = exp(4*pi^2 / log lam).

This script prints the exact quantities and normalises the four measured
|E| values by |R'(1/2)|, which is the factor relating D = K - R to P.
"""

from __future__ import annotations

import sys

import mpmath as mp

sys.path.insert(0, "/Volumes/dream/halfexp/kneser/src")

from kneser._regular import engine  # noqa: E402

mp.mp.dps = 40

ETA = mp.e ** (1 / mp.e)


def lam_of_base(b):
    """Solve log b = lam * exp(-lam) for the attracting branch lam in (0,1)."""
    t = mp.log(b)
    return mp.findroot(lambda x: x * mp.exp(-x) - t, mp.mpf("0.5"))


def base_of_lam(lam):
    return mp.exp(lam * mp.exp(-lam))


def report(b, Eabs=None, label=""):
    lam = lam_of_base(b)
    L = mp.exp(lam)
    h = 2 * mp.pi / abs(mp.log(lam))
    Lam = mp.exp(4 * mp.pi**2 / mp.log(lam))
    eng = engine(mp.nstr(b, 30), 30)
    _, dR = eng.sexp(mp.mpf("0.5"), derivative=True)
    row = dict(b=b, lam=lam, L=L, h=h, Lam=Lam, dR=dR)
    if Eabs is not None:
        row["E"] = mp.mpf(Eabs)
        row["chat"] = mp.mpf(Eabs) / dR
    row["label"] = label
    return row


MEASURED = [
    ("1.05", "6.02e-3", "theta-map, 20 digits"),
    ("1.10", "1.4086e-2", "theta-map, 20 digits"),
    ("1.15", "2.280e-2", "theta-map, 20 digits"),
    (mp.sqrt(2), "7.155e-2", "Paulsen 2019, 120 digits"),
]

if __name__ == "__main__":
    print(f"eta = {mp.nstr(ETA, 12)}")
    print()
    hdr = f"{'b':>12} {'lam':>12} {'h':>10} {'Lambda':>12} {'R_(1/2)':>12} {'|E|':>11} {'|E|/R_':>11}"
    print(hdr)
    print("-" * len(hdr))
    rows = []
    for b, E, note in MEASURED:
        r = report(mp.mpf(b) if isinstance(b, str) else b, E, note)
        rows.append(r)
        print(f"{mp.nstr(r['b'], 7):>12} {mp.nstr(r['lam'], 7):>12} "
              f"{mp.nstr(r['h'], 6):>10} {mp.nstr(r['Lam'], 6):>12} "
              f"{mp.nstr(r['dR'], 7):>12} {mp.nstr(r['E'], 5):>11} "
              f"{mp.nstr(r['chat'], 5):>11}")

    print()
    print("ratios chat/lam and chat/(lam(1-lam)) etc:")
    for r in rows:
        lam = r["lam"]
        print(f"  b={mp.nstr(r['b'], 7):>9} lam={mp.nstr(lam, 6):>9} "
              f"chat={mp.nstr(r['chat'], 6):>10} "
              f"chat/lam={mp.nstr(r['chat'] / lam, 6):>10} "
              f"chat/lam^2={mp.nstr(r['chat'] / lam**2, 8):>10} "
              f"chat/(lam*|log lam|)={mp.nstr(r['chat'] / (lam * abs(mp.log(lam))), 6):>10}")

    print()
    print("saddle-node scaling near eta:  |log lam| ~ sqrt(2e(log eta - log b))")
    for db in ["1e-2", "1e-3", "1e-4", "1e-6"]:
        b = ETA - mp.mpf(db)
        lam = lam_of_base(b)
        approx = mp.sqrt(2 * mp.e * (mp.log(ETA) - mp.log(b)))
        print(f"  eta-b={db:>6}  |log lam|={mp.nstr(abs(mp.log(lam)), 8):>12} "
              f"approx={mp.nstr(approx, 8):>12}  ratio={mp.nstr(abs(mp.log(lam)) / approx, 8)}")
        print(f"          Lambda = exp({mp.nstr(4 * mp.pi**2 / mp.log(lam), 8)})")
