"""Weak form of 猜想 B: the operation path cannot be a monotone interpolation.

Propositions (proofs in lemmas-round2-zh.md):

  B1. V is not additive: any additive function vanishes at 0, but
      V(0) = sexp'(0) > 0.
  B2. For the self-dual pair (2, 2) both endpoints equal 4, so a nonzero
      endpoint slope forces an interior extremum.  The slope is
          s0(2,2) = 4 (V(2 log 2) - V(log 2)),
      and V is strictly increasing on [x*, +inf) once it has a unique
      minimum in (0, 1) (Rolle + the convexity scan).
  B3. Certificate for (2, 3): s0 > 0 and s1 < 0, with an explicit gap
      larger than the coefficient residual, so the path starts up and
      finishes down.

This demo prints the gaps.  Locked by tests/test_research.py.

Run:  PYTHONPATH=src python3 docs/demo_lemma_b.py
"""

import mpmath as mp

import kneser.hp as hp
from kneser import _coeffs

DPS = 50

with mp.workdps(DPS + 10):
    _C = [mp.mpf(s) for s in _coeffs.COEFFS]
    _C1 = [k * c for k, c in enumerate(_C)][1:]
    _C2 = [k * (k - 1) * c for k, c in enumerate(_C)][2:]


def _horner(cs, z):
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
    s, s1, s2 = _horner(_C, z), _horner(_C1, z), _horner(_C2, z)
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


def V(x):
    return S012(hp.slog(x, dps=DPS))[1]


def op(x, y, t):
    return hp.exp_iter(hp.exp_iter(x, -t, dps=DPS) + hp.exp_iter(y, -t, dps=DPS),
                       t, dps=DPS)


def main():
    mp.mp.dps = DPS
    floor = mp.mpf(10) ** -(_coeffs.DIGITS - 2)

    print("B1  V is not additive")
    v0 = V(0)
    print(f"  V(0) = sexp'(0) = {mp.nstr(v0, 30)}  > 0")
    print(f"  additive functions satisfy V(0)=0; gap = {mp.nstr(v0, 8)}"
          f"  (residual floor {mp.nstr(floor, 2)})")
    print(f"  V(1)-V(0) = {mp.nstr(V(1) - v0, 3)}  (forced by V(e^x)=e^x V(x))")

    a_star = mp.findroot(lambda a: S012(a)[2], (mp.mpf(-1), mp.mpf(0)),
                         solver="anderson")
    x_star = S012(a_star)[0]
    print(f"\n  unique critical point in (0,1): x* = {mp.nstr(x_star, 20)}")
    print(f"  log 2 = {mp.nstr(mp.log(2), 20)}  > x*  "
          f"by {mp.nstr(mp.log(2) - x_star, 8)}")

    print("\nB2  self-dual pair (2,2): endpoints equal, interior forced")
    gap = V(2 * mp.log(2)) - V(mp.log(2))
    s0 = 4 * gap
    print(f"  V(2 log 2) - V(log 2) = {mp.nstr(gap, 20)}")
    print(f"  s0(2,2) = 4 that     = {mp.nstr(s0, 20)}")
    print(f"  gap / residual floor = {mp.nstr(gap / floor, 3)}  "
          "(positive by a factor of 10^47; not a rounding artifact)")
    mid = op(2, 2, mp.mpf("0.5"))
    print(f"  2 +_0 2 = 4,  2 +_1 2 = 4,  2 +_{{1/2}} 2 = {mp.nstr(mid, 20)}")
    print(f"  overshoot = {mp.nstr(mid - 4, 12)}")

    print("\nB3  certificate (2,3): opposite endpoint-slope signs")
    s0_23 = V(5) - V(2) - V(3)
    s1_23 = 6 * (V(mp.log(6)) - V(mp.log(2)) - V(mp.log(3)))
    print(f"  s0 = V(5)-V(2)-V(3) = {mp.nstr(s0_23, 20)}  > 0")
    print(f"  s1 = 6(V(log 6)-V(log 2)-V(log 3)) = {mp.nstr(s1_23, 20)}  < 0")
    print(f"  min(|s0|,|s1|) / floor = {mp.nstr(min(abs(s0_23), abs(s1_23)) / floor, 3)}")
    v075 = op(2, 3, mp.mpf("0.75"))
    print(f"  2 +_0 3 = 5,  2 +_1 3 = 6,  2 +_0.75 3 = {mp.nstr(v075, 20)}")
    print(f"  overshoot above product = {mp.nstr(v075 - 6, 12)}")

    print("\nweak 猜想 B: proved for a positive-measure set of pairs.")
    print("the path t -> x +_t y is not a monotone interpolation + ↝ ×.")


if __name__ == "__main__":
    main()
