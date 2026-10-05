"""Periodicity of tetration in the height, regime by regime.

  1 < a < eta   : sexp is exactly periodic, P = 2*pi*i / ln(lambda), purely imaginary
  complex a in the Shell-Thron region: exactly periodic, complex P
  a > eta (Kneser): no exact period; asymptotic period 2*pi*i/log L in the
                    upper half-plane, its conjugate below, the real axis in between

Run (on a machine with spare memory):  PYTHONPATH=src python3 docs/demo_periodicity.py
"""

import mpmath as mp

import kneser
from kneser._regular import engine
from kneser._general import general_engine


def main():
    mp.mp.dps = 25
    e = engine("1.3", 20)
    P = 2j * mp.pi / e.loglam
    print("base 1.3 (regular): lambda =", mp.nstr(e.lam, 10), " P =", mp.nstr(P, 12))
    for z in [mp.mpf("0.3"), mp.mpc("1.2", "0.4"), mp.mpf("-1.5")]:
        print("   |sexp(z+P)-sexp(z)| =", mp.nstr(abs(e.sexp(z + P) - e.sexp(z)), 3),
              "  |sexp(z+P/2)-sexp(z)| =", mp.nstr(abs(e.sexp(z + P / 2) - e.sexp(z)), 3))
    g = general_engine("1j", 20)
    P = 2j * mp.pi / g.loglam
    print("base i (Shell-Thron interior): lambda =", mp.nstr(g.lam, 8), " P =", mp.nstr(P, 10))
    for z in [mp.mpf("0.3"), mp.mpc(0, 1)]:
        print("   |sexp(z+P)-sexp(z)| =", mp.nstr(abs(g.sexp(z + P) - g.sexp(z)), 3))
    L = mp.mpc("0.3181315052047641", "1.3372357014306895")
    P = 2j * mp.pi / mp.log(L)
    print("base e (Kneser): L =", mp.nstr(L, 8), " asymptotic P =", mp.nstr(P, 10))
    z = mp.mpc("0.3", "0.2")
    print("   z =", mp.nstr(z, 3), " |sexp(z+P)-sexp(z)| =",
          mp.nstr(abs(kneser.hp.sexp(z + P, dps=20) - kneser.hp.sexp(z, dps=20)), 3),
          " (not a period; decays like exp(-2 Im L * Im z) upward)")


if __name__ == "__main__":
    main()
