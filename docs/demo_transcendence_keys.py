"""Companion demo for essay-transcendence-keys-zh.md.

Part 1 — the metal detector that found new mathematics: PSLQ rediscovers
the BBP formula for pi (found by machine in 1995, published as
Bailey-Borwein-Plouffe 1997).

Part 2 — a key that reaches: Omega = W(1), the expansion point of
semi_exp's first method, is provably transcendental via Lindemann
(Omega * e^Omega = 1); we anchor the identity numerically.

Run:  python3 docs/demo_transcendence_keys.py
"""

import mpmath as mp


def main():
    with mp.workdps(60):
        # --- Part 1: rediscover BBP -------------------------------------
        xs = [mp.nsum(lambda k, j=j: 1 / (mp.mpf(16) ** k * (8 * k + j)),
                      [0, mp.inf]) for j in range(1, 9)]
        rel = mp.pslq([mp.pi] + xs, maxcoeff=100, maxsteps=20000)
        print("PSLQ integer relation:", rel)
        resid = rel[0] * mp.pi + mp.fsum(r * x for r, x in zip(rel[1:], xs))
        print("residual at 50+ digits:", mp.nstr(abs(resid), 3))
        c = [-r for r in rel[1:]]
        terms = " ".join(f"{c[j]:+d}/(8k+{j + 1})" for j in range(8) if c[j])
        print(f"\n  =>  pi = sum_k (1/16^k) * [ {terms} ]")

        # --- Part 2: a constant the keys DO reach -----------------------
        om = mp.lambertw(1)
        print("\nOmega = W(1) =", mp.nstr(om, 30))
        print("|Omega*e^Omega - 1| =", mp.nstr(abs(om * mp.exp(om) - 1), 3))
        # transcendence in three lines: e^Omega = 1/Omega; if Omega were
        # algebraic, Lindemann makes e^Omega transcendental while 1/Omega
        # stays algebraic -- contradiction.


if __name__ == "__main__":
    main()
