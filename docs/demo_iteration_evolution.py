"""Companion demo for essay-iteration-evolution-zh.md.

The whole point in one experiment: iteration alone does not explain
adaptive complexity — the third ingredient, a *selection ratchet*, does.
Both columns below iterate; they differ only in whether each round's gain
is kept. That single difference is ~34 orders of magnitude.

(Dawkins' "weasel". Its target is fixed, unlike real evolution, whose
fitness function IS the moving environment; the demo isolates one
variable — the ratchet — not a faithful model of biology.)

Run:  python3 docs/demo_iteration_evolution.py
"""

import random

TARGET = "ITERATION BECOMES EVOLUTION"
ALPHABET = " ABCDEFGHIJKLMNOPQRSTUVWXYZ"
MUT = 0.05          # per-character mutation rate
BROOD = 100         # offspring per generation


def fitness(s):
    return sum(a == b for a, b in zip(s, TARGET))


def mutate(s):
    return "".join(c if random.random() > MUT else random.choice(ALPHABET)
                   for c in s)


def main():
    random.seed(7)
    L = len(TARGET)

    # iteration + variation + SELECTION (cumulative): keep the fittest child
    parent = "".join(random.choice(ALPHABET) for _ in range(L))
    gen = 0
    while parent != TARGET:
        gen += 1
        best, bf = parent, fitness(parent)
        for _ in range(BROOD):
            child = mutate(parent)
            f = fitness(child)
            if f > bf:
                best, bf = child, f
        parent = best
        if gen in (1, 5, 15, 30) or parent == TARGET:
            print(f"  gen {gen:>3}: {parent!r}  fitness {bf}/{L}")

    trials = gen * BROOD
    blind = 27 ** L
    print(f"\ncumulative selection: {gen} generations x {BROOD} = {trials} trials")
    print(f"blind iteration (no selection): expected ~27^{L} = 10^{len(str(blind))-1} trials")
    print(f"ratio: about 10^{len(str(blind)) - 1 - len(str(trials))}")
    print("\nBoth columns iterate. The gap is the ratchet: selection.")


if __name__ == "__main__":
    main()
