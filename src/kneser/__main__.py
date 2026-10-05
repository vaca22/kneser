"""Command-line interface.

    python -m kneser 0.7              f(0.7) where f(f(x)) = e^x
    python -m kneser --sexp 0.5       tetration base e
    python -m kneser --sexp 2.5 --base 2  tetration base 2
    python -m kneser --slog 2.0       super-logarithm
    python -m kneser --iter 0.25 2.0  exp^[0.25](2.0)
    python -m kneser --digits 50 0.7  any of the above at 50 digits
    python -m kneser --table          values of f on [0, 1]
    python -m kneser --verify         residual check of f(f(x)) = e^x
"""

from __future__ import annotations

import argparse
import math
import sys


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(
        prog="python -m kneser",
        description="Kneser's half-exponential f (f(f(x)) = e^x) and friends")
    ap.add_argument("x", nargs="?", type=str, help="evaluate f(x)")
    g = ap.add_mutually_exclusive_group()
    g.add_argument("--sexp", metavar="Z", help="tetration sexp(Z)")
    g.add_argument("--slog", metavar="X", help="super-logarithm slog(X)")
    g.add_argument("--iter", nargs=2, metavar=("T", "X"), help="iterate x -> base**x T times starting at X")
    g.add_argument("--table", action="store_true", help="print f on [0, 1]")
    g.add_argument("--verify", action="store_true",
                   help="max |f(f(x)) - base**x| over a grid")
    ap.add_argument("--base", default="e",
                    help="exponential base: 'e', 2, or any real > 1 except e^(1/e) (default: e)")
    ap.add_argument("--prepare", type=int, metavar="DIGITS",
                    help="build/cache the table for --base at DIGITS digits and exit")
    ap.add_argument("--digits", type=int, default=None,
                    help="use the mpmath path at this many digits")
    args = ap.parse_args(argv)

    try:
        return _run(args, ap)
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2


def _run(args, ap) -> int:
    import kneser

    d = args.digits
    base = args.base
    equation = "e^x" if base == "e" else f"{base}^x"

    if args.prepare:
        t = kneser.prepare(base, args.prepare)
        print(f"base {t.BASE}: {t.DIGITS} digits, residual {t.RESIDUAL}")
        return 0

    def bpow(x):
        return math.exp(x) if base == "e" else math.pow(float(base), x)

    def show(v):
        if d:
            import mpmath as mp
            print(mp.nstr(v, d))
        else:
            print(repr(v))

    if args.table:
        mod = kneser.hp if d else kneser
        label = "exp^[1/2](x)" if base == "e" else f"({base}^x)^[1/2](x)"
        print(f" x      f(x) = {label}")
        for i in range(11):
            x = i / 10
            v = mod.half_exp(str(x), dps=d, base=base) if d else mod.half_exp(x, base=base)
            if d:
                import mpmath as mp
                print(f" {x:3.1f}    {mp.nstr(v, d)}")
            else:
                print(f" {x:3.1f}    {v:.15f}")
        return 0

    if args.verify:
        if d:
            import mpmath as mp
            worst = mp.mpf(0)
            skipped = 0
            with mp.workdps(d + 10):
                for i in range(-20, 21):
                    x = mp.mpf(i) / 10
                    try:
                        err = abs(kneser.hp.half_exp(kneser.hp.half_exp(x, dps=d, base=base), dps=d, base=base)
                                  - (mp.exp(x) if base == "e" else mp.power(mp.mpf(base), x)))
                    except ValueError:  # x >= alpha for a base below e^(1/e)
                        skipped += 1
                        continue
                    worst = max(worst, err)
            note = f", {skipped} grid points above the tower limit skipped" if skipped else ""
            print(f"max |f(f(x)) - {equation}| on [-2, 2] = {mp.nstr(worst, 3)}  (dps={d}{note})")
        else:
            worst = 0.0
            skipped = 0
            for i in range(-20, 21):
                x = i / 10
                try:
                    err = abs(kneser.half_exp(kneser.half_exp(x, base=base), base=base) - bpow(x))
                except ValueError:  # x >= alpha for a base below e^(1/e)
                    skipped += 1
                    continue
                worst = max(worst, err)
            note = f", {skipped} grid points above the tower limit skipped" if skipped else ""
            print(f"max |f(f(x)) - {equation}| on [-2, 2] = {worst:.3e}  (float64{note})")
        return 0

    if args.sexp is not None:
        show(kneser.hp.sexp(args.sexp, dps=d, base=base) if d else kneser.sexp(float(args.sexp), base=base))
    elif args.slog is not None:
        show(kneser.hp.slog(args.slog, dps=d, base=base) if d else kneser.slog(float(args.slog), base=base))
    elif args.iter is not None:
        t, x = args.iter
        show(kneser.hp.exp_iter(x, t, dps=d, base=base) if d
             else kneser.exp_iter(float(x), float(t), base=base))
    elif args.x is not None:
        show(kneser.hp.half_exp(args.x, dps=d, base=base) if d else kneser.half_exp(float(args.x), base=base))
    else:
        ap.print_help()
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
