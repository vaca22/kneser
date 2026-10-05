# External validation: this library against fatou.gp

Every other check in this repository is *internal*. `--verify` measures the
residual `|f(f(x)) - e^x|`; `docs/error-certificate.md` bounds the seam defect
with interval arithmetic; the theta certificates bound the contraction. All of
them answer "does this table solve the functional equation?". None of them
answers "is this table Kneser's solution?" — the last section of
`error-certificate.md` says so explicitly: the Abel function still carries the
theta degree of freedom, so a small residual is compatible with a different
solution.

This document closes that gap from the outside, by comparing against an
implementation that shares no code, no language, and no author with ours.

## 1. The reference

`tests/data/external_reference.json` is a curated subset of

    https://github.com/Lightrunnerwastaken/gp-tetration
    -> research/reference/values.json   (meta.generated 2026-07-10)

announced on the Tetration Forum in
[*Mixed-base tetration: five preprints, a faster fatou.gp fork, and a
base-change calculator*](https://tetrationforum.org/showthread.php?tid=1824)
(Janis, forum handle "Lightrunner", July 2026). The values are computed in
PARI/GP with an optimised fork of Sheldon Levenstein's `fatou.gp`, which is the
community's reference implementation of Kneser's construction
([thread](https://tetrationforum.org/showthread.php?tid=1017)). Upstream pairs
each run with a second run at higher precision ("Fehler-Vektor") and records
how many digits that pair proves; the entries we use are proven to 99, 194 or
more digits.

Nothing about that pipeline resembles ours: they build Schroeder functions at
both fixed points in PARI and iterate two theta mappings numerically at ~500
digits; we build a single Taylor table by the contraction in `kneser.build` and
bake it. Agreement is therefore evidence about the *solution*.

## 2. What agrees

`tests/test_external_reference.py`, 16 grid points per row
(`x = -0.4375, -0.3125, ..., 1.4375` for `sexp`, `x = 1.25, 1.5, ..., 5.0` for
`slog`), worst relative deviation:

| function | base | our table | worst rel. deviation |
| --- | --- | --- | --- |
| `sexp` | e | baked, 50 digits | `1.1e-52` |
| `slog` | e | baked, 50 digits | `1.5e-52` |
| `sexp` | 2 | baked, 50 digits | `5.2e-53` |
| `slog` | 2 | baked, 50 digits | `7.6e-53` |
| `sexp` | 10 | built on first use, 17 digits | `1.5e-19` |
| `slog` | 10 | built on first use, 17 digits | `6.6e-20` |

and at the one deeply computed point,

    sexp_e(1/2) vs the 200/500/700/1000-digit entries   agrees to > 52 digits
    sexp_2(1/2) vs the 200-digit entry                  agrees to > 52 digits

So: the two baked tables are Kneser's solution to the full 50 digits they
claim, confirmed against an independent construction — and the on-demand
builder (`kneser.build`, exercised here on base 10, which ships no table) is
right to *better* than its nominal 17 digits.

This is the first check in the repository that constrains the theta degree of
freedom rather than the residual.

## 3. What does not agree: complex bases inside the Shell–Thron region

The reference set also contains `sexp_b(1/2)` for three complex bases. We
disagree with all three:

| base | multiplier modulus at the principal fixed point | rel. deviation |
| --- | --- | --- |
| `0.8 + 0.4i` | 0.388 | `9.5e-5` |
| `1 + i` | 0.711 | `3.3e-3` |
| `2 + i` | 0.988 | `1.4e-1` |

This is not a precision problem. Our answers are converged (identical from
`dps=15` to `dps=35`), satisfy `sexp(z+1) = b^sexp(z)` to `1e-46`, and satisfy
`sexp(0) = 1`. Two superfunctions that both normalise at 0 differ by a
non-trivial 1-periodic function, and that is what this is.

The cause is a construction choice, and the forum states it plainly. All three
bases are **inside** the Shell–Thron region: the principal fixed point is
attracting (`|lambda| < 1`) and the second one is repelling. In that situation

* **we** return the regular (Koenigs/Schroeder) superfunction at the attracting
  fixed point — `_general.GeneralRegularEngine`, chosen by `hp._engine` because
  its normalisation `F(z0) = 1` succeeds. `_cbuild` explicitly refuses
  ("fixed points must both be repelling for the theta construction").
* **fatou.gp** returns the *merged two-fixed-point* solution, which it builds
  inside the region as well as outside. From sheldonison's announcement of
  `tetcomplex.gp`
  ([thread](https://tetrationforum.org/showthread.php?tid=729)): the program
  "figures out if they're both repelling, or if one of them is attracting",
  then builds both Schroeder functions and two theta mappings either way, and
  "for bases at the real axis > eta, this is mathematically identical to my
  Kneser tetration algorithm". In the same thread he notes the visible
  consequence inside the region: the attracting fixed point is periodic, so the
  merged solution has *repeated* singularities rather than the single cut at
  `z = -2`.

The deviation growing with `|lambda|` fits: as the base approaches the
Shell–Thron boundary the two solutions' periods collide and the 1-periodic gap
between them stops being exponentially small.

### Confirming the diagnosis, and the `solution=` keyword

`_cbuild` already had the machinery: `build_complex(..., allow_attracting=True)`
admits one attracting fixed point (added for
`docs/paulsen-continuation-zh.md`). It had simply never been reachable from the
public API, and had never been compared to anything outside this repository.
Seeded from the regular solution it converges at base `1 + i` and lands on

    fatou.gp        1.2623631316171 + 0.4705989028950 i
    merged (ours)   1.2623631316173 + 0.4705989028966 i     rel  1.2e-12
    regular (ours)  1.2638138645967 + 0.4747668681784 i     rel  3.3e-3

so the merged solution agrees to its own residual floor (`2.8e-12`) and the
diagnosis is settled: the gap is the construction, not the accuracy.

`sexp` therefore now takes a `solution` keyword on both the float64 and the
`hp` path:

```python
>>> kneser.sexp(0.5, base="1+1j")                      # 'auto': regular
(1.2638138645966965+0.4747668681784409j)
>>> kneser.sexp(0.5, base="1+1j", solution="kneser")   # merged, = fatou.gp
(1.2623631316173458+0.47059890289657025j)
```

`"auto"` (the default) keeps the previous behaviour; `"kneser"` always uses the
merged two-fixed-point construction; `"regular"` always uses the Koenigs one.
The merged tables are cached separately (`cbaseA-*.json`), because inside the
region they are a different function from anything under `cbase-*.json`.

Limits, measured: `1 + i` works (~20 s for 10 digits). `2 + i` is refused —
`|lambda| = 0.988` is inside the ±0.02 neutral band around the Shell–Thron
boundary, where neither fixed point gives a usable hyperbolic superfunction.
`0.8 + 0.4i` fails with "theta iteration diverging" from every parameter
setting we tried, even from the regular seed; §5 has the diagnosis. That is why
`"auto"` stays on the regular solution: the merged one is not yet available
everywhere the regular one is.

### Outside the region: the first external check of `_cbuild`

No published value covers a base with both fixed points repelling, which is
`_cbuild`'s main path. Running `fatou.gp` locally (`read("fatou.gp");
sexpinit(3+2*I); sexp(0.5)`; ten minutes at `\p 40`, about six at `\p 30`)
gives three:

| base | our 8-digit table | agreement |
| --- | --- | --- |
| `3 + 2i` | residual `9.5e-10` | `2.0e-10` |
| `2 + 2i` | residual `4.4e-10` | `1.4e-10` |
| `-1 + i` | residual `8.9e-10` | `2.2e-10` |

So the complex-base Kneser continuation is confirmed from the outside, to the
accuracy each table claims. `-1 + i` is the useful one: `_cbuild` picks a sheet
there (`docs/base-plane-zh.md` §4 could only pin it down by conjugation
symmetry, "the sheet reached from the upper half of the base plane"), and it is
`fatou.gp`'s sheet — the conjugate value is 1.5 away.

Bases with negative imaginary part are a different story: `sexpinit(3-2*I)` at
`\p 30` had still not converged long after `2+2i` and `-1+i` had each finished
in six minutes at the same precision, which matches sheldonison's own note that
the program "works best with imag(base)>0".

The values are stored under `local` in `tests/data/external_reference.json`
with the exact commands and the `fatou.gp` hash used.

## 4. A defect in the reference set

`sexp|2|0.5|1000` upstream disagrees with upstream's own `sexp|2|0.5|200` and
`sexp|2|0.5|500` from digit 44 on:

    ours (50 digits)  1.458781816036421700683971661038587135296606605330907102
    upstream 200/500  1.458781816036421700683971661038587135296606605330907141
    upstream 1000     1.458781816036421700683971661038587135296604326403002207

The 200- and 500-digit entries agree with each other in full (upstream records
the 200-digit one as proven to 194 digits) and with our independent table to 53
digits, so the 1000-digit entry is the outlier, not ours. Note that upstream's
`meta` claims verification only for the corrected entries; the base-2
1000-digit run is not among them. The base-e 1000-digit entry is fine (it
extends the 200/500/700 entries consistently).

`tests/test_external_reference.py::test_known_bad_upstream_entry_is_still_bad`
asserts the defect, so it will fail loudly if upstream republishes the value.
Worth reporting in the forum thread.

## 5. What the forum says about `fatou.gp`'s own limits

Read before trusting any comparison above beyond its stated accuracy. Sources:
the `fatou.gp` thread
([tid=1017](https://tetrationforum.org/showthread.php?tid=1017), 4 pages,
2015–2026) and the `tetcomplex.gp` thread
([tid=729](https://tetrationforum.org/showthread.php?tid=729)).

**Inside the Shell–Thron region it really is the Kneser continuation.** This
was disputed on the forum and then settled. JmsNxn first wrote (tid=1017 p.3)
that "this program does not produce Kneser as a mathematical object within the
interior", then retracted two days later: "I thought it'd run the Schroder for
`i`, didn't realize it ran the kneser algorithm. […] for `1 < b < eta` Sheldon's
algorithm runs a kneser algorithm which roughly approximates the Schroder
iteration. But for complex values it runs the Kneser iteration, as an analytic
continuation." Our measurement in §3 is an independent confirmation of the
corrected version: at base `1 + i` the merged construction reproduces `fatou.gp`
to `1.2e-12` and the regular one is `3.3e-3` away.

**Near the Shell–Thron boundary `fatou.gp` loses most of its precision.**
sheldonison, tid=1017 p.1: "For bases near the Shell Thron boundary, where the
imag(pseudo-period) is small, there is no theta mapping, so convergence is much
slower", and "there are bases near the Shell Thron boundary where there's no
theta mapping. Without a theta mapping, you only get 15-16 decimal digits of
precision in fatou.gp." Of the three published complex-base values, `2 + i` has
`|lambda| = 0.988` — by far the closest to the boundary — and it is also the one
we disagree with most (`0.14`), so this was the obvious thing to suspect.

We checked it, and the suspicion is wrong. Running `sexpinit(2+I)` ourselves at
`\p 30` and again at `\p 45` gives

    \p 30   1.5267683457574202059961517529056
          + 0.28122500375971223304287363322222 i
    \p 45   1.52676834575742020599615175290556503868378985
          + 0.281225003759712233042873633222220583659187387 i

which agree with each other and with the published 80-digit entry to the full
45 digits, with `sexp(0) = 1` to `5e-57`. So `fatou.gp` is not degrading at
`2 + i`, and the `0.14` gap is a genuine difference of solution, exactly as at
the other two bases — not noise near the boundary. (Reproducibility across
precisions still does not by itself say *which* solution a program converged
to; that is what §3's merged-vs-regular comparison settles.)
`setmaxconvergence()` before `sexpinit` is sheldonison's own remedy for bases
whose pseudo-period is close to 2, should a base ever actually need it.

**Bases with `imag(base) < 0` are deliberately unsupported.** sheldonison
disabled them ("it turns out its a harder problem, so I can't get the sexp(z) to
work for those upside down bases") and gives a conjugate wrapper instead:
`sexpinit(conj(b))` then `conj(sexp(conj(z)))`. That is why `sexpinit(3-2*I)`
above never returned — do not retry it, wrap the conjugate instead. It also
corroborates our own convention for negative real bases ("the sheet reached
from the upper half of the base plane"; docs/base-plane-zh.md §4).

**There is a linear-solve alternative to iterating theta.** `matrix_ir(B, lctr,
ltht, myctr, myir)` solves in one shot the same system that `sexpinit` reaches
by iteration — "loop1 will converge to the exact same solution as matrix_ir
generates" — with `lctr` Taylor samples, `ltht` theta samples, `myctr` the
sampling-circle radius ratio and `myir` the inner-circle ratio. sheldonison
reports 35 digits from a 112×112 matrix for base e, and gives settings that
rescue bases where the iteration struggles, e.g.
`matrix_ir(0.2*I,400,90,14/15,45/46)` and
`matrix_ir(0.15,400,90,14/15,45/46)`. This is the obvious next thing to try for
our own failure below.

### Our remaining failure at `0.8 + 0.4i`, diagnosed

`build_complex(..., allow_attracting=True)` will not converge there, and it is
not a tuning problem. Measured: it fails identically for `idelta` in
{0.05, 0.1, 0.2, 0.3} crossed with `idelta_dn` in {0.02, 0.05, 0.3, 0.5}, and
for `nt`/`n_circ` raised from 48/256 to 160/1024 (`build_complex` now takes
`nt` and `n_circ` so this is reproducible).

The trace says where it goes wrong. The regular seed enters with residual
`5.3e-20` — i.e. the residual functional does **not** separate the two
solutions, both satisfy it — and the first pass throws it to `3.7e-5`. On the
lower (repelling, `|lambda| = 3.385`) side the diagnostics show `|theta_dn|`
around `2.97`, comparable to that side's period `-2.50 + 3.20i`, with a
periodicity wrap defect of `6e-3` that never shrinks. So the lower theta is
sitting on the wrong sheet of the Abel function by roughly a full period, which
is the failure mode already recorded for `isuperf` in
docs/base-plane-zh.md §4 — not a sampling or step-size issue. Fixing it means
reworking the lower-side branch continuation, or replacing the iteration with
the `matrix_ir`-style linear solve above.

## 6. Reproducing

```console
$ PYTHONPATH=src python3 -m pytest tests/test_external_reference.py -q
```

The base-10 row builds a 17-digit table on first use (about ten seconds, then
cached under `~/.cache/kneser`); everything else is table lookups.
