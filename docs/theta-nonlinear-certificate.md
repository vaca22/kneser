# Nonlinear finite theta-map certificate

Follow-up: the fixed discrete map now also has a certified infinite Taylor
extension on the normalized real Wiener space, with q<0.054816 and distance
<7.244e-39. See the [infinite discrete certificate](theta-infinite-discrete-certificate.md).
The continuous ideal operator and true-Kneser identification remain open.

2026-09-12. This report supersedes the *nonlinear arithmetic and branch* gaps
of the earlier candidate runs only for the fresh runs named below. It does not
retroactively certify the old `out2/out4` data, and does not prove distance to
Kneser's actual function.

## 1. Precisely stated object

For fixed parameters `(D,nt,delta,n_modes,nf,n_circ)`, let `P_c(z)` be the
polynomial with real coefficients c, with `c0=1`. Define T by the four steps
in `theta-contraction.md` §1: inverse regular-function samples on
`t_j+i delta`, finite Fourier projection, arc/functional-equation-band values
on the unit circle, and the finite Cauchy coefficient projection, replacing
output coefficient zero by 1.

In the certified mathematical map, sample fractions are exact rational
numbers, delta is the exact binary64 value supplied by `BuildParams` (the
value conventionally displayed as 0.1), and unit-circle points are exact
roots of unity. Cardinal roots are set to ±1, ±i exactly. The fixed point L
is **the unique root in the saved interval box**, as certified by a Krawczyk
inclusion with a nonsingular exact dyadic preconditioner. No global uniqueness
claim about roots of exp(L)=L in the upper half-plane is made.

The scalar evaluator enforces the same arc/band choices as the builder,
certifies their separation, and fixes all nearest-integer unwrap decisions
throughout the coefficient ball. This is an exact-arithmetic finite map
modeled on the builder, not a statement that a finite-precision program is a
contraction on floating-point states.

For an exact rational `0<r<1`, use

\[
 \|h\|_r=\sum_{k=0}^{nt-1}|h_k|r^k,\qquad
 B=\{c:c_0=1,\ \|c-P\|_r\le R\}.
\]

All coefficient boxes used to enclose B have `c0=1` exactly and
`|c_k-P_k|≤R/r^k` for k≥1. This box can be larger than B; that only makes the
bounds conservative.

## 2. What has changed since the candidate certificate

1. `theta_ball.py` uses a circular enclosure D(c,r). Every centre operation
   is evaluated on singleton directed intervals; an exact dyadic corner of
   the resulting rectangle is chosen as centre and the upward diagonal is
   added to the radius. Analytic image-radius bounds are also evaluated
   with directed interval operations. There is no empirical ulp inflation.
2. `theta_branch.py` checks the distance of every principal-log argument to
   zero and to the closed negative real ray. It proves every unwrap quotient
   lies strictly inside the chosen half-integer cell, and applies the shifts
   before the next stage. The point and ball passes use the same shifts.
3. `theta_certify.py` assembles complex Jacobian factors using FLINT/Arb
   matrix arithmetic. It does not use the earlier NumPy/gamma error model.
   Exact dyadic disc centres/radii are converted to rectangular Arb balls;
   all matrix products and divisions remain enclosures.
4. Final matrix endpoints, componentwise point-defect bounds, weights and
   comparisons are converted to exact rational arithmetic. The independent
   `check_theta_certificate.py` recomputes the norm and self-mapping test,
   and checks recorded root, geometry, log and unwrap inequalities.

The trusted numerical base is [mpmath interval arithmetic](https://mpmath.org/doc/current/contexts.html#arbitrary-precision-interval-arithmetic-iv) and [FLINT/Arb](https://python-flint.readthedocs.io/en/latest/arb_mat.html),
plus the stated elementary circular-enclosure formulas and chain rule. This
is a computer-assisted interval proof, not a proof-assistant formalization
of those libraries. mpmath documents interval support as experimental; this
implementation uses elementary operations with explicit enclosure formulas,
not arbitrary high-level mpmath routines. Tests compare the scalar backend with independent FLINT
Acb evaluation and exercise rejection of invalid branches; they support the
implementation audit but do not replace enclosure formulas.

The checker verifies the saved inequalities and their consistency. It does
not independently reconstruct every elementary exp/log enclosure from a full
arithmetic trace. Re-running the evaluator from the saved source snapshots
is the reproduction path for that part of the proof.

## 3. Fixed-point theorem applied by the verifier

Let `[J_ij]` enclose `∂T_i/∂c_j` uniformly on B. Principal-log separation,
geometry separation and unwrap stability make T continuously differentiable
on a neighborhood of B. Define

\[
 q=\max_{1\le j<nt}\sum_i\sup|[J_{ij}]|r^{i-j},\qquad
 \eta\ge\|T(P)-P\|_r.
\]

Column zero may be omitted because every admissible tangent has h0=0.
Earlier runs that include column zero give a valid but more conservative
bound. If

\[
 q<1,\qquad \eta+qR<R,
\]

then the mean-value integral gives `||T(c)-T(d)||≤q||c-d||` on B and
`||T(c)-P||≤eta+qR<R`. Banach's theorem yields one and only one fixed point
c* **in B**, with

\[
 \|P-c^*\|_r\le\eta/(1-q),\qquad
 \sup_{|z|\le r}|P(z)-P_{c^*}(z)|\le\eta/(1-q).
\]

The result concerns the polynomial associated to that finite fixed point.
It does not say that polynomial solves the tetration equation exactly, or
that it is the Taylor polynomial of the true Kneser solution.

## 4. Completed runs

The first end-to-end run used base e, digits-12 builder parameters:
D=95, nt=48, nf=124, n_modes=52, n_circ=256; interval precision 100 decimal
digits, matrix precision 100 bits, r=1/2, R=1e-8. Its exact-rational checker
passed, including source hashes. Outward-rounded readable bounds are

\[
 q<0.425833,\qquad \eta<2.318\cdot10^{-14},\qquad
 \|P-c^*\|_{1/2}<4.037\cdot10^{-14}.
\]

This run retained input column zero. The full rational values and all
witnesses are in `smoke/certificate.json`, not inferred from these rounded
display numbers. The source snapshot is under `smoke/sources/`.

### 4.1 Shipped 50-digit base-e table, r=1/2

The fresh run used D=370, nt=150, nf=404, n_modes=192, n_circ=600,
interval precision 210 decimal digits, matrix precision 100 bits, and
R=1e-50. Both evaluator and independent checker passed. Readable outward
bounds are

\[
 q<0.425422,\qquad \eta<3.555\cdot10^{-52},\qquad
 \|P-c^*\|_{1/2}<6.187\cdot10^{-52}.
\]

This is the first completed fresh 50-digit **nonlinear ball** certificate in
this project. It validates the finite-dimensional hypotheses that were only
candidates in the previous report. It still includes input column zero in
its norm and hence is conservative on the normalized affine space.

The proof data and source snapshot are in
`docs/_generated/goal3-rigorous/e50-rhalf/` (`certificate.json`, `check.log`,
`rejection-tests.log`, `run.log`, `sources/`). Scalar point and ball passes
took about 399 and 393 seconds, and factor assembly/matrix evaluation another
105 seconds on galic. The first driver version did not explicitly assert
that the Krawczyk centre belongs to its box; the independent checker
verified that premise directly from the saved exact centre and box before
accepting this certificate. Its original executed source was preserved
without mutation; later versions add that assertion at evaluation time.

### 4.2 Shipped 50-digit base-e table, r=11/20

The second full run used the same discrete parameters, 180 decimal digits,
100 matrix bits, and the exact rational weight r=11/20, with R=1e-48.
It uses only input columns j≥1, as appropriate to c0=1. Both the complete
interval evaluation and the independent exact checker passed:

\[
 q<0.054816,\qquad \eta<4.336\cdot10^{-52},\qquad
 \boxed{\|P-c^*\|_{11/20}<4.588\cdot10^{-52}.}
\]

The last bound is recomputed from the full rational witness, rather than
obtained by dividing the separately rounded display bounds. It applies
uniformly to polynomial values for |z|≤11/20. The certified ball has radius
1e-48; the point defect plus q times that radius is strictly smaller than
its radius. All principal-log and unwrap decisions were verified across
this ball, not only at P. The ball pass checked 149,904 principal-log
arguments; the smallest certified cut-distance margin exceeds 0.1088.
All unwrap shifts are zero, with minimum half-integer-cell margin exceeding
0.4996. These readable lower bounds are rounded downward from the witnesses.

Witnesses are in `docs/_generated/goal3-rigorous/e50-r055/`. The point and
ball passes took about 390 and 372 seconds, with another 100 seconds for
factor assembly/matrix evaluation. `certificate.json` contains the exact
rational q, eta and distance, the entire interval Jacobian, fixed-root box,
geometry and branch evidence, coefficients, runtime versions and source
hashes. `sources/` was frozen at the start of execution.

The large improvement in q compared with §4.1 is mainly due to excluding
the inadmissible c0 perturbation, not a claim that changing the weight alone
improves the full-space norm. Different norms also give different point
defects, so the two eta values should not be compared as if they were the
same quantity.

**Disposition:** the finite-dimensional nonlinear version of M3.3 is now
completed for the stated base-e map and neighborhoods. M3's original
true-Kneser error target is not completed.

## 5. Why this is not yet the true-function error certificate

The finite map discards Taylor modes, truncates regular exp/log chains, and
uses two discrete Fourier/Cauchy projections. None of those approximations
vanishes merely because T has a unique local fixed point. Identification of
an ideal fixed point with Kneser's normalized solution remains a separate
mathematical requirement.

The norm r=1/2 also fails an important infinite-dimensional prerequisite:
`|±1/2+i delta|>1/2`, so sampling is not a continuous functional on the
corresponding infinite coefficient space. The completed r=11/20 run addresses that
geometric prerequisite for the finite certificate; it cannot by itself
establish infinite-dimensional contraction or identify the fixed point.
See `theta-ideal-operator.md` for the input/output tail formulas, the
nonperiodic-theta obstruction to unjustified exponential Fourier error
bounds, and the remaining normalization/gluing issue.

Paulsen–Cowgill already had a fast high-accuracy tetration algorithm in
2017. High precision or a numerical contraction rate alone is not a new
research claim. A complete, independently reproducible true-function error
certificate would be the stronger target; no priority claim is made here.

## 6. Reproduction and validation scope

Run numerical work on galic only. The driver needs `mpmath`, `numpy` (for
legacy module import) and `python-flint`; the actual verified matrix path
uses FLINT rather than NumPy. The runtime and executed source hashes are
stored by current driver versions, with an immutable source copy in each
output directory.

```sh
cd /data/kneser-exp/goal3-rigorous/w55
PYTHONPATH=/data/kneser-verify/src python3 -u theta_certify.py \
  --base e --digits 50 --dps 180 --weight 11/20 --radius 1e-48 --out out
python3 check_theta_certificate.py out/certificate.json --sources out/sources
```

Before claiming success, check both evaluator exit status and the independent
checker. Failed runs must remain failed. The checker deliberately rejects
modified q, broken c0 normalization, mismatched unwrap shifts, missing root
axes and missing log coverage; these rejection tests were run against the
completed preliminary certificate.
