# Error certificate for the shipped tables (bases e and 2)

Companion of [`demo_certificate.py`](demo_certificate.py), which computes
every number below in **interval arithmetic** (`mpmath.iv`, 80 decimal
digits, outward rounding; the decimal strings of the tables are parsed to
enclosing intervals).  The script asserts the bounds; its output is pasted
verbatim at the end.  Run on a machine with memory to spare:

```console
PYTHONPATH=src python3 docs/demo_certificate.py          # both tables, ~20 s
python3 -m pytest tests/test_certificate.py -q            # quick mode re-check, ~6 s
```

## 0. What is being certified, and what is not

The library ships a table $c_0,\dots,c_{N-1}$ of exact decimal strings
(`_coeffs.py`: $N=150$ for base $e$; `_coeffs_2.py`: $N=200$ for base 2;
$c_0 = 1$ exactly).  Write $b$ for the base, $\ell=\log b$, and

$$
P(z)=\sum_{k<N}c_k z^k,\qquad
E(w)=b^{w}=e^{\ell w},\qquad
S(z)=E^{\circ k}\bigl(P(z-k)\bigr),\quad k=\lceil z-\tfrac12\rceil ,
$$

with $E^{\circ(-1)}=\log_b$.  $S$ is exactly the function `kneser.sexp` and
`kneser.hp.sexp` compute (`_core.py`/`hp.py`: reduce $z$ into
$(-\tfrac12,\tfrac12]$, Horner, then $k$ exponentials or logarithms), up to
the floating-point evaluation error bounded in rung 1.

Everything here is a statement about $P$ and $S$.  **Nothing here bounds
the distance between $S$ and Kneser's true superexponential** $F$; section
4 explains why that gap cannot be closed from the table alone.  Until now
every precision claim in the README ("50 digits", "residual 2.6e-52") was
the single number $|P(\tfrac12)-e^{P(-1/2)}|$, evaluated in floating point.
This document replaces that with rigorous enclosures of what *is* provable,
and names what is not.

Notation: $\mathrm{Horner}$ error constants use Higham's
$\gamma_n = nu/(1-nu)$ with unit roundoff $u$.  All inequalities are
evaluated with outward rounding, so every printed bound is a true upper
bound of the exact real number it names.

## 1. Rung 1 — the polynomial $P$ and its evaluation

### 1.1 Coefficient envelope (verified for every stored $k$)

The script checks, for all $0\le k<N$,

$$|c_k|\le C_{\mathrm{env}}\,2^{-k},\qquad |c_k|\le C_{\log}\,\frac{2^{-k}}{k}\ (k\ge1),$$

and reports the smallest constants that make this true.  For base $e$,
$C_{\mathrm{env}} = 2.1835$ and $C_{\log} = 7.767$, and the last term has
$|c_{149}|\,2^{149}\cdot149 = 1.0$: the stored coefficients follow the
$2^{-k}/k$ envelope of a logarithmic singularity at $z=-2$ (where
$\mathrm{sexp}=\log\mathrm{sexp}(z+1)\to-\infty$) essentially exactly.
For base 2 the stored tail decays only like $0.53^k$ ($C_{\mathrm{env}}
= 2.2\cdot10^5$), which is an observation about that table, not a
certified property of $\mathrm{sexp}_2$.

This rung does **not** bound a tail $\sum_{k\ge N}$: the true coefficients
beyond $N$ are unknown.  If the envelope continued, the omitted tail on
$|z|\le\tfrac12$ would be at most $C_{\mathrm{env}}4^{-N}/(1-\tfrac14)
\approx 1.4\cdot10^{-90}$ (base $e$) — quoted only to show that truncating
at $N$ is not where the precision is lost.  The library evaluates the
polynomial $P$, and rungs 2–4 certify $P$.

### 1.2 Float64 Horner on $|z|\le\tfrac12$

`_core._series` is Horner's rule with $n=N-1$ multiplications and additions
on `float(c_k)`.  Two ingredients:

* **Coefficient rounding.** Python's `float(str)` is correctly rounded, so
  $\tilde c_k = c_k(1+\delta_k)$, $|\delta_k|\le u = 2^{-53}$.  Hence
  $|\sum\tilde c_k z^k - P(z)|\le u\sum|c_k||z|^k$.
* **Horner's rule** (Higham, *Accuracy and Stability of Numerical
  Algorithms*, 2nd ed., Thm 5.1): for a degree-$n$ polynomial with
  coefficients $a_i$, $|\mathrm{fl}(p(x))-p(x)|\le\gamma_{2n}\sum|a_i||x|^i$.
  Applied to $\tilde c_k$: $\le\gamma_{2n}(1+u)\sum|c_k||z|^k$.

With $S_1=\sum_{k<N}|c_k|2^{-k}$ (an interval computation) and the argument
$z$ exact (the reduction `z -= k` is exact by Sterbenz's lemma for
$|k|\ge1$, trivially for $k=0$),

$$
\boxed{\ |\mathrm{fl}(P(z))-P(z)|\le\bigl(u+\gamma_{2n}(1+u)\bigr)S_1
\quad\text{for all }|z|\le\tfrac12\ }
$$

giving $5.47\cdot10^{-14}$ (base $e$, $S_1 = 1.6464$) and $6.47\cdot10^{-14}$
(base 2).  This is the standard a-priori bound; it is uniform on the disc and
about 100× pessimistic compared with observed errors, which is the price
of a proof.  The subsequent `math.exp`/`math.log` steps are not certified:
libm's `exp` is not guaranteed correctly rounded, and the platform-
dependent 1-ulp errors are outside this document.

### 1.3 mpmath Horner at `dps` digits

`hp._base_coeffs` parses the strings at `DIGITS+20 = 70` dps (precision
$p_c=236$ bits, so $u_c=2^{-236}$), and `hp._series` runs Horner at
`dps+10` digits ($p_h=$ `dps_to_prec(dps+10)` bits, $u_h=2^{-p_h}$).
mpmath rounds every `mpf` operation to nearest at `prec` bits, so the
relative error per operation is $\le 2^{-p}$; the same theorem gives

$$
|\mathrm{fl}(P(z))-P(z)|\le\bigl(u_c+\gamma_{2n}(u_h)(1+u_c)\bigr)S_1,
$$

i.e. $3.8\cdot10^{-59}$ at `dps=50`, $5.6\cdot10^{-39}$ at `dps=30`,
$1.5\cdot10^{-71}$ at `dps=100` (base $e$).  At `dps=100` the coefficient
parsing floor $u_c S_1$ dominates: the table cannot deliver more than
$\approx 70$ digits of *its own* polynomial, and (rung 2) only $\approx 51$
of a solution of the functional equation.

## 2. Rung 2 — the functional-equation defect of $P$

Let $D(z)=P(z+1)-E(P(z))$.  The library never needs $D$ away from the seam:
$S$ satisfies $S(z+1)=E(S(z))$ *identically* by construction.  What $D$
measures is how well the analytic base piece $P$ glues to its own
exponential image across the seam $z=\pm\tfrac12$.  Because $P(z+1)$ is
evaluated at radius $|z+1|$ up to $\tfrac32$, where the $N$-term truncation
is only $\sim(3/4)^N/N$ accurate, $D$ is small only *near* the seam, and
the honest object is a profile in the distance $t$ from the seam.

### 2.1 Exact Taylor data at the seam

$P(\tfrac12+w)=\sum_k s_k w^k$ and $P(-\tfrac12+w)=\sum_k \sigma_k w^k$ are
computed by exact Taylor shift, $s_k=\sum_{j\ge k}\binom jk c_j 2^{-(j-k)}$
(binomials exact integers, powers of $\tfrac12$ exact).  The entire function
$E(P(-\tfrac12+w))=\exp(Q(w))$, $Q=\ell\sum\sigma_kw^k$, has Taylor
coefficients $e_k$ given by the recurrence obtained from $E'=Q'E$:

$$e_0=e^{Q(0)},\qquad (k+1)e_{k+1}=\sum_{j=0}^{\min(k,N-2)}(j+1)q_{j+1}e_{k-j},$$

computed for $k<K$ ($K=3N+100$) in interval arithmetic.  Then
$D(-\tfrac12+w)=\sum_{k<K}d_kw^k-\sum_{k\ge K}e_kw^k$ with $d_k=s_k-e_k$
($s_k=0$ for $k\ge N$).

### 2.2 The $C^m$ mismatch of $S$ at the seam

$S$ equals $P(z)$ for $z\le\tfrac12$ and $E(P(z-1))$ for $z>\tfrac12$; the
$m$-th derivatives from the two sides differ by exactly $D^{(m)}(-\tfrac12)
= m!\,d_m$.  These are rigorous enclosures (width $\sim10^{-79}$):

| $m$ | base $e$: $\lvert D^{(m)}(-\tfrac12)\rvert$ | base 2 |
|---|---|---|
| 0 (the seam residual) | $2.618\cdot10^{-52}$ | $7.850\cdot10^{-53}$ |
| 1 | $5.814\cdot10^{-52}$ | $3.388\cdot10^{-53}$ |
| 2 | $6.334\cdot10^{-51}$ | $3.211\cdot10^{-52}$ |
| 3 | $2.560\cdot10^{-50}$ | $2.981\cdot10^{-52}$ |
| 4 | $1.520\cdot10^{-49}$ | $4.572\cdot10^{-51}$ |

So the library function is not merely $C^0$-continuous up to $2.6\cdot
10^{-52}$ at the seam: it is $C^4$-continuous up to $1.5\cdot10^{-49}$.
(The README's "residual 2.618e-52" is the $m=0$ row, now certified rather
than floating-point.)

### 2.3 Uniform bound on discs around the seam

For $|w|\le t$: $|D(-\tfrac12+w)|\le\sum_{k<K}|d_k|t^k+T_K(t)$, where the
tail is bounded by Cauchy's estimate on $|w|=R>t$:

$$|e_k|\le\frac{M(R)}{R^k},\qquad
M(R)=\max_{|w|=R}|e^{Q(w)}|\le\exp\Bigl(\sum_{k<N}|q_k|R^k\Bigr),\qquad
T_K(t)=M(R)\frac{(t/R)^K}{1-t/R}.$$

The script tries $R\in\{1.25,1.5,1.75,2\}$ and keeps the smallest tail (any
$R$ is valid).  The tail is $<10^{-67}$ in every case, so the bound is the
$\ell^1$ sum.  Certified profile (the disc $|z+\tfrac12|\le t$ contains the
real segment $[-\tfrac12-t,-\tfrac12+t]$):

| $t$ | base $e$: $\sup\lvert D\rvert$ | base 2 |
|---|---|---|
| 1/64 | $2.72\cdot10^{-52}$ | $7.91\cdot10^{-53}$ |
| 1/8 | $3.94\cdot10^{-52}$ | $8.54\cdot10^{-53}$ |
| 1/4 | $7.10\cdot10^{-52}$ | $9.87\cdot10^{-53}$ |
| 1/2 | $9.29\cdot10^{-48}$ | $2.05\cdot10^{-52}$ |
| 3/4 | $3.1\cdot10^{-33}$ | $1.6\cdot10^{-35}$ |
| 1 | $2.4\cdot10^{-21}$ | $5.7\cdot10^{-20}$ |

The $\ell^1$ bound is tight: the certified point values on the real axis
(e.g. base $e$: $|D(-\tfrac38)|=3.941\cdot10^{-52}$, $|D(-\tfrac14)|
=7.095\cdot10^{-52}$) coincide with the $t=1/8$, $t=1/4$ bounds to the
printed digits — the maximum of $|D|$ on each disc sits on the real axis
at $z=-\tfrac12+t$, and the bound loses nothing.  The growth beyond
$t\approx0.4$ (base $e$) is the truncation of $P$ itself at radius
$\tfrac12+t$: $|D(0)|=|P(1)-e|=3.1\cdot10^{-48}\approx2^{-150}/150$, exactly
the size of the first omitted term of the $2^{-k}/k$ envelope at $|z|=1$.
The library evaluates $P$ only on $|z|\le\tfrac12$, so this growth never
enters a returned value; it does enter the "range of validity" question in
rung 3.

### 2.4 Monotonicity, convexity, ranges

With the mean-value form $f(I)\subseteq f(m)+f'(I)(I-m)$ on 1024
subintervals of $[-\tfrac12,\tfrac12]$ (overestimation $O(h^2)$):

* base $e$: $P''\subseteq[0.0214, 1.5423]>0$ and $P'\subseteq[0.9567,1.5752]>0$.
  Hence $P$ is strictly convex and increasing, so the ranges are *exactly*
  the endpoint values, certified to $10^{-80}$:
  $P'\in[P'(-\tfrac12),P'(\tfrac12)]=[0.95675517789\ldots,\,1.57515793778\ldots]$,
  $P\in[0.49856328794\ldots,\,1.64635423375\ldots]$.
* base 2: $P'\subseteq[0.8891,0.9704]>0$ (increasing), but
  $P''(-\tfrac12)<0<P''(\tfrac12)$: **$\mathrm{sexp}_2$'s table has an
  inflection point inside $(-\tfrac12,\tfrac12)$**; the range of $P$ is
  still $[P(-\tfrac12),P(\tfrac12)]=[0.54476412146\ldots,\,1.45878181604\ldots]$.

## 3. Rung 3 — from the residual to properties of the library function

### 3.1 $S$ solves the functional equation exactly; its only defect is the seams

For every $z$, $k(z+1)=k(z)+1$, so $S(z+1)=E(S(z))$ holds identically
(in exact arithmetic).  $S$ is real-analytic on each open interval
$(k-\tfrac12,k+\tfrac12)$ and has a jump at every half-integer.

**Proposition (seam jumps).** Let $A_0=P(\tfrac12)$, $B_0=E(P(-\tfrac12))$,
$A_k=E(A_{k-1})$, $B_k=E(B_{k-1})$.  The jump of $S$ at $z=k+\tfrac12$ is
$J_k=A_k-B_k$, with $J_0=D(-\tfrac12)$ the seam residual, and

$$|J_k|\le \ell\,\max(A_k,B_k)\,|J_{k-1}|,\qquad
\frac{|J_k|}{\min(A_k,B_k)}\le e^{\ell|J_{k-1}|}-1 .$$

*Proof.* $|e^{\ell a}-e^{\ell b}|\le\ell\max(e^{\ell a},e^{\ell b})|a-b|$ by
the mean value theorem, and $A_k/B_k=e^{\ell J_{k-1}}$. $\square$

At the negative seams, $z=-\tfrac12$: left limit $\log_bA_0$, right limit
$P(-\tfrac12)=\log_bB_0$, so $|J_{-1}|\le|J_0|/(\ell\min(A_0,B_0))$; at
$z=-\tfrac32$ once more through $\log_b$.  The script computes the jumps
both directly (interval difference, tight) and through this chain (they
agree).  Base $e$:

| seam | $-\tfrac32$ | $-\tfrac12$ | $\tfrac12$ | $\tfrac32$ | $\tfrac52$ | $\tfrac72$ |
|---|---|---|---|---|---|---|
| $\lvert J\rvert$ | $3.19\cdot10^{-52}$ | $1.59\cdot10^{-52}$ | $2.62\cdot10^{-52}$ | $1.36\cdot10^{-51}$ | $2.43\cdot10^{-49}$ | $1.5\cdot10^{29}$ |
| relative | — | — | $1.59\cdot10^{-52}$ | $2.62\cdot10^{-52}$ | $1.36\cdot10^{-51}$ | $2.43\cdot10^{-49}$ |

(At $z=\tfrac72$, $S\approx6\cdot10^{77}$; the absolute jump is meaningless
and the relative one is what a user sees.  float64 overflows before
$z=4.4$.)  So: **the library function is an exact solution of
$S(z+1)=b^{S(z)}$ whose jumps are below $3.2\cdot10^{-52}$ (absolute) at
the seams $-\tfrac32,-\tfrac12,\tfrac12$, $1.4\cdot10^{-51}$ at $\tfrac32$,
and relatively below $1.4\cdot10^{-51}$ at $\tfrac52$ and $2.5\cdot10^{-49}$
at $\tfrac72$ (the last seam before float64 overflow); it is $C^4$ up to
$1.5\cdot10^{-49}$ at the base seam.**  That is the provable content of
"residual $2.6\cdot10^{-52}$".

### 3.2 How far the analytic base piece extends

For $z\in[\tfrac12,\tfrac12+t]$, $|P(z)-S(z)|=|D(z-1)|\le\sup_{|w|\le t}|D|$;
for $z\in[-\tfrac12-t,-\tfrac12]$, $|P(z)-S(z)|=|\log_bE(P(z))-\log_bP(z+1)|
\le|D(z)|/(\ell\,m)$ with $m$ a certified lower bound of both
$E(P(z))$ and $P(z+1)$ there ($m=0.4986$ for base $e$).  So the polynomial
$P$ agrees with $S$ to $7.1\cdot10^{-52}$ on $[\tfrac12,\tfrac34]$ and to
$1.4\cdot10^{-51}$ on $[-\tfrac34,-\tfrac12]$, but only to $10^{-21}$ on
$[-\tfrac32,\tfrac32]$: the table is a 51-digit representation of a
solution on a strip of half-width $\approx0.75$ around $0$, not on the
whole disc of convergence.

### 3.3 Conditional propagation (proved, hypothesis not certified)

**Proposition.** If $|P-F|\le\varepsilon\le10^{-40}$ on $[-\tfrac12,\tfrac12]$
for the true $F$, then $|S-F|\le\Lambda_k\varepsilon$ on $[k-\tfrac12,k+\tfrac12]$
with $\Lambda_1=\ell E(P(\tfrac12)+\varepsilon)$,
$\Lambda_k=\Lambda_{k-1}\ell E^{\circ k}(P(\tfrac12)+\varepsilon)$,
$\Lambda_{-1}=1/(\ell(P(-\tfrac12)-\varepsilon))$, and on $[-\tfrac74,-\tfrac32]$
$\Lambda_{-2}=\Lambda_{-1}/(\ell(\log_bP(\tfrac14)-\Lambda_{-1}\varepsilon))$.

*Proof.* Same mean value inequalities as 3.1, with $\max(S,F)\le S+\varepsilon$
on the forward side and $\min(S,F)\ge S-\varepsilon$ on the log side; on
$[-\tfrac32,-\tfrac12]$ the argument $z+1$ lies in the base interval where
$S\ge P(-\tfrac12)$ by monotonicity; on $[-\tfrac74,-\tfrac32]$,
$S(z+1)=\log_bP(z+2)\ge\log_bP(\tfrac14)$.  Near $z=-2$ the Lipschitz
constant of $\log$ is unbounded, so no uniform constant exists there. $\square$

Base $e$: $\Lambda_{-2}\le7.79$, $\Lambda_{-1}\le2.01$, $\Lambda_1\le5.19$,
$\Lambda_2\le930$, $\Lambda_3\le5.7\cdot10^{80}$ (absolute; relative
propagation is $\le e^{\Lambda_{k-1}\varepsilon}-1$).  This is exactly the
statement "if the base interval were right to $\varepsilon$, so would be
everything a user calls" — it converts a *hypothetical* base-interval error
into a certified whole-domain error.  The hypothesis is the open item.

## 4. What is NOT certified: the distance to Kneser's $F$

Nothing above bounds $\|P-F\|$ on $[-\tfrac12,\tfrac12]$, and this is not a
gap in the computation but in the mathematics available:

1. **A small residual on the real line does not imply closeness to $F$.**
   For any 1-periodic real-analytic $\theta$ with $\theta(0)=0$, $F_\theta(z)=
   F(z+\theta(z))$ satisfies $F_\theta(z+1)=e^{F_\theta(z)}$ *exactly*,
   $F_\theta(0)=1$, and is real-analytic and increasing on $z>-2$ for small
   $\theta$; it differs from $F$ by $\approx\theta F'$, which is arbitrary.
   Its Taylor polynomial has a functional-equation defect near the seam
   comparable to $P$'s.  The real-axis residual, the seam jumps, the $C^m$
   mismatches, the derivative and range bounds are all blind to $\theta$.
   What singles out Kneser's $F$ is behaviour in the upper half-plane
   ($F(z)\to L$ as $\operatorname{Im}z\to+\infty$, Trappmann–Kouznetsov
   uniqueness); the shipped table is a polynomial and carries no such
   information.  The theta-iteration in `kneser.build` *targets* that
   condition (it keeps only Fourier modes decaying upward), and the
   empirical contraction ($\approx0.017$–$0.03$ per pass,
   `demo_kappa_mechanism.py`, `demo_build_contraction.py`) is strong
   evidence that it converged to $F$ — evidence, not proof.
2. **What a proof would need.** A quantitative stability estimate for the
   uniqueness theorem: an operator $\mathcal T$ (the builder's one pass:
   Fourier projection of $\theta$ at height $\delta$ + Cauchy resampling)
   shown to be a contraction on an explicit neighbourhood of $F$ in a norm
   $\|\cdot\|$ that controls the real segment, with constant $\kappa<1$ and
   an explicit bound on $\|\mathcal TP-P\|$; then $\|P-F\|\le\|\mathcal TP-P\|
   /(1-\kappa)$.  Both pieces are missing: $\kappa$ is only measured, and
   $\mathcal T$ itself uses the linearised superfunction whose error
   $O(|L|^{-\mathrm{DEPTH}})$ ($1.37^{-370}\approx10^{-51}$) would also
   need a rigorous constant.  Alternatively, a computer-assisted proof
   through Paulsen–Cowgill's formulation (their 180-node method reaches
   $10^{-50}$) could be made rigorous by interval enclosure of their linear
   system — that too is future work.
3. **Independent agreement is not a certificate either.**  The tests show
   $<10^{-47}$ agreement with the sibling `semi_exp` implementation.  Two
   implementations of the same algorithm family converging to the same
   $F_\theta$ would agree just as well.

Therefore the honest precision statement for the library is:

> `kneser.sexp` computes an exact solution $S$ of $S(z+1)=b^{S(z)}$,
> $S(0)=1$, real-analytic between half-integers, with certified seam jumps
> below $3.2\cdot10^{-52}$ absolute on $(-2,\tfrac32)$, $1.4\cdot10^{-51}$ at
> $\tfrac32$, and $2.5\cdot10^{-49}$ relative at $\tfrac72$, and
> $C^4$-continuous to $1.5\cdot10^{-49}$ at the base seam; float64
> evaluation adds at most $5.5\cdot10^{-14}$, mpmath at `dps=50` at most
> $3.8\cdot10^{-59}$, per series evaluation.  Its distance to Kneser's
> solution is **not** certified; it is supported by the construction and by
> cross-checks only.

## 5. Rung 4 — derived constants (enclosures of the table's values)

All widths are $\le10^{-80}$; the README's float64 quotes are the correctly
rounded doubles of these intervals.  Base $e$ (the caveat of section 4
applies to the last column, i.e. to the claim that these are Kneser's
numbers):

| quantity | how the library computes it | certified enclosure (55 digits) |
|---|---|---|
| $\mathrm{sexp}(\tfrac12)$ | $P(\tfrac12)$ | $1.6463542337511945809719240315921145182053116489690417$ |
| $\mathrm{sexp}(-\tfrac12)=f(0)$ | $\log P(\tfrac12)$ (reduction, $k=-1$) | $0.49856328794111443467961909249313329400247186492241935$ |
| same via the series | $P(-\tfrac12)$ | $0.49856328794111443467961909249313329400247186492241919$ |
| $\mathrm{sexp}'(-1)$ | $c_1$ (since $c_0=1$) | $1.0917673512583209918013845500271516443847311771937481$ |
| $\mathrm{sexp}'(-\tfrac12)$ | $P'(\tfrac12)/P(\tfrac12)$ | $0.95675517789104594687752254572357303084995397891396077$ |
| $f'(0)=\mathrm{sexp}'(-\tfrac12)/\mathrm{sexp}'(-1)$ | left/right seam values | $0.87633613222481309394808927154811959614628509947979705$ / $\ldots9797969$ |
| $\lim_{x\to-\infty}f(x)=\log\mathrm{sexp}(-\tfrac12)$ | $\log\log P(\tfrac12)$ | $-0.69602474088608417173296092502920405275724683287608229$ |
| $\mathrm{slog}(\tfrac12)$ | root of $P(z)=\tfrac12$ (interval Newton) | $-0.49849837513116899712732121511037885697154317325483180$ |
| $f(\tfrac12)=\mathrm{half\_exp}(\tfrac12)$ | $P(\mathrm{slog}(\tfrac12)+\tfrac12)$ | $1.0016400378866631889882297295807994303276834552788148$ |

Two facts a reader should notice: the library's $\mathrm{sexp}(-\tfrac12)$ is
$\log P(\tfrac12)$, not $P(-\tfrac12)$; the two differ by $1.59\cdot10^{-52}$
(the seam jump $J_{-1}$), and $f'(0)$ likewise has two values that differ
by $1.8\cdot10^{-52}$ $\bigl(=(D'(-\tfrac12)-P'(-\tfrac12)J_0)/(c_1P(\tfrac12))\bigr)$.  The 16
digits the README quotes ($0.8763361322248131$) are unaffected; a 50-digit
quote should say which side of the seam it is.

The root enclosure uses one interval-Newton step: with $I=[\zeta-10^{-20},
\zeta+10^{-20}]$ around a floating Newton iterate $\zeta$,
$N(I)=\zeta-(P(\zeta)-\tfrac12)/P'(I)$; the script checks $N(I)\subsetneq I$,
which (since $P'>0$ on $I$) proves existence and uniqueness of the root in
$N(I)$ (Moore's interval Newton theorem).

Base 2: $\mathrm{sexp}_2(\tfrac12)=P_2(\tfrac12)\in1.4587818160364217006839716610385871352966066053309071\pm10^{-80}$,
$\mathrm{sexp}_2(-\tfrac12)=\log_2P_2(\tfrac12)=0.54476412145955673398012188582572447003547801542736938$,
$f_2'(0)=0.74798531300884998942109549476750834455376111423689544$.

## 6. Summary of the ladder

| rung | status | headline (base $e$) |
|---|---|---|
| 1 polynomial evaluation | **rigorous** | float64 $\le5.5\cdot10^{-14}$; mpmath dps=50 $\le3.8\cdot10^{-59}$ on $\lvert z\rvert\le\tfrac12$ |
| 2 FE defect near the seam | **rigorous** | $\le3.9\cdot10^{-52}$ on $\lvert z+\tfrac12\rvert\le\tfrac18$, $\le7.1\cdot10^{-52}$ on $\le\tfrac14$; $C^4$ mismatch $\le1.5\cdot10^{-49}$; $P$ convex increasing, ranges exact |
| 3 library function $S$ | **rigorous** | exact FE solution; seam jumps $\le3.2\cdot10^{-52}$ on $(-2,\tfrac32)$, $\le1.4\cdot10^{-51}$ at $\tfrac32$, $\le2.5\cdot10^{-49}$ relative at $\tfrac72$; propagation constants $\Lambda_k$ proved |
| 3′ distance to Kneser's $F$ | **not certified** | requires a quantitative uniqueness/contraction theorem; not obtainable from real-axis data |
| 4 derived constants | **rigorous as table values** | $\mathrm{sexp}(\tfrac12)$, $f(0)$, $f'(0)$, $f(\tfrac12)$, asymptote to $10^{-80}$ |

Base 2: the same machinery, seam residual $7.85\cdot10^{-53}$, defect
$\le9.9\cdot10^{-53}$ on $|z+\tfrac12|\le\tfrac14$, seam jumps
$\le7.0\cdot10^{-52}$ absolute on $(-2,3)$ and $\le4.9\cdot10^{-52}$
relative at $\tfrac72$.

## 7. Output of `docs/demo_certificate.py` (galic, Python 3.12, mpmath 1.3)

```text
==============================================================================
TABLE base e: N = 150 coefficients, DIGITS = 50, stated RESIDUAL = 2.618e-52   (iv.dps = 80)
==============================================================================

[rung 1] the polynomial P(z) = sum_{k<N} c_k z^k
  |c_k| <= C_env * 2^-k     for all k < N with C_env = 2.1835347
  |c_k| <= C_log * 2^-k / k for 1 <= k < N with C_log = 7.7672285   (last term: |c_149| 2^149 (149) = 1.0)
  (hypothetical, NOT certified) if the envelope continued past N, the omitted
   tail on |z|<=1/2 would be <= C_env 4^-N/(1-1/4) = 1.43e-90
  S1  = sum |c_k| 2^-k        <= 1.646354234
  S1' = sum |c_k| (3/2)^k     <= 5.188161782
  float64 Horner (Higham Thm 5.1, gamma_2n with n=149, plus coefficient rounding):
    |fl(P(z)) - P(z)| <= (u + gamma_2n (1+u)) S1 = 5.465e-14   for all |z| <= 1/2 (z exact)
  mpmath  Horner at dps= 50 (prec 203 bits; coefficients at 236 bits): |fl(P(z)) - P(z)| <= 3.816e-59
  mpmath  Horner at dps= 30 (prec 136 bits; coefficients at 236 bits): |fl(P(z)) - P(z)| <= 5.632e-39
  mpmath  Horner at dps=100 (prec 369 bits; coefficients at 236 bits): |fl(P(z)) - P(z)| <= 1.491e-71

[rung 2] functional-equation defect D(z) = P(z+1) - b**P(z) near the seam z = -1/2
  Taylor coefficients at the seam: P(1/2+w) exact shift; b**P(-1/2+w) by recurrence, K = 550 terms
  C^m mismatch of the reduced function S at the seam z = 1/2:  S^(m)(1/2-) - S^(m)(1/2+) = D^(m)(-1/2)
    m=0: D^(0)(-1/2) in [2.6176931e-52, 2.6176931e-52] (width 4.5e-79)   |.| <= 2.618e-52
    m=1: D^(1)(-1/2) in [5.8141940e-52, 5.8141940e-52] (width 7.0e-79)   |.| <= 5.814e-52
    m=2: D^(2)(-1/2) in [6.3335454e-51, 6.3335454e-51] (width 9.5e-79)   |.| <= 6.334e-51
    m=3: D^(3)(-1/2) in [2.5602208e-50, 2.5602208e-50] (width 2.3e-78)   |.| <= 2.56e-50
    m=4: D^(4)(-1/2) in [1.5202924e-49, 1.5202924e-49] (width 6.3e-78)   |.| <= 1.52e-49
  uniform bound on the disc |z + 1/2| <= t  (covers the real segment [-1/2 - t, -1/2 + t]):
    t = 1/64: sup |D| <= 2.716e-52   (l1 part 2.72e-52, tail 2.0e-1088 with R = 1.5)
    t = 1/32: sup |D| <= 2.832e-52   (l1 part 2.83e-52, tail 7.4e-923 with R = 1.5)
    t = 1/16: sup |D| <= 3.116e-52   (l1 part 3.12e-52, tail 2.8e-757 with R = 1.5)
    t =  1/8: sup |D| <= 3.941e-52   (l1 part 3.94e-52, tail 1.1e-591 with R = 1.5)
    t =  1/4: sup |D| <= 7.095e-52   (l1 part 7.09e-52, tail 4.3e-426 with R = 1.5)
    t =  1/2: sup |D| <= 9.285e-48   (l1 part 9.28e-48, tail 2.0e-260 with R = 1.5)
    t =  3/4: sup |D| <= 3.14e-33   (l1 part 3.14e-33, tail 1.9e-163 with R = 1.5)
    t =    1: sup |D| <= 2.369e-21   (l1 part 2.37e-21, tail 1.5e-94 with R = 1.5)
  (the growth with t is the truncation of the 150/200-term polynomial P at radius 1/2 + t,
   which the library never uses: it evaluates P on |z| <= 1/2 only)
  certified point values |D(z)| on the real segment (D uses P(z+1) at radius up to 3/2):
    z = -1/2: |D(z)| in [2.618e-52, 2.618e-52] (width 8.4e-81)
    z = -3/8: |D(z)| in [3.941e-52, 3.941e-52] (width 1.3e-80)
    z = -1/4: |D(z)| in [7.095e-52, 7.095e-52] (width 1.3e-80)
    z = -1/8: |D(z)| in [1.418e-51, 1.418e-51] (width 1.7e-80)
    z =    0: |D(z)| in [3.124e-48, 3.124e-48] (width 1.3e-80)
    z =  1/8: |D(z)| in [1.411e-40, 1.411e-40] (width 3.0e-80)
    z =  1/4: |D(z)| in [9.912e-34, 9.912e-34] (width 3.4e-80)
    z =  3/8: |D(z)| in [1.544e-27, 1.544e-27] (width 4.2e-80)
    z =  1/2: |D(z)| in [6.939e-22, 6.939e-22] (width 5.9e-80)
  P''([-1/2,1/2]) subset [0.0214092, 1.54229] (width 1.5)  -> P convex on the segment: True
  P' ([-1/2,1/2]) subset [0.956755, 1.57516] (width 0.62)  -> P increasing: True
  since P'' > 0, range of P' is exactly [P'(-1/2), P'(1/2)]:
    P'(-1/2) in [0.956755177891045946877522545724, 0.956755177891045946877522545724] (width 4.2e-81)
    P'(1/2)  in [1.57515793778430081238788527127, 1.57515793778430081238788527127] (width 4.2e-81)
  since P' > 0, range of P is exactly [P(-1/2), P(1/2)]:
    P(-1/2) in [0.498563287941114434679619092493, 0.498563287941114434679619092493] (width 2.1e-81)
    P(1/2)  in [1.64635423375119458097192403159, 1.64635423375119458097192403159] (width 4.2e-81)
  P([-3/2,-1/2]) subset [-0.696025, 0.498563] (width 1.2)   (subdivision, used for a lower bound only)

[rung 3] the reduced library function S(z) = E^k(P(z-k)), k = ceil(z-1/2)
  S satisfies S(z+1) = b**S(z) EXACTLY for every z; its only defect is a jump at each seam.
  seam z = k+1/2: left S = E^k(P(1/2)), right S = E^k(b**P(-1/2)); jump J_k = left - right
   k=0: |J_k| <= 2.618e-52 (direct)  <= 2.618e-52 (MVT chain);  relative |J_k|/S <= 1.59e-52;  S ~ 1.64635
   k=1: |J_k| <= 1.358e-51 (direct)  <= 1.358e-51 (MVT chain);  relative |J_k|/S <= 2.618e-52;  S ~ 5.18803
   k=2: |J_k| <= 2.433e-49 (direct)  <= 2.433e-49 (MVT chain);  relative |J_k|/S <= 1.358e-51;  S ~ 179.116
   k=3: |J_k| <= 1.496e+29 (direct)  <= 1.496e+29 (MVT chain);  relative |J_k|/S <= 2.433e-49;  S ~ 6.15009e+77
   seam z = -1/2: |J| <= 1.59e-52 (direct)  <= 1.59e-52 (MVT chain);  S ~ 0.498563
   seam z = -3/2: |J| <= 3.189e-52 (direct)  <= 3.189e-52 (MVT chain);  S ~ -0.696025
  the analytic continuation of the base piece P versus S across the seams:
    |P - S| <= 3.94e-52 on [1/2, 1/2 + 1/8],   |P - S| <= 7.91e-52 on [-1/2 - 1/8, -1/2]
    |P - S| <= 7.09e-52 on [1/2, 1/2 + 1/4],   |P - S| <= 1.42e-51 on [-1/2 - 1/4, -1/2]
    |P - S| <= 9.28e-48 on [1/2, 1/2 + 1/2],   |P - S| <= 1.86e-47 on [-1/2 - 1/2, -1/2]
    |P - S| <= 2.37e-21 on [1/2, 1/2 + 1],   |P - S| <= 4.75e-21 on [-1/2 - 1, -1/2]
  conditional (hypothesis NOT certified): if |P - sexp| <= eps <= 1e-40 on [-1/2,1/2] then
  |S - sexp| <= Lambda_k eps on [k-1/2, k+1/2] (Lambda_-2: on [-7/4, -3/2]) with
     Lambda_-2 <= 7.7927
     Lambda_-1 <= 2.0058
     Lambda_ 1 <= 5.188
     Lambda_ 2 <= 929.26
     Lambda_ 3 <= 5.715e+80

[rung 4] derived constants, as enclosures of the TABLE's values (not of Kneser's sexp)
  sexp(1/2)   = P(1/2)              in [1.646354233751194580971924031592114518205311648969041692,
                                                    1.646354233751194580971924031592114518205311648969041692]  (width 4.2e-81)
  sexp(-1/2)  = log_b P(1/2) [library path] in [0.4985632879411144346796190924931332940024718649224193502,
                                                    0.4985632879411144346796190924931332940024718649224193502]  (width 3.2e-81)
              = P(-1/2)      [series path]  in [0.4985632879411144346796190924931332940024718649224191912,
                                                    0.4985632879411144346796190924931332940024718649224191912]  (width 2.1e-81)
              difference of the two           in [1.58999e-52, 1.58999e-52] (width 5.3e-81)
  S'(-1)      = c_1 / log b         in [1.091767351258320991801384550027151644384731177193748086,
                                                    1.091767351258320991801384550027151644384731177193748086]  (width 2.1e-81)
  S'(-1/2^-)  = P'(1/2)/(log b P(1/2)) in [0.9567551778910459468775225457235730308499539789139607735,
                                                    0.9567551778910459468775225457235730308499539789139607735]  (width 6.3e-81)
  S'(-1/2^+)  = P'(-1/2)            in [0.9567551778910459468775225457235730308499539789139605724,
                                                    0.9567551778910459468775225457235730308499539789139605724]  (width 4.2e-81)
  half_exp'(0) = S'(-1/2)/S'(-1):   left  in [0.8763361322248130939480892715481195961462850994797970529,
                                                    0.8763361322248130939480892715481195961462850994797970529]  (width 8.4e-81)
                                    right in [0.8763361322248130939480892715481195961462850994797968687,
                                                    0.8763361322248130939480892715481195961462850994797968687]  (width 6.3e-81)
  log_b sexp(-1/2) (negative-tail asymptote of half_exp) in [-0.6960247408860841717329609250292040527572468328760822945,
                                                    -0.6960247408860841717329609250292040527572468328760822945]  (width 7.4e-81)
  ok   interval Newton: N(I) strictly inside I, unique root of P(z)=1/2 in N(I)
  slog(1/2) = root of P(z) = 1/2     in [-0.4984983751311689971273212151103788569715431732548318037,
                                                    -0.4984983751311689971273212151103788569715431732548318037]  (width 4.2e-81)
  half_exp(1/2) = P(slog(1/2) + 1/2) in [1.001640037886663188988229729580799430327683455278814798,
                                                    1.001640037886663188988229729580799430327683455278814798]  (width 6.3e-81)

[asserts]
  ok   last stored term |c_(N-1)| 2^-(N-1) = 1.32e-92 < 1e-80
  ok   float64 Horner bound 5.47e-14 < 1e-12
  ok   mpmath Horner bound at dps=50 < 1e-56
  ok   seam residual |D(-1/2)| = 2.62e-52 < 1e-50
  ok   sup |D| on |z + 1/2| <= 1/8 is 3.94e-52 < 1e-48
  ok   sup |D| on |z + 1/2| <= 1/2 is 9.28e-48 < 1e-40
  ok   C^0..C^3 seam mismatches all < 1e-46
  ok   P' > 0 on [-1/2, 1/2] (P strictly increasing)
  ok   seam jumps at 1/2, 3/2, 5/2 all < 1e-45
  ok   seam jumps at -1/2, -3/2 both < 1e-50

  table base e: 8.5 s
==============================================================================
TABLE base 2: N = 200 coefficients, DIGITS = 50, stated RESIDUAL = 7.851e-53   (iv.dps = 80)
==============================================================================

[rung 1] the polynomial P(z) = sum_{k<N} c_k z^k
  |c_k| <= C_env * 2^-k     for all k < N with C_env = 218882.37
  |c_k| <= C_log * 2^-k / k for 1 <= k < N with C_log = 43557592.0   (last term: |c_199| 2^199 (199) = 4.3558e+7)
  (hypothetical, NOT certified) if the envelope continued past N, the omitted
   tail on |z|<=1/2 would be <= C_env 4^-N/(1-1/4) = 1.13e-115
  S1  = sum |c_k| 2^-k        <= 1.459574153
  S1' = sum |c_k| (3/2)^k     <= 2.915340876
  float64 Horner (Higham Thm 5.1, gamma_2n with n=199, plus coefficient rounding):
    |fl(P(z)) - P(z)| <= (u + gamma_2n (1+u)) S1 = 6.466e-14   for all |z| <= 1/2 (z exact)
  mpmath  Horner at dps= 50 (prec 203 bits; coefficients at 236 bits): |fl(P(z)) - P(z)| <= 4.519e-59
  mpmath  Horner at dps= 30 (prec 136 bits; coefficients at 236 bits): |fl(P(z)) - P(z)| <= 6.669e-39
  mpmath  Horner at dps=100 (prec 369 bits; coefficients at 236 bits): |fl(P(z)) - P(z)| <= 1.322e-71

[rung 2] functional-equation defect D(z) = P(z+1) - b**P(z) near the seam z = -1/2
  Taylor coefficients at the seam: P(1/2+w) exact shift; b**P(-1/2+w) by recurrence, K = 700 terms
  C^m mismatch of the reduced function S at the seam z = 1/2:  S^(m)(1/2-) - S^(m)(1/2+) = D^(m)(-1/2)
    m=0: D^(0)(-1/2) in [-7.8502480e-53, -7.8502480e-53] (width 6.3e-79)   |.| <= 7.85e-53
    m=1: D^(1)(-1/2) in [-3.3879660e-53, -3.3879660e-53] (width 5.7e-79)   |.| <= 3.388e-53
    m=2: D^(2)(-1/2) in [-3.2109929e-52, -3.2109929e-52] (width 6.5e-79)   |.| <= 3.211e-52
    m=3: D^(3)(-1/2) in [-2.9809701e-52, -2.9809701e-52] (width 1.3e-78)   |.| <= 2.981e-52
    m=4: D^(4)(-1/2) in [-4.5723803e-51, -4.5723803e-51] (width 3.3e-78)   |.| <= 4.572e-51
  uniform bound on the disc |z + 1/2| <= t  (covers the real segment [-1/2 - t, -1/2 + t]):
    t = 1/64: sup |D| <= 7.907e-53   (l1 part 7.91e-53, tail 5.1e-1332 with R = 1.25)
    t = 1/32: sup |D| <= 7.972e-53   (l1 part 7.97e-53, tail 2.7e-1121 with R = 1.25)
    t = 1/16: sup |D| <= 8.126e-53   (l1 part 8.13e-53, tail 1.5e-910 with R = 1.25)
    t =  1/8: sup |D| <= 8.539e-53   (l1 part 8.54e-53, tail 8.1e-700 with R = 1.25)
    t =  1/4: sup |D| <= 9.869e-53   (l1 part 9.87e-53, tail 4.8e-489 with R = 1.25)
    t =  1/2: sup |D| <= 2.046e-52   (l1 part 2.05e-52, tail 3.4e-278 with R = 1.25)
    t =  3/4: sup |D| <= 1.562e-35   (l1 part 1.56e-35, tail 9.3e-155 with R = 1.25)
    t =    1: sup |D| <= 5.727e-20   (l1 part 5.73e-20, tail 5.3e-67 with R = 1.25)
  (the growth with t is the truncation of the 150/200-term polynomial P at radius 1/2 + t,
   which the library never uses: it evaluates P on |z| <= 1/2 only)
  certified point values |D(z)| on the real segment (D uses P(z+1) at radius up to 3/2):
    z = -1/2: |D(z)| in [7.850e-53, 7.850e-53] (width 8.4e-81)
    z = -3/8: |D(z)| in [8.539e-53, 8.539e-53] (width 8.4e-81)
    z = -1/4: |D(z)| in [9.869e-53, 9.869e-53] (width 1.1e-80)
    z = -1/8: |D(z)| in [1.225e-52, 1.225e-52] (width 1.3e-80)
    z =    0: |D(z)| in [1.806e-52, 1.806e-52] (width 1.1e-80)
    z =  1/8: |D(z)| in [1.836e-44, 1.836e-44] (width 2.1e-80)
    z =  1/4: |D(z)| in [1.562e-35, 1.562e-35] (width 2.1e-80)
    z =  3/8: |D(z)| in [2.062e-27, 2.062e-27] (width 2.1e-80)
    z =  1/2: |D(z)| in [5.727e-20, 5.727e-20] (width 3.0e-80)
  P''([-1/2,1/2]) subset [-0.325529, 0.316401] (width 0.64)  -> P convex on the segment: False
  P' ([-1/2,1/2]) subset [0.889102, 0.970428] (width 0.081)  -> P increasing: True
  P''(-1/2) in [-0.3255286251, -0.3255286251] (width 2.1e-81),  P''(1/2) in [0.3164014083, 0.3164014083] (width 2.1e-81)  -> sign change: P has an inflection point in (-1/2, 1/2)
  since P' > 0, range of P is exactly [P(-1/2), P(1/2)]:
    P(-1/2) in [0.544764121459556733980121885826, 0.544764121459556733980121885826] (width 1.1e-81)
    P(1/2)  in [1.45878181603642170068397166104, 1.45878181603642170068397166104] (width 2.1e-81)
  P([-3/2,-1/2]) subset [-0.876297, 0.544764] (width 1.4)   (subdivision, used for a lower bound only)

[rung 3] the reduced library function S(z) = E^k(P(z-k)), k = ceil(z-1/2)
  S satisfies S(z+1) = b**S(z) EXACTLY for every z; its only defect is a jump at each seam.
  seam z = k+1/2: left S = E^k(P(1/2)), right S = E^k(b**P(-1/2)); jump J_k = left - right
   k=0: |J_k| <= 7.85e-53 (direct)  <= 7.85e-53 (MVT chain);  relative |J_k|/S <= 5.381e-53;  S ~ 1.45878
   k=1: |J_k| <= 1.496e-52 (direct)  <= 1.496e-52 (MVT chain);  relative |J_k|/S <= 5.441e-53;  S ~ 2.74876
   k=2: |J_k| <= 6.968e-52 (direct)  <= 6.968e-52 (MVT chain);  relative |J_k|/S <= 1.037e-52;  S ~ 6.7214
   k=3: |J_k| <= 5.097e-50 (direct)  <= 5.097e-50 (MVT chain);  relative |J_k|/S <= 4.83e-52;  S ~ 105.522
   seam z = -1/2: |J| <= 7.764e-53 (direct)  <= 7.764e-53 (MVT chain);  S ~ 0.544764
   seam z = -3/2: |J| <= 2.056e-52 (direct)  <= 2.056e-52 (MVT chain);  S ~ -0.876296
  the analytic continuation of the base piece P versus S across the seams:
    |P - S| <= 8.54e-53 on [1/2, 1/2 + 1/8],   |P - S| <= 2.26e-52 on [-1/2 - 1/8, -1/2]
    |P - S| <= 9.87e-53 on [1/2, 1/2 + 1/4],   |P - S| <= 2.61e-52 on [-1/2 - 1/4, -1/2]
    |P - S| <= 2.05e-52 on [1/2, 1/2 + 1/2],   |P - S| <= 5.42e-52 on [-1/2 - 1/2, -1/2]
    |P - S| <= 5.73e-20 on [1/2, 1/2 + 1],   |P - S| <= 1.52e-19 on [-1/2 - 1, -1/2]
  conditional (hypothesis NOT certified): if |P - sexp| <= eps <= 1e-40 on [-1/2,1/2] then
  |S - sexp| <= Lambda_k eps on [k-1/2, k+1/2] (Lambda_-2: on [-7/4, -3/2]) with
     Lambda_-2 <= 13.083
     Lambda_-1 <= 2.6483
     Lambda_ 1 <= 1.9053
     Lambda_ 2 <= 8.8766
     Lambda_ 3 <= 649.26

[rung 4] derived constants, as enclosures of the TABLE's values (not of Kneser's sexp)
  sexp(1/2)   = P(1/2)              in [1.458781816036421700683971661038587135296606605330907102,
                                                    1.458781816036421700683971661038587135296606605330907102]  (width 2.1e-81)
  sexp(-1/2)  = log_b P(1/2) [library path] in [0.5447641214595567339801218858257244700354780154273693775,
                                                    0.5447641214595567339801218858257244700354780154273693775]  (width 5.3e-81)
              = P(-1/2)      [series path]  in [0.5447641214595567339801218858257244700354780154273694551,
                                                    0.5447641214595567339801218858257244700354780154273694551]  (width 1.1e-81)
              difference of the two           in [-7.76368e-53, -7.76368e-53] (width 6.3e-81)
  S'(-1)      = c_1 / log b         in [1.283082409572120593427321890868481450263911838872563115,
                                                    1.283082409572120593427321890868481450263911838872563115]  (width 6.3e-81)
  S'(-1/2^-)  = P'(1/2)/(log b P(1/2)) in [0.9597267977399520838995880913377771164575917254294358860,
                                                    0.9597267977399520838995880913377771164575917254294358860]  (width 7.4e-81)
  S'(-1/2^+)  = P'(-1/2)            in [0.9597267977399520838995880913377771164575917254294358678,
                                                    0.9597267977399520838995880913377771164575917254294358678]  (width 2.1e-81)
  half_exp'(0) = S'(-1/2)/S'(-1):   left  in [0.7479853130088499894210954947675083445537611142368954407,
                                                    0.7479853130088499894210954947675083445537611142368954407]  (width 1.1e-80)
                                    right in [0.7479853130088499894210954947675083445537611142368954265,
                                                    0.7479853130088499894210954947675083445537611142368954265]  (width 6.3e-81)
  log_b sexp(-1/2) (negative-tail asymptote of half_exp) in [-0.8762964052981492840736341183552772757910685728448699078,
                                                    -0.8762964052981492840736341183552772757910685728448699078]  (width 1.8e-80)

[asserts]
  ok   last stored term |c_(N-1)| 2^-(N-1) = 3.39e-115 < 1e-80
  ok   float64 Horner bound 6.47e-14 < 1e-12
  ok   mpmath Horner bound at dps=50 < 1e-56
  ok   seam residual |D(-1/2)| = 7.85e-53 < 1e-50
  ok   sup |D| on |z + 1/2| <= 1/8 is 8.54e-53 < 1e-48
  ok   sup |D| on |z + 1/2| <= 1/2 is 2.05e-52 < 1e-40
  ok   C^0..C^3 seam mismatches all < 1e-46
  ok   P' > 0 on [-1/2, 1/2] (P strictly increasing)
  ok   seam jumps at 1/2, 3/2, 5/2 all < 1e-45
  ok   seam jumps at -1/2, -3/2 both < 1e-50

  table base 2: 11.2 s

ALL CERTIFICATE ASSERTIONS PASSED
```
