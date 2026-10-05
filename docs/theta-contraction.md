# The theta-mapping iteration as an operator: linearisation, spectra, and what is (not) proved

Goal 3 of `world-class-plan-zh.md`.  Companion script: `docs/demo_theta_operator.py`
(runs on galic; raw outputs in `docs/_generated/goal3/`).

**Further work:** the separate [nonlinear certificate report](theta-nonlinear-certificate.md)
records fresh directed-disc/FLINT runs. Its completed base-e 50-digit
nonlinear certificate proves q<0.054816 in the normalized r=0.55 norm and
distance to the finite fixed point <4.588e-52. The old runs retain their
original status; see that report for the precise new parameters and scope.

**Audited status (2026-09-12).** The operator and chain-rule formulas below
are finite-dimensional mathematical identities on a fixed, regular branch.
The recovered numerical spectrum is strong evidence of local contraction:
base $e$, digits 50 gives $\rho=0.03311591986$; base 2 gives
$0.05659841552$. An exact rational calculation now proves contraction of the
**stored binary64 linear models**, with weighted $\ell^1$ norms below
$0.426$ and $0.098$ respectively (§4.5).

The previous draft overstated the interval runs as rigorous certificates.
The ball runs did finish, but branch/unwrap and outward-rounding obligations
remain (§6). Their numbers are **candidate bounds**, not accepted proofs of
contraction of the nonlinear $T$, and certainly not of error to Kneser's
function. The correct digits-50 eigen-norm candidate is $0.033158$ (box run,
$r=1/2$), not the old summary's $0.0321$ (a digits-12 value). Sections 5–6
state the conditional finite-dimensional theorem and the outstanding gaps.

---

## 1. The operator $T$ exactly as `build.py` implements it

Fix a base $b>\eta=e^{1/e}$, $\ell=\log b$, $E(w)=e^{\ell w}$, $E^{-1}(w)=\log(w)/\ell$
(principal branch).  $L$ is the fixed point of $E$ with $0<\operatorname{Im}L<\pi$
(base $e$: $L=0.3181\ldots+1.3372\ldots i$), $\lambda=\ell L=E'(L)$ its
multiplier ($|\lambda|=1.3746$ for base $e$).  Parameters of the shipped build
(`plan(50)`, base $e$):

| symbol | name in `build.py` | value |
|---|---|---|
| $D$ | `depth` | 370 |
| — | `dps` | 114 |
| $n$ | `nt` | 150 |
| $\delta$ | `idelta` | 0.1 |
| $M$ | `n_modes` | 192 |
| $n_f$ | `nf` | 404 |
| $N$ | `n_circ` | 600 |

(Base 2: $D=616$, dps $=126$, $n=200$, $N=800$, same $\delta,M,n_f$.)

**Truncated regular superfunction and its inverse.**

$$
S_D(z)=E^{\circ D}\bigl(L+\lambda^{\,z-D}\bigr),\qquad
S_D^{-1}(w)=\log_\lambda\!\bigl(\lambda^{D}\,(E^{\circ(-D)}(w)-L)\bigr),
$$

(`superf`, `isuperf`).  $S_D^{-1}\circ S_D=\mathrm{id}$ *exactly* (modulo the
period $2\pi i/\log\lambda$ of $\log_\lambda$), while
$S_D(z+1)-E(S_D(z))=E^{\circ D}(L+\lambda\varepsilon)-E^{\circ D}(E(L+\varepsilon))$,
$\varepsilon=\lambda^{z-D}$, is $O(|\lambda|^{-D})$: this is the *linearisation
floor* $|\lambda|^{-D}=|\lambda|^{-370}\approx7.6\cdot10^{-52}$ that caps the accuracy of the
whole construction.

**Input.**  $c=(c_0,\dots,c_{n-1})\in\mathbb R^{n}$ with $c_0=1$;
$P_c(z)=\sum_{k<n}c_kz^k$.

**(A) theta samples.**  $t_j=j/n_f-\tfrac12$, $z_j=t_j+i\delta$
($j=0,\dots,n_f-1$),

$$\theta_j=S_D^{-1}\bigl(P_c(z_j)\bigr)-z_j ,$$

followed by `unwrap` (adds integer multiples of the period so that the samples
are continuous — a locally constant operation with zero derivative; for the
bases treated here it never fires at the fixed point).

**(B) Fourier modes.**  $a_m=\frac1{n_f}\sum_j\theta_je^{-2\pi imt_j}$,
$m=0,\dots,M-1$ (non-negative frequencies only: the modes that decay as
$\operatorname{Im}z\to+\infty$).  Define the trigonometric polynomial
$\Theta_a(z)=\sum_{m<M}a_me^{2\pi im(z-i\delta)}$; on the sample line it is the
positive-frequency part of the interpolant of the samples, and
$|e^{2\pi im(z-i\delta)}|=e^{-2\pi m(\operatorname{Im}z-\delta)}\le1$ for
$\operatorname{Im}z\ge\delta$.

**(C) circle values.**  $\zeta_j=e^{2\pi ij/N}$.  If $\operatorname{Im}\zeta_j<0$
put $z=\bar\zeta_j$ ("lower"), else $z=\zeta_j$.  Then

$$
v_j=\begin{cases}
S_D\bigl(z+\Theta_a(z)\bigr), & \operatorname{Im}z\ge\delta \quad\text{(arc)},\\[2pt]
E\bigl(P_c(z-1)\bigr), & \operatorname{Im}z<\delta,\ \operatorname{Re}z>0\quad\text{(band}^+),\\[2pt]
E^{-1}\bigl(P_c(z+1)\bigr), & \operatorname{Im}z<\delta,\ \operatorname{Re}z\le0\quad\text{(band}^-),
\end{cases}
$$

and $v_j\mapsto\overline{v_j}$ for lower points.  With $\alpha=\arcsin\delta$
the band is the pair of arcs $|\arg\zeta|<\alpha$ and $|\arg\zeta-\pi|<\alpha$;
its harmonic measure from $0$ is $\mu(\delta)=2\alpha/\pi$ ($=0.0638$ for
$\delta=0.1$; $38$ of the $600$ points are band points, $562$ arc points).

**(D) Cauchy integral (trapezoidal rule).**

$$
c'_k=\frac1N\operatorname{Re}\sum_{j<N}v_j\,\zeta_j^{-k},\quad k=1,\dots,n-1;\qquad c'_0:=1 .
$$

$T(c):=c'$.  The iteration is $c^{(i+1)}=T(c^{(i)})$ until the seam residual
$|P_c(\tfrac12)-E(P_c(-\tfrac12))|<10^{-51}$.  The shipped table $P$ is an approximate fixed point of $T$ with the
parameters above; the measured operator defect is reported in §3.5.

Two remarks on the structure.  (i) The only non-linear, deep computations are
the two chains of $D$ exponentials/logarithms in $S_D$ and $S_D^{-1}$; the rest
is polynomial evaluation and two discrete Fourier transforms.  (ii) $T$ is not
an operator on $\theta$ alone: the band uses $c$ directly through the
functional equation, so the natural state space is the coefficient vector $c$
(equivalently the polynomial $P_c$ on the closed unit disc), and $\theta$ is an
intermediate variable.  The document therefore works with $DT$ on $\mathbb R^n$
and relates it to $\theta$-space in §2.3.

## 2. The linearisation $DT$

### 2.1 Exact chain-rule formula (finite-dimensional, any $c$)

Let $h\in\mathbb R^n$ be a perturbation of $c$ and $\delta P(z)=\sum_kh_kz^k$.
Then, in the order of the four steps,

$$
\delta\theta_j=(S_D^{-1})'\bigl(P_c(z_j)\bigr)\,\delta P(z_j),\qquad
(S_D^{-1})'(w)=\frac{1}{\log\lambda\,(w_D-L)}\prod_{i=0}^{D-1}\frac1{\ell\,w_i},
\quad w_0=w,\ w_{i+1}=E^{-1}(w_i);
$$

$$
\delta a_m=\frac1{n_f}\sum_j\delta\theta_j\,e^{-2\pi imt_j};
$$

$$
\delta v_j=\begin{cases}
S_D'\bigl(z+\Theta_a(z)\bigr)\sum_{m<M}\delta a_m\,e^{2\pi im(z-i\delta)}, & \text{arc},\\[2pt]
\ell\,E\bigl(P_c(z-1)\bigr)\,\delta P(z-1), & \text{band}^+,\\[2pt]
\dfrac{\delta P(z+1)}{\ell\,P_c(z+1)}, & \text{band}^-,
\end{cases}
\qquad
S_D'(\zeta)=\log\lambda\cdot\lambda^{\zeta-D}\prod_{i=1}^{D}\ell\,w_i,\ \ w_0=L+\lambda^{\zeta-D},\ w_{i+1}=E(w_i),
$$

with $\delta v_j\mapsto\overline{\delta v_j}$ for lower points (legitimate because
$h$ is real, so $\delta P(\bar z)=\overline{\delta P(z)}$), and finally

$$
(DT\,h)_k=\frac1N\operatorname{Re}\sum_j\delta v_j\,\zeta_j^{-k}\ (k\ge1),\qquad (DT\,h)_0=0 .
$$

In matrix form, with $A\in\mathbb C^{n_f\times n}$, $A_{jk}=(S_D^{-1})'(P_c(z_j))z_j^k$;
$B\in\mathbb C^{M\times n_f}$, $B_{mj}=e^{-2\pi imt_j}/n_f$;
$C_\theta\in\mathbb C^{N_{\rm arc}\times M}$, $(C_\theta)_{jm}=S_D'(z_j+\Theta_a(z_j))e^{2\pi im(z_j-i\delta)}$;
$C_{\rm band}\in\mathbb C^{N_{\rm band}\times n}$ the band rows above;
$\mathcal E\in\mathbb C^{n\times N}$, $\mathcal E_{kj}=\zeta_j^{-k}$:

$$
DT=\frac1N\operatorname{Re}\Bigl(\mathcal E\,\bigl[\,\overline{\phantom{x}}^{\,\rm lower}\!\bigl(C_\theta BA\;;\;C_{\rm band}\bigr)\bigr]\Bigr),\qquad
DT=DT_{\rm arc}+DT_{\rm band}.
$$

This is what `demo_theta_operator.py` evaluates: the scalar factors
$(S_D^{-1})'$, $S_D'$, $\ell E(P_c(z-1))$, $1/(\ell P_c(z+1))$ in mpmath at the
build precision (chain rule through the $D$-fold chains), the matrices in
float64, and the products in numpy.  Two independent checks: finite differences
$\bigl(T(c+\varepsilon e_k)-T(c)\bigr)/\varepsilon$ with $\varepsilon=10^{-38}$ at
dps 114 agree with the columns of $DT$ to $\sim10^{-13}$ relative (§3), and the
script's $T(c)$ agrees with one pass of `kneser.build` itself (`seed="baked"`,
`n_loops=1`) to the working precision.

### 2.2 Function-space form at the fixed point

Let $F$ be Kneser's sexp for base $b$ and $S$ the exact regular superfunction at
$L$.  Then $F(z)=S(z+\theta(z))$ with $\theta$ $1$-periodic, holomorphic in the
upper half-plane, $\theta(z)\to a_0$ as $\operatorname{Im}z\to\infty$
(only non-negative Fourier modes).  At height $\delta=0.1$ the shipped table
gives $\max_j|\theta_j|=1.106$ — $\theta$ is not small, it is the whole
difference between the regular superfunction and Kneser's solution; what is
small is its high modes ($|a_m|\lesssim e^{-2\pi m\delta}$ relative).

Differentiating $S^{-1}(F(z))=z+\theta(z)$ gives $(S^{-1})'(F(z))=(1+\theta'(z))/F'(z)$.
Put

$$
\sigma(z):=S'\bigl(z+\theta(z)\bigr)=\frac{F'(z)}{1+\theta'(z)},\qquad u:=\frac{h}{\sigma}\quad(h=\delta P).
$$

Then $\delta\theta=u$ on the sample line, and, using
$F'(z)=\ell E(F(z-1))F'(z-1)$ and the periodicity of $1+\theta'$,

$$
\ell E(F(z-1))\,h(z-1)=\frac{F'(z)}{F'(z-1)}\,\sigma(z-1)\,u(z-1)=\sigma(z)\,u(z-1),\qquad
\frac{h(z+1)}{\ell F(z+1)}=\sigma(z)\,u(z+1).
$$

So, writing $\Pi_+^\delta u:=\Theta_{a(u)}$ for the positive-frequency
trigonometric interpolant of the samples $u(t_j+i\delta)$ evaluated at
$z-i\delta$, and $\mathcal P$ for the (discrete) Cauchy projection (D),

$$
\boxed{\;DT\,h=\mathcal P\bigl[\sigma\cdot W u\bigr],\qquad
(Wu)(\zeta)=\begin{cases}\Pi_+^\delta u(\zeta) & \text{arc}\\ u(\zeta\mp1) & \text{band}^\pm\end{cases},\quad u=h/\sigma\;}
$$

(with conjugate-symmetric extension to the lower half circle).  In words: $DT$
is conjugate, by the multiplier $\sigma$, to the map $W$ that replaces $u$ on the
arc by the upward-decaying half of its periodisation and on the band by the
shift $u(\zeta\mp1)$ — which lands at $|\zeta\mp1|\le2\sin(\alpha/2)\approx\delta$,
i.e. at the expansion point where $u$ is best known — followed by the Cauchy
projection.  On the arc and on the sample line the multiplier is bounded and
bounded away from zero (base $e$: $0.66\le|\sigma|\le2.38$ at the arc points,
$0.50\le|(S_D^{-1})'|\le1.45$ on the line).

*Caveat (real axis).*  Kneser's $\theta$ is analytic in the upper half-plane
but singular at the integers: $S^{-1}\circ F$ passes through $\log0$ at
$z=0,\pm1$ ($F(0)=1$, $F(1)=e$, $F(-1)=0$ are on the singular orbit of the
logarithm chain).  Hence $\sigma=F'/(1+\theta')\to0$ as $z\to\pm1$, $u=h/\sigma$
blows up there, and the rewriting of the band data as $\sigma(z)u(z\mp1)$ is only
formal near $\zeta=\pm1$; the band data itself, $F'(z)h(z-1)/F'(z-1)$, is
perfectly regular.  This is precisely why `build.py` uses the functional
equation and not the theta correction near the real axis.  The
$u$-coordinates are used below only on the arc and on the sample line.

### 2.3 Where the contraction comes from

Take $u$ itself $1$-periodic and real-symmetric, $u=\sum_mb_me^{2\pi imz}$ with
$b_{-m}=\bar b_m$: this is the tangent direction of the family
$F_\varepsilon(z)=F(z+\varepsilon(z))$ of *exact* solutions of the functional
equation that the real-axis residual cannot see (`error-certificate.md`, §4),
and it is exactly the family the operator must annihilate for the fixed point
to be Kneser's.  For such $u$, $W u$ equals $\Pi_+u$ on the arc and $u$ on the
band, so with $\Pi_-u=\sum_{m<0}b_me^{2\pi imz}$ (the part that *grows*
upward), and $\Pi_+'$ the strictly positive part,

$$
DT h=\mathcal P[\sigma u]-\mathcal P\bigl[\sigma\,(\Pi_-u\,\mathbf 1_{\rm upper\ arc}+\Pi_+'u\,\mathbf 1_{\rm lower\ arc})\bigr] .
$$

If $\sigma\Pi_-u$ were holomorphic in the disc one would have
$\mathcal P[\sigma\Pi_-u\mathbf 1_{\rm circle}]=\sigma\Pi_-u$ (up to aliasing), hence

$$
DT h\approx b_0\sigma+\mathcal P\Bigl[\sigma\bigl(\Pi_-u\,\mathbf 1_{\{\operatorname{Im}\zeta<\delta\}}+\Pi_+'u\,\mathbf 1_{\{\operatorname{Im}\zeta>-\delta\}}\bigr)\Bigr]-(\text{normalisation}),
$$

and on the indicated sets the respective parts are the *decaying* ones:
$|\Pi_-u(\zeta)|\le\sum_{m\ge1}|b_m|e^{2\pi m\operatorname{Im}\zeta}$ with
$\operatorname{Im}\zeta<\delta$.  The input $h=\sigma u$, by contrast, contains the
growing part on the whole circle, of size $|b_m|e^{2\pi m}$ at the top of the
circle.  This is the mechanism: **the theta step keeps, of each periodic mode,
only the half that decays upward; the conjugate symmetry keeps only the half
that decays downward; the Cauchy projection then sees a function that is
$O(e^{2\pi m\delta}|b_m|)$ instead of $O(e^{2\pi m}|b_m|)$.**  Because of the
real-axis singularities of $\theta$ (caveat in §2.2) this derivation is
heuristic — $\sigma\Pi_-u$ is holomorphic only off the real axis — and its
quantitative content is checked numerically in §3.4: the measured
tangent-direction contraction is $\approx e^{-\pi m}$ per mode in the
$(1,\tfrac12)$-norm and $\approx e^{-2\pi m}$ in $\ell^2$, exactly the growth of
the norm of $\cos(2\pi mz)$ on $|z|=\tfrac12$ resp. $|z|=1$, and the only direction
that is not strongly contracted at the first step is $m=0$ (the constant shift
$\theta\mapsto\theta+b_0$, i.e. $F(z)\mapsto F(z+b_0)$), which the normalisation
$c_0'=1$ turns into $b_0(\sigma-\sigma(0))$ — a non-periodic direction that the
next pass contracts.  The spectral radius, not the one-pass norm, is what the
empirical per-pass rate measures.

For a *general* (non-periodic) $u$, $\Pi_+^\delta u$ is the positive half of the
periodisation of $u|_{\rm line}$; the periodisation has a jump at
$\pm\tfrac12+i\delta$ and Fourier coefficients decaying only like $1/m$.  The
arc data is then not small pointwise near the ends of the arc, and the
contraction of $DT$ on such $u$ is a genuinely two-dimensional cancellation
between the arc data and the Cauchy kernel.  This is why the analytic bounds
of §4.2 are loose and the matrix has to be evaluated.

## 3. Numerical spectra and norms

All numbers from `demo_theta_operator.py` on galic (32 cores, mpmath 1.3,
numpy 2.5); JSON files in `docs/_generated/goal3/`.  "Fixed point" means the
shipped table (base $e$, base 2: `_coeffs.py`, `_coeffs_2.py`, truncated to
the `nt` of the parameter set), or the registry table built on demand by
`kneser.build` with the linear seed (bases 3, 10, 20, 100).  For the
parameter sets with `digits` $<50$ the shipped 50-digit table is a fixed point
of the corresponding $T$ only up to its own floor $|\lambda|^{-D}$, which is
irrelevant for the Jacobian.

Norms used below, for a coefficient vector $h=(h_k)$:
$\|h\|_{1,r}=\sum_k|h_k|r^k$ (so $\sup_{|z|\le r}|\delta P|\le\|h\|_{1,r}$),
$\|h\|_{2,r}=(\sum|h_k|^2r^{2k})^{1/2}$, $\|h\|_{\infty,w}=\max_k w_k|h_k|$.
Induced operator norms are exact (column/row sums, largest singular value) on
the float64 matrix; the spectral radius $\rho(DT)$ is from `numpy.linalg.eigvals`
after diagonal balancing and is insensitive to the balancing weight, to
truncating the matrix to the first $n/2$ or $3n/4$ coefficients (all
$\rho$'s agree to 5 digits), and to the parameter set (`digits` 12, 24, 50).

### 3.1 Base $e$: $\rho(DT)$ against the empirical law

The empirical per-pass residual multiplier from `research-findings-zh.md`
§4.2 (`digits=24`, Carleman seed, clean regime) is $10^{-(\text{digits/loop})}$;
the four-point fit was $\kappa(\delta)\approx0.017+\delta/2\pi$.

| $\delta$ | `digits` | $M$ | $n_f$ | $\rho(DT)$ | $0.017+\delta/2\pi$ | measured $10^{-\mathrm{d/loop}}$ (d=24) | next eigenvalues |
|---|---|---|---|---|---|---|---|
| 0.05 | 24 | 184 | 388 | **0.02421** | 0.02496 | $10^{-1.606}=0.0248$ | 0.00795, $-2.7\cdot10^{-5}\pm5.9\cdot10^{-5}i$ |
| 0.05 | 50 | 375 | 770 | **0.02451** | 0.02496 | — | 0.00798 |
| 0.10 | 12 | 52 | 124 | 0.03208 | 0.03292 | — | 0.00649 |
| 0.10 | 24 | 96 | 212 | **0.03273** | 0.03292 | $10^{-1.481}=0.0330$ | 0.00676, $-1.7\cdot10^{-4}$ |
| 0.10 | 50 | 192 | 404 | **0.03312** | 0.03292 | ($10^{-1.413}=0.039$ at d=80, loops 0–20 average) | 0.00662, $-1.8\cdot10^{-4}$, $6.5\cdot10^{-5}$ |
| 0.20 | 24 | 52 | 124 | **0.04945** | 0.04883 | $10^{-1.305}=0.0495$ | 0.00243, $-0.00201$ |
| 0.20 | 50 | 100 | 220 | **0.04995** | 0.04883 | — | 0.00247, $-0.00189$ |
| 0.30 | 24 | 38 | 96 | **0.06388** | 0.06475 | $10^{-1.196}=0.0637$ | $-0.0056\pm0.0019i$ |

The spectral radius of the linearisation reproduces the *measured* per-pass
contraction approximately at every $\delta$ (0.0242/0.0248, 0.0327/0.0330,
0.0495/0.0495, 0.0639/0.0637), i.e. better than the two-parameter fit does.
The leading eigenvalue is real and simple; the second is real and about 5
times smaller at $\delta=0.1$ (the ratio $\rho_1/\rho_2$ is $\approx5.0$ at
$\delta=0.1$, $3.1$ at $\delta=0.05$, $20$ at $\delta=0.2$).  The convergence of
the builder is therefore governed by a single real mode, whose coefficient
vector (normalised $h_1=1$) starts $0,\,1,\,0.66,\,1.81,\,0.86,\,1.15,\,0.49,\,0.57,\,0.23,\,0.27,\dots$
— a real-symmetric perturbation with the $2^{-k}$ envelope of the table itself,
not a single Fourier mode of $\theta$.

### 3.2 Base dependence

| base | `digits` | $\delta$ | $D$ | $|\lambda|$ | $\rho(DT)$ | second eigenvalue | measured (source) |
|---|---|---|---|---|---|---|---|
| 2 | 12 | 0.1 | 160 | 1.2277 | 0.05657 | 0.00818 | `plan`: `n_loops = digits+12` ($\approx1.2$ digits/loop $\leftrightarrow0.06$) |
| 2 | 50 | 0.1 | 616 | 1.2277 | 0.05660 | 0.00863 | |
| 3 | 17 | 0.1 | 129 | 1.4140 | 0.02575 | 0.00091 | — |
| $e$ | 50 | 0.1 | 370 | 1.3746 | 0.03312 | 0.00662 | 0.033 |
| 10 | 20 | 0.03 | 99 | 1.7499 | 0.15679 | 0.0323 | — |
| 20 | 16 | 0.03 | 75 | 1.8799 | 0.23839 | 0.0517 | 0.37 at $\delta=0.1$ (`general-base.md`) |
| 100 | 16 | 0.03 | 66 | 2.1037 | 0.33371 | $-0.231$ | **0.34** at $\delta=0.03$ (`plan()` comment) |

For base 100 the two leading eigenvalues ($0.334$ and $-0.231$) are of
comparable size, so the residual sequence there should show the beat pattern
of two modes; for base $e$ it does not.  Base 2 contracts more slowly than
base $e$ ($0.057$ vs $0.033$) although $|\lambda|$ is smaller, and base 3 faster
($0.026$): the rate is not a monotone function of the multiplier alone.  For
large bases the multiplier $S_D'$ on the arc becomes large ($\sup|S_D'|=25$ for
base 10, $67$ for base 20, $540$ for base 100, against $2.38$ for base $e$),
which is the visible reason for the slow-down.

### 3.3 Norms, blocks, resolvent (base $e$, `digits=50`, $\delta=0.1$)

Operator norms of $DT$ (float64 matrix; the candidate interval versions in §4.3 agree
to the digits shown):

| norm | $\|DT\|$ | $\|DT_{\rm arc}\|$ | $\|DT_{\rm band}\|$ | $\|(I-DT)^{-1}\|$ |
|---|---|---|---|---|
| $(1,\tfrac12)$ | **0.4254** | 0.3543 | 0.0749 | **1.4428** |
| $(1,0.51)$ | 0.4390 | | | 1.4570 |
| $(1,0.55)$ | 0.51 | | | |
| $(1,0.7)$ | 0.76 | | | |
| $(1,1)$ | 1.665 | 2.52 | 1.93 | 2.718 |
| $(1,1.5)$ | $9\cdot10^{22}$ | | | |
| $(2,\tfrac12)$ | 0.2986 | | | 1.184 |
| $(2,1)$ | 0.8074 | | | 1.524 |
| $(\infty,1)$ | 0.597 | | | |
| $(\infty,2^{-k})$ | 1.164 | | | |
| $(\infty,2^{k})$ | $2\cdot10^{41}$ | | | |

Spectral radii of the blocks: $\rho(DT_{\rm arc})=0.03327$,
$\rho(DT_{\rm band})=3.2\cdot10^{-4}$.  **The per-pass rate is carried entirely by
the theta (arc) block**; the functional-equation band is, by itself, an almost
nilpotent operator (it maps a perturbation to its values at $|\zeta\mp1|\lesssim0.1$,
i.e. near the expansion point, and the Cauchy step then spreads that over
$\mu(\delta)=6\%$ of the circle).  The $\delta$-dependence of $\rho$ is therefore
not the harmonic measure of the band but the height at which the Fourier modes
of $\theta$ are sampled and reconstructed.

Norms with $r<\rho_\delta$ may amplify sample evaluation; norms with $r>1$ or with rapidly growing output weights can also be large
because $T$ evaluates $P_c$ on the sample line $|z_j|\le0.51$ and on the band
at $|\zeta\mp1|\le0.1$ but never on the unit circle, so a perturbation that is
small in a norm controlling only $|z|\le\tfrac12$ can be large where $T$ looks;
conversely the Cauchy step produces coefficients with a $1/k$ tail from any
jump in the circle data, which the $2^k$-weighted norm punishes with $2^{149}$.
The natural norms are $(1,r)$ and $(2,r)$ with $r\in[0.51,\,1]$, and among them
$\|DT\|<1$ holds for $r\le0.7$ in the $\ell^1$ family and for $r\le1$ in the
$\ell^2$ family.  (For $\delta=0.2$ and $0.3$, where $\sqrt{1/4+\delta^2}=0.54,\,0.58$,
the $(1,\tfrac12)$ norms are $113$ and $155$ — the norm must be taken with
$r\ge\sqrt{1/4+\delta^2}$; $\rho$ is unaffected.)

Powers, $\|DT^n\|_{1,1/2}$ for $n=1,\dots,8$:
$0.425,\ 0.0167,\ 5.8\cdot10^{-4},\ 1.9\cdot10^{-5},\ 6.4\cdot10^{-7},\ 2.1\cdot10^{-8},\ 7.1\cdot10^{-10},\ 2.3\cdot10^{-11}$
— after the first pass the ratio settles at $\rho=0.0331$; the one-pass norm
$0.43$ is the transient of a non-normal operator, not the asymptotic rate.
Consistently, $\|(I-DT)^{-1}\|_{1,1/2}=1.4428$, close to $1/(1-0.4254)=1.74$ only
as an upper bound and much closer to $1+0.43+0.017+\dots$.

### 3.4 The $\theta$-family tangent directions

For $h=P'(z)\cos(2\pi mz)$ and $P'(z)\sin(2\pi mz)$ (tangents to
$F(z+\varepsilon(z))$, §2.3), the ratios $\|DT\,h\|/\|h\|$:

| $m$ | $(1,\tfrac12)$, cos | $(1,\tfrac12)$, sin | $\ell^2$, cos | $\ell^2$, sin |
|---|---|---|---|---|
| 0 | 0.307 | — | 0.643 | — |
| 1 | $1.72\cdot10^{-2}$ | $4.0\cdot10^{-3}$ | $5.5\cdot10^{-3}$ | $2.2\cdot10^{-3}$ |
| 2 | $6.8\cdot10^{-4}$ | $1.6\cdot10^{-4}$ | $1.4\cdot10^{-5}$ | $8.6\cdot10^{-6}$ |
| 3 | $3.2\cdot10^{-5}$ | $6.0\cdot10^{-6}$ | $3.8\cdot10^{-8}$ | $3.0\cdot10^{-8}$ |
| 4 | $1.7\cdot10^{-6}$ | $2.0\cdot10^{-7}$ | $1.1\cdot10^{-10}$ | $9.9\cdot10^{-11}$ |

Per mode the $(1,\tfrac12)$ ratio drops by $\approx0.045\approx e^{-\pi}$ and the
$\ell^2$ ratio by $\approx e^{-2\pi}$: exactly the growth of the norm of
$\cos(2\pi mz)$ on $|z|=\tfrac12$ resp. $|z|=1$, while the output stays $O(1)$
— the mechanism of §2.3.  The $m=0$ direction ($F\mapsto F(z+b_0)$) is the
least contracted, as predicted ($0.643$ in $\ell^2$ is
$\|F'-F'(0)\|/\|F'\|$).  These directions are the ones invisible to the
real-axis residual; the operator kills them fastest.

### 3.5 Consistency checks

* Finite differences: $\bigl(T(c+\varepsilon e_k)-T(c)\bigr)/\varepsilon$,
  $\varepsilon=10^{-38}$, dps 114, against column $k$ of $DT$: relative
  deviation $1.2\cdot10^{-14}$ ($k=1$), $1.1\cdot10^{-14}$ ($k=5$),
  $1.4\cdot10^{-14}$ ($k=20$), $9.6\cdot10^{-8}$ ($k=60$, a column of size
  $1.2\cdot10^{-20}$, i.e. $10^{-27}$ absolute: float64 assembly noise).
  Same level for every base.
* `kneser.build` itself (`seed="baked"`, `n_loops=1`) versus the script's
  $T(c)$: $\max_k|\Delta c_k|=3.5\cdot10^{-65}$ (dps 114 rounding).
* $\|T(P)-P\|_{1,1/2}=3.55\cdot10^{-52}$, $\|T(P)-P\|_{1,1}=3.5\cdot10^{-51}$,
  $\max_k|T(P)_k-P_k|=6.5\cdot10^{-52}$: the shipped table is a fixed point of
  the truncated $T$ to the linearisation floor $|\lambda|^{-370}=7.6\cdot10^{-52}$.
  (In the $2^k$-weighted norm the same vector has size $1.8\cdot10^{-9}$: the
  tail coefficients are known absolutely, not relatively.)
* Lipschitz constant of $c\mapsto DT(c)$ in the $(1,\tfrac12)$ norm, from one
  finite difference of size $10^{-4}$: $\approx0.35$ (and $\approx0.99$ in $(1,1)$).
  This single-direction estimate does not bound a neighborhood; the candidate
  ball enclosure in §4.4 targets that stronger statement.

## 4. What is proved about $\|DT\|$

Throughout, $\rho_\delta:=\sqrt{1/4+\delta^2}=\max_j|z_j|$ ($=0.5099$ for
$\delta=0.1$), and the legacy script label "verified" means only that: every scalar factor was evaluated in
interval arithmetic (mpmath `iv` boxes at 230 decimal digits for base $e$,
279 for base 2; independently with the circular-interval arithmetic of §4.4),
the fixed point $L$ was enclosed by a Krawczyk test, and the matrix products
and norms were evaluated in Rump's midpoint–radius arithmetic with Higham's
$\gamma_n$ bound for every float64 dot product (`iv_matmul`,
`verified_norms` in the script).  This is not yet an audited enclosure: the unresolved proof obligations are
spelled out in §6. Numerical factor bounds below inherit that limitation.

### 4.1 Elementary rigorous pieces

**(P1) The Cauchy step.**  From $(DT h)_k=\frac1N\operatorname{Re}\sum_j\delta v_j\zeta_j^{-k}$,
$|(DTh)_k|\le\frac1N\sum_j|\delta v_j|\le\max_j|\delta v_j|$, hence for every $r<1$

$$\|DTh\|_{1,r}\le\frac{1}{1-r}\cdot\frac1N\sum_j|\delta v_j| .$$

The discrete Cauchy projection is bounded from the mean modulus of the
circle data to every $(1,r)$-norm with constant $1/(1-r)$ (not a contraction
when that constant exceeds 1) (and it is an
orthogonal projection, constant 1, from $\ell^2$ of the circle samples to the
$\ell^2$ coefficient norm).

**(P2) The band block.**  For a band point, $|z\mp1|\le2\sin(\alpha/2)=0.1002\le\rho_\delta$, so
$|\delta P(z\mp1)|\le\|h\|_{1,\rho_\delta}$ and $|\delta v_j|\le\beta\|h\|_{1,\rho_\delta}$ with
$\beta=\max\bigl(\max_{\rm band^+}|\ell E(P(z-1))|,\max_{\rm band^-}|1/(\ell P(z+1))|\bigr)$.
With (P1):

$$\|DT_{\rm band}\|_{(1,\rho_\delta)\to(1,\rho_\delta)}\le\frac{N_{\rm band}}{N}\cdot\frac{\beta}{1-\rho_\delta}.$$

Base $e$, digits 50: $N_{\rm band}/N=38/600$, $\beta=e$ (attained at $\zeta=1$:
$\ell E(P(0))=e$; candidate interval value $2.718281828459045$), giving
$\|DT_{\rm band}\|\le0.3513$.  The true norm is $0.0749$.  Base 2:
$\beta=1/\ln2=1.4427$, bound $0.184$, true $0.030$.

**(P3) Sup-bounds of the deep factors** (estimated by interval evaluation at
the finitely many points where they enter): base $e$,
$\max_{\rm arc}|S_D'(z+\Theta)|\le2.375913$, $\max_j|(S_D^{-1})'(P(z_j))|\le1.450733$;
base 2: $1.072463$ and $1.768444$.

**(P4) The arc block, crude bound.**  $|\delta\theta_j|\le\bar\sigma\|h\|_{1,\rho_\delta}$
with $\bar\sigma$ from (P3); by Parseval for the DFT,
$\sum_{m<M}|\delta a_m|^2\le\frac1{n_f}\sum_j|\delta\theta_j|^2\le\bar\sigma^2\|h\|^2_{1,\rho_\delta}$;
by Cauchy–Schwarz over the modes,
$|\delta v_j|\le s\,\bar\sigma\,\|h\|_{1,\rho_\delta}\,K_j$ with $s=\max|S_D'|$ and
$K_j=\bigl(\sum_{m<M}e^{-4\pi m(y_j-\delta)}\bigr)^{1/2}\le\min\bigl(M,(1-e^{-4\pi(y_j-\delta)})^{-1}\bigr)^{1/2}$;
and by (P1)

$$\|DT_{\rm arc}\|_{(1,\rho_\delta)\to(1,\rho_\delta)}\le\frac{s\,\bar\sigma}{1-\rho_\delta}\cdot\frac1N\sum_{\rm arc}K_j .$$

Base $e$, digits 50: $\frac1N\sum K_j=0.9993$, bound $=2.04\cdot2.3759\cdot1.4507\cdot0.9993=7.03$;
total analytic bound $\|DT\|_{1,\rho_\delta}\le7.38$.  Base 2: $3.91+0.18=4.10$.
**The analytic inequalities are rigorous; their displayed numerical evaluations are candidates and exceed 1** ($>1$); the true norms are
$0.35$ (arc) and $0.43$ (total) for base $e$, $0.10$ for base 2.  The loss is
in the Cauchy–Schwarz step over the modes (it assumes all $M$ modes of
$\delta\theta$ to be aligned and of equal size, while for any smooth $h$ the
$\delta a_m$ decay) and in (P1) applied to the arc data (which is nearly the
boundary value of an analytic function, so that the Cauchy projection loses
most of it by cancellation; (P1) ignores all cancellation).  A sharper
analytic bound would have to keep track of the phase of the modes on the arc
— i.e. do what the matrix does.

### 4.2 Heuristic bound for the periodic directions

For $h=\sigma u$ with $u=2\operatorname{Re}(b_me^{2\pi imz})$, the derivation of §2.3
gives (idealised operator, aliasing and the real-axis singularity ignored)

$$
\frac{\|DTh\|_{\ell^2}}{\|h\|_{\ell^2}}\lesssim\frac{\sup|\sigma|}{\inf|\sigma|}\cdot
\frac{\bigl(J_m(\delta)\bigr)^{1/2}}{\|\cos(2\pi m\,\cdot)\|_{L^2(\mathbb T)}},\qquad
J_m(\delta)=\frac1\pi\int_{\{\sin\varphi<\delta\}}e^{4\pi m\sin\varphi}\,d\varphi .
$$

For $m=1$, $\delta=0.1$: $J_1=0.18$, $\|\cos(2\pi\cdot)\|_{L^2(\mathbb T)}=\bigl(\tfrac12(I_0(4\pi)+J_0(4\pi))\bigr)^{1/2}=127$,
ratio $\lesssim3.6\cdot0.42/127=0.012$ (with $\sup|\sigma|/\inf|\sigma|=2.38/0.66$); measured $0.0055$ (cos) and $0.0022$
(sin).  For $m\ge2$ the bound decays like $e^{-2\pi m(1-\delta)}$; measured
$1.4\cdot10^{-5}$, $3.8\cdot10^{-8}$, $1.1\cdot10^{-10}$ for $m=2,3,4$.  So the
mechanism of §2.3 accounts quantitatively for the annihilation of the
$\theta$-family, which is the part of the uniqueness question that the
real-axis residual cannot see.  It does not account for $\rho(DT)$ itself,
which lives on non-periodic directions.

### 4.3 Candidate enclosures of the finite-dimensional operator

Base $e$, `plan(50)` parameters, $DT$ at the shipped table $P$ (interval
precision 230 digits; enclosure radius of every matrix entry
$\le3.3\cdot10^{-13}$, dominated by the float64 $\gamma_n$ terms; midpoints agree
with the float64 build to $4\cdot10^{-15}$):

| quantity | candidate bound | float value |
|---|---|---|
| $\|DT(P)\|_{1,1/2}$ | $\le0.425422$ | 0.42542 |
| $\|DT(P)\|_{1,0.51}$ | $\le0.439040$ | 0.43904 |
| $\|DT(P)\|_{1,1}$ | $\le1.665183$ | 1.66518 |
| $\|(I-DT(P))^{-1}\|_{1,1/2}$ | $\le1.442760$ | 1.44276 |
| $\|(I-DT(P))^{-1}\|_{1,0.51}$ | $\le1.457032$ | 1.45703 |
| $\|(I-DT(P))^{-1}\|_{1,1}$ | $\le2.718282$ | 2.71828 |
| $\|DT(P)\|_{G}$, $\|x\|_G:=\|Gx\|_\infty$, $G\approx V^{-1}$, $V$ the float eigenbasis of the $2^{-k}$-balanced matrix | $\le0.033158$ | ($\rho=0.033116$) |
| $\|DT(P)\|_{G}$, same with $0.51^{k}$ balancing | $\le0.033126$ | |
| $\|T(P)-P\|_{1,1/2}$ | $\le3.555\cdot10^{-52}$ | $3.5545\cdot10^{-52}$ |

If its enclosure and rounding obligations are validated, the eigen-norm line would prove "$\rho(DT)<1$": there is
an explicit norm (the $\infty$-norm after the change of basis $G$, a $150\times150$
float64 matrix constructed during the run, but not saved) in which $DT(P)$ is a contraction with
constant $0.0332$; the bound is $\|GBV\|_\infty/(1-\|I-GV\|_\infty)$ with
$\|I-GV\|_\infty\le1.2\cdot10^{-3}$ (condition number of $V$: $6\cdot10^{15}$).
For $r=1$ the eigenbasis is too ill-conditioned ($10^{58}$) and the test fails;
for base 2 it fails already at $r=\tfrac12$ ($10^{22}$), but there
$\|DT\|_{1,1/2}\le0.0975$ makes it unnecessary.

Base 2, `plan(50)` parameters ($D=616$, interval precision 279):

| quantity | candidate bound |
|---|---|
| $\|DT(P)\|_{1,1/2}$ | $\le0.097483$ |
| $\|DT(P)\|_{1,1}$ | $\le0.495098$ |
| $\|(I-DT(P))^{-1}\|_{1,1/2}$ | $\le1.098626$ |
| $\|T(P)-P\|_{1,1/2}$ | $\le3.814\cdot10^{-53}$ |

### 4.4 Candidate enclosure over a ball (Lipschitz-free contraction)

Box (`iv`) arithmetic cannot enclose $DT$ over a ball of coefficient vectors:
a box of radius $10^{-48}$ around $P(z_j)$ is rotated $370$ times by the
argument of $\lambda$, and rectangular enclosures grow by a factor
$|\cos\arg\lambda|+|\sin\arg\lambda|=1.2$ per rotation, $10^{27}$ in total,
before the $(w-L)$ division amplifies by another $10^{51}$.  The script
therefore implements circular complex intervals (`Disc`, `DiscCtx`): centre
$c$, radius $r$, with $\exp$: $r\mapsto|e^c|(e^r-1)$, $\log$: $r\mapsto-\log(1-r/|c|)$,
products $r\mapsto|c_1|r_2+|c_2|r_1+r_1r_2$, transcendental centers evaluated through `iv` point evaluations, while
basic arithmetic centers use ordinary mpmath operations and generous radius
inflation. This mixed implementation still needs the rounding audit in §6.  Discs are rotation-invariant, so the
chains propagate radii exactly like the derivative does.  With the coefficient
discs $x_k\in\{|x_k-c_k|\le R\,2^k\}$, which contain the $(1,\tfrac12)$-ball of
radius $R$, a correct implementation of all enclosure and branch operations would give
a bound uniform over the ball. The coefficient box is a conservative
superset, including variation in $c_0$ that the affine ball does not need.

Recovered completed runs (all $R=10^{-50}$ in the $(1,1/2)$ norm):

| base | candidate $\sup_{B_R(P)}\|DT\|_{1,1/2}$ | candidate point defect $\eta=\|T(P)-P\|_{1,1/2}$ | source |
|---|---|---|---|
| $e$ | 0.4254218508914162 | $3.5545137615010434\cdot10^{-52}$ | `out4/ball/dt_e_d50_delta0.1.json`, `out4/point/dt_e_d50_delta0.1.json` |
| 2 | 0.09748303284179527 | $3.813360538609268\cdot10^{-53}$ | corresponding base-2 files |

These pass the numerical self-mapping inequality $\eta+qR<R$ by a wide
margin. They do **not** yet establish its hypotheses rigorously: the disc
principal-log guard was absent in the recovered runs, interval evaluation
skips unwrap, and all rounding stages have not been audited. The added guard
is a defensive repair; it does not retroactively certify these outputs.
The low-precision exploratory run `out4/dt_e_d12_delta0.1.json` used
$R=10^{-13}$ while the point defect is about $1.8\cdot10^{-11}$; it does not
even pass self-mapping and must not be used for a fixed-point claim.

### 4.5 Exact certificate for the stored finite linear models

Let $A$ denote exactly the real matrix represented by
`out2/dt_e_d50_delta0.1.npy` (or its base-2 counterpart), interpreting each
binary64 entry as its exact dyadic rational. Set $w_k=2^{-k}$ and

$$q_A=\max_j\sum_i |A_{ij}|2^{j-i}.$$

`--certify-stored-matrix` evaluates this formula with Python `Fraction`:
there are no rounded sums, powers, or comparisons. The archived JSON contains
the exact numerator/denominator of $q_A$, its Neumann bound, and the SHA-256
of the input matrix. It proves:

| precise object | dimension | proved $q_A$ bound | proved resolvent bound |
|---|---|---|---|
| base-$e$ stored linear model | 150 | $q_A<0.426$ | $\|(I-A)^{-1}\|<1/0.574$ |
| base-2 stored linear model | 200 | $q_A<0.098$ | $\|(I-A)^{-1}\|<1/0.902$ |

Indeed $\|A^m\|\le q_A^m$ and the absolutely convergent Neumann series
inverts $I-A$. This is an unconditional finite-dimensional theorem about
these explicit rational matrices. It is **not** a certificate that
$A=DT(P)$ or that the interval matrix contains $DT$ on a ball. To transfer
the result one still needs a rigorous bound on $\|DT(x)-A\|$ uniformly in
the chosen ball, smaller than $1-q_A$.


## 5. The finite-dimensional theorem and the conditional error certificate

Work in the affine space $c_0=1$ with norm $\|h\|_{1,1/2}$ (thus $h_0=0$).
The full matrices above also include column 0; their bounds are conservative
for this invariant affine space. Let $B_R(P)$ be the closed ball there.
Suppose $T$ is continuously differentiable on an open neighborhood of that
ball, all chosen logarithm branches and unwrap decisions are stable, and
rigorous enclosures establish

$$\|T(P)-P\|\le\eta,\qquad
  \sup_{x\in B_R(P)}\|DT(x)\|\le q<1,\qquad \eta+qR\le R.$$

Then the mean-value integral gives
$\|T(x)-T(y)\|\le q\|x-y\|$ on the convex ball and
$\|T(x)-P\|\le\eta+qR\le R$. Banach's theorem gives a unique fixed point
$c^*$ **in that ball**, and

$$\|P-c^*\|_{1,1/2}\le\frac{\eta}{1-q},\qquad
\sup_{|z|\le1/2}|P(z)-P_{c^*}(z)|\le\frac{\eta}{1-q}.$$

Using deliberately rounded candidate values, base $e$ would give
$\eta\le3.555\cdot10^{-52}$, $q\le0.426$, hence distance
$<6.20\cdot10^{-52}$; base 2 would give $\eta\le3.814\cdot10^{-53}$,
$q\le0.098$, hence $<4.23\cdot10^{-53}$. Both fit in $R=10^{-50}$.
These are **conditional numerical conclusions**, pending §6's audit.
The point resolvent estimate $1.44276$ cannot replace $1/(1-q)$ in this
nonlinear theorem without a separate Newton/remainder argument. Neither can
the spectral radius $0.03312$ be substituted into a different norm's bound.

Even a completed proof here would control the polynomial $P_{c^*}$, not
Kneser's $F$. To get the latter, one possible rigorous route is an ideal
operator $\mathcal T$ with fixed point $F$, uniform contraction $q$ in a
specified function norm, and consistency error
$\|\mathcal T(P)-T(P)\|\le\varepsilon_{\rm disc}$. Then, provided the invariant
neighborhood hypotheses hold,

$$\|P-F\|\le\frac{\eta+\varepsilon_{\rm disc}}{1-q}.$$

Alternatively establish $\|P_{c^*}-F\|\le\varepsilon_K$ independently and add
that term to the finite-dimensional distance. No value of
$\varepsilon_{\rm disc}$ or $\varepsilon_K$ is proved here.
The real-axis functional-equation defect (for example $7\cdot10^{-52}$)
is not $\eta=\|T(P)-P\|$ and has an infinite-dimensional ambiguity described
in `error-certificate.md` §4. A formula $C\,\mathrm{residual}/(1-q)$ would
additionally require a proved estimate linking that residual to the operator
defect and controlling the ambiguity. There is no established $C$ here.

## 6. Certification gaps and reproduction

The original `verified_*` function names and old JSON keys are historical
labels. Revised script outputs explicitly record `certificate_status:
not_certified` for nonlinear experiments. The exact stored-matrix command
states its narrower object separately.

1. **Principal logarithm and regularity.** The recovered `DiscCtx.log`
   checked only whether the disc contains zero. A disc centered at $-1$ with
   positive radius avoids zero yet crosses the principal cut; its principal
   logarithm is discontinuous, so the radius formula for a local analytic
   logarithm is not an enclosure of that principal branch. The code now
   rejects discs meeting the nonpositive real axis. This must be exercised
   through a fresh complete run, and all divisors must stay separated from
   zero over the ball. Freezing sample geometry defines a valid finite
   operator, but equivalence to the builder also needs branch decisions to
   match at the center and throughout the ball.
2. **Unwrap.** Floating evaluation unwraps consecutive theta samples by a
   nearest-integer test. Interval/disc evaluation does not perform this
   operation at all. A rigorous local proof must record every center integer
   and show the interval for its decision variable stays strictly within the
   corresponding half-integer cell. If integers are not all zero, their
   shifts must be included in interval theta values. Freezing the shifts is
   valid only after this separation test. Successful scalar evaluation alone
   does not prove stability of the branch-selection algorithm.
3. **Outward rounding.** Disc centers use ordinary mpmath arithmetic for
   addition, multiplication and inverse, with generous fixed inflation; this
   is not the claimed per-operation interval point evaluation everywhere.
   A complete error proof for these inflations, endpoint conversion,
   `expm1`/`log1p`, absolute values and final reductions is absent. Float
   matrix products use a plausible gamma bound, but the final norm,
   resolvent and eigen-norm divisions are not explicitly rounded upward.
   The $0.51^k$ weights have accumulated power error not accounted for by
   merely saying four epsilons suffice (or else the exact stored weights
   should define a different norm). Use exact dyadic $r=1/2$ and directed
   interval arithmetic throughout the final reduction for the minimal
   nonlinear certificate. The exact-rational model certificate avoids these
   issues only for its precisely stated stored matrix.
4. **Reproducible witnesses.** Existing `.npy` files save only the ordinary
   float matrix, not the interval radii or claimed eigenbasis. The old text's
   assertion that the eigenbasis was stored was false. A completed verifier
   should persist center/radius matrices, branch separation witnesses,
   fixed-point enclosure and parameter/source hashes; use a separate small
   checker. Eigenbasis work is unnecessary for the $\ell^1$ contraction.
5. **From truncation to the true function.** Finite depth, Taylor tail, both
   Fourier aliasing errors, continuation between sample nodes, and the
   identification of the ideal fixed point with Kneser's normalized solution
   need quantitative bounds. $|\lambda|^{-D}$ gives an asymptotic scale, not
   a rigorous absolute error bound with constant 1. M3.3's nonlinear
   contraction and M3.4's true-function certificate remain incomplete.

The shortest remaining nonlinear route is to keep $r=1/2$, enclose every
scalar operation with an audited complex-ball backend, record branch and
unwrap margins uniformly on $R=10^{-50}$, save the full Jacobian enclosure,
and sum its absolute weighted columns with directed/exact arithmetic. The
candidate $q\approx0.4254$ has ample margin below 1; there is no reason to
spend that margin on an ill-conditioned eigenbasis. Recheck the point defect
with the same backend and verify $\eta+qR<R$. Only after that should the
infinite-dimensional consistency work begin.

All numerical work and the exact-rational certificates run on galic; local
operations only edited files and parsed/copied existing output. Recovered
files were copied without modifying their numerical fields to
`docs/_generated/goal3/{out,out2,out4}/`. The distinct subdirectories matter:
older `out` interval precision gave a loose base-$e$ defect enclosure around
$3\cdot10^{-27}$, while `out2` achieved $3.55\cdot10^{-52}$. Do not mix these.
The directory is git-ignored; archive it separately if the experiment must
be transported to another checkout.

Reproduce the exact finite linear-model certificate (no rebuild required):

```sh
scp docs/demo_theta_operator.py galic:/data/kneser-exp/goal3/demo_theta_operator_audited.py
ssh galic 'PYTHONPATH=/data/kneser-verify/src python3 /data/kneser-exp/goal3/demo_theta_operator_audited.py --certify-stored-matrix /data/kneser-exp/goal3/out2/dt_e_d50_delta0.1.npy'
ssh galic 'PYTHONPATH=/data/kneser-verify/src python3 /data/kneser-exp/goal3/demo_theta_operator_audited.py --certify-stored-matrix /data/kneser-exp/goal3/out2/dt_2_d50_delta0.1.npy'
```

A fresh candidate nonlinear run, with its own output directory:

```sh
ssh galic 'env PYTHONPATH=/data/kneser-verify/src KNESER_CACHE=/data/kneser-verify/.cache OPENBLAS_NUM_THREADS=1 timeout 36000 python3 /data/kneser-exp/goal3/demo_theta_operator_audited.py --base e --digits 50 --delta 0.1 --interval --disc --ball 1e-50 --out /data/kneser-exp/goal3/audited-ball'
```

The guard patch does not resolve all gaps above; this command is not advertised
as a complete certificate. To regenerate ordinary spectra, omit interval,
disc and ball flags; add `--fd 1,5,20,60 --build-check` for base $e$ or 2.
For the base comparison use the parameter choices in §3.2.
