# A no-go theorem for absolute monotonicity of tetration

Status: 2026-09-12. This document proves an obstruction, not a new uniqueness
characterization of Kneser's tetration. The proof is independent of coefficient
tables and applies to every normalized real-analytic solution. Numerical results
and their limitations are in [the Chinese report](bohr-mollerup-zh.md).

**Proved.** No normalized real-analytic tetration can have every positive-order
derivative nonnegative on a single common right half-line. This also rules out
analogous absolute-monotonicity conditions on any fixed derivative, on log F,
and on log F' (where defined).

**Not proved.** A useful alternative real-axis characterization; complete
monotonicity of the inverse derivative on some common half-line; uniqueness under
order-dependent eventual positivity for arbitrary bases. For base e, the independent
Hardy-field argument shows that this weaker condition does not give uniqueness
either (section 5). In particular no numerical finite-order test
establishes an all-orders statement.

## 1. The quantifiers

Let a > 1, c = log a, and let F be real analytic on (-2,infinity), real valued,
with F(0)=1 and F(x+1)=exp(c F(x)) for x>-2. Compare

\[
(\mathrm S)\quad \exists X>-2\ \forall n\ge1\ \forall x>X:
 F^{(n)}(x)>0,
\]

with

\[
(\mathrm W)\quad \forall n\ge1\ \exists X_n>-2\ \forall x>X_n:
 F^{(n)}(x)>0.
\]

Theorem 2 excludes even the non-strict version of S. Its proof does not exclude
W: the Taylor bound below needs **all** orders nonnegative between the same two
points. Failure at one finite x, n cannot by itself exclude either an unspecified
common half-line or W. A finite grid of positive signs likewise cannot prove them.

## 2. An elementary entire-extension lemma

**Lemma 1.** Let f be real analytic on (X,infinity). If f^(n)(x)>=0 for every
n>=1 and x>X, then f is the restriction of an entire function.

**Proof.** Fix t>X. Set g(x)=f(x)-f(t)+1, so g(t)=1 and g(x)>=1 for x>=t.
For any b>t, Taylor's formula with Lagrange remainder and nonnegative derivatives
implies, for each integer N>=0,

\[
 g(b)\ge \sum_{k=0}^{N}\frac{g^{(k)}(t)}{k!}(b-t)^k.
\]

Indeed the remainder is g^(N+1)(xi)(b-t)^(N+1)/(N+1)! for some xi in (t,b)
and is nonnegative. Each summand is nonnegative. Thus for every n>=1,

\[
0\le \frac{f^{(n)}(t)}{n!}\le\frac{g(b)}{(b-t)^n}.
\]

The limit superior of the nth roots of these coefficients is at most 1/(b-t).
As b can be arbitrarily large, that limit superior is zero. The Taylor series
of f at t therefore defines an entire function E. Real analyticity gives E=f
on a neighborhood of t. The real-analytic identity theorem on the connected
interval (X,infinity) gives E=f throughout that interval. QED.

No boundedness assumption at infinity, uniform-in-order asymptotic estimate,
complex singularity location, or representation theorem is used here.

**Theorem 2 (no common absolutely monotone tail).** No F satisfying the assumptions
in section 1 has F^(n)(x)>=0 for all n>=1 on a common right half-line.

**Proof.** Suppose such a half-line exists. Lemma 1 gives an entire E equal to F
on that tail. Since both restrictions are real analytic, equality extends to
all of (-2,infinity). The entire function

\[
H(z)=E(z+1)-\exp(cE(z))
\]

vanishes on a real interval, hence is identically zero by the complex identity
theorem. At x=-1 the original functional equation and F(0)=1 give
exp(c F(-1))=1. Because F(-1) is real and c>0, F(-1)=0. Therefore E(-1)=0.
But H(-2)=0 implies E(-1)=exp(cE(-2)), which cannot vanish. Contradiction. QED.

The argument works for all a>1, not merely a>exp(1/e). For a>exp(1/e), the actual
Kneser solution and every normalized analytic periodic reparameterization are
therefore excluded by S. This is a failure of the proposed condition itself;
it is not a uniqueness proof distinguishing the unperturbed solution.

## 3. Immediate alternative-condition obstructions

**Corollary 3.** Under the same hypotheses, none of the following can have all
positive-order derivatives nonnegative on one common right half-line:

1. F^(k), for any fixed integer k>=0;
2. log F, on a tail where F>0;
3. log F', on a tail where F'>0.

**Proof.** For (1), Lemma 1 makes F^(k) entire. Repeated entire antiderivatives,
with constants chosen at a real point of agreement, give an entire extension of
F. The contradiction in Theorem 2 applies. For (2), log F(x)=c F(x-1) follows
from the functional equation, so the proposed condition is precisely a shifted
and positively scaled version of S. For (3), Lemma 1 extends log F' to an entire
G. The entire function exp(G) extends F'; an entire antiderivative with the
correct constant extends F. Again Theorem 2 applies. QED.

These are absolute-monotonicity statements (all signs positive), not statements
about alternating signs or logarithmic convexity alone.

## 4. Periodic perturbations and normalization

Let theta be real analytic, 1-periodic, theta(0)=0, and 1+theta'(x)>0. Then
h(x)=x+theta(x) is increasing, h(-2)=-2, h(0)=0, and h(x+1)=h(x)+1. Hence
G=F composed with h is real analytic on (-2,infinity), has G(0)=1, and satisfies
G(x+1)=exp(cG(x)). Such perturbations inherit the no-go theorem, just as F does.

For theta(x)=epsilon sin(2 pi m x), |epsilon|<1/(2 pi m) suffices. The numerical
script also uses raw epsilon cos(2 pi x), which preserves the equation on its
natural domain but not G(0)=1. Those rows are diagnostic only, not normalized
competitors. Subtracting epsilon from that theta would restore normalization,
but the published rows do not make that modification.

A common heuristic compares epsilon(2 pi m)^n to n!/R^n and claims the periodic
term must dominate at high order. That implication is false: for fixed R,m,
(2 pi m R)^n/n! tends to zero. Moreover derivatives of the composition contain
mixed terms and altered singularities. None of the finite-grid observations is
used to justify a universal perturbation theorem.

## 5. Remaining questions and explicit gaps

- S is impossible, so M1.2 plus M1.3 of the original plan cannot establish its
  proposed theorem. M1.3 is false under these quantifiers.
- For base e, [the Hardy-field investigation](hardy-field.md), using the stated
  external ADH criterion, proves that every smooth tetration with eventually
  everywhere positive derivative generates a Hardy field. Consequently it
  satisfies W: every derivative has an eventual sign; if its kth derivative
  were eventually nonpositive, repeated integration would bound F above by a
  polynomial of degree at most k-1. This contradicts F(x+1)=exp(F(x)) and
  F(x)>=x-C on a tail. Thus its kth derivative is eventually positive.
  Both Kneser F and F(x+epsilon sin(2 pi x)), 0<epsilon<1/(2 pi), satisfy W.
  W therefore also fails to characterize Kneser at base e. This does not prove
  the same Hardy statement for all other bases, nor for merely strictly
  increasing smooth functions whose derivatives have recurrent zeros.
- Complete monotonicity of slog' would mean (-1)^(n-1) slog^(n)>=0 for every
  n>=1 on a specified x-domain. The experiment rules out this condition on all
  x>0 but does not settle whether some later common tail works.
- Numerical sign stability is not interval certification of the underlying
  Kneser function or its differentiated table errors. The tables are finite,
  and their functional-equation residual is not a proof of those errors.
- No new real-axis uniqueness theorem is claimed.
