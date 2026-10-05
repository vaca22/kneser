# Hardy fields and tetration: what Goal 4 actually establishes

Status: 2026-09-12, resumed after the Claude quota interruption. The previous
file contained a literature section and a summary referring to proofs that had
not been written. Its original is preserved in
`docs/_generated/claude-recovery-20260912/hardy-field.md`.

**Proved below, using a stated external Hardy-field criterion:** every smooth real solution of
`G(x+1)=exp(G(x))` with **G'>0 everywhere on a final interval**
generates a Hardy field. This includes Kneser's solution and its periodic
reparametrisations with everywhere positive phase derivative. Thus **the uniqueness conclusion in Goal 4 is false**.
The proof verifies the analytic hypotheses of the cited criterion; it does not
claim to reprove the external differential-algebra machinery.

**Not proved:** uniqueness by a different real-axis condition, an identification
with a formal hyperseries, or o-minimality. No claim of a new literature result
is made. **Numerics:** none are needed in this report.

## 1. Definitions and precisely scoped literature

A Hardy field is a field of germs of differentiable real functions at positive
infinity closed under differentiation. Each nonzero member is eventually
nonzero, and therefore eventually has a constant sign. Applying this to its
derivative shows that each member is eventually monotone or constant.
“Hardian” means belonging to some Hardy field, not every Hardy field.
Write `f ≺ g` for `f/g → 0` and `f ≼ g` for `|f|=O(|g|)`.

Boshernitzan's *Hardy fields and existence of transexponential functions*,
Aequationes Mathematicae 30 (1986), 258–280, is the historical source. Its full
text was not verified here; its precise theorem numbering is not asserted.
[ADH's ICM exposition](https://arxiv.org/abs/1711.06936), discussion of Kneser,
attributes Hardy-field membership to this work. Ordinary finite-height
logarithmic-exponential transseries do not contain a function dominating every
finite iterate of exp; admitting tetration requires a larger setting.

[Padgett, *Sublogarithmic-transexponential series*](https://arxiv.org/html/2211.06736v1#S1),
Theorem 1.2, gives a composition-closed Hardy field of germs of terms in a language
containing Kneser's function, its derivatives and compositional inverses. This is
a preprint theorem, not a proof here of quantifier elimination or o-minimality.
It includes the half-iterate `F(F^{-1}(x)+1/2)` as a term. In particular, the old
claim that joint membership of `F(x)` and `F(x+c)` was unresolved is inconsistent
with this cited theorem: both are terms, with real parameter `c`.

The proof below uses the following facts from
[Aschenbrenner–van den Dries–van der Hoeven, *Maximal Hardy Fields*, v3](https://arxiv.org/pdf/2304.10846v3):
The Liouville-closed field `H=Li(R)` is omega-free, contains all iterated
logarithms `ell_n`, and these are
coinitial among its positive infinite elements (end of §5.5 and p. 275).
Lemma 5.6.8 says that a smooth germ `y` is H-hardian if, for every
`ell ∈ H`, `ell → +∞`,

1. `1 ≺ y ≺ ell`;
2. `(ell'^{-1} d/dx)^k y ≼ 1` for every `k ≥ 1`;
3. `y'` is eventually nonzero and `|(1/ell)'| ≼ |y'/y|`.

Lemma 5.3.5 gives hardianity of compositional inverses. Compositional conjugation
in §5.3 allows changing independent variable by an increasing infinite member
of a Hardy field. These are external inputs; the rest is the verification for
an arbitrary Abel function, not just the Kneser one.

## 2. The Abel estimates, with no Hardy-field assumption on G

Let `G` be smooth on a final interval, `G'>0`, and
`G(x+1)=exp(G(x))`. Since `exp(t)-t ≥ 1` for real `t`, the values of `G` along
integer translates tend to infinity. Monotonicity gives `G(x)→∞` without
restricting to an integer sequence. Its smooth inverse `A=G^{-1}` is defined
on a final interval, has `A'>0`, and satisfies

\[
 A(e^t)=A(t)+1,\qquad A(x)=A(\log x)+1.                 \tag{2.1}
\]

All statements below concern sufficiently large arguments, where every
composition is defined.

### 2.1 Every positive-order derivative of A is bounded

Differentiating the second identity k times gives constants `c_{kj}` with
`c_{kk}=1` such that

\[
 A^{(k)}(x)=x^{-k}\sum_{j=1}^k c_{kj}A^{(j)}(\log x).
                                                               \tag{2.2}
\]

For example `A'(x)=A'(log x)/x`. Induct on k. Suppose all lower derivatives
are bounded on a final interval; their contribution to the sum is bounded by
some C (C=0 for k=1). Choose T large enough that the identities hold for
`t≥T`, `e^T>T`, and `x^{-k}≤1/2` for `x≥e^T`. Take M at least C and the
maximum of `|A^{(k)}|` on `[T,e^T]`. If the bound M holds at `log x`, (2.2)
gives `|A^{(k)}(x)|≤(M+C)/2≤M`. Induction on the intervals with endpoints
`T,e^T,e^{e^T},…` covers the entire final interval. This proves boundedness
for every fixed k; the bound and threshold may depend on k.

In particular `A'(x)≤M/x`, and integration yields

\[
 A(x)\le C_0+M\log x.
                                                               \tag{2.3}
\]

### 2.2 A lower bound needed for the logarithmic derivative

Increase T so that `t^{3/2}≤e^{t/2}` for `t≥T`.
Strict positivity and compactness give c>0 with
`A'(t)≥c t^{-3/2}` on `[T,e^T]`. If this holds at `t=log x`, then

\[
 A'(x)=A'(t)/x\ge c t^{-3/2}/x\ge c x^{-3/2}.
\]

The same interval induction extends this bound to all sufficiently large x.
Together with (2.3) and `A(x)→∞` it gives

\[
 \frac{x^2 A'(x)}{A(x)+n}\longrightarrow+\infty
 \quad\hbox{for every fixed integer }n\ge0.             \tag{2.4}
\]

### 2.3 Iterated-log changes of variable

Put `ell_0(x)=x`, `ell_n(x)=log_n(x)`, and
`delta_n=(ell_n')^{-1}d/dx`. Iterating (2.1) gives
`A(exp_n(t))=A(t)+n`. Therefore

\[
 (\delta_n^k A)(x)=A^{(k)}(\ell_n(x)),\qquad k\ge1,      \tag{2.5}
\]

so these derivatives are bounded. Also
`A(x)=A(ell_n(x))+n=O(log(ell_n(x)))+n=o(ell_n(x))`.
Finally, setting `t=ell_n(x)` in the chain rule gives

\[
 \frac{A'(x)/A(x)}{|(1/\ell_n)'(x)|}
 =\frac{t^2 A'(t)}{A(t)+n}\longrightarrow+\infty.        \tag{2.6}
\]

## 3. Verification for every comparison germ in H

The criterion requires every infinite `ell∈H`, not only iterated logarithms.
This missing quantifier cannot be skipped. Choose n with `ell_n ≼ ell`,
using coinitiality. Both are increasing and unbounded. Hardy-field
l'Hopital comparison gives

\[
 f:=\ell_n'/\ell'\preccurlyeq1,
 \qquad |(1/\ell)'|\preccurlyeq |(1/\ell_n)'|.           \tag{3.1}
\]

For completeness, these comparisons follow because the ratios of the
respective derivatives are Hardy-field elements and hence have limits in the
extended real line. An infinite derivative ratio would, by l'Hopital's rule,
force an infinite ratio of the functions, contradicting respectively
`ell_n=O(ell)` or `1/ell=O(1/ell_n)`. The relevant derivatives are nonzero.

Change variable to `t=ell_n(x)`. The conjugate `H∘exp_n` is a Hardy field
containing t: explicitly, `d(h∘exp_n)/dt=(h'/ell_n')∘exp_n`, and
`h'/ell_n'` belongs to H. The element `f_t=f∘exp_n` is bounded. Each of its derivatives
is bounded too: a bounded Hardy germ has eventually constant-sign monotone
derivatives, and its first derivative must tend to zero; repeat for higher
derivatives. In this coordinate the ell-derivation becomes

\[
 (\ell'^{-1}\partial_x)=f_t\partial_t.
\]

Expanding `(f_t ∂_t)^k(A(t)+n)` gives a finite sum of derivatives `A^{(j)}(t)`
with `j≥1`, multiplied by polynomials in `f_t` and its derivatives. Every
factor is bounded by §2.1. Thus condition 2 holds for this ell.
Condition 1 follows from `A=o(ell_n)` and `ell_n=O(ell)`;
condition 3 follows from (2.6), (3.1), and `A'>0`.
The external criterion now proves that **A is H-hardian**.

To see inverse closure directly in this instance, take the Hardy field
`K=H⟨A⟩`, which contains x and A'. The field `K∘G` contains `x∘G=G`
and is closed under differentiation because

\[
 (h\circ G)'=(h'/A')\circ G\quad(h\in K).
\]

It also contains x, since `A∘G=x`. Hence `R(x)⟨G⟩` is a differential
subfield of a Hardy field and is itself a Hardy field. This proves the
asserted result for every smooth G with eventually everywhere positive derivative. If G is analytic,
all germs in `R(x)⟨G⟩` are analytic on suitable final intervals.

The field generated by all integer translates can also be included:
positive translates are iterated exponentials of G; negative translates
are iterated logarithms. The Liouville closure of a Hardy field containing
G contains these germs, and hence their differential field.

### 3.1 Positive derivative is essential

Strict increase alone does **not** imply the hypothesis `G'>0`. For example,
`h(x)=x-sin(2*pi*x)/(2*pi)` is analytic and strictly increasing, but
`h'(m)=0` at every integer m. Then `G=F∘h` is a normalized, strictly
increasing analytic tetration whose derivative vanishes at every integer
and is positive at every half-integer. Its derivative is a nonzero germ
with unbounded zeros, so G is not hardian. The theorem above excludes this
example explicitly; its inverse would not satisfy the smoothness and
positive-derivative hypotheses used in §2. This also supplies a concrete
failure case for the broadest version of M4.2.

## 4. Explicit failure of the proposed uniqueness direction

Let F be Kneser's base-e tetration. Choose `0<epsilon<1/(2*pi)` and set

\[
 h(x)=x+\epsilon\sin(2\pi x),\qquad G(x)=F(h(x)).
\]

Then `h'>0`, `h(x+1)=h(x)+1`, and `h(0)=0`. Thus G is analytic,
strictly increasing, normalized by `G(0)=1`, and

\[
 G(x+1)=F(h(x)+1)=\exp G(x).
\]

It differs from F, but §3 proves that **both individually generate Hardy
fields**. This disproves M4.3 and the claimed characterization in the plan.
No numerical inference is involved.

They cannot belong to one common Hardy field: `G-F` vanishes at every
integer, and is nonzero at every sufficiently large integer plus 1/4.
It is therefore a nonzero germ with arbitrarily large zeros, impossible
in a field of continuous germs. This is compatible with individual
hardianity. One cannot place F into the field generated by G without
proof and then use `G-F` to claim that G is not hardian.

More generally, the same argument works whenever a nonconstant periodic
reparametrisation has infinitely many intersections with a fixed integer
shift of F. No general assertion about all other reparametrisations is
needed for the counterexample.

## 5. Connection to Goal 1 and final disposition

Each derivative `G^{(k)}` is a Hardy germ, so its eventual sign exists.
Moreover G dominates every polynomial: (2.1)'s original recurrence gives
`G(x)≥x-C`, and then `G(x+1)≥exp(x-C)`. If `G^{(k)}` were eventually
nonpositive, successive integration would bound G above by a polynomial
of degree at most k-1. If the derivative were the zero germ, the same
conclusion follows. Both contradict exponential growth. Consequently

\[
 \forall k\ge1\ \exists X_k\ \forall x>X_k:
 G^{(k)}(x)>0.
\]

This is the weak, order-dependent threshold statement. It is not
`exists X for all k`: see `proof-bohr-mollerup.md` for the fixed-half-line
obstruction. The old draft's stronger derivative asymptotic formulas and
ordered-differential-field isomorphism claims are unnecessary here and
are not retained as established results.

- **M4.1:** definitions, directly checked modern sources and external inputs
  are explicit. The 1986 source itself remains checked through later authors.
- **M4.2:** Hardy-field membership is established above relative to the stated
  ADH criterion; it is not an original discovery of Kneser membership.
- **M4.3:** false, by the explicit normalized sine reparametrisation.
- **Outcome:** stop the uniqueness route in its current form. Its prescribed
  success criterion cannot hold, even though Hardy membership holds.

No tests or floating-point experiments can replace the mathematical proof in
§§2–4. Review should focus on the all-ell quantifier in §3 and on keeping
individual membership separate from membership in one common Hardy field.

Independent review: two agents checked §§2–4 against the stated criterion.
Their strict-increase versus positive-derivative objection is incorporated in
§3.1; both found the all-ell verification valid under the corrected hypothesis.
This records review scope, not a substitute for the proof or external sources.
