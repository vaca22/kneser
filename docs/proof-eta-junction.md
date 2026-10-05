# The $\eta$ junction: $S_a \to S_\eta$ as $a \uparrow \eta = e^{1/e}$

Companion to `docs/base-plane-zh.md` §2.1 and `docs/demo_eta_junction.py`, which observe
numerically (13 digits) that the regular superfunction $S_a$ of base $a<\eta$ tends,
for every real $z>-2$, to the parabolic superfunction $S_\eta$ as $a\uparrow\eta$.
This note proves it.

## 0. Statement

**Theorem.** For $1<a<\eta$ let $S_a:(-2,\infty)\to(-\infty,\alpha_a)$ be the regular
(Koenigs–Schröder) superfunction of $E_a(w)=a^w$ at its attracting fixed point
$\alpha_a$, normalised by $S_a(0)=1$; let $S_\eta:(-2,\infty)\to(-\infty,e)$ be the
Fatou (parabolic) superfunction of $E_\eta$ on the attracting petal of the fixed point
$e$, normalised by $S_\eta(0)=1$ (precise definitions in §1). Then

$$S_a(z)\;\longrightarrow\;S_\eta(z)\qquad(a\uparrow\eta),$$

uniformly on compact subsets of $(-2,\infty)$. Equivalently, the Abel functions
$A_a=S_a^{-1}$ converge to $A_\eta=S_\eta^{-1}$ uniformly on compact subsets of
$(-\infty,e)$.

**What is proved here, fully.** Everything in the chain

concavity of $S_a$ on $(-2,\infty)$ (§3) $\Rightarrow$ equi-Lipschitz family $\{A_a\}$
(§5) $\Rightarrow$ subsequential limits are convex Abel functions of $E_\eta$ (§5)
$\Rightarrow$ every such limit is $A_\eta$ (uniqueness of convex Abel functions at a
parabolic point, §4) $\Rightarrow$ $A_a\to A_\eta$ (§5) $\Rightarrow$ $S_a\to S_\eta$ (§6).

**Inputs taken from the literature (not re-proved).**

- (K) Koenigs' linearisation theorem: for $0<\lambda<1$ the Schröder equation
  $\sigma(E_a(w))=\lambda\,\sigma(w)$ has a unique solution analytic near $\alpha_a$
  with $\sigma'(\alpha_a)=1$, and $\sigma^{-1}$ is analytic near $0$.
- (F) Fatou coordinate: for $g(u)=e^u-1$ the attracting petal at $0$ (containing a real
  interval $(-\rho,0)$) carries an analytic $F$ with $F(g(u))=F(u)+1$ and
  $F(u)= -2/u+\tfrac13\log(-u)+h(u)$, where $h$ has an asymptotic power series
  $\sum_{k\ge1}c_ku^k$ as $u\to0$ in the petal, differentiable term by term; $F$ is
  unique up to an additive constant among Abel functions injective on the petal.
  (Fatou; Écalle; Milnor, *Dynamics in One Complex Variable*, §10, Thm. 10.9 and the
  discussion of the asymptotic expansion.)

**GAP list.** None in the logical chain. Two remarks that are *not* gaps in the proof but
should be recorded:

1. Lévy's limit formula, suggested as the route, is **not** an Abel function in the
   hyperbolic case $0<\lambda<1$ (§2); it is therefore not used. The proof instead uses
   a convexity characterisation, which is where the uniformity in $a$ is obtained for
   free.
2. The code sums the *divergent* (Gevrey-1) asymptotic series of $F$ at $|u|\le0.02$
   with 40 terms; its truncation error ($\sim e^{-c/|u|}$) is a numerical, not a
   mathematical, matter. The theorem is about the exact Fatou coordinate.

## 1. Definitions, matching the code

Throughout $\eta=e^{1/e}$, $E_a(w)=a^w=e^{w\ln a}$.

**Regular regime $1<a<\eta$** (`src/kneser/_regular.py`, class `RegularEngine`).
$E_a$ has two real fixed points $\alpha_a<\beta_a$;
$\alpha_a=-W_0(-\ln a)/\ln a$ is attracting with multiplier
$\lambda_a=E_a'(\alpha_a)=\alpha_a\ln a\in(0,1)$. Since $E_a-\mathrm{id}$ is convex with
zeros $\alpha_a,\beta_a$, $E_a(w)>w$ for $w<\alpha_a$; the tower $1,a,a^a,\dots$
increases to $\alpha_a$. The map $a\mapsto\alpha_a$ is continuous on $(1,\eta]$ with
$\alpha_\eta=e$ (continuity of $W_0$ on $[-1/e,0)$), and $\alpha_a\uparrow e$.

By (K) let $u_a=\sigma_a^{-1}$ be the inverse Schröder series,
$u_a(s)=s+c_2s^2+\cdots$, $E_a(\alpha_a+u_a(s))=\alpha_a+u_a(\lambda_as)$ (the code
computes exactly these $c_k$ in `_schroeder_inverse`). Define

$$\tilde S_a(z)=\alpha_a+u_a(-\lambda_a^{\,z})\qquad(z\ \text{real},\ \lambda_a^z<s_0),$$

so $\tilde S_a(z+1)=E_a(\tilde S_a(z))$, and continue leftwards by
$\tilde S_a(z-1)=\log_a\tilde S_a(z)$ with the real logarithm (`_F`). Then
$\tilde S_a$ is real-analytic and strictly increasing on $(-2,\infty)$: for large $z$,
$\tilde S_a'(z)=u_a'(s)\,s\log\lambda_a>0$ with $s=-\lambda_a^z<0$; going backwards,
$\tilde S_a'(z)=\tilde S_a'(z+1)/(\ln a\;\tilde S_a(z+1))>0$ as long as
$\tilde S_a(z+1)>0$. Its range is $(-\infty,\alpha_a)$: $\tilde S_a(z)\uparrow\alpha_a$
as $z\to\infty$, and the value $0$ is taken at some $z_1$, below which one more
logarithm sends the values in $(0,1)$ to $(-\infty,0)$. Finally
$S_a(z)=\tilde S_a(z+z_0)$ with $z_0$ fixed by $S_a(0)=1$ (`_normalize`). Then
$S_a(-1)=0$, $S_a(z)\to-\infty$ as $z\downarrow-2$, and

$$A_a:=S_a^{-1}:(-\infty,\alpha_a)\to(-2,\infty)$$

is a strictly increasing real-analytic bijection with $A_a(1)=0$ and
$A_a(E_a(w))=A_a(w)+1$. Note $A_a=\log(-\sigma_a(w))/\log\lambda_a+\text{const}$;
this is Szekeres' regular (principal) Abel function of $E_a$ at $\alpha_a$.

**Parabolic base $a=\eta$** (`src/kneser/_general.py`, class `ParabolicEngine`).
$E_\eta(w)=e^{w/e}$ has the single real fixed point $e$ with multiplier $1$, and
$E_\eta(w)>w$ for $w\ne e$. With $w=e(1+u)$ the map becomes $g(u)=e^u-1=u+u^2/2+\cdots$.
Let $F$ be the Fatou coordinate of (F), real on $(-\rho,0)$ (the complex conjugate
of $F$ is again a Fatou coordinate, hence differs from $F$ by a constant, which the
real-part convention of the code removes). The code computes the $c_k$
(`_abel_coefficients`), solves $F(u)=z+n$ by Newton at $|u|\le 0.02$ and applies
$u\mapsto\log(1+u)$ $n$ times (`_F`). Thus, with $U:=F^{-1}$ on $(F(-\rho),\infty)$
extended leftwards by $U(z-1)=\log(1+U(z))$,

$$\tilde S_\eta(z)=e\,(1+U(z)),\qquad S_\eta(z)=\tilde S_\eta(z+z_0),\quad S_\eta(0)=1 .$$

The same backward argument shows $S_\eta$ is strictly increasing and real-analytic on
$(-2,\infty)$ with range $(-\infty,e)$, and

$$A_\eta:=S_\eta^{-1}:(-\infty,e)\to(-2,\infty),\qquad A_\eta(1)=0,\qquad
A_\eta(E_\eta(w))=A_\eta(w)+1 ,$$

$A_\eta(w)=F(w/e-1)+\text{const}$ for $w$ close to $e$.

## 2. Why Lévy's formula is not the right tool here

For a real map $f$ with $f(x)\to\xi$ and multiplier $s=f'(\xi)$, Lévy's limit is

$$L(x)=\lim_{n\to\infty}\frac{f^n(x)-f^n(x_0)}{f^{n+1}(x_0)-f^n(x_0)} .$$

When $0<s<1$ Koenigs gives $f^n(x)-\xi=\sigma(x)s^n(1+o(1))$ uniformly on compacts,
hence

$$L(x)=\frac{\sigma(x)-\sigma(x_0)}{(s-1)\,\sigma(x_0)},\qquad
L(f(x))-L(x)=\frac{\sigma(x)}{\sigma(x_0)}\ne1\ \ (x\ne x_0).$$

So $L$ is an affine function of the Koenigs coordinate, not an Abel function; Lévy's
formula produces the Abel function only in the parabolic case $s=1$ (Lévy 1928;
Szekeres 1958 §4; Kuczma–Choczewski–Ger, *Iterative Functional Equations*, Ch. 3,
where the hypothesis is precisely $\lim (f^{n+1}(x)-f^n(x))/(f^{n+1}(x_0)-f^n(x_0))=1$,
false for $s<1$). Consequently "uniformity of the Lévy limit in $a$ up to $a=\eta$"
would not even give $A_a$ for $a<\eta$. We use a different characterisation of the
principal solutions: convexity.

## 3. Concavity of $S_a$ (hence convexity of $A_a$)

**Lemma 3.1.** For every $1<a<\eta$, $S_a$ is concave on $(-2,\infty)$; equivalently
$A_a$ is convex on $(-\infty,\alpha_a)$. The same holds for $a=\eta$.

*Proof.* (i) *Near $+\infty$.* Write $s=-\lambda^z$ ($\lambda=\lambda_a$), so
$ds/dz=s\log\lambda$ and $\tilde S_a(z)=\alpha_a+u_a(s)$. Then

$$\tilde S_a''(z)=(\log\lambda)^2\; s\,\bigl(u_a'(s)+s\,u_a''(s)\bigr).$$

Since $u_a$ is analytic at $0$ with $u_a'(0)=1$, the bracket tends to $1$ as $s\to0$,
so $\tilde S_a''<0$ on some $[z_*,\infty)$ (where $s<0$ is small).

(ii) *Backward propagation.* Pass to the normalised $S_a$ (a shift of $\tilde S_a$),
concave on $I_0=[z_*,\infty)$ by (i). For $z>-2$ we have $S_a(z)=L(S_a(z+1))$ with
$L=\log_a$ increasing and concave on $(0,\infty)$, and $S_a(z+1)>0$ (because
$z+1>-1$ and $S_a(-1)=0$, $S_a$ increasing). Put $I_k=(\max(-2,z_*-k),\infty)$.
If $S_a$ is concave on $I_k$, then for $z\in I_{k+1}$ we have $z+1\in I_k$, so on
$I_{k+1}$ the function $S_a=L\circ S_a(\cdot+1)$ is the composition of an increasing
concave function with a concave one, hence concave. After finitely many steps
$I_k=(-2,\infty)$.

(iii) *Inverse.* A strictly increasing concave function has a convex inverse.

For $a=\eta$: (ii) and (iii) are identical. For (i), $U=F^{-1}$ satisfies
$U'=1/F'(U)$ with $F'(u)=2/u^2+1/(3u)+O(1)$ by (F), so
$U'=\tfrac12U^2\,(1+O(U))$ and, differentiating once more (the $O$-terms are
differentiable by (F)), $U''=\tfrac12U^3(1+O(U))<0$ for $U<0$ small, i.e. for $z$
large. $\square$

*Remark.* Only the case $a<\eta$ is used below; concavity of $S_\eta$ is recorded
because it shows the limit object has the same shape and because §4 does not depend
on it.

## 4. Uniqueness: convex Abel functions of $E_\eta$

**Lemma 4.1.** Let $w_*<e$ and let $B:(w_*,e)\to\mathbb R$ be convex with
$B(E_\eta(w))=B(w)+1$ whenever $w,E_\eta(w)\in(w_*,e)$. Then $B=A_\eta+\text{const}$
on $(w_*,e)$.

*Proof.* Pass to $u=w/e-1\in(u_*,0)$ and $g(u)=e^u-1$; write $B(u)$ for
$B(e(1+u))$ and let $F$ be the Fatou coordinate (§1), so $A_\eta(e(1+u))=F(u)+\text{c}$
for $u\in(-\rho,0)$. Shrinking $u_*$ we may assume $u_*\ge-\rho$ and that $F$ is
strictly increasing on $(u_*,0)$ (it is: $F'=2/u^2(1+O(u))>0$). $B$ is continuous
(convex on an open interval), so

$$P(t):=B(F^{-1}(t))-t,\qquad t>F(u_*),$$

is continuous, and $P(t+1)=P(t)$ by the two Abel equations (for $u$ with $g(u)>u_*$,
which is automatic once $u>u_*$ and $g(u)<0$). Extend $P$ $1$-periodically; it is
bounded and continuous. We show $P$ is midpoint-convex, hence convex (continuous
midpoint-convex functions are convex), hence constant (a periodic convex function on
$\mathbb R$ is constant).

Fix $t_0\in\mathbb R$ and $\tau>0$, and let $s=t_0+N$ with $N\to\infty$. Put
$G=F^{-1}$ and $u=G(s)$, $u_\pm=G(s\pm\tau)$, so $u_-<u<u_+<0$ and all three tend to
$0$. Convexity of $B$ on $[u_-,u_+]$ gives

$$B(u)\le\theta B(u_-)+(1-\theta)B(u_+),\qquad
\theta=\frac{u_+-u}{u_+-u_-}\in(0,1).$$

Substituting $B(u_\pm)=s\pm\tau+P(s\pm\tau)$, $B(u)=s+P(s)$ and using periodicity:

$$P(t_0)\le\theta P(t_0-\tau)+(1-\theta)P(t_0+\tau)+\tau(1-2\theta). \tag{4.1}$$

It remains to see $\theta\to\tfrac12$ as $N\to\infty$. From (F),
$G(s)=-2/s+O(s^{-2}\log s)$ and $G'(s)=1/F'(G(s))=\tfrac12G(s)^2(1+O(G(s)))=
\tfrac{2}{s^2}\bigl(1+O(s^{-1}\log s)\bigr)$, so $G'(s')/G'(s)\to1$ uniformly for
$|s'-s|\le\tau$. Hence

$$\frac{u_+-u}{u-u_-}=\frac{\int_s^{s+\tau}G'}{\int_{s-\tau}^{s}G'}\longrightarrow1,
\qquad\text{i.e. }\theta\to\tfrac12 .$$

Letting $N\to\infty$ in (4.1): $P(t_0)\le\tfrac12\bigl(P(t_0-\tau)+P(t_0+\tau)\bigr)$
for all $t_0$ and all $\tau>0$. So $P$ is constant, and $B(u)=F(u)+\text{const}$ on
$(u_*,0)$; the Abel equation then propagates the identity $B=A_\eta+\text{const}$ to
all of $(w_*,e)$ (every $w\in(w_*,e)$ reaches $(e(1-\rho),e)$ under finitely many
iterations of $E_\eta$, along which both sides increase by $1$ per step). $\square$

*Remark.* This is the real-line analogue of the uniqueness of the Fatou coordinate:
Milnor's uniqueness is among injective analytic solutions on the petal; Lemma 4.1
replaces analyticity by mere convexity, which is what survives pointwise limits.
Compare Kuczma, *Functional Equations in a Single Variable* (1968), Ch. VI, on convex
solutions of Abel's equation; the proof above is self-contained so that no hypothesis
mismatch with the literature can arise.

## 5. Convergence of the Abel functions

**Proposition 5.1.** $A_a\to A_\eta$ uniformly on compact subsets of $(-\infty,e)$ as
$a\uparrow\eta$.

*Proof.* **Step 1: uniform bounds.** For every $a\in(1,\eta]$ and every
$w<\alpha_a$: $A_a(w)\ge-2$ (indeed $A_a(w)=A_a(a^w)-1$ and $a^w>0=S_a(-1)$, so
$A_a(a^w)>-1$). For an upper bound on $[\,\cdot\,,q]$ with $q<e$: choose $N$ with
$E_\eta^N(1)>q$ (possible since the $\eta$-tower increases to $e$). Since
$a\mapsto E_a^N(1)$ is continuous, there is $a_0<\eta$ with $E_a^N(1)>q$ for
$a\in[a_0,\eta]$, and then $A_a(q)<A_a(E_a^N(1))=N$ by monotonicity. So on any
$[p,q]\subset(-\infty,e)$, $|A_a|\le M:=\max(2,N)$ for all $a\in[a_0,\eta)$ (with
$a_0$ also chosen so that $\alpha_a>q$).

**Step 2: equi-Lipschitz.** Fix a compact $[p,q]\subset(-\infty,e)$ and $r>0$ with
$q+r<e$. By Lemma 3.1 each $A_a$ is convex on $[p-r,q+r]$ (for $a$ close to $\eta$
so that $\alpha_a>q+r$), and by Step 1 bounded there by some $M$ independent of $a$.
A convex function bounded by $M$ on $[p-r,q+r]$ is $(2M/r)$-Lipschitz on $[p,q]$
(the slope of any chord inside $[p,q]$ is squeezed between the slopes of chords
reaching the margins). Hence $\{A_a\}_{a\in[a_1,\eta)}$ is uniformly bounded and
equi-Lipschitz on every compact subset of $(-\infty,e)$.

**Step 3: subsequential limits.** Let $a_k\uparrow\eta$. By Arzelà–Ascoli and a
diagonal argument there is a subsequence (not relabelled) and a function $B$ on
$(-\infty,e)$ with $A_{a_k}\to B$ uniformly on compacts. $B$ is convex (pointwise
limit of convex functions), continuous, nondecreasing, and $B(1)=0$. It satisfies the
Abel equation of $E_\eta$: for fixed $w<e$, $E_{a_k}(w)\to E_\eta(w)<e$, so the points
$E_{a_k}(w)$ lie in a compact subset of $(-\infty,e)$ for large $k$, on which
convergence is uniform and $B$ is continuous; therefore

$$B(E_\eta(w))=\lim_k A_{a_k}(E_{a_k}(w))=\lim_k\bigl(A_{a_k}(w)+1\bigr)=B(w)+1 .$$

**Step 4: identification.** By Lemma 4.1 (with $w_*=-\infty$), $B=A_\eta+c$, and
$B(1)=0=A_\eta(1)$ forces $c=0$. Thus every sequence $a_k\uparrow\eta$ has a
subsequence along which $A_{a_k}\to A_\eta$ locally uniformly; the limit being
independent of the subsequence, the whole family converges. $\square$

*Where the uniformity in $a$ came from.* No estimate on the Schröder series (whose
radius shrinks to $0$) or on the speed of $E_a^n\to\alpha_a$ (which slows without
bound) was needed. Convexity of $A_a$ is a property of the *whole* interval
$(-\infty,\alpha_a)$, proved by backward propagation from a neighbourhood of the fixed
point whose size may depend on $a$ arbitrarily; and convexity is exactly what
(a) gives compactness and (b) singles out the Fatou coordinate in the limit.

## 6. Reduction: from $A_a\to A_\eta$ to $S_a\to S_\eta$

**Proposition 6.1.** Proposition 5.1 implies $S_a\to S_\eta$ uniformly on compact
subsets of $(-2,\infty)$.

*Proof.* *Pointwise.* Fix $z>-2$ and put $w=S_\eta(z)\in(-\infty,e)$. Given
$\varepsilon>0$ with $w+\varepsilon<e$, set
$\delta=\min\bigl(A_\eta(w+\varepsilon)-z,\;z-A_\eta(w-\varepsilon)\bigr)>0$
($A_\eta$ is strictly increasing). By Proposition 5.1 there is $a_2<\eta$ such that
for $a\in[a_2,\eta)$, $|A_a-A_\eta|<\delta/2$ on $[w-\varepsilon,w+\varepsilon]$
(and $\alpha_a>w+\varepsilon$). Then $A_a(w-\varepsilon)<z<A_a(w+\varepsilon)$, and
since $A_a$ is a strictly increasing bijection onto $(-2,\infty)$ with inverse $S_a$,
$S_a(z)\in(w-\varepsilon,w+\varepsilon)$, i.e. $|S_a(z)-S_\eta(z)|<\varepsilon$.

*Locally uniform.* On a compact $[z_1,z_2]\subset(-2,\infty)$ take a grid
$z_1=t_0<\dots<t_m=z_2$ so fine that $S_\eta(t_{j+1})-S_\eta(t_j)<\varepsilon$
($S_\eta$ is continuous). For $a$ close to $\eta$, $|S_a(t_j)-S_\eta(t_j)|<\varepsilon$
at all grid points; monotonicity of $S_a$ and $S_\eta$ then gives
$|S_a(z)-S_\eta(z)|<2\varepsilon$ for every $z\in[z_1,z_2]$. $\square$

*Remark (the functional-equation extension).* Had Proposition 5.1 been proved only on
compacts of $(0,e)$, the extension to compacts of $(-\infty,e)$ would follow from
$A_a(w)=A_a(a^w)-1$: for $w$ in a compact $K\subset(-\infty,e)$, the points $a^w$
($a$ near $\eta$) lie in a compact subset of $(0,e)$, and
$A_a(a^w)-A_\eta(\eta^w)=[A_a-A_\eta](a^w)+[A_\eta(a^w)-A_\eta(\eta^w)]\to0$
uniformly on $K$ by uniform convergence on that compact and uniform continuity of
$A_\eta$ there. In the present proof this was unnecessary since Lemma 3.1 covers the
whole interval.

## 7. What the code computes, and why these are the principal solutions

**$a<\eta$ (`RegularEngine`).** The engine builds the inverse Schröder series
$u_a(s)=\sum c_ks^k$ from the recurrence
$c_k=\alpha_a P_k/(\lambda_a^k-\lambda_a)$, sums it at $|s|\le s_{\max}$ (chosen
inside the disc of convergence from the tail ratios of the $c_k$), and reaches a
general $z$ by $n$ real logarithms. This is Koenigs' linearisation, and the Abel
function $\log(-\sigma_a)/\log\lambda_a$ obtained from it is what Szekeres calls the
regular (principal) Abel function of $E_a$ at the attracting fixed point: it is the
unique Abel function, up to a constant, that is $C^1$ with
$A_a'(w)\,(\alpha_a-w)\log\lambda_a\to-1$ as $w\uparrow\alpha_a$, equivalently the
unique one whose superfunction is analytic at $z=+\infty$ in the variable
$\lambda_a^z$ (Szekeres 1958, §§2–3; Kuczma–Choczewski–Ger, Ch. 3). Any other
continuous Abel function is $A_a+P\circ A_a$ with $P$ $1$-periodic, and destroys this
asymptotic unless $P$ is constant. Lemma 3.1 shows that this $A_a$ is convex on the
whole of $(-\infty,\alpha_a)$; the proof above never used more than that.

**$a=\eta$ (`ParabolicEngine`).** The engine determines the coefficients $c_k$ of the
formal solution $\varphi(u)=-2/u+\tfrac13\log(-u)+\sum_{k\ge1}c_ku^k$ of
$\varphi(e^u-1)=\varphi(u)+1$ (the leading terms are forced: with
$g(u)=u+u^2/2+u^3/6+\cdots$ one checks
$-2/g(u)+2/u=1-u/6+O(u^2)$ and $\tfrac13\log(g(u)/u)=u/6+O(u^2)$, so the $u$-terms
cancel exactly when the log coefficient is $\tfrac13$). By (F), $\varphi$ is the
asymptotic expansion of the Fatou coordinate $F$ on the attracting petal; the series
$\sum c_ku^k$ is in general divergent (Gevrey-1), so the engine truncates it (40
terms at $|u|\le0.02$), incurring an error of order $e^{-c/|u|}$ that is far below the
working precision — a numerical remark, not part of the theorem. The mathematical
object is $F$ itself, unique up to an additive constant among injective analytic Abel
functions on the petal (Milnor, Thm. 10.9), and — by Lemma 4.1 — unique up to an
additive constant among *convex* Abel functions on any real interval $(w_*,e)$.

**The junction, in one sentence.** Both engines compute the unique convex Abel
function of their map (Lemma 3.1 and Lemma 4.1); convexity survives locally uniform
limits, and convexity alone pins down the Fatou coordinate at the parabolic point
(Lemma 4.1); therefore the limit of the regular solutions is the parabolic solution,
which is what `docs/demo_eta_junction.py` observes to 13 digits.

*Remark (Lévy's quotient in the limit).* For the Möbius model
$f_\lambda(x)=\lambda x/(1-(1-\lambda)x/c)$, both the regular Abel function
$\log(-\sigma_\lambda)/\log\lambda$ and Lévy's quotient tend to the Fatou coordinate
$-c/x$ as $\lambda\uparrow1$, although they differ for each $\lambda<1$. This is
consistent with, but not needed for, the theorem; a direct proof along those lines
would require uniform estimates through the crossover between the parabolic
($x_n\sim-2/n$) and the geometric ($x_n\sim C\lambda^n$) phases of the orbits,
which the convexity argument sidesteps.

## References

- P. Lévy, *Fonctions à croissance régulière et itération d'ordre fractionnaire*,
  Ann. Mat. Pura Appl. (4) 5 (1928), 269–298.
- G. Szekeres, *Regular iteration of real and complex functions*, Acta Math. 100
  (1958), 203–258.
- M. Kuczma, *Functional Equations in a Single Variable*, PWN, Warsaw 1968, Ch. VI
  (convex solutions of Schröder's and Abel's equations).
- M. Kuczma, B. Choczewski, R. Ger, *Iterative Functional Equations*, Encyclopedia of
  Mathematics and its Applications 32, Cambridge 1990, Ch. 3 (principal solutions of
  Schröder's and Abel's equations; Lévy's theorem).
- J. Milnor, *Dynamics in One Complex Variable*, 3rd ed., Princeton 2006, §10
  (parabolic fixed points, Fatou coordinates, Thm. 10.9 and the asymptotic
  expansion).
- J. Écalle, *Théorie itérative: introduction à la théorie des invariants
  holomorphes*, J. Math. Pures Appl. 54 (1975), 183–258.
- G. Koenigs, *Recherches sur les intégrales de certaines équations fonctionnelles*,
  Ann. Sci. ÉNS (3) 1 (1884), 3–41.
