# Hellmuth Kneser (1950), aligned with the German scan + secondary literature

This note follows the **structure and claims** of Hellmuth Kneser’s paper *Reelle analytische Lösungen der Gleichung \(\vartheta(\vartheta(x))=\mathrm{e}^x\) und verwandter Funktionalgleichungen*, *J. Reine Angew. Math.* **187** (1950), **56–67** (received **1 November 1948**; publication delayed—see footnote 1 in the article).

**PDF alignment (`Kneser1950-paper/`):** in `Kneser1950_Reelle_analytische_Loesungen_pp56-67.pdf`, **PDF pages 1–12 = journal pages 56–67** (starts at the title page).

Sources fused here: **GDZ scan + English OCR transcript** (`_ocr/kneser_full_ocr_eng.txt`) and **standard secondary expositions** ([EuDML entry](https://eudml.org/doc/150158); [Wikipedia: Half-exponential function](https://en.wikipedia.org/wiki/Half-exponential_function); Trappmann–Kouznetsov, *Aequ. Math.* **81** (2011), [doi:10.1007/s00010-010-0021-6](https://doi.org/10.1007/s00010-010-0021-6); Kouznetsov, *Math. Comp.* **78** (2009), [doi:10.1090/S0025-5718-09-02188-7](https://doi.org/10.1090/S0025-5718-09-02188-7)).

---

## Historical hook (from Kneser’s introduction, OCR)

In **October 1941**, at the DMV meeting in **Jena**, the headline functional equation was discussed; Kneser records that an industrial motivation pressed for a **“reasonable”** (*„vernünftige“*) solution. He contrasts earlier work supplying merely **continuous**, **\(C^k\)**, or even **\(C^\infty\)** **real** solutions with his sharper target: **globally real-valued and real-analytic on \(\mathbb{R}\)** (“überall im Reellen reelle und analytische Lösung”).

**Prior real solutions (introduction footnotes 2–4, p. 56):**

- **Continuous** real solutions: G. H. Hardy, *Orders of infinity*, Cambridge Tracts in Math. **12**, 2nd ed. (1924), p. 31.
- **Finitely / infinitely differentiable** real solutions: U. T. **Bödewadt**, *Math. Z.* **49** (1943), 497–516.
- **Schröder/Koenigs machinery** used in § 2: G. **Koenigs**, *Ann. sci. ENS* (3) **1** (1884), Supplément, 3–41.

Footnote 1 on the same page records that publication was delayed by *„äußere Umstände“* — the paper carries a Carathéodory-70th-birthday dedication dated **13. 9. 1943** but appeared only in 1950, **received 1 November 1948**, in slightly revised form.

---

## Logical spine: why Abel, and where the difficulty sits

1. **Goal.** Construct \(\varphi:\mathbb{R}\to\mathbb{R}\) with \(\varphi(\varphi(x))=\mathrm{e}^x\), **real-analytic** and **strictly increasing** (hence \(C^\infty\)).

2. **Abel linearizes iteration.** If \(\Psi(\mathrm{e}^x)=\Psi(x)+1\), then \(\mathrm{e}^n(x)\) becomes translation by \(n\) in the \(\Psi\)-coordinate; formally,
   $$
   \mathrm{e}^n(x)=\Psi^{-1}(\Psi(x)+n)\qquad(n\in\mathbb{Z}),
   $$
   and the **half-step** \(\Psi^{-1}(\Psi(x)+\tfrac12)\) composes to \(\mathrm{e}^x\) exactly as in § 1’s general Abel formalism.

3. **Obstacle A — no real fixed point for \(\mathrm{e}^z\).** Koenigs’s local Schröder theory needs an **attracting fixed point** on the sheet where the branch of \(\ln\) is fixed. On \(\mathbb{R}\), \(\mathrm{e}^x\) has none; § 3 parametrizes **complex** fixed points \(c\) with \(\mathrm{e}^c=c\).

4. **Obstacle B — the “natural” Schröder object is not usable on \(\mathbb{R}\) as-is.** Starting from the \(\ln\)-fixed-point \(c\) nearest \(\mathbb{R}\), § 4 builds a Schröder function \(\chi\) (Koenigs limit) and continues it; along the way Kneser stresses singularities / non-real behaviour tied to the orbit \(\ldots,\mathrm{e}^{\mathrm{e}^x},\mathrm{e}^x,x,\ln x,\ln\ln x,\ldots\) (OCR mentions trouble at **\(0,1,\mathrm{e},\mathrm{e}^{\mathrm{e}},\ldots\)** before repair).

5. **Repair — § 5 conformal normalization.** A carefully chosen **conformal mapping** turns the abstract Abel coordinate into a function \(\Psi\) that is **real-analytic on \(\mathbb{R}\)**, **strictly increasing**, \(\Psi'(x)>0\), and satisfies \(\Psi(\mathrm{e}^x)=\Psi(x)+1\) after continuation (**Satz 9**).

6. **Closure — § 6.** Set \(\varphi(x)=\Psi^{-1}(\Psi(x)+\tfrac12)\); verify \(\varphi(\varphi(x))=\mathrm{e}^x\) on \(\mathbb{R}\).

This is the article’s actual narrative arc; the optional \(F_t\) packaging below is modern shorthand.

---

## Title page (German)

**Reelle analytische Lösungen der Gleichung \(\vartheta(\vartheta(x))=\mathrm{e}^x\) und verwandter Funktionalgleichungen.**  

*Von Hellmuth Kneser in Tübingen.*  

Dedication: *Herrn Constantin Carathéodory zu seinem siebzigsten Geburtstag am 13. 9. 1943 gewidmet.*

Section roadmap (printed §§ 1–6):

| § | Content (short) |
|---|------------------|
| § 1 | Abel \((1)\) and Schröder \((2)\); iterate \(\nu^{-1}(\nu+n\beta)\); half-step \(\nu^{-1}(\nu+\beta/2)\). |
| § 2 | **Satz 1–3**: Koenigs construction/uniqueness around an attracting fixed point. |
| § 3 | Complex fixed points of \(\mathrm{e}^z\); **Satz 5** counts them by half-strips; numeric \(c=a+\mathrm{i}b\). |
| § 4 | Schröder solution for \(\ln\) near \(c\); continuation to a domain \(\mathfrak{G}\); **Satz 6**; \(\chi^{-1}\) entire with \(\chi^{-1}(c\zeta)=\exp(\chi^{-1}(\zeta))\) (paper’s \((14)\)). |
| § 5 | From \(\chi\) to a **real** Abel function \(\Psi\) via conformal glueing + Schwarz reflection; geometry of regions (**Satz 7–8**); **Satz 9** summarizes \(\Psi\) on \(\mathbb{R}\). |
| § 6 | \(\varphi=\Psi^{-1}(\Psi+\tfrac12)\); closing remarks + logarithmic series hint at \(z=c\). |

---

## § 1 — Abel / Schröder templates

**Abel** (his \((1)\)): \(\nu(f(x))=\nu(x)+\beta\).  
**Schröder** (his \((2)\)): \(\chi(f(x))=\gamma\,\chi(x)\).

They are locally equivalent via \(\chi=\exp(\cdots)\), \(\gamma=\mathrm{e}^{\cdots}\) as Kneser writes.

Iterates and half-iterates (same §):
$$
f^n(x)=\nu^{-1}\bigl(\nu(x)+n\beta\bigr),\qquad
\varphi(x)=\nu^{-1}\!\left(\nu(x)+\tfrac{\beta}{2}\right)\Rightarrow \varphi\circ\varphi=f.
$$

---

## § 2 — Koenigs’ theorem and uniqueness (Sätze 1–3, pp. 57–59)

Kneser reproduces Koenigs’ proof, but **with weakened smoothness hypotheses** (Hölder-type rather than full analyticity), since this costs nothing extra.

**Satz 1 (Koenigs limit).** Suppose

1. \(f(x)\) is defined in a neighbourhood of \(x=c\);
2. \(c\) is a fixed point: \(f(c)=c\);
3. at \(c\), \(f\) is *slightly more than differentiable*: there exist \(a\), \(M\), and \(\delta>1\) with
   $$
   \bigl|f(x)-c-a(x-c)\bigr|\le M\,|x-c|^{\delta};
   $$
4. \(c\) is **simple and attracting**: \(0<|a|<1\).

Then for \(x\) close enough to \(c\),
$$
\chi(x)=\lim_{n\to\infty}a^{-n}\bigl(f^n(x)-c\bigr)
$$
exists and satisfies the Schröder equation \(\chi(f(x))=a\,\chi(x)\) (so \(\gamma=a\)). The proof estimates the increments
$$
\bigl|a^{-n-1}(x_{n+1}-c)-a^{-n}(x_n-c)\bigr|\le \frac{Mr^{\delta}}{|a|}\!\left(\frac{q^{\delta}}{|a|}\right)^{\!n}
\qquad\text{(eq. (7))}
$$
with \(|a|<q<|a|^{1/\delta}\), so the telescoping series converges geometrically.

**Zusatz (addendum).** If \(f\) is **analytic at \(c\)** then \(\chi\) is analytic at \(c\) with \(\chi'(c)=1\); hypothesis 3 then reduces to specifying \(a=f'(c)\).

**Satz 2.** \(\chi\) of Satz 1 is differentiable at \(c\) with \(\chi'(c)=1\) (even without analyticity).

**Satz 3 (uniqueness up to scale).** If \(\chi_a(x)\) is *any* solution of Schröder \(\chi_a(f(x))=\gamma\,\chi_a(x)\) that is differentiable at \(c\) with **non-zero derivative**, then necessarily \(\gamma=a\) and
$$
\chi_a(x)=\chi_a'(c)\,\chi(x).
$$
The proof iterates Schröder \(n\) times, observes that \(\gamma^n\chi_a(x)=\chi_a(f^n(x))\to\chi_a(c)\), forces \(|\gamma|<1\) (the boundary case \(\gamma=1\) is excluded by differentiability of \(f\) at \(c\)), then evaluates \((\gamma/a)^n\) along the orbit to conclude \(\gamma=a\).

This is the **uniqueness pillar** that later (§ 4) singles out the Schröder solution at the complex fixed point \(c\) of \(\ln\).

---

## § 3 — the fixed point used numerically (from the paper / OCR)

Among complex solutions of \(\mathrm{e}^c=c\), take the pair **closest to the real axis** (upper half-plane representative)
$$
c=a+\mathrm{i}b,\quad a\approx 0{.}3181315,\quad b\approx 1{.}3372357,\quad |c|=\mathrm{e}^a\approx 1{.}3745570.
$$
For \(\ln\) this fixed point is **attracting** (\(|(\ln)'(c)|=1/|c|<1\)), enabling § 2’s machinery after choosing the principal branch of \(\ln\) in \(\operatorname{Im}z>0\) as Kneser does.

### How Kneser actually finds the fixed points (real-equation derivation)

Set \(z = x + \mathrm{i}y\) in \(\mathrm{e}^z = z\). The real and imaginary parts give
$$
\mathrm{e}^x\cos y = x,\qquad \mathrm{e}^x\sin y = y.
$$
Conjugation \(y\to -y\) leaves both equations invariant, so fixed points come in **conjugate pairs**; restrict to \(y>0\), which by the second equation forces
$$
\sin y > 0. \tag{9}
$$
Dividing the two equations and squaring-and-adding gives the **decoupled system**
$$
x = y\cot y,\qquad y^2 = \mathrm{e}^{2x} - x^2. \tag{10}
$$

- The first relation, in each strip \(k\pi < y < (k+1)\pi\), determines \(x\) as a continuous monotone-decreasing function of \(y\) (Kneser checks \(\tfrac{\partial}{\partial y}(y\cot y) = \tfrac{\sin 2y - 2y}{2\sin^2 y}<0\)).
- The second relation determines \(y^2\) as a continuous **increasing** function of \(x\); it equals \(1\) at \(x=0\) and equals \(0\) at the unique real root of \(\mathrm{e}^x + x = 0\), namely
$$
\boxed{\,x \approx -0{.}5671433\,}\quad\text{(the *Omega constant* \(-W(1)\) in modern notation).}
$$

Each crossing of the two curve families in Fig. 1 (p. 60) gives a fixed point; the strip-by-strip count is **Satz 5**:

> **Satz 5.** In each half-strip \(\{x>0,\ 2k\pi < y < (2k+1)\pi\}\) (\(k=0,1,2,\dots\)) the exponential function has **exactly one** fixed point; together with their conjugates, these are **all** fixed points.

The pair closest to \(\mathbb{R}\) is the \(k=0\) one and its conjugate; that is the \(c=a+\mathrm{i}b\) above.

### How Kneser computes \(c\) numerically (Fig. 2 — graphical regula falsi)

Iterating \(z_{n+1}=\ln z_n\) converges geometrically with ratio \(1/|c|\approx 0{.}728\), which Kneser calls *practically inadequate*. He instead applies **regula falsi**: given three successive iterates \(x_0, x_1=\ln x_0, x_2=\ln x_1\), the improved guess
$$
x'_0 = \frac{x_0 x_2 - x_1^{\,2}}{x_0 - 2x_1 + x_2}
$$
is the point in the complex plane forming **two similar triangles** with \(\{x_0, x_1\}\) and \(\{x_1, x_2\}\). Kneser carries this out **graphically** on a large-scale drawing using **four perpendiculars, two compass arcs, and one bisection** (Fig. 2 on p. 61), avoiding any hand multiplication/division of complex numbers. He notes the same construction works for **any** equation \(z=f(z)\) with analytic \(f\).


---

## § 4 — Schröder solution at \(c\) and its analytic continuation (Satz 6, Satz 7)

**Branch choice.** Take \(\ln z\) on the open upper half-plane to be the principal value. Then \(\ln c = c\), and since \(|(\ln)'(c)| = 1/|c| < 1\), \(c\) is a **simple attracting** fixed point of \(\ln\) (Sätze 1–2 apply).

**Local solution.** In a disc \(|z-c|<\varrho\) the Koenigs limit yields \(\chi(z)\) with
$$
\chi(z) = z - c + a_2\,(z-c)^2 + \cdots,\qquad \chi'(c)=1,
$$
satisfying
$$
\chi(\ln z) = \tfrac{1}{c}\,\chi(z) \tag{11}
$$
on a slightly smaller disc \(\mathfrak{U}'\subset\mathfrak{U}\), and equivalently
$$
\chi(\mathrm{e}^z) = c\,\chi(z). \tag{12}
$$

**Singular orbit (the chain Kneser explicitly excludes).** Iterating \(z\mapsto\mathrm{e}^z\) starting at \(0\):
$$
e_0 = 0,\quad e_1 = 1,\quad e_2 = \mathrm{e},\quad e_3 = \mathrm{e}^{\mathrm{e}},\quad e_4 = \mathrm{e}^{\mathrm{e}^{\mathrm{e}}},\quad \dots,\quad e_{n+1} = \mathrm{e}^{e_n}.
$$
Define the domain
$$
\mathfrak{G} = \{\,z : \operatorname{Im} z > 0,\ z \ne e_n\ (n=0,1,2,\dots)\,\}
$$
(with \(\ln\) on the negative real semi-axis given imaginary part \(\pi\)). Inductively defining
$$
\chi_{n+1}(z) := c\,\chi(\ln z) \quad \text{for } z\in\mathfrak{G}_{n+1}, \tag{13}
$$
where \(\mathfrak{G}_n\subset\mathfrak{G}\) are nested subdomains exhausting \(\mathfrak{G}\), gives an **analytic continuation** of \(\chi\) to all of \(\mathfrak{G}\) on which (11) holds; on the subset where \(\mathrm{e}^z\in\mathfrak{G}\) too, (12) holds.

> **Satz 6.** There exists a function \(\chi(z)\) analytic on \(\mathfrak{G}\) with \(\chi'(c)=1\) and (11). It is **completely determined** by these properties.

**\(\chi^{-1}\) is entire.** Since \(\chi'(c)=1\), the inverse \(\chi^{-1}(z)\) is regular near \(z=0\), and from (12),
$$
\chi^{-1}(c\zeta) = \exp\bigl(\chi^{-1}(\zeta)\bigr) \tag{14}
$$
on \(|\zeta|<\varrho/|c|\). Iterating (14) extends the disc radius from \(r\) to \(|c|\,r\) at each step, so \(\chi^{-1}\) extends to an **entire function** of \(\zeta\). Consequently \(\chi\) is **univalent on \(\mathfrak{G}\)** (it never repeats a value, and \(\chi'\) never vanishes).

Moreover \(\chi^{-1}\) **grows faster than every iterate of \(\exp\)** — its order exceeds the entire exponential growth scale (a remark Kneser makes explicit). Translated back to \(\chi\):
$$
|\chi(z)|\to\infty \text{ as } |z|\to\infty;\qquad |\chi(z)|\to\infty \text{ as } z\to e_n \text{ within } \mathfrak{G}.
$$

**The fundamental triangle \(\mathfrak{G}_0\) (Fig. 3, p. 63).** Restrict to the **circular-arc triangle**
$$
\mathfrak{G}_0 \;=\; \bigl\{\, z \;:\; y\ge 0,\ x\ge a,\ |z|\le |c|,\ z\ne 1\,\bigr\}
$$
with boundary pieces

- \(\mathfrak{A}_0\) — the segment \(x = a,\ 0\le y\le b\);
- \(\mathfrak{C}_0\) — the arc \(|z|=|c|,\ 0\le \arg z\le b\);
- \(\mathfrak{B}_0\) — the segment \(a\le x\le 1,\ y=0\);
- \(\mathfrak{B}'_0\) — the segment \(1\le x\le |c|,\ y=0\);

and translates \(\mathfrak{A}_n,\mathfrak{C}_n,\mathfrak{B}_n,\mathfrak{B}'_n\) obtained from these by repeated \(z\to\mathrm{e}^z\) (or \(z\to\ln z\)). The key adjacency: \(\mathfrak{G}_{-1}, \mathfrak{G}_0, \mathfrak{G}_1\) are pairwise disjoint **except** on the shared boundary segment \(\mathfrak{A}_0\) (between \(\mathfrak{G}_{-1}\) and \(\mathfrak{G}_0\)) and on the shared boundary arc \(\mathfrak{C}_0\) (between \(\mathfrak{G}_0\) and \(\mathfrak{G}_1\)).

> **Satz 7 (image geometry).** \(\chi\) maps \(\mathfrak{G}_n\) onto a region \(\mathfrak{G}'_n\) bounded by **four analytic arcs** \(\mathfrak{C}_n, \mathfrak{C}_{n+1}, \mathfrak{D}_n, \mathfrak{D}'_n\). The arcs \(\mathfrak{C}_n, \mathfrak{C}_{n+1}\) meet at the origin at angle \(b\); the arcs \(\mathfrak{C}_n,\mathfrak{D}_n\) meet at \(\chi(a)\) at a **right angle**; the arcs \(\mathfrak{C}_n,\mathfrak{D}'_n\) meet at \(\chi(|c|)\) at a **right angle**. The arcs \(\mathfrak{D}_n, \mathfrak{D}'_n\) extend to infinity. The transformation \(w\mapsto cw\) carries \(\mathfrak{G}'_n\) to \(\mathfrak{G}'_{n+1}\) — a **rotation–dilation by \(c\)** at the level of \(\chi\), the analytic conjugate of the shift \(z\mapsto\mathrm{e}^z\) at the level of \(z\).

(Fig. 4 on p. 63 sketches \(\mathfrak{G}'_0\); the qualitative picture, not numerically faithful, is what matters.)

---

## § 5 — from \(\chi\) to a real-analytic Abel function (Satz 8, Satz 9)

**Step 1: pass to a logarithmic Abel function.** The simply-connected region \(\mathfrak{G}_{-1}\cup\mathfrak{G}_0\cup\mathfrak{G}_1\) contains the origin only as a boundary point, so a single-valued branch of \(\ln\) is selectable. Excluding \(z=c\) (where \(\chi=0\)), the function
$$
w(z) = \ln\chi(z),
$$
with the branch fixed by
$$
\lim_{z\to c}\bigl[w(z) - \ln(z-c)\bigr] = 0 \tag{15}
$$
(principal value of \(\ln(z-c)\)), is well defined. From (12) it satisfies the **\(c\)-step Abel equation**
$$
\boxed{\,w(\mathrm{e}^z) = w(z) + c\,}. \tag{16}
$$

> **Satz 8.** \(w\) maps each \(\mathfrak{G}_n\) onto a region \(\mathfrak{U}_n\) bounded by four analytic arcs \(\mathfrak{E}_n, \mathfrak{E}_{n+1}, \mathfrak{F}_n, \mathfrak{F}'_n\), with \(\mathfrak{E}_n,\mathfrak{F}_n\) and \(\mathfrak{E}_{n+1},\mathfrak{F}'_n\) meeting at right angles. The arcs \(\mathfrak{E}_n\) extend to \(-\infty\) (with \(\operatorname{Im} z\to -\pi+nb\)); the arcs \(\mathfrak{F}_n, \mathfrak{F}'_n\) extend to \(+\infty\). The shift \(z\to\mathrm{e}^z\) corresponds to \(w\mapsto w+c\): a **translation by \(c\)** on the Abel side.

**Step 2: rule out the hyperbolic case.** Let \(\mathfrak{B}=\bigcup_n\mathfrak{U}_n\). Conformally map \(\mathfrak{B}\) onto a disc \(\mathfrak{S}\). The \(c\)-translation becomes a Möbius automorphism of the disc with no interior fixed point, hence either **parabolic** (one boundary fixed point) or **hyperbolic** (two boundary fixed points). Kneser **excludes** the hyperbolic case as follows: consider \(\mathrm{e}^{w/c}\); it is bounded to the left of any line of slope angle \(b\), with the bound arbitrarily small as the line moves far left. Transferring to the disc, this would produce a regular non-vanishing function with a zero limit on each of the two boundary arcs between the two fixed points — impossible. So the \(c\)-translation is **parabolic**.

**Step 3: send the disc to a half-plane and normalize.** Choose \(\mathfrak{S}\) to be the upper half-plane and conjugate so the parabolic fixed point is at \(\infty\); the translation becomes a **real shift** along \(\mathbb{R}\). A scale factor remains free; choose it so the shift length equals \(+1\) (orientation pinned by the positive winding around an interior point through three test arcs).

This produces \(\Psi(z)\) satisfying
$$
\Psi(\mathrm{e}^z) = \Psi(z) + 1. \tag{17}
$$

**Step 4: real-analyticity via Schwarz reflection.** \(\Psi\) is initially defined on the upper-half-plane part of \(\mathfrak{G}_{-1}\cup\mathfrak{G}_0\cup\mathfrak{G}_1\). The **real-axis segment** \([\,\ln a,\ \mathrm{e}^{|c|}\,]\) lies on the boundary of this region; \(\Psi\) is defined there and maps a one-sided strip onto a one-sided strip in the upper half-plane of the \(v\)-plane — exactly the setup for the **Schwarz reflection principle**, which extends \(\Psi\) **across that real-axis segment** as an analytic function. Equation (17) then propagates the analytic continuation **along the entire real axis**: from \(\alpha<z<\mathrm{e}^{\beta}\) (\(0<\alpha<\beta\)) one defines \(\Psi_1(z) := \Psi(\ln z) + 1\) on \(\mathrm{e}^{\alpha}<z<\exp(\mathrm{e}^{\beta})\) and \(\Psi_2(z) := \Psi(\mathrm{e}^z) - 1\) on \(\ln\alpha<z<\beta\); both agree with \(\Psi\) on the overlap, giving regular extensions in either direction.

**Step 5: monotonicity, growth, normalization.** \(\Psi\) maps a one-sided strip on \(\mathbb{R}\) onto a one-sided strip in the upper half-plane of the \(v\)-plane, so \(\Psi'>0\) on the original segment; the continuation steps preserve positivity, hence \(\Psi'(x)>0\) on all of \(\mathbb{R}\). To the right \(\Psi(x)\to+\infty\) (it gains \(+1\) under \(x\mapsto\mathrm{e}^x\)). To the left, taking \(z\to-\infty\) in (17) gives \(\Psi(x)\to\Psi(0)-1\). Since \(\Psi\) is determined only up to an **additive constant**, fix that constant by
$$
\boxed{\,\lim_{x\to-\infty}\Psi(x) = 0\,}.
$$
Then \(\Psi(\mathbb{R}) = (0,\infty)\), strictly increasing.

> **Satz 9 (the article’s summary).** \(\Psi(z)\) is **regular** on \(\bigl(\mathfrak{G}_{-1}\cup\mathfrak{G}_0\cup\mathfrak{G}_1\bigr)\setminus\{c\}\) **together with the entire real axis**. On \(\mathbb{R}\) it has positive derivative and is strictly increasing onto \((0,\infty)\). On \((\mathfrak{G}_{-1}\cup\mathfrak{G}_1)\setminus\{c\}\) and on \(\mathbb{R}\) it satisfies (17).

---

## § 6 — solution of \(\vartheta(\vartheta(x))=\mathrm{e}^x\)

By Satz 9, \(\Psi^{-1}\) is defined on **all positive reals**, real-analytic, with positive derivative. Since \(\Psi(\mathbb{R}) = (0,\infty)\), the value \(\Psi(x)+\tfrac12\) is positive for **every** \(x\in\mathbb{R}\), so
$$
\boxed{\,\varphi(x) = \Psi^{-1}\!\left(\Psi(x) + \tfrac12\right)\,}
$$
is well-defined on all of \(\mathbb{R}\), real-analytic with positive derivative, and from (17),
$$
\varphi(\varphi(x)) = \Psi^{-1}\bigl(\Psi(\varphi(x))+\tfrac12\bigr) = \Psi^{-1}\bigl(\Psi(x)+1\bigr) = \mathrm{e}^x.
$$

**Closing remark — Fourier–Puiseux expansion at \(z=c\) (last paragraph of the paper, p. 67, no proof given).** \(\Psi\) is regular on \(\mathfrak{G}_0\) and its boundary except at \(z=c\); near that point Kneser asserts the **uniformly and absolutely convergent representation**
$$
\Psi(z) = c + \ln(z-c) + \sum_{0\le m\le n} c_{mn}\,(z-c)^{\,m + 2n\pi\mathrm{i}/c}
$$
on a small disc around \(c\), where the powers \((z-c)^{\,m+2n\pi\mathrm{i}/c}\) are read using the principal branch of \(\ln(z-c)\). The presence of the **\(\ln(z-c)\) term** shows that \(z=c\) is a logarithmic-singular point of \(\Psi\) (hence its exclusion in Satz 9); the **non-integer exponents \(2n\pi\mathrm{i}/c\)** reflect the irrational argument of \(c\) and produce the modular / quasi-periodic features later studied by Trappmann–Kouznetsov.

Kneser closes by noting that the same machinery applies to many *„ähnliche Aufgabe“* — only a handful of properties of \(\exp\) (no real fixed point, attracting complex fixed point with \(|c|>1\) for the inverse, suitable orbit geometry) were used.

---

## Equivalent semigroup packaging (modern language)

Define \(F_t(x):=\Psi^{-1}(\Psi(x)+t)\) wherever injective. Then \(F_{s+t}=F_s\circ F_t\) and \(F_1=\exp\); \(F_{1/2}=\varphi\).

---

## Uniqueness & later literature (beyond Kneser’s existence proof)

Kneser proves **existence** of a distinguished **real-analytic** monotone solution package; he does **not** settle uniqueness among **all** conceivable compositional square roots.

Later work argues that **holomorphic Abel functions** tied to the **complex fixed-point pair** satisfy a **sharp uniqueness criterion**; Trappmann–Kouznetsov show **Kneser’s real-analytic Abel function** meets that criterion in the complex setup ([doi:10.1007/s00010-010-0021-6](https://doi.org/10.1007/s00010-010-0021-6), arXiv:[1006.3981](https://arxiv.org/abs/1006.3981)). Numerical plotting / algorithms for related Abel–super-exponential objects appear e.g. in Kouznetsov (*Math. Comp.* **78** (2009)).

Popular exposition also notes **many continuous** solutions exist by patching (see [Wikipedia: Half-exponential function](https://en.wikipedia.org/wiki/Half-exponential_function)), highlighting why **real-analyticity** is the substantive constraint Kneser addresses.

---

## Numerical samples (not from Kneser’s closed form — caveat)

No elementary closed formula for \(\varphi\) is expected ([Hardy-field obstruction discussion](https://en.wikipedia.org/wiki/Half-exponential_function)). Wikipedia records numerical samples for the **Kneser-type** half-exponential, e.g. \(\varphi(0)\approx 0{.}49856\), \(\varphi(1)\approx 1{.}64635\) — treat these as **computed approximations**, not as quotations from the 1950 paper.

---

## Primary bibliography / scans

- H. Kneser, *Reelle analytische Lösungen der Gleichung \(\vartheta(\vartheta(x))=\mathrm{e}^x\) und verwandter Funktionalgleichungen*, *J. Reine Angew. Math.* **187** (1950), 56–67. DOI: [10.1515/crll.1950.187.56](https://doi.org/10.1515/crll.1950.187.56). EuDML: [https://eudml.org/doc/150158](https://eudml.org/doc/150158). MR [0035385](https://mathscinet.ams.org/mathscinet-getitem?mr=0035385).

---

## OCR caveat

The GDZ PDF lacks a reliable text layer; internal **equation numbers** were cross-checked against OCR but may be mis-read on individual lines. For lemmas **Satz 1–9** and branch conventions, prefer the **printed pages 56–67**.
