# 孙宇晨奖题库 — 解析方向条目清单

抓取日期：2026-09-18　来源：`TheJustinSunPrize/awards` 的 `problems/catalog-*.md`（全库 1022 条）

口径：`Mathematical area` 含 Analysis / Polynomials / Irrationality / Probability / Operator / Topology / Dynamical / PDE / Transcendental，共 **100 条**。
状态：Solved 45 / Open 55；带 Lean 证明且可领奖 10 条。

> 与超运算的关系：全库无 tetration / hyperoperation / 半迭代 / Abel 方程 / Schröder 方程 / 复动力系统条目。唯一挂 `Analysis / Function iteration` 的 JSP-000752 是整函数导数零点稠密性，与迭代无关；八条 `Number theory / Function iteration` 均为 φ、σ 的整数迭代。详见 [[kneser-base-separation]] 一线的工作定位。


## 多项式模的几何

| ID | 状态 | Lean | 可领 | 领域 | 标题 |
| --- | --- | --- | --- | --- | --- |
| [JSP-000038](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000038) | Solved | ✓ | ✓ | Complex analysis / Geometry of polynomial zeros | Sendov conjecture |
| [JSP-000124](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000124) | Open |  |  | Polynomials / Analysis | How long can the complex-plane curve where a monic polynomial has absolute value one be? |
| [JSP-000127](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000127) | Solved | ✓ | ✓ | Analysis / Polynomials | If all zeros of a polynomial lie on the unit circle, how does its maximum modulus on the prescribed region grow with its degree? |
| [JSP-000393](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000393) | Solved |  |  | Analysis / Polynomials | What bounds relate the number of nonzero terms of a polynomial to that of its square? |
| [JSP-000408](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000408) | Open |  |  | Analysis / Polynomials | How small can the total radii of disks covering the set where a polynomial has modulus at most one be? |
| [JSP-000410](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000410) | Solved |  |  | Analysis | How many components of the region where a polynomial has modulus at most one can exceed a prescribed diameter? |
| [JSP-000861](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000861) | Open |  |  | Analysis | For a monic real-rooted polynomial, how long in total can the real intervals on which its absolute value is less than one be? |
| [JSP-000862](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000862) | Open |  |  | Analysis / Polynomials | How large a disk can lie in the region where a polynomial has modulus at most one? |
| [JSP-000863](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000863) | Open |  |  | Analysis | Under restrictions on polynomial zeros, how do the area and transfinite diameter of a modulus sublevel set relate? |
| [JSP-000864](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000864) | Open |  |  | Analysis / Polynomials | Can two polynomial zeros be joined within its unit-modulus sublevel set by a path of uniformly bounded length? |
| [JSP-000865](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000865) | Solved |  |  | Analysis | How does the transfinite diameter of the zero set bound the number of components of a polynomial sublevel set? |
| [JSP-000866](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000866) | Solved | ✓ | ✓ | Analysis | Among the allowed polynomials, how small can the maximum boundary length of their sublevel sets be? |
| [JSP-000867](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000867) | Open |  |  | Analysis | For a complex point set of fixed diameter, how large can the product of all pairwise distances be? |
| [JSP-000868](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000868) | Solved |  |  | Analysis | If a polynomial's unit-modulus sublevel set is connected, must it lie in a disk of radius two? |
| [JSP-000925](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000925) | Solved |  |  | Analysis / Polynomials | For a real-rooted polynomial with equally spaced zeros, do gaps between consecutive derivative zeros satisfy the specified monotonicity? |
| [JSP-000931](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000931) | Open |  |  | Analysis | Within the specified polynomial modulus region, how short a path joins the origin to the unit circle? |
| [JSP-001020](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-1001-1022.md#JSP-001020) | Solved |  |  | Analysis | For a polynomial whose zeros all lie on the unit circle, is there a uniformly bounded-length path in the specified modulus region? |

## 整函数与亚纯函数的增长/值分布

| ID | 状态 | Lean | 可领 | 领域 | 标题 |
| --- | --- | --- | --- | --- | --- |
| [JSP-000204](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000204) | Solved |  |  | Analysis | For a transcendental entire function, determine the limiting ratio between its largest power-series term and its maximum modulus on a circle. |
| [JSP-000411](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000411) | Open |  |  | Analysis | What is the optimal guaranteed liminf of the ratio of the largest series term of a transcendental entire function to its maximum modulus on a circle? |
| [JSP-000412](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000412) | Open |  |  | Analysis | Does every transcendental entire function have a path to infinity along which its modulus grows faster than every polynomial? |
| [JSP-000413](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000413) | Solved |  |  | Analysis | Does a transcendental entire function have a path to infinity on which a specified negative power of its modulus is integrable? |
| [JSP-000414](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000414) | Open |  |  | Analysis | Must an entire function with sufficiently sparse nonzero power-series terms attain every complex value infinitely often? |
| [JSP-000752](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000752) | Open |  |  | Analysis / Function iteration | Is there an entire function such that the union of zeros of any infinite selection of its derivatives is dense in the complex plane? |
| [JSP-000926](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000926) | Solved |  |  | Analysis | How short can a path to infinity be along which a given entire function tends to infinity? |
| [JSP-000927](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000927) | Solved |  |  | Analysis | Under the stated conditions, can a meromorphic function's counts of taking two distinct values have arbitrarily extreme ratios? |
| [JSP-000928](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000928) | Open |  |  | Analysis | At how many points of one circle can an entire function attain its maximum modulus? |
| [JSP-000929](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000929) | Solved |  |  | Analysis | How fast must an entire function grow if the region above a prescribed modulus threshold has finite area? |
| [JSP-000930](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000930) | Solved |  |  | Analysis / Set theory | How large can a family of entire functions be if the number of possible values at each point is restricted? |

## 无理性与超越性

| ID | 状态 | Lean | 可领 | 领域 | 标题 |
| --- | --- | --- | --- | --- | --- |
| [JSP-000021](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000021) | Open |  |  | Transcendental number theory | Schanuel conjecture |
| [JSP-000086](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000086) | Open |  |  | Number theory / Irrationality | Is the series obtained by summing the reciprocals of factorials minus one irrational? |
| [JSP-000087](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000087) | Solved |  |  | Number theory / Irrationality | Is the specified generating series involving the number of distinct prime factors of an integer irrational? |
| [JSP-000214](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000214) | Open |  |  | Number theory / Irrationality | What structure must a nearly quadratically growing integer sequence have if its reciprocal sum is rational? |
| [JSP-000217](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000217) | Open |  |  | Number theory / Irrationality | Is the infinite series defined by sparse nonzero binary digits transcendental? |
| [JSP-000218](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000218) | Open |  |  | Number theory / Irrationality | Is the series with Euler totient values as numerators and powers of two as denominators irrational? |
| [JSP-000219](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000219) | Open |  |  | Number theory / Irrationality | Is the binary generating series constructed from primes irrational? |
| [JSP-000220](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000220) | Open |  |  | Number theory / Irrationality | Are the series with divisor-power sums as numerators and factorials as denominators irrational? |
| [JSP-000223](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000223) | Open |  |  | Irrationality | Under the stated conditions, is every infinite subsum of reciprocals of powers of two minus one irrational? |
| [JSP-000224](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000224) | Solved | ✓ | ✓ | Irrationality | Is the reciprocal series with product denominators constructed from the divisor-counting function irrational? |
| [JSP-000225](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000225) | Open |  |  | Irrationality | Must the binary-weighted infinite sum associated with the specified sparse integer sequence be irrational? |
| [JSP-000227](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000227) | Open |  |  | Irrationality | Is there an integer sequence whose reciprocal sum remains irrational after every term undergoes the prescribed asymptotically small perturbation? |
| [JSP-000228](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000228) | Open |  |  | Irrationality | Is there an integer sequence whose reciprocal sum remains irrational under arbitrary bounded perturbations of its terms? |
| [JSP-000229](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000229) | Open |  |  | Irrationality | ambiguous statement |
| [JSP-000230](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000230) | Open |  |  | Irrationality | When must the reciprocal sum of a sparse subsequence of Fibonacci numbers be irrational? |
| [JSP-000231](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000231) | Open |  |  | Irrationality | Determine the arithmetic properties of the specified reciprocal sum of least common multiples for integers generated by finitely many primes. |
| [JSP-000869](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000869) | Open |  |  | Irrationality | Under the stated conditions, is the reciprocal sum of powers of a rational number minus one irrational? |
| [JSP-000870](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000870) | Solved |  |  | Irrationality | Is the series of reciprocals of powers of two minus three irrational? |
| [JSP-000871](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000871) | Solved | ✓ | ✓ | Irrationality | For a doubly exponentially growing integer sequence, is the reciprocal sum of consecutive-term products irrational? |
| [JSP-000952](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000952) | Solved |  |  | Irrational numbers / Additive bases | For a fixed irrational number, do integers whose squared multiples of it lie close to integers form an asymptotic basis of order two? |

## 随机多项式与随机游走

| ID | 状态 | Lean | 可领 | 领域 | 标题 |
| --- | --- | --- | --- | --- | --- |
| [JSP-000416](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000416) | Open |  |  | Number theory / Probability | Do partial sums of a random multiplicative function satisfy the predicted law of the iterated logarithm and fluctuation scale? |
| [JSP-000417](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000417) | Open |  |  | Analysis / Polynomials / Probability | Does the number of real roots of a polynomial with independent random sign coefficients almost surely follow the specified asymptotic law? |
| [JSP-000418](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000418) | Open |  |  | Analysis / Polynomials / Probability | How many roots of a polynomial with random sign coefficients lie inside the unit circle? |
| [JSP-000419](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000419) | Solved |  |  | Analysis / Probability / Polynomials | What is the typical maximum modulus on the unit circle of a polynomial with random sign coefficients? |
| [JSP-000420](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000420) | Open |  |  | Analysis / Probability / Polynomials | What is the typical maximum on the specified real interval of a polynomial with random sign coefficients? |
| [JSP-000421](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000421) | Solved |  |  | Analysis / Probability / Polynomials | How small is the typical minimum modulus on the unit circle of a polynomial with random sign coefficients? |
| [JSP-000422](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000422) | Solved |  |  | Probability / Geometry | What conditions on arc lengths make randomly placed arcs cover the entire circle almost surely? |
| [JSP-000423](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000423) | Solved |  |  | Analysis / Probability | Does a power series with randomly signed coefficients converge at some point of the unit circle? |
| [JSP-000425](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000425) | Open |  |  | Geometry / Probability | How fast does the mean endpoint distance of a random self-avoiding lattice walk grow with its length? |
| [JSP-000949](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000949) | Open |  |  | Number theory / Probability | Do partial sums of a random completely multiplicative function infinitely often exceed every fixed multiple of the square root of the summation range? |
| [JSP-000969](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000969) | Solved |  |  | Probability | How fast does the radius of a disk whose lattice points have all been visited by a planar random walk grow with the number of steps? |
| [JSP-000970](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000970) | Solved |  |  | Probability | What is the probability that multiple sites tie for most visited in a planar random walk? |
| [JSP-000971](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000971) | Solved |  |  | Probability | How many distinct sites have ever been most visited during a planar random walk? |
| [JSP-000984](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000984) | Solved |  |  | Additive combinatorics / Probability | How many random elements of a finite abelian group make subset-sum representation counts approximately uniform? |

## 一致分布・差异理论・插值

| ID | 状态 | Lean | 可领 | 领域 | 标题 |
| --- | --- | --- | --- | --- | --- |
| [JSP-000545](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0501-0600.md#JSP-000545) | Open |  |  | Analysis | If interpolation amplification factors diverge at every point, can every continuous function still have a point of interpolation convergence? |
| [JSP-000820](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000820) | Solved | ✓ | ✓ | Analysis / Discrepancy theory | For exponential sums from an arbitrary infinite real sequence, how much growth in partial sums is forced as frequency varies? |
| [JSP-000823](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000823) | Solved | ✓ | ✓ | Analysis | How far from uniform can the arguments of roots of a sparse polynomial be? |
| [JSP-000827](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000827) | Solved |  |  | Analysis / Discrepancy theory | Under repeated irrational rotation of a circle, does the visiting frequency of a measurable set equal its measure? |
| [JSP-000828](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000828) | Open |  |  | Analysis / Discrepancy theory | For a square-integrable function sampled along dilations from a sparse integer sequence, how fast do partial sums grow for typical inputs? |
| [JSP-000829](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000829) | Open |  |  | Analysis | Does sufficiently fast decay of Fourier approximation error ensure convergence of averages along the prescribed sparse sequence? |
| [JSP-000830](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000830) | Solved | ✓ | ✓ | Analysis / Discrepancy theory / Primes | Can the fractional parts of primes multiplied by an irrational number satisfy the specified stronger uniform-distribution property? |
| [JSP-000831](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000831) | Solved |  |  | Analysis / Diophantine approximation | What necessary and sufficient conditions on interval endpoints give bounded counting discrepancy for an irrational rotation? |
| [JSP-000834](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000834) | Open |  |  | Analysis / Diophantine approximation | What limiting distribution arises from normalized cumulative centered fractional parts of an irrational rotation? |
| [JSP-000936](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000936) | Solved |  |  | Analysis / Polynomials | Which Lagrange interpolation nodes minimize the maximum amplification of input errors? |
| [JSP-000937](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000937) | Solved |  |  | Analysis / Polynomials | Which interpolation nodes maximize the smallest peak error-amplification factor among intervals between consecutive nodes? |
| [JSP-000938](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000938) | Open |  |  | Analysis / Polynomials | What is the minimum sum of squared integrals of the Lagrange basis functions? |
| [JSP-000939](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000939) | Open |  |  | Analysis / Polynomials | For interpolation built from successive initial segments of an infinite node sequence, what lower bound must the amplification factor satisfy at a fixed point? |
| [JSP-000940](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000940) | Open |  |  | Analysis / Polynomials | Even allowing degree slightly above the minimum, can bounded interpolation data force every interpolating polynomial to have large amplitude? |
| [JSP-000955](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000955) | Open |  |  | Analysis / Polynomials | For sign-coefficient polynomials, must the maximum modulus on the unit circle exceed the square root of the number of terms by a fixed proportion? |
| [JSP-000956](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000956) | Open |  |  | Analysis / Polynomials | With Chebyshev interpolation nodes, can all limit points of the interpolation sequence at the specified positions be prescribed? |
| [JSP-000957](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000957) | Open |  |  | Analysis / Polynomials | Can a slight increase in interpolation degree avoid almost-everywhere divergence for continuous functions? |
| [JSP-000958](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000958) | Solved |  |  | Analysis / Polynomials | For every choice of interpolation nodes, must error amplification on each fixed subinterval grow at least logarithmically? |

## 其他（千禧年题与单点条目）

| ID | 状态 | Lean | 可领 | 领域 | 标题 |
| --- | --- | --- | --- | --- | --- |
| [JSP-000005](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000005) | Solved | ✓ | ✓ | Partial differential equations / Fluid mathematics | Existence and smoothness of the 3D Navier–Stokes equations |
| [JSP-000007](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000007) | Solved |  |  | Geometric topology / Geometric analysis | Poincaré conjecture |
| [JSP-000010](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000010) | Open |  |  | Diophantine analysis / Arithmetic geometry | abc conjecture |
| [JSP-000015](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000015) | Open |  |  | Harmonic analysis / Geometric measure theory | Kakeya dimension conjecture (general dimension) |
| [JSP-000024](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000024) | Open |  |  | Functional analysis / Operator theory | Invariant subspace problem for Hilbert spaces |
| [JSP-000026](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000026) | Open |  |  | Number theory / Dynamical systems | Decimal normality of pi |
| [JSP-000032](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000032) | Open |  |  | Harmonic analysis / Geometry | Fuglede conjecture (dimensions one and two) |
| [JSP-000042](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000042) | Open |  |  | Matrix analysis / Operator theory | Crouzeix conjecture |
| [JSP-000399](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000399) | Solved |  |  | Analysis / Additive combinatorics | Can a finite set be uniquely recovered from the multiset of all sums of a prescribed number of distinct elements? |
| [JSP-000409](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000409) | Open |  |  | Analysis | Chowla's cosine problem |
| [JSP-000753](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000753) | Solved |  |  | Analysis | If every translation difference of a function is measurable, does the function decompose into parts with the specified regularity? |
| [JSP-000754](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000754) | Solved |  |  | Analysis / Topology | Can a space and its Cartesian square have the same nontrivial finite dimension? |
| [JSP-000755](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000755) | Solved |  |  | Topology | Must a connected Euclidean set contain connected subsets of several distinct homeomorphism types? |
| [JSP-000807](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000807) | Open |  |  | Analysis | For a complex number outside the unit circle, can sums of consecutive powers approach zero exponentially fast? |
| [JSP-000808](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000808) | Open |  |  | Number theory / Divisors / Polynomials | How fast does the average divisor count of integer values of an irreducible polynomial grow? |
| [JSP-000959](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000959) | Open |  |  | Analysis | Can subrings or subfields of the reals have any prescribed Hausdorff dimension strictly between zero and one? |
| [JSP-001000](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-001000) | Solved |  |  | Number theory / Analysis | How fast can the measure of a real set grow if no ratio of distinct elements is an integer? |
| [JSP-001002](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-1001-1022.md#JSP-001002) | Solved | ✓ | ✓ | Analysis | Can integer dilates of a positive-measure real set cover all sufficiently distant lattice points along almost every prescribed ray? |

## 三角多项式与二项式乘积的模

| ID | 状态 | 领域 | 标题 |
| --- | --- | --- | --- |
| [JSP-000203](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000203) | Solved | Analysis | How large can the specified integral of a trigonometric polynomial be under the problem's real-zero conditions? |
| [JSP-000222](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000222) | Open | Analysis | How large must the maximum modulus of the specified product of binomials on the unit circle be? |
