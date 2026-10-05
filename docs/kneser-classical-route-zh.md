# 改道：Kneser 原始路线只需经典黎曼映射定理

2026-09-16。本文记录一个**战略层面的更正**：项目此前认定的终极障碍——可测黎曼映射定理
（Ahlfors–Bers）——**不是 Kneser 定理的障碍，而是本项目自己选的那条现代化路线引入的**。

---

## 1. 更正的内容

`formal/GEOMETRIC-ROUTE-STATUS.md` 与 [墙 A 的归约](wall-a-reduction-zh.md) 都写道：
`F` 的构造走 [§3–§6](theta-qc-global-existence.md) 的**周期 Beltrami 修正**，依赖
[可测黎曼映射定理](theta-periodic-beltrami.md)，mathlib 没有、可预见的时间内也不会有，
**这才是 Lean 内无法闭合的真实原因**。

该判断对**那条路线**成立，但那条路线不是 Kneser 的。
[Kneser 1950 原证](../../kneser1950-paper/Kneser-half-exponential-proof-zh.md) 第六步原文：

> 由 **Riemann 映射定理**，把 𝔅 共形映到上半平面。平移 `T(w)=w+c` 在上半平面中对应一个
> 无内点不动点的自同构。Kneser 排除双曲情形，得到它必为抛物型自同构。于是可选择共形映射 `R`，
> 使得 `R(w+c) = R(w)+1`。

**用的是经典 RMT。** 而经典 RMT 在 mathlib 里的状态是：

> `Mathlib/Analysis/Complex/RiemannMapping.lean` 文件头：
> "This file contains partial results towards Riemann Mapping Theorem.
> **A complete proof is available at https://github.com/leanprover-community/mathlib4/pull/33505**,
> ... It is being brought up to Mathlib code standards and merged in a series of smaller PRs."

即：**完整 Lean 证明已经存在，正在分批并入 mathlib。** 这把"原则上不可能"换成了
"卡在一个在途 PR 加一批常规工作"。

---

## 2. Kneser 七步逐条对账

| 步 | 内容 | 现状 |
|---|---|---|
| 1 | Abel 化：`Ψ(eˣ)=Ψ(x)+1` ⟹ `ϑ=Ψ⁻¹(Ψ+½)` | 机械 |
| 2 | 复不动点 `e^c=c`，`0<b<π` | **仓库已证**：`ExponentialFixedPoint`（Newton 认证，`‖c‖≥1.37`） |
| 3 | Koenigs 线性化（`log` 的吸引不动点，`\|1/c\|<1`） | **仓库已有**：`Koenigs`、`KoenigsUnique`（极限构造、收敛、胚唯一、`certifiedKoenigs`） |
| 4 | χ 单叶——靠整函数逆 `g(cζ)=exp g(ζ)` | **仓库已有**：`Poincare`、`GlobalPoincare`（`poincareExtension`，前提正是 `1<‖L‖`，即 Kneser 的 `\|c\|>1`） |
| 5 | `w=log χ`，Abel 方程 `w(e^z)=w(z)+c` | 机械 |
| **6** | **RMT + 抛物型归一化** | RMT 在 PR #33505；**自同构识别已补**（见 §3）；**抛物/双曲正规形已补**（见 §3.8）；**"排除双曲情形"的解析核心已补**（见 §3.9），只剩见证函数的构造（要 RMT 与 𝔅） |
| **7** | **Schwarz 反射 → 实轴上实解析** | ✅ **本轮已证**（见 §3.5） |

前几步这个仓库**已经做在里面了**，只是后续接到了 QC 分支上。

---

## 3. 本轮补上的：圆盘自同构群与 Cayley 变换

第六步要把诱导映射**识别成 Möbius 变换**才能谈"抛物型"。mathlib 有 Schwarz 引理
**连等号情形**（`Complex.affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div'`），却没有这条经典推论：
`Mathlib/Analysis/Complex/UnitDisc/` 下只有 `Basic.lean`，没有自同构 API；
`UnitDisc` 与 `UpperHalfPlane` 之间**零连接**，没有 Cayley 变换。

补上了十二个模块，**84 条定理，全部通过公理审计**（仅 `propext`/`Classical.choice`/`Quot.sound`），
且**只依赖 mathlib**，不依赖本仓库其余部分：

### `formal/Kneser/BlaschkeFactor.lean`

```lean
noncomputable def blaschke (a z : ℂ) : ℂ := (z-a)/(1-(starRingEnd ℂ) a*z)

theorem one_sub_normSq_blaschke (h : 1-(starRingEnd ℂ) a*z ≠ 0) :
    1-‖blaschke a z‖^2 = (1-‖a‖^2)*(1-‖z‖^2)/‖1-(starRingEnd ℂ) a*z‖^2
```

核心 Schwarz–Pick 恒等式，加上映入性、互逆 `blaschke (-a) ∘ blaschke a = id`、解析性。

### `formal/Kneser/DiscRotation.lean`

```lean
theorem eqOn_rotation_of_ball_bijective ... :
    ∃ C, ‖C‖ = 1 ∧ Set.EqOn f (fun z => C*z) (Metric.ball 0 1)
```

固定原点的自同构必是旋转：Schwarz 两次夹出 `‖f z‖=‖z‖`，再用等号情形。

### `formal/Kneser/CayleyTransform.lean`

```lean
noncomputable def cayley (w : ℂ) : ℂ := (w-Complex.I)/(w+Complex.I)
noncomputable def cayleyInv (z : ℂ) : ℂ := Complex.I*(1+z)/(1-z)
```

`‖cayley w‖<1 ⟺ Im w>0`（靠 `‖w−i‖² = ‖w+i‖² − 4·Im w`）、
`Im(cayleyInv z) = (1−‖z‖²)/‖1−z‖²>0`、双向互逆、两侧解析性，
以及**共轭搬运** `cayleyConj F = cayley ∘ F ∘ cayleyInv`（MapsTo／解析性／逆／还原）。

### `formal/Kneser/DiscAutomorphism.lean`

```lean
theorem exists_blaschke_of_ball_bijective ... :
    ∃ a C : ℂ, ‖a‖ < 1 ∧ ‖C‖ = 1 ∧ EqOn f (fun z => C*blaschke a z) (ball 0 1)

theorem exists_blaschke_of_upperHalf_bijective ... :
    ∃ a C : ℂ, ‖a‖ < 1 ∧ ‖C‖ = 1 ∧
      ∀ w ∈ upperHalf, F w = cayleyInv (C*blaschke a (cayley w))
```

**单位圆盘的每个双全纯自同构都是 Möbius 变换**，以及经 Cayley 得到的上半平面版本——
后者正是第六步要的形状。证明是教科书路线：取 `a := g 0`，前合成 `blaschke (-a)` 把原点固定住，
于是是旋转，再解开。

非平凡性见证：恒等映射，以及 `blaschke (1/2)` 与其逆——**不是真空真**。

### 3.5 `formal/Kneser/SchwarzReflection.lean` 等三个模块

路线图 §11 的 **Schwarz 反射原理**，mathlib 也缺。三块共 **17 条定理，审计通过**：

```lean
theorem schwarz_reflection {U : Set ℂ} (hU : IsOpen U)
    (hsymm : ∀ x : ℂ, x ∈ U ↔ (starRingEnd ℂ) x ∈ U) {f : ℂ → ℂ}
    (hc : ContinuousOn f {x : ℂ | x ∈ U ∧ 0 ≤ x.im})
    (hd : DifferentiableOn ℂ f {x : ℂ | x ∈ U ∧ 0 < x.im})
    (hreal : ∀ x ∈ U, x.im = 0 → (f x).im = 0) :
    DifferentiableOn ℂ (reflectExtend f) U
```

- `RectangleConservative`：`IsConservativeOn` ⟺ 矩形边界积分为零（靠 mathlib 的
  `wedgeIntegral_add_wedgeIntegral_eq`，两边**逐字相同**），以及**跨实轴矩形在高度 0 处切分**。
- `ReflectedFunction`：`reflectExtend f z = if 0 ≤ z.im then f z else conj (f (conj z))`，
  下半平面可微（用 mathlib 已有的 `DifferentiableAt.conj_conj`）、以及全 `U` 上的连续性
  （两片相对闭集粘接，实轴上一致由"f 在实轴取实值"给出）。
- `SchwarzReflection`：用 Morera 的充要形式
  `Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn` 合拢。

**关键是这个证明不需要任何极限论证。** 跨实轴的矩形切成上下两半后，每半都直接满足
`integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn` 的前提
（闭矩形上连续、开内部可微），公共边相消。路线图 §20 把 Morera 列为反射原理的工具——
mathlib 的 `HasPrimitives.lean` 正好有，所以走的就是标准路线。

### 3.6 `formal/Kneser/DiscFixedPoints.lean` —— §13.2

自同构 `z ↦ C·blaschke a z` 的不动点方程清分母后是**二次式**

```lean
noncomputable def discFixedPoly (a C z : ℂ) : ℂ := (starRingEnd ℂ) a*z^2+(C-1)*z-C*a
```

**关键事实：两根之积的模恒为 1。** 根之积 `= −Ca/ā`，模 `= ‖C‖‖a‖/‖a‖ = 1`。
形式化时不去做因式分解，而是直接给出**伴根**：

```lean
theorem discFixedPoly_companion (ha0 : a ≠ 0) (hz0 : z ≠ 0) (h : discFixedPoly a C z = 0) :
    discFixedPoly a C (-(C*a)/((starRingEnd ℂ) a*z)) = 0
theorem norm_companion (ha0 : a ≠ 0) (hz0 : z ≠ 0) (hC : ‖C‖ = 1) :
    ‖(-(C*a)/((starRingEnd ℂ) a*z))‖ = 1/‖z‖
```

于是"无内点不动点"直接逼出全部根落在单位圆上：若某根模 < 1，它本身就是内点不动点；
若模 > 1，伴根的模 = 1/‖z‖ < 1，还是内点不动点。两边都矛盾，故模 = 1。

```lean
theorem disc_no_interior_fixedPoint_boundary_dichotomy (ha : ‖a‖ < 1) (hC : ‖C‖ = 1)
    (hno : ∀ z : ℂ, ‖z‖ < 1 → C*blaschke a z ≠ z) :
    a ≠ 0 ∧ (∀ z, discFixedPoly a C z = 0 → ‖z‖ = 1) ∧
      ∀ z₁ z, discFixedPoly a C z₁ = 0 → discFixedPoly a C z = 0 →
        z = z₁ ∨ z = -z₁-(C-1)/((starRingEnd ℂ) a)
```

"至多两根"用**显式因式分解** `P z − P z₁ = (z−z₁)(ā(z+z₁)+(C−1))` 给出，不动用多项式 API。

非平凡性见证给的是一个**真正的双曲型**自同构：`a = 1/2`（实）、`C = 1`，
不动点多项式为 `(1/2)(z²−1)`，两根 `±1` 都在圆周上、内部无不动点
（`blaschke_half_no_interior_fixedPoint`、`blaschke_half_fixedPoints`）。

### 3.7 `formal/Kneser/UpperHalfAutomorphism.lean` —— `Aut(ℍ) = PSL(2,ℝ)`

mathlib 有 ℍ 上 `GL(2,ℝ)` 的 Möbius 作用（`UpperHalfPlane/MoebiusAction`）和它的不动点分类
（`UpperHalfPlane/FixedPoints`，含椭圆/抛物/双曲），**但没有"抽象自同构就是这个作用"这座桥**。
补上了：

```lean
theorem upperHalf_aut_real_moebius {F G : ℂ → ℂ} (双全纯自同构的六条假设) :
    ∃ α β γ δ : ℝ, 0 < α*δ-β*γ ∧
      ∀ w ∈ upperHalf, F w = ((α:ℂ)*w+(β:ℂ))/((γ:ℂ)*w+(δ:ℂ))
```

三步：

1. `MoebiusComposite`：把 `cayleyInv ∘ (C·blaschke a) ∘ cayley` 算成闭式
   `(A w + B)/(Γ w + Δ)`，四个复系数显式给出，分母的非零性分解成三个非零因子之积。
2. `MoebiusConjRel`：**四个系数都满足同一条关系 `C·x̄ = −x`**
   （两条"对称"组合乘 `i` 后翻号，与两条"反对称"组合合流），且两个分母系数不可能全为零
   （其和为 `2(1+Ca)`，而 `‖Ca‖ = ‖a‖ < 1`）。
3. `RealMoebius`：两个满足该关系的非零数比值为实（`conj(x/y) = x̄/ȳ = (−x/C)/(−y/C) = x/y`），
   于是除以其中非零的一个，四个系数**同时变实**；行列式为正则由虚部公式
   `Im((αw+β)/(γw+δ)) = (αδ−βγ)·Im w/‖γw+δ‖²` 在**单点 `w = i`** 处取值得到。

第 2 步是整套方法的命门。我在纸上推时其中两条的符号错了，Lean 当场揪出来——
那一步我在纸上写的是"显然对称"。

---

### 3.8 `formal/Kneser/{RealMoebiusMap,MoebiusFixedPoint,ParabolicNormalForm,HyperbolicNormalForm,UpperHalfNormalForm}.lean` —— 无内点不动点自同构的正规形

**`upperHalf_aut_normal_form`**：`ℍ` 的双全纯自同构若在 `ℍ` 内无不动点，则存在
实系数 Möbius 映射 `R`（`ad-bc ≠ 0`）使得

```
R (F w) = R w + 1        （抛物）      或      R (F w) = λ · R w，λ > 0, λ ≠ 1   （双曲）
```

mathlib 有 `Matrix.IsParabolic`/`IsHyperbolic`/`IsElliptic` 的判别式定义与椭圆情形的
完整不动点理论（`Analysis/Complex/UpperHalfPlane/FixedPoints`），**但没有任何正规形**。

抛物那支把唯一的实不动点 `w₀=(α-δ)/(2γ)` 搬到 `∞`（`R w = b/(w-w₀)`，`b=(α+δ)/(2γ)`）；
双曲那支用两个实不动点的交比 `R w=(w-w₁)/(w-w₂)`，乘子 `λ=p/q`，其中 `p,q` 是
特征多项式两根，只靠 `p+q=α+δ`、`pq=αδ-βγ` 两条对称关系即可，平方根只出现一次。

⚠ 陈述里是 `ad-bc ≠ 0` 而非 `> 0`，这是**必须**的：`ζ↦ζ+1` 与 `ζ↦ζ-1` 在 `PSL(2,ℝ)`
中不共轭，`translation_neg_not_positively_conjugate` 给出了反证。

5 模块 / **25 条定理**，详见 [upper-half-normal-form-zh.md](upper-half-normal-form-zh.md)。

---

### 3.9 `formal/Kneser/{DiscTwoPointVanishing,UpperHalfTwoPointVanishing,HyperbolicExclusion}.lean` —— "排除双曲情形"的解析核心

Kneser 排除双曲情形的整段论证，落到最后是一句话（原文 p. 62）：

> …eine in 𝔊 reguläre, nicht identisch verschwindende Funktion, die bei Annäherung an einen der
> beiden Bögen zwischen den beiden Ruhepunkten gegen Null strebt. **Da es eine solche nicht gibt**,
> muß die Substitution parabolisch sein.

"Da es eine solche nicht gibt"（**这样的函数不存在**）就是全部内容。本轮把它证掉了，
3 模块 / **19 条定理**，审计通过（`audit/hyperbolic-exclusion-result.json`）：

```lean
theorem disc_eq_zero_of_boundary_limits {f : ℂ → ℂ} {p q : ℂ} {M : ℝ}
    (hd : DifferentiableOn ℂ f (ball 0 1))
    (hM : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ M)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hlim : ∀ ζ : ℂ, ‖ζ‖ = 1 → ζ ≠ p → ζ ≠ q → Tendsto f (𝓝[ball 0 1] ζ) (𝓝 0)) :
    ∀ z ∈ ball (0 : ℂ) 1, f z = 0
```

**关键是不需要任何边界唯一性理论**（Fatou / Privalov / F. and M. Riesz，mathlib 全无）。
乘上二次式 `(z−p)(z−q)` 之后得到的函数**真的能连续延拓到闭圆盘且边界值为 0**——
在普通边界点靠 `f → 0`、多项式有界，在两个例外点反过来靠 `f` 有界、多项式 → 0——
于是 mathlib 的普通极大模原理 `Complex.norm_le_of_forall_mem_frontier_norm_le` 以 `C = 0`
一次打完。辅助函数 `discPunch f p q z = if ‖z‖ < 1 then f z * ((z−p)*(z−q)) else 0`，
闭圆盘上的连续性按 `closedBall = ball ∪ sphere` 拆成 `nhdsWithin_union` 的两支。

- `UpperHalfTwoPointVanishing`：经 `CayleyTransform` 搬到上半平面，例外点 `{1,−1}` 变成 `{∞,0}`，
  于是 `upperHalf_eq_zero_of_real_limits`：**上半平面上有界全纯、在每个非零实点边界极限为 0 ⟹ 恒零**。
  这正是 §3.8 双曲正规形 `ζ↦λζ` 的坐标（两不动点 `0` 与 `∞`，两段弧就是两条实半轴）。
  新算的只有一条：`cayleyInv` 把**单位圆周**（除 `1`）映到实轴（`cayleyInv_im_eq_zero`）——
  `CayleyTransform.im_cayleyInv` 原来只对开圆盘陈述，虽然那段计算根本没用到假设。
- `HyperbolicExclusion`：接到仓库自己的 §13.2 上。`disc_automorphism_boundary_vanishing` 对
  **任意**无内点不动点的圆盘自同构 `C·blaschke a`，取其不动点多项式的两个根作 `p,q`
  （由 `disc_no_interior_fixedPoint_boundary_dichotomy` 知它们在圆周上），得到同样的结论；
  `hyperbolic_case_excluded` 是 `False` 形态。非平凡性见证用的是 §3.6 那个真双曲的
  `a=1/2, C=1`（不动点 `±1`）。

⚠ **不主张什么**：这只证了**不存在这样的函数**，没有构造 Kneser 的见证函数。
后者是把 `e^{w/c}` 沿黎曼映射从 `w`-平面搬过来，需要区域 𝔅 与 RMT 本身（PR #33505）。
该义务没有被公理化，它留在 `hyperbolic_case_excluded` 的假设位置上。
顺带说明这条引理为什么对抛物情形也成立（它不区分 `p=q`）：所以双曲性必须用在**构造**里
——`e^{w/c}` 的有界性只在双曲替换所保持的那族直线左侧成立。

---

## 4. 剩下什么

| 缺口 | 性质 |
|---|---|
| 经典 RMT（§12） | **已有完整 Lean 证明**（PR #33505），在途并入 mathlib |
| ~~§13.2：无内点不动点 ⟹ 1 或 2 个边界不动点~~ | ✅ **已证**（见 §3.6） |
| ~~`Aut(ℍ) = PSL(2,ℝ)`~~ | ✅ **已证**（见 §3.7）——解锁 mathlib 已有的 `UpperHalfPlane/FixedPoints` 矩阵分类 |
| 排除双曲情形：**解析核心** | ✅ **已证**（见 §3.9）——"两段边界弧上极限都为零的有界全纯函数只能恒零"，圆盘与上半平面两种坐标都有 |
| 排除双曲情形：**见证函数的构造** | 未做。把 `e^{w/c}` 沿黎曼映射从 `w`-平面搬到圆盘，需要区域 𝔅 与 RMT 本身；是 §3.9 诸定理的假设位置 |
| ~~抛物型 ⟹ 共轭于 `ζ↦ζ+1`~~ | ✅ **已证**（见 §3.8） |
| ~~Schwarz 反射原理~~ | ✅ **已证** |
| 第 2–4 步的装配 | 仓库零件齐，但接到 Kneser 主线上还需对接工作 |
| Jordan 曲线定理 | mathlib 无——但只有 Trappmann–Kouznetsov 的**唯一性**那半要用，Kneser 存在性不需要 |

---

## 5. 不主张什么

1. **没有证明 Kneser 定理**，也没有构造出 `F`。
2. **没有说 QC 路线是错的**——[§8](theta-qc-global-existence.md) 经对抗性复核**无逻辑缺口**。
   它只是选了一条在 Lean 里走不通的路。
3. 第 2–4 步"仓库已有"指的是**零件齐备**（不动点、Koenigs、Poincaré 整函数），
   不等于已经按 Kneser 的方式装配好。
4. 本轮补的十二个模块是**经典复分析**，不是新数学；价值在于它们是 mathlib 的真实空白，
   且卡在关键路径上。（对比：[墙 A 归约](wall-a-reduction-zh.md) §0 记录了一次相反的教训——
   那里的半带引理 mathlib 早已有，属于重复劳动。**先搜库**。）

---

## 6. 复现

```sh
# 圆盘自同构群 + Cayley
ssh galic 'docker exec -u lean lean-build bash -lc \
  "cd ~/projects/kneser-formal && python3 audit_modules.py --name disc-automorphism \
     --module BlaschkeFactor --module DiscRotation --module CayleyTransform \
     --module DiscAutomorphism"'
# Schwarz 反射
ssh galic 'docker exec -u lean lean-build bash -lc \
  "cd ~/projects/kneser-formal && python3 audit_modules.py --name schwarz-reflection \
     --module RectangleConservative --module ReflectedFunction --module SchwarzReflection"'
```

分别输出 `PASS: 35 theorems in 4 selected modules` 与 `PASS: 17 theorems in 3 selected modules`，
一次性合并审计八个模块（加上 `DiscFixedPoints`）输出
`PASS: 84 theorems in 12 selected modules; allowed axioms only.`

```sh
# 无内点不动点自同构的正规形（§3.8）
ssh galic 'docker exec -u lean lean-build bash -lc \
  "cd ~/projects/kneser-formal && python3 audit_modules.py --name upper-half-normal-form \
     --module RealMoebiusMap --module MoebiusFixedPoint --module ParabolicNormalForm \
     --module HyperbolicNormalForm --module UpperHalfNormalForm"'
```

输出 `PASS: 25 theorems in 5 selected modules; allowed axioms only.`

```sh
# 排除双曲情形的解析核心（§3.9）
ssh galic 'docker exec -u lean lean-build bash -lc \
  "cd ~/projects/kneser-formal && python3 audit_modules.py --name hyperbolic-exclusion \
     --module DiscTwoPointVanishing --module UpperHalfTwoPointVanishing \
     --module HyperbolicExclusion"'
```

输出 `PASS: 19 theorems in 3 selected modules; allowed axioms only.`
二十模块合计 **128 条定理**审计通过。
全项目 `lake build` 为 48028 job。
