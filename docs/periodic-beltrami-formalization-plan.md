# 周期 Beltrami 定理的 Lean 形式化施工计划

2026-09-17。本文是**施工计划**，不是状态记录——状态见
[formal/GEOMETRIC-ROUTE-STATUS.md](../formal/GEOMETRIC-ROUTE-STATUS.md)。

目标定理是 [theta-periodic-beltrami.md](theta-periodic-beltrami.md) §1，
它是 [theta-qc-global-existence.md](theta-qc-global-existence.md) §5 的唯一入口，
因而也是墙 A 第 (1) 条（`F` 在 Lean 内没有实例）的唯一通路。

## 0. 目标陈述

设 μ 在复平面上可测、1-周期，`μ(z) = 0` 当 `|Im z| > Y`（`0 < Y ≤ 1`），`‖μ‖∞ ≤ k`。
则存在唯一固定 `0`、`1`、`∞` 的定向保持拟共形同胚 χ，满足

```
χ_z̄ = μ · χ_z
χ(z+1) = χ(z) + 1
sup_ℂ ‖χ(z) − z‖ ≤ 40k/(1 − Ck)
```

其中 `C` 是平面 Beurling 算子在 `L⁴` 上的算子范数界（见 §1）。
若 `μ(z̄) = conj(μ(z))` 则 χ 实对称；`χ(z) − z` 在上下两端分别趋于常数，
且在每个端点的足够高半平面内解析。

## 1. 先定一件事：不要去证 `‖B‖_{L⁴} < 12`

原文取的 `12` 是**宽松常数**，文档自己写明"这个宽松常数由 Bañuelos–Janakiraman 的
Theorem 1.1 直接推出"。它在整条链里只出现两处：

- 收缩条件 `12k < 1`；
- `‖v‖₄ ≤ ‖μ‖₄/(1 − 12k)`。

换成任意显式常数 `C`，结论只是变成 `sup‖χ − id‖ ≤ 40k/(1 − Ck)`，其余不动。

证书实测 `ε = 3.2655e-38`，故 `k = 10⁵ε = 3.2655e-33`。
要 `Ck < 1` 需 **`C < 3.06e32`**。theta-periodic-beltrami.md §1 亦注明
"只要求 k<1/12 是为得到下面的显式收缩预算；一般存在性并不需要这个较强限制"。

**结论**：模块 #7 的目标不是 `12`，而是**任何低于 `3.06e32` 的显式常数**。
作为参照，已知的非尖锐界（Nazarov–Volberg 的 `2(p−1) = 6`、
Bañuelos–Janakiraman 的 `≈ 4.7`）都远小于 12——**真值与要求之间有 32 个数量级**。

⚠ **但"任何显式 `C` 都行"是错的，见 §8。** 余量虽有 32 个数量级，
却不是无限：RiemannDynamics 现成的那个常数是 **2.79e46**，恰好超出。
§8 是对本节的实测更正，以 §8 为准。

⚠ 但"显式"是硬要求。[will1491/RiemannDynamics](https://github.com/will1491/RiemannDynamics)
的 `beurling_lp_bound` 形如

```lean
theorem beurling_lp_bound (hp : 1 < p) (hp' : p ≠ ⊤) :
    ∃ C : ℝ, IsCalderonZygmundBound beurling p C
```

**`C` 是存在量词**（`p > 2` 那支还要再 `obtain` 一次 `eLpNorm_beurling_Lp_le_high`
的存在常数），喂不进 `Ck < 1`。这一格必须自建。

## 2. 模块表

难度栏：低 = 常规、中 = 需要设计、高 = 长证明、❌ = 门。

### L0 基础设施

| # | 模块 | 内容 | 难度 | 可复用 |
|---|---|---|---|---|
| 1 | `CylinderLp` | 圆柱 `ℂ/ℤ` 的 `L^p`：基本条带上的积分、与 1-周期平面函数的对应、光滑紧支撑周期函数在圆柱 `L⁴` 中稠密（§2 末尾延拓 `B_per` 要用） | ✅ **已证**（含稠密性） | mathlib 测度论 |
| 2 | `PeriodicSupport` | 1-周期 ＋ `supp ⊂ \|Im z\| ≤ Y` 的类；`‖μ‖₄ ≤ k(2Y)^{1/4}` | ✅ **已证** | — |

> ## ✅ **L0 第一阶段完成**（2026-09-17）
>
> `Kneser/PeriodicSupport.lean`（**6 条**）＋ `Kneser/CylinderLp.lean`（**8 条**），
> 共 **14 条定理**，`audit_modules.py --name l0-layer` 通过，全项目 **48033 job**。
>
> **#2 `PeriodicSupport` 全部完成**：
> - `fundamentalStrip Y`＝`Re ∈ (−1/2, 1/2]` ∧ `|Im| ≤ Y`
> - `volume_fundamentalStrip`：面积恰为 `2Y`（经 `Complex.volume_preserving_equiv_real_prod`）
> - **`volume_fundamentalStrip_le_two`**：`Y ≤ 1` ⟹ 面积 ≤ 2
> - `lintegral_rpow_le_of_bound`：`‖μ‖∞ ≤ k` ⟹ `∫_D ‖μ‖⁴ ≤ k⁴·2Y`，即 §4 的 `‖μ‖₄ ≤ k(2Y)^{1/4}`
> - ⭐ **`lintegral_kernel_rpow_le_strip`——兑现了 #4 遗留的末端打包**：
>   把 #4 的域无关结论实例化到真正的基本条带上。**#4 至此完全闭合。**
>
> **#1 `CylinderLp` 第一阶段**（铺砌与周期不变性，#8 真正要用的那块）：
> - `stripTranslate Y n`、`stripTranslate_eq_preimage`（＝基本条带在 `w ↦ w−n` 下的原像）
> - `volume_stripTranslate`：平移不改面积
> - `stripTranslate_disjoint` ＋ `iUnion_stripTranslate`：**整数平移铺满整条带 `|Im w| ≤ Y`**
> - `periodic_int`：1-周期推广到整数周期（`Int.induction_on`）
> - **`lintegral_stripTranslate_of_periodic`**：1-周期函数在每个平移条带上的积分都相同
>
> mathlib 只有 ℝ 上的 `isAddFundamentalDomain_Ioc`，**没有 ℂ 上沿实轴方向的版本**，故自建。
>
> **#1 仍欠**：光滑紧支撑周期函数在圆柱 `L⁴` 中稠密（§2 末尾延拓 `B_per` 要用）。
>
> ⚠ 踩的坑：`Set.Ioc (-(1/2) + n) …` 里 `n : ℤ` 会被当成 `Set ℤ`，**必须显式写 `(n : ℝ)`**；
> `ℝ≥0∞` 记号要 `open scoped ENNReal`；没有 `measure_preimage_sub_right`，
> 用 `(measurePreserving_sub_right volume c).measure_preimage`；
> 本版 `Int.induction_on` 的 case 名是 **`zero`/`succ`/`pred`**（不是 `hz`/`hp`/`hn`）；
> `ENNReal.ofReal_rpow_of_nonneg` 方向是 `ofReal x ^ y = ofReal (x^y)`，**别加 `←`**。

### L1 cot 核的显式估计（对应 §3）

> ## ✅ **L1 整层已完成**（2026-09-17）
>
> #3 + #4 + #5 共 **26 条定理**（8 + 14 + 4），三个模块各自 `lake build` 与
> `audit_modules.py` 均通过，全部并入根导入，全项目 `lake build` 由 48028 升至
> **48031 job**，整体仍通过。
>
> **L1 证出的三个数**，正是 §3 那条链上的三个常数：
>
> | 常数 | 出处 | Lean 定理 |
> |---|---|---|
> | `1 + 1/(2d)` | cot 的逐点模界 | `norm_cot_pi_mul_le`（#3） |
> | `3π` | 单位圆盘上 `∫ d^{-4/3}` | `lintegral_ball_norm_rpow_le`（#4） |
> | `10` | `‖cot 核‖_{L^{4/3}}` | `closing_arith` ＋ `l43_norm_le_ten`（#4/#5） |
> | `20` | `‖Pv(z) − Pv(0)‖ ≤ 20‖v‖₄` | `potential_difference_bound`（#5） |
>
> **原文 §3 的每个常数都已验算成立**，且 `10` 有余量（实际约 9.32）。
>
> 顺带补的 mathlib 空白共 **6 条**：`norm_sq_sin_ofReal_add_mul_I`、
> `norm_sq_cos_ofReal_add_mul_I`、`abs_sinh_eq_sinh_abs`（#3）；
> `volume_complex_ball`、`superlevel_set_norm_rpow`、`lintegral_Ioi_one_rpow`（#4）。
>
> **下一步转 L0**（#1 `CylinderLp`、#2 `PeriodicSupport`）：
> #4/#5 都刻意写成了**域无关**形式，L0 把 `D` 定义出来后直接代入即可，
> 不需要回头改 L1。

> **#3 已完成**（2026-09-17）。`formal/Kneser/CotKernelBound.lean`，**8 条定理**，
> galic 上 `lake build Kneser.CotKernelBound` 通过，
> `audit_modules.py --name cot-kernel-bound --module CotKernelBound` 通过
> （`audit/cot-kernel-bound-result.json`：8 theorems, allowed axioms only，
> 无 `sorry`、无自定义公理、无 `native_decide`）。已并入根导入，
> 全项目 `lake build` 从 48028 升至 **48029 job**，整体仍通过。
>
> 主定理 `Kneser.norm_cot_pi_mul_le`：
> ```lean
> theorem norm_cot_pi_mul_le {x y : ℝ} (hx : |x| ≤ 1 / 2) (hxy : 0 < x ^ 2 + y ^ 2) :
>     ‖Complex.cot ((π : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I))‖
>       ≤ 1 + 1 / (2 * Real.sqrt (x ^ 2 + y ^ 2))
> ```
> 八条依次是：`norm_sq_sin_ofReal_add_mul_I`、`norm_sq_cos_ofReal_add_mul_I`（模平方公式，
> **mathlib 无此二条**）、`two_mul_abs_le_abs_sin_pi_mul`、`abs_sinh_eq_sinh_abs`
> （**mathlib 亦无**）、`two_mul_abs_le_abs_sinh_pi_mul`、`four_mul_sq_add_sq_le_denom`、
> `norm_sq_cot_ofReal_add_mul_I_le`、`norm_cot_pi_mul_le`。
>
> 用到的 mathlib 支点：`Complex.sin_add_mul_I` / `cos_add_mul_I`、
> `Complex.normSq_eq_norm_sq`、`Complex.cot_eq_cos_div_sin`、
> `Real.mul_abs_le_abs_sin`（Jordan 不等式）、`Real.self_le_sinh_iff`、
> `Real.cosh_sq`、`Real.pi_gt_three`。
>
> ⚠ 踩到的坑：`le_or_lt` 在本版 mathlib 已不存在，要用 **`le_or_gt`**；
> 没有 `Real.sin_sq_nonneg`，用 `sq_nonneg (Real.sin x)`。

> **#4 部分完成**（2026-09-17）。`formal/Kneser/CotKernelL43.lean`，**7 条定理**，
> `lake build` 与 `audit_modules.py --name cot-kernel-l43 --module CotKernelL43` 均通过。
> 已并入根导入，全项目 **48030 job**，整体仍通过。
>
> **已证的七条**，分两组：
>
> *逐点分区界与收尾算术（5 条）*
> - `one_add_inv_two_mul_le_near`：`0 < d ≤ 1` ⟹ `1 + 1/(2d) ≤ (3/2)/d`
> - `one_add_inv_two_mul_le_far`：`1 ≤ d` ⟹ `1 + 1/(2d) ≤ 3/2`
> - `cube_three_pi_add_two_lt`：`(3π+2)³ < (20/3)⁴`
> - `three_pi_add_two_lt_rpow`：`3π + 2 < (20/3)^{4/3}`
> - `closing_arith`：**`(3/2)·(3π+2)^{3/4} < 10`**——即"若 `∫ ≤ (3/2)^{4/3}(3π+2)`
>   则 `‖·‖_{4/3} < 10`"。**原文那个 `10` 已经验算过，成立且有余量**
>   （实际值约 9.32）。
>
> *第二阶段的可复用件（2 条）*
> - `volume_complex_ball`：`volume (ball (0:ℂ) r) = ofReal r ^ 2 * ofReal π`，
>   由 `InnerProductSpace.volume_ball_of_dim_even` 特化（`finrank ℝ ℂ = 2·1`）
> - `superlevel_set_norm_rpow`：`t > 0` ⟹
>   `{w : t < ‖w‖^(-4/3)} = {w : w ≠ 0 ∧ ‖w‖ < t^(-3/4)}`
>
> **Layer cake 与收尾装配已补齐**（同日稍后）。模块现为 **14 条定理**，
> 审计仍通过，全项目 **48030 job**。新增两组：
>
> *Layer cake（4 条）*
> - `lintegral_Ioi_one_rpow`：`∫₁^∞ t^{-3/2} dt = 2` 的 lintegral 形式
> - `meas_superlevel_le_pi` / `meas_superlevel_le_rpow`：超水平集测度的两个界
>   （全局 `π`；`t` 大时 `π t^{-3/2}`）
> - **`lintegral_ball_norm_rpow_le`：`∫_{ball 0 1} ‖w‖^{-4/3} ≤ 3π`**
>   ——这就是原文那个 `3π`，由 layer cake 精确复现：
>   `∫ = ∫₀^∞ vol{‖w‖^{-4/3} > t} dt`，把 `(0,∞)` 拆成 `(0,1]`（用全局界 `π`，长度 1）
>   与 `(1,∞)`（用 `π t^{-3/2}`，积分 2），合计 `π(1+2)`。
>
> *收尾装配（3 条）*
> - `kernel_rpow_le_near` / `kernel_rpow_le_far`：逐点界升到 `4/3` 次幂
> - **`lintegral_kernel_rpow_le`**：在**任何**面积 ≤ 2 的可测域 `S` 上
>   `∫_S (1 + 1/(2‖w‖))^{4/3} ≤ (3/2)^{4/3}(3π + 2)`。
>   与 `closing_arith` 合起来即 `‖·‖_{4/3} < 10`。
>
> 这条收尾**刻意写成域无关的形式**（只要求 `MeasurableSet S` 与 `volume S ≤ 2`），
> 所以不必等 #1/#2 就能证。**仍欠的只是末端打包**：把它套到具体的
> `D = 基本条带 ∩ |Im w| ≤ Y` 上并换成 `eLpNorm` 记法——那需要 #1/#2 先定义出 `D`。
> **#4 的数学内容已全部形式化。**
>
> ⚠ 又踩的坑：`rw [← hval]`（`hval : ∫ … = 2`）会把指数 `-3/2` 里的 `2` **一起替换掉**，
> 要改成正向 `rw [← ofReal_integral_eq_lintegral_ofReal …]` 再 `congr 1`；
> `Measure.restrict_apply_le` 给的是 `μ.restrict s A ≤ μ A`，想要 `≤ μ s` 得走
> `Measure.restrict_apply'` ＋ `measure_mono Set.inter_subset_right`；
> `Set.diff_subset` 已废弃，用 `Set.sdiff_subset`；`gcongr` 会把目标直接降到子集包含，
> 此时给 `Set.inter_subset_right` 而不是 `lintegral_mono_set`。
>
> ⚠ 踩到的坑：rpow 要显式 `import Mathlib.Analysis.SpecialFunctions.Pow.Real`，
> 否则 `^` 连实指数的 instance 都合成不出来，所有 `Real.rpow_*` 报 Unknown constant；
> `lt_inv_comm₀` 的参数顺序是 `(ha : 0 < a) (hb : 0 < b) : a < b⁻¹ ↔ b < a⁻¹`，写反会类型不匹配。

| # | 模块 | 内容 | 难度 | 可复用 |
|---|---|---|---|---|
| 3 | `CotKernelBound` | `‖cot(π(x+iy))‖ ≤ 1 + 1/(2d)`，靠 `|sin πx| ≥ 2|x|`、`|sinh πy| ≥ 2|y|` 与 cot 的模平方公式；`d` = `Re(z−w)` 约化到 `[−1/2,1/2]` 后到 `0` 的欧氏距离 | ✅ **已证** | mathlib 三角/双曲函数 |
| 4 | `CotKernelL43` | `‖cot 核‖_{L^{4/3}} < 10`，**且与 z 无关**；积分域面积 ≤ 2，`d < 1` 部分的 `d^{−4/3}` 积分 ≤ 单位圆盘上的 `3π`，`d ≥ 1` 部分 ≤ 2 | ✅ **已证**（末端打包已由 #2 的 `lintegral_kernel_rpow_le_strip` 兑现） | — |
| 5 | `PotentialUniformBound` | Hölder ⟹ `‖P v(z) − P v(0)‖ ≤ 20‖v‖₄`，即原文 (4) | ✅ **已证** | mathlib Hölder |

### L2 周期 Beurling 算子（对应 §2，最重）

| # | 模块 | 内容 | 难度 | 可复用 |
|---|---|---|---|---|
| 6 | `PeriodizedKernel` | `−1/(πz²)` 按水平整数平移周期化；收敛性及与 cot 的关系（`∑ₙ 1/(z+n)² = π²/sin²(πz)`） | 🟡 **恒等式已证**（上半平面；下半平面待补） | **mathlib 有 `iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow`** |

> ## 🟡 **#6 第一阶段完成**（2026-09-17）
>
> `Kneser/PeriodizedKernel.lean`，**3 条定理**，
> `audit_modules.py --name periodized-kernel` 通过，全项目 **48034 job**。
>
> **主结论 `tsum_inv_sq_add_int`**（在开上半平面 `ℍₒ` 上）：
> ```lean
> theorem tsum_inv_sq_add_int {z : ℂ} (hz : z ∈ ℍₒ) :
>     ∑' n : ℤ, 1 / (z + n) ^ 2 = (π : ℂ) ^ 2 / (Complex.sin ((π : ℂ) * z)) ^ 2
> ```
> 左边正是（去掉 `−1/π` 因子的）**周期化 Beurling 核**，右边是
> `−(1/π)·d/dz[π cot(πz)]`，即**周期 Cauchy 势的 `∂` 导数**——这就是 §2 要的那条关系。
>
> **省力的关键**：mathlib 已有全阶导数展开
> `iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow`
> （`= (−1)^k · k! · ∑' n:ℤ, 1/(z+n)^{k+1}`），取 `k = 1` 即可。
> 我们只需自补 **`hasDerivAt_cot`**（`deriv cot = −1/sin²`，**mathlib 没有这条**，
> 由 `cot = cos/sin` ＋ `HasDerivAt.div` ＋ 毕达哥拉斯恒等式现推）
> 与 `deriv_pi_mul_cot_pi_mul`。
>
> **#6 仍欠**：恒等式目前只在**开上半平面**上（mathlib 那条定理的定义域）。
> 下半平面可由共轭对称补出；实轴去掉 ℤ 后在 ℂ 中是**零测集**，对 `L^p` 估计无影响。
> 另欠周期化核本身的定义与收敛性陈述。
>
> ⚠ 踩的坑：`Cotangent.lean` 里的引理**都在根命名空间**（`sin_pi_mul_ne_zero`、
> `iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow`），**不是 `Complex.` 下**；
> `Complex.cot_eq_cos_div_sin` 带显式参数；`HasDerivAt.comp` 产生的函数是
> `cot ∘ HMul.hMul ↑π`，与 `fun x => (↑π * x).cot` **只是 defeq 不是语法相同**——
> `rw [hcomp.deriv]` 会失败，要改用 `exact hcomp.deriv`。
| 7 | `PlaneBeurlingLpExplicit` | **平面 `‖B‖_{L⁴} ≤ C`，`C` 显式且 `< 3.06e32`**（见 §8 实测、§9 路线） | 🟡 **有明确路线**（原判 ❌） | RiemannDynamics 的 **`eLpNorm_czOperator_beurling` 已给 `2⁹ = 512`**；换掉插值的 `L²` 输入即得 **6.52e22**，清过预算 10 个数量级。见 §9 |
| 8 | `BeurlingTransfer` | 平面界 → 圆柱界 (2)，**拆成 #8a–#8e，见下** | ❌ **唯一剩下的门**；#8a 已证 | — |
| 9 | `PeriodicCauchyPotential` | `P_per v(z) = ∫_{[0,1]×ℝ} cot(π(z−w)) v(w) dA(w)` 的定义，及 `∂̄P_per v = v`、`∂P_per v = B_per v`，即原文 (3)；先对光滑紧支撑输入按分布求导，再由 (2) 与 #5 延拓到定理所需输入 | 高 | — |

### L3 不动点（对应 §4 前半）

| # | 模块 | 内容 | 难度 | 可复用 |
|---|---|---|---|---|
| 10 | `PeriodicBeltramiFixedPoint` | 在圆柱 `L⁴` 上解 `v = μ(1 + B_per v)` (5)：线性部分范数 `≤ Ck < 1`、常数项 `μ ∈ L⁴`，Banach 给唯一 `v`，`‖v‖₄ ≤ ‖μ‖₄/(1−Ck) ≤ 2k/(1−Ck)`；并由 (5) 证 `supp v ⊂ |Im z| ≤ Y` | 低 | mathlib `ContractingWith` |
| 11 | `ChiConstruction` | `u = P_per v − P_per v(0)`、`χ(z) = z + u(z)`；由 (3) 得 `χ_z̄ = v = μ(1 + B_per v) = μ χ_z`；由 (4) 得位移界；`u` 周期 ⟹ `χ(z+1) = χ(z)+1`；`u(0) = 0` ⟹ `χ(0)=0`、`χ(1)=1` | 低 | — |

### L4 同胚性（对应 §4 后半）

| # | 模块 | 内容 | 难度 | 可复用 |
|---|---|---|---|---|
| 12 | `StoilowFactorization` | χ 连续、局部 `W^{1,4}`、Beltrami 系数模 `< 1`；取 MRMT 给的平面拟共形坐标 `q`（同系数 μ），弱导数链式法则把 `χ∘q⁻¹` 的 `∂̄` 化为零，Weyl 引理使之成为整函数。这是平面 Stoïlow 分解 | 中 | ✅ **`mrmt_exists` ＋ 对方 `QC/Calculus/Weyl.lean` 直接接** |
| 13 | `ProperDegreeOne` | `χ = id + u`、`u` 全局有界 ⟹ χ proper；proper 同伦 `z ↦ z + t·u(z)` 与恒等映射同拓扑次数 1；故整函数 `χ∘q⁻¹` 亦 proper、次数 1，必是一次多项式 | 高 | ⚠ mathlib 拓扑次数覆盖不全，proper 同伦不变性未必现成——**动手前先确认** |
| 14 | `ChiHomeomorph` | 合拢：χ 是定向保持拟共形同胚 | 低 | — |

### L5 附加性质（对应 §4 末尾）

| # | 模块 | 内容 | 难度 | 可复用 |
|---|---|---|---|---|
| 15 | `ChiUniqueness` | 固定 `0`、`1`、`∞` 的归一化解唯一 | 中 | ✅ 可直接用 `mrmt_unique_normalized` |
| 16 | `ChiRealSymmetric` | `μ(z̄) = conj μ(z)` ⟹ χ 实对称：反射后的解满足同一系数与同一归一化，由 #15 逼出相等 | 低 | 依赖 #15 |
| 17 | `ChiEndLimits` | `cot(π(z−w))` 在上下两端分别一致趋 `−i`、`i`；`v` 紧支撑且 `∈ L¹` ⟹ `u` 分别趋于常数；支撑外 `v = 0`，由 (3) 得 `u` 解析 | 中 | — |
| 18 | `PeriodicBeltramiTheorem` | §0 完整陈述的装配 | 低 | — |

### 下游（不属于本定理，列出以便排期）

| # | 模块 | 内容 |
|---|---|---|
| 19 | `QcCorrection` | theta-periodic-beltrami.md §5 的应用：`F = F_hat ∘ χ⁻¹` 在 `χ(H)` 上解析、满足完整函数方程、`F(0)=1`；`‖F − p‖ ≤ ε + MD`；Cauchy 系数估计给 `‖F−p‖_r ≤ [s/(s−r)](ε + MD)`。这是 theta-qc-global-existence.md §5 的 (5) |

## 3. 依赖关系

```
#1 CylinderLp ──┬─→ #8 BeurlingTransfer ──→ #9 PeriodicCauchyPotential ──┐
#2 PeriodicSupport ┘                                                     │
                                                                          │
#7 PlaneBeurlingLpExplicit ──→ #8                                        │
                                                                          │
#3 CotKernelBound ──→ #4 CotKernelL43 ──→ #5 PotentialUniformBound ──────┤
                                                                          │
#6 PeriodizedKernel ──→ #8, #9                                           │
                                                                          ↓
                                              #10 PeriodicBeltramiFixedPoint
                                                          ↓
                                                  #11 ChiConstruction
                                                          ↓
                          #12 StoilowFactorization ──→ #13 ProperDegreeOne
                                                          ↓
                                                  #14 ChiHomeomorph
                                                          ↓
                          #15 ChiUniqueness ──→ #16 ChiRealSymmetric
                                                          ↓
                                #17 ChiEndLimits ──→ #18 PeriodicBeltramiTheorem
                                                          ↓
                                                    #19 QcCorrection
```

两条链在 #10 汇合：L1（cot 核，右支）与 L2（Beurling 算子，左支）互不依赖。

## 4. 建议次序

1. ~~**先做 L1（#3–#5）**~~ —— ✅ **整层已完成**（26 条定理，见上）。
2. **现在做 #1、#2、#6**。基础设施，难度可控，为 L2 铺路。
   #4/#5 已写成域无关形式，L0 定义出 `D` 后直接代入，不必回头改 L1。
3. **然后攻 #7**。按 §1 改成"任意显式 `C`"。这一格的成败决定整件事的工期。
4. **#8 紧随其后**。纯硬分析的极限论证，没有捷径。#7 与 #8 是仅有的两道门。
5. **#9–#11 一气呵成**。#10、#11 本身很轻，卡住只会是因为 #9 的分布求导。
6. **L4、L5 最后**。#12、#15 接外部代码，#13 有 mathlib 覆盖风险，先探再写。

## 5. 外部依赖的真实收益

十八格里只有两格能真正接上 RiemannDynamics：

- **#12** —— `mrmt_exists` 给的 `q` 就是 §4 里"平面拟共形坐标 q"，签名一字不差，
  可直接 `obtain ⟨q, hq⟩ := mrmt_exists b`；Weyl 引理用对方的 `QC/Calculus/Weyl.lean`。
- **#15** —— 直接用 `mrmt_unique_normalized`。

其余十六格都要自己写。**不要把 RiemannDynamics 说成"§5 交钥匙"**：
MRMT 是整条链里最重、最不想自己证的一块，但它只占十八格里的两格。

依赖它需要把工具链从 `leanprover/lean4:v4.32.0` 抬到 `v4.33.0`
（RiemannDynamics 下游于 mathlib v4.33.0 + RMT4 + Carleson）。
另有指数错配：对方的 `IsQCAnalytic` 打包的是 `MemW12loc`（`L²`），
而本定理与 §4 的 `F_hat` 走局部 `W^{1,4}`；对方有 `L⁴` 机器
（`beurling_ae_tendsto_neg_pi_two_four` 的插值端点就是 `p₀=2`、`p₁=4`），
但没打包进 `IsQCAnalytic`，接的时候要自己补一层。

## 6. 已知风险

| 风险 | 说明 | 处置 |
|---|---|---|
| #7 的常数太大 | **已探查，见 §8/§9**。常数不是拿不到，是接线时被放大丢了 | **已找到路线**：把插值的 `L²` 输入从 `C10_1_6 4 = 2¹⁶⁶` 换成他们自己的 `2⁹`，`C` 从 2.79e46 降到 **6.52e22**，清过预算 10 个数量级。无新数学，见 §9 |
| #7 的工具链 | §9 的四步都在 RiemannDynamics 代码里（v4.33.0），本项目在 v4.32.0 | **未决**：上游 PR vs 移植（后者要一并引入 Carleson）。动手前必须先定 |
| #13 的拓扑次数 | mathlib 的 Brouwer 次数覆盖不全，proper 同伦不变性未必现成 | 动手前 grep 确认，别重蹈"以为 mathlib 有"的覆辙 |
| #8 的极限论证 | 三重极限（`M → ∞`、`ε → 0`、高度放开）嵌套，形式化中最易失控的一类 | 先把纸面证明逐步拆细，确认每步的一致性来源 |
| 工具链抬升 | v4.32.0 → v4.33.0 可能冲击现有 492 个模块 | 在 galic 上开分支试编，不要在主线上做 |

## 7. 纪律

同项目既有规则：编译只在 galic 容器（`lean-build`，用户 `lean`），
任何"已证"以 `lake build` 通过 ＋ `audit_modules.py` 公理审计通过为准
（无 `sorry`、无自定义公理、无 `native_decide`，只允许
`propext` / `Classical.choice` / `Quot.sound`）。

⚠ 审计脚本的正则是 `^theorem\s+(\w+)`——写成 `@[simp] theorem` 的定理不会进入审计，
要审计就把属性后置成 `attribute [simp] foo`。

⚠ 本计划中"平面 `‖B‖_{L⁴} ≤ C`"（#7）在补齐之前，应当留在**假设位置**，
不要公理化——与项目对 Kneser 见证函数构造的处理一致。

## 8. #7 可行性探查结果（2026-09-17）

**结论：走 (a) 收紧证书行不通，必须走 (b) 专门的 Beurling 估计。**
但 (b) 的目标极软——有 30 个以上数量级的余量。

⚠ 本节**更正**了 §1 的说法。§1 写"目标是任何显式可算的 `C`"，
这是**错的**：余量虽大但有限，而现成常数恰好超出。§1 的其余部分仍然成立。

### 8.1 常数不是拿不到——是被 `∃` 包起来了

[will1491/RiemannDynamics](https://github.com/will1491/RiemannDynamics) 的整条链都是显式闭式：

| 环节 | 内容 |
|---|---|
| `eLpNorm_beurling_Lp_le_high` | 陈述写成 `∃ C`，但证明里 `set C := 1/π * beurlingTruncLpConst p'`，docstring 明写"The constant is `(1/π) · beurlingTruncLpConst p'`" |
| `beurlingTruncLpConst p` | `= C_realInterpolation 1 2 1 2 p (C10_0_3 4) (C10_1_6 4) 1 (2(1−p⁻¹))` |
| `C_realInterpolation` | Carleson 项目的**完全显式闭式**，无存在量词 |
| `C10_0_3 a` | `= 2^(a³+19a)`，a=4 时 **2¹⁴⁰ ≈ 1.39e42** |
| `C10_1_6 a` | `= 2^(a³+24a+6)`，a=4 时 **2¹⁶⁶ ≈ 9.35e49** |

所以"解开存在量词"是**机械工作**，不需要新数学。

### 8.2 但这个常数太大了 14 个数量级

`p' = 4/3` ⟹ `t = 2(1−3/4) = 1/2`，几何平均 `2⁷⁰·2⁸³ = 2¹⁵³`，
加前因子（`2A=2`、`(4/3)^{3/4}`、`(3/2+3)^{3/4}`）再除以 `π`：

    C ≈ 2.79e46

收缩要求 `C·k < 1`。证书 `qc-overlap-e50/sewing-budgets.json` 的实测值：

| 量 | 值 |
|---|---|
| `epsilon_upper` | 3.2655e-38 |
| `beltrami_norm_upper` `k = 10⁵ε` | 3.2655e-33 |
| **`C·k`** | **9.10e13**（需要 < 1） |
| 现有证书能容忍的最大常数 | **3.06e32**（= 2¹⁰⁷·⁹） |
| 要用现成常数则需 | `ε < 3.59e-52` |

### 8.3 收紧 ε 的成本：已实测

ε 的来源已定位：`remainder = G·(1/2)^order/(1−1/2)`，order=128 时 `2⁻¹²⁷ = 5.9e-39`。
**seam 区 100% 由它主导，upper 区 72%。**

在 galic 上实跑 `certify_theta_qc_overlap.py`（基线精确复现原证书）：

| | order 128 | order 192 | 变化 |
|---|---|---|---|
| 耗时 | 110 s | 158 s | **1.44×** |
| seam 界 | 2.36e-38 | **4.90e-52** | 降 14 个数量级 |
| upper 界 | 3.27e-38 | **9.20e-39** | 只降 3.5× |

**提阶几乎免费**（1.44×，不是预想的 `O(cap²)`），且 seam 区一步到位。
但 **upper 区卡死**。order 192 下的分解：

| 项 | 值 |
|---|---|
| `remainder` | 1.27e-57 ← 已死 |
| `finite_bound` | 3.80e-39 |
| `extra = depth + LS·theta_error` | 5.41e-39（`theta_error = 1.95e-39`，`LS = 2.78`） |
| **合计** | **9.20e-39** |

两项都来自**上游的 Fourier/contraction 证书**，不是这个脚本。
`theta_error` 的尾部是 `G·q^192/(1−q)`，`q = 0.6242`，`q^192 = 4.6e-40`；
要压到 1e-53 需要约 **264 个 Fourier 模**而非 192。

### 8.4 致命处：系数表硬顶在 50 位

    fixed_point_strings("e", 50, 150) -> DIGITS=50  RESIDUAL=2.618e-52
    fixed_point_strings("e", 70, 150) -> DIGITS=50  RESIDUAL=2.618e-52   ← 静默返回同一张表
    fixed_point_strings("e", 90, 150) -> DIGITS=50  RESIDUAL=2.618e-52

`coefficients(base, digits)` 对 base `e` 是**出厂缓存**（docstring：
"built on demand for bases other than e and 2"），请求更高位数被静默忽略。

于是整条流水线的底线就是这张表的 **RESIDUAL = 2.618e-52**。
而用现成常数所需的是 `ε < 3.59e-52`——**同一个数量级，余量只有 1.4 倍**，
且这还假设上游其余所有项都变得可忽略。**这不是一个可用的方案。**

### 8.5 结论与建议

**(a) 收紧 ε：否决。** 提阶免费，但系数表硬顶在 2.6e-52，与需求同量级，没有工程余量。
（若将来重建了 base `e` 的高位系数表，这条路会重新打开——那是 kneser 库那边的事。）

**(b) 专门的 Beurling 估计：必做，但目标极软。**
Carleson 的两个常数是**一般 CZ 算子在 doubling 度量空间上**的（维数参数 a=4），
`C10_1_6` 自己的 docstring 就写着 "It is not tight and can be improved"。
平面上 Beurling 核的真实 `L⁴` 范数 ≤ 3（Nazarov–Volberg 给 6，
Bañuelos–Janakiraman 给 ≈4.7，猜想的锐值 `p−1 = 3`）。

**用现有证书（ε = 3.27e-38）只需 `C < 3.06e32`，而真值是 3。**
也就是说，一个比最优解糟糕 **32 个数量级**的粗糙论证就够用。
#7 的任务因此应当重述为：

> 给平面 Beurling 变换在 `L⁴` 上做一个**自足的、常数显式的**有界性证明，
> 常数只要低于 `10³²` 即可——不必接近 `3`，不必复用 Carleson 的一般机器。

### 8.6 附带确认

- 基线可复现：galic 上重跑 `certify_theta_qc_overlap.py` 得到与归档证书**逐位相同**的
  `3.26547217545012e-38` / `2.3569244175322955e-38`。
- galic 主机 python 有 `flint 0.9.0`；跑这套需要
  `PYTHONPATH=/data/kneser-verify/src`，且 `docs/` 下需补齐
  `theta_ball` / `theta_certify` / `theta_regular` / `theta_branch` /
  `certify_theta_continuous` / `check_theta_certificate`（探查时已从本机同步过去）。

## 9. #7 的可行路线（2026-09-17，接 §8）

**#7 不再是门。** §8 说"必须做专门的 Beurling 估计"，这仍然对，
但**所需的那条估计 RiemannDynamics 已经证了**，只是在往上游接 Carleson 接口时被放大丢掉了。

### 9.1 被丢掉的那个常数

`RiemannDynamics/Analysis/SingularIntegral/Beurling/L2Core.lean`：

```lean
lemma eLpNorm_czOperator_beurling {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : BoundedFiniteSupport f volume) :
    eLpNorm (czOperator beurlingKernel r f) 2 volume
      ≤ (2 : ℝ≥0∞) ^ 9 * eLpNorm f 2 volume
```

**截断 Beurling 算子的 `L²` 界是 `2⁹ = 512`，一致于 `r`**，
走的是 Plancherel（截断核的 Fourier 符号一致有界）。其 docstring 自陈
"The constant `2⁹` is far from sharp; only finiteness and uniformity in `r` are used downstream."

然后它被逐级放大：

| 层 | 常数 | 放大原因 |
|---|---|---|
| `eLpNorm_czOperator_beurling` | **2⁹ = 512** | —— |
| `czOperator_beurling_strongType_L2` | `C_Ts 4 = 2⁶⁴` | 对齐 Carleson 的 `hT` 接口（代码里就一行注释 `-- 2⁹ ≤ C_Ts 4`） |
| `hasStrongType_czOperator_beurling_two` | `C10_1_6 4 = 2¹⁶⁶` | 经非切向极大算子扩展到整个 `L²` |
| 喂进插值的 `hweak₂` | `C10_1_6 4 = 2¹⁶⁶` | 同上 |

### 9.2 换掉 `hweak₂` 就够了

`C_realInterpolation` 在 `t = 1/2` 时取的是 **`√(C₀·C₁)`**，不是 `C₀`。所以：

| `C₁`（`L²` 输入） | `√(2¹⁴⁰·C₁)` | 除 π 加前因子后的 `C` | 对 `3.06e32` |
|---|---|---|---|
| `2¹⁶⁶`（现状） | `2¹⁵³` | **2.79e46** | ✗ 超 14 个数量级 |
| **`2⁹`** | `2⁷⁴·⁵` | **6.52e22** | ✅ **低 10 个数量级** |

弱 (1,1) 的 `C10_0_3 4 = 2¹⁴⁰` 不必动——开方后只有 `2⁷⁰ ≈ 1.2e21`。

⚠ 指数保持 `p = 4`、`p' = 4/3` 不变。虽然 `p' = 1.8` 能把常数压到 `3.0e7`，
但那要重做 #4/#5 的全部常数，而 `6.52e22` 已经低于预算 10 个数量级，**不值得动**。
L1 那 26 条定理不受影响。

### 9.3 #7 的实际任务（四步）

1. **把 `eLpNorm_czOperator_beurling` 从 `BoundedFiniteSupport` 扩到整个 `L²`**，
   得 `HasWeakType (czOperator beurlingKernel r) 2 2 volume volume (2^9)`。
   标准的稠密性 ＋ Fatou 论证；所需机器该文件里已有
   （`exists_contDiff_seq_tendsto_L2`、`Lp.eLpNorm_le_of_ae_tendsto`），
   正是 `eLpNorm_simpleNontangential_beurling_le_L2` 用的那套——
   只是不必绕非切向极大算子。
2. **重做 `eLpNorm_czOperator_beurling_Lp`**，把 `hweak₂` 的常数从 `C10_1_6 4` 换成 `2^9`。
   其余一字不动（`hweak₁`、`hA`、`hsub`、`exists_hasStrongType_real_interpolation` 全部照抄）。
3. **沿他们现成的对偶 ＋ Fatou 链推到 `p > 2`**（`eLpNorm_beurling_Lp_le_high`），
   但把结论写成**暴露常数**的形式而不是 `∃ C`。
4. **算出并验证**
   `C = (1/π)·C_realInterpolation 1 2 1 2 (4/3) (2^140) (2^9) 1 (1/2) ≈ 6.52e22 < 3.06e32`。

**全程没有新数学**——是"把已有引理按不同常数重新接线"。

### 9.4 唯一的实际障碍：工具链

这四步都发生在 **RiemannDynamics 的代码里**（Lean v4.33.0，下游于 mathlib v4.33.0 + RMT4 + Carleson），
而本项目 `formal/` 在 **v4.32.0**。两条路：

- **(i) 上游**：把改动作为 PR 提给 RiemannDynamics，请他们把常数暴露出来。
  最干净，但受制于对方的节奏（注意他们连 mathlib 上游都还在等）。
- **(ii) 自建**：把所需的 Beurling 链条移植进本项目。
  代价是要一并引入 Carleson（`C10_0_3`、`C_realInterpolation`、
  `exists_hasStrongType_real_interpolation`）——这是个大依赖。

这个选择需要先定，再动手。


## 10. #8 `BeurlingTransfer` 的拆分（2026-09-17）

#8 是**唯一剩下的门**，也是整个计划里最长的一段。它不是一次能做完的，拆成五块：

| 子块 | 内容 | 状态 |
|---|---|---|
| **#8a** `KernelTailBound` | 被略去的核尾部是 `O(1/N)`——§2 那句"核的远端绝对积分为 `O(1/(εM))`"的定量形式 | ✅ **已证**（4 条定理） |
| **#8b** `TruncatedRepetition` | 把 1-周期 `v` 的水平重复截到长度 `2M`；截断函数与 `v` 的关系、其平面 `L⁴` 范数 | ✅ **已证**（8 条定理） |
| **#8c** `InnerStripComparison` | 在距两端 `≥ εM` 的内部条带上，`B(截断)` 与 `B_per v` 之差被尾部界控制 | ✅ **已证**（3 条定理）；⚠ **修正了 #8a 的形式** |
| **#8d** `TransferLimits` | 三重极限 | 🟡 **极限骨架已证**（6 条）；算子层面待做 |
| **#8e** `DensityExtension` | 用 #1 的稠密性把 `B_per` 从光滑紧支撑周期函数延拓到整个圆柱 `L⁴` | 🟡 **稠密性输入已备**（`exists_periodic_smooth_approx_restrict`）；**延拓本身依赖 #8d** |

### #8a 已完成

`Kneser/KernelTailBound.lean`，**4 条定理**，
`audit_modules.py --name kernel-tail-bound` 通过，全项目 **48035 job**。

- `inv_sq_sub_le_of_far`：`|x| ≤ R`、`2R ≤ N < m` ⟹ `1/(x−m)² ≤ 4·(m²)⁻¹`
  （靠 `|x−m| ≥ |m|−R ≥ |m|/2`）
- **`tail_sum_right_le`**：`∑_{m ∈ Ioo N K} 1/(x−m)² ≤ 8/(N+1)`，**与截断位置 `K` 无关**
  ——这个"与 K 无关"正是 §2 要的"一致趋于零"
- `tail_sum_left_le`（由 `x ↦ −x` 对称）、`tail_sum_two_sided_le`（合计 `≤ 16/(N+1)`）

地基是 mathlib 的 `sum_Ioo_inv_sq_le (k n) : ∑ i ∈ Ioo k n, (i²)⁻¹ ≤ 2/(k+1)`。

⚠ 踩的坑：结论里写 `8 / (N + 1)` 时 `N : ℕ` 会把整个式子推成 `HDiv ℝ ℝ ℕ`——
**必须写 `8 / ((N : ℝ) + 1)`**；`linarith` 不认 `8/(N+1) + 8/(N+1) = 16/(N+1)`
（变量分母非线性），要先 `have ... := by ring` 把它喂进去。

### 现实判断

#8b/#8c 是常规工作量。**#8d 是真正的长活**——三重嵌套极限是形式化里最容易失控的一类，
纸面证明必须先逐步拆细再动手。#8e 还卡着 #1 的稠密性。
所以 #8 的关键路径是 **#1 稠密性 → #8b → #8c → #8d → #8e**。


## 11. #1 稠密性的进展与剩余（2026-09-17）

### 已做：完整基本域（`Kneser/CylinderDomain.lean`）

`CylinderLp.lean` 处理的是**有限高度**条带 `fundamentalStrip Y`（承载 μ 的支撑用）。
但圆柱 `L⁴` 住在**无限高**的基本域上，故另立

    cylinderDomain = {w : ℂ | Re w ∈ (−1/2, 1/2]}。

已证（**11 条定理**，含在 8 模块 58 条的总审计里）：

- `cylinderTranslate_disjoint` ＋ **`iUnion_cylinderTranslate`：整数平移铺满整个 ℂ**
  （不再只是 `|Im| ≤ Y` 的条带）
- `lintegral_cylinderTranslate_of_periodic`：1-周期函数在每个平移基本域上积分相同
- `cylinderTrunc n = cylinderDomain ∩ {|Im| ≤ n}`，单调、并起来是 `cylinderDomain`
- **`iSup_lintegral_cylinderTrunc`：截断积分单调上升到全积分**
  ——**这是稠密性论证的第一步**（高度截断）

### 剩余两步，以及其中真正的难点

1. **平面上的光滑逼近**：mathlib 有
   `MeasureTheory.Lp.dense_hasCompactSupport_contDiff (hp : p ≠ ⊤)`，
   给的是**全平面** `L^p` 中光滑紧支撑函数的稠密性。常规。

2. ⚠ **周期化**：把逼近函数按整数平移求和 `G = ∑_n g(· + n)`。
   **这一步是唯一需要动脑的地方**：若 `g` 的支撑横跨 `m` 个周期，
   周期化会把 `L⁴` 误差按平移**逐个累加**（`ℓ¹` 而非 `ℓ⁴`），
   即 `‖G − f‖_{L⁴(D)} ≤ ∑_n ‖g − f̃‖_{L⁴(D−n)}`，而右端**不被** `‖g − f̃‖_{L⁴(ℂ)}` 控制。
   正确做法是**先把 `f` 用光滑截断限制在一个周期宽度内**，再逼近，
   使周期化只涉及常数个（≤ 3）平移，于是误差只放大常数倍，取 `ε/3` 即可。

### 进展（同日稍后）：第 1 步已证，陷阱已形式化

`Kneser/CylinderTruncDense.lean`（**5 条定理**）：

- `lintegral_cylinderTrunc_add_compl`、`monotone_lintegral_cylinderTrunc`、
  `tendsto_lintegral_cylinderTrunc`
- ⭐ **`tendsto_lintegral_cylinderTrunc_compl`——第 1 步完成**：
  基本域上积分有限时，被截掉的部分趋于零。
  `L⁴` 的用法是取 `f w = ‖g w‖ₑ^4`，结论即"截断函数在圆柱 `L⁴` 中稠密"。
- ⭐ **`periodization_translate_eq_zero`——陷阱的解药已形式化**：
  `h` 支撑在 `|Re| ≤ 3/4`（一个周期宽度内）⟹ 对基本域中任一点，
  `|m| ≥ 2` 的平移全部为零。于是周期化逐点只有 ≤ 3 项，误差只放大常数倍。

### 装配进展（同日再稍后）：陷阱的解药已完整

模块增至 **8 条定理**，新增三条把"周期化只放大常数倍"走完：

- **`tsum_periodization_eq`**：`h` 支撑在一个周期宽度内 ⟹ 基本域上
  `∑'_{m∈ℤ} h(w+m) = h(w−1) + h w + h(w+1)`——**无穷和塌成三项有限和**
- **`norm_tsum_periodization_le`**：逐点 `‖∑'‖ ≤ ‖h(w−1)‖ + ‖h w‖ + ‖h(w+1)‖`
- **`lintegral_translate_cylinderDomain_le`**：`∫_D h(·+c) ≤ ∫_ℂ h`
  （平移测度保持 ＋ `restrict_le_self`）

三条合起来即 `‖周期化‖_{L⁴(D)} ≤ 3‖h‖_{L⁴(ℂ)}`。**§11 的陷阱至此完全解决。**

### 仍欠的：纯粹是光滑性机器

第 2 步的 mathlib 接口已定位：
`MeasureTheory.MemLp.exist_eLpNorm_sub_le (hp : p ≠ ⊤) (hp₂ : 1 ≤ p) (hf : MemLp f p μ) (hε : 0 < ε)`
`: ∃ g, HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧ eLpNorm (f − g) p μ ≤ ENNReal.ofReal ε`
（ε 形式，正合用）。

剩下的全是**光滑性机器**，不含新数学：

1. ~~光滑截断函数 χ 的构造（`ContDiffBump`）~~ ✅ **已完成，见下**；
2. 周期化和式 `G = ∑_m g'(·+m)` 的 `ContDiff`（逐点有限和，由 `tsum_periodization_eq` 保证）；
3. ε/3 的最终合成。

### 光滑截断已装完（`Kneser/CylinderCutoff.lean`，9 条定理）

    cutoff w = reBump w.re，  reBump : ContDiffBump (0:ℝ)，rIn = 1/2、rOut = 3/4。

- `cutoff_nonneg` / `cutoff_le_one`：取值于 `[0,1]`
- `cutoff_eq_one`：`|Re| ≤ 1/2` 上恒为 `1`——**恰好覆盖基本域**
- `cutoff_eq_zero`：`|Re| ≥ 3/4` 上恒为 `0`
- `cutoff_contDiff`：`ContDiff ℝ ∞ cutoff`（bump 光滑 ∘ `Complex.reCLM`）
- ⭐ **`cutoff_mul_eq_self`**：`cutoff · f = f`，只要 `f` 支撑在基本域内
  ——**截断不改变要逼近的函数**
- ⭐ **`cutoff_mul_eq_zero_of_far` / `cutoff_mul_support`**：`cutoff · g` 支撑在一个周期宽度内
  ——**截断后的逼近函数可以安全周期化**
- ⭐ **`tsum_periodization_cutoff`**：`∑'_m cutoff(w+m)·g(w+m)` 在基本域上**塌成三项**

**至此 §11 第 3 步的工具全部齐备**：`cutoff_mul_eq_self` 保证截断不损失，
`tsum_periodization_cutoff` 保证周期化只放大常数倍，两头都接上了。

⚠ 踩的坑：`ContDiffBump` 的函数化要 `HasContDiffBump` 实例，**`BumpFunction/Basic.lean`
不提供**，得 import `BumpFunction/FiniteDimension.lean` ＋ `InnerProduct.lean`；
`ContDiffBump.nonneg` 等的 `f` 是显式参数，要写 `reBump.nonneg` 而非 `ContDiffBump.nonneg`；
`ContDiffBump.contDiff` 的 `n : ℕ∞`，而 `ContDiff ℝ ∞` 的 `∞ : ℕ∞ω`，
要写 `(reBump.contDiff (n := (⊤ : ℕ∞)))` 才对得上。

## ✅ **#1 的稠密性已完成**（2026-09-17）

`Kneser/PeriodizationSmooth.lean`（4 条）＋ `Kneser/CylinderDense.lean`（3 条），
连同前面的 `CylinderLp` / `CylinderDomain` / `CylinderTruncDense` / `CylinderCutoff`，
全项目 **82 条定理 / 12 模块**一次性审计通过，**48040 job**。

**主结论**：

```lean
theorem exists_periodic_smooth_approx {f : ℂ → ℂ} (hf : MemLp f 4 volume)
    (hsupp : ∀ w, w ∉ cylinderDomain → f w = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℂ → ℂ, ContDiff ℝ ∞ G ∧ (∀ w, G (w + 1) = G w) ∧
      eLpNorm (fun w => f w - G w) 4 (volume.restrict cylinderDomain)
        ≤ ENNReal.ofReal ε
```

即 theta-periodic-beltrami.md §2 末尾"用光滑紧支撑函数在圆柱 `L⁴` 中的稠密性
定义并延拓 `B_per`"所需的那条。

**ε/3 链**：`‖f − G‖_{L⁴(D)} ≤ 3‖f − cutoff·g‖_{L⁴(ℂ)} ≤ 3‖f − g‖_{L⁴(ℂ)} ≤ 3·(ε/3)`。
第一个 `3` 来自周期化的三项（陷阱的解药），第二个不等号来自 `|cutoff| ≤ 1` 且 `cutoff·f = f`。

补齐的两块：
- `contDiff_periodization`：周期化光滑。关键是**局部有限**——在 `w₀` 的 `1/4` 邻域内
  只有 `|m − ⌈−Re w₀⌉| ≤ 2` 的项非零，故局部等于有限和
  （`periodization_eventuallyEq_finset` ＋ `ContDiffAt.congr_of_eventuallyEq`）。
- `periodization_periodic`：`ℤ` 上求和的平移不变性（`Equiv.addRight (1:ℤ)).tsum_eq`）。
- `eLpNorm_translate_cylinderDomain_le` / `eLpNorm_three_term_le`：`L⁴` 侧的三倍界。

⚠ 踩的坑：`MemLp` 展开成 `And`，**点记号 `hf.exist_eLpNorm_sub_le` 失效**，
要写全限定名 `MeasureTheory.MemLp.exist_eLpNorm_sub_le ... hf ...`；
该引理所在的 `Mathlib/Analysis/Normed/Lp/SmoothApprox.lean` **需单独 import**；
`set ... with h` 之后用 `simp only [h]` 展开容易卡在 beta 归约，改用 `show` 强制定义展开。

**#8e `DensityExtension` 的阻塞已解除。**


## 12. #8e 的现状与依赖（2026-09-17）

⚠ **#8e 依赖 #8d，不是依赖 #1。** #1 的稠密性已完成，但 #8e 要延拓的是 `B_per`，
而 `B_per` 的有界性 `‖B_per‖_{L⁴} ≤ C` **正是 #8d 的结论**。
没有 #8d，就没有有界线性映射可延拓——#8e 的主体无法开始。

### 已备好的那一半：稠密性输入

`CylinderDense.exists_periodic_smooth_approx_restrict`（**无支撑侧条件**）：

```lean
theorem exists_periodic_smooth_approx_restrict {f : ℂ → ℂ}
    (hf : MemLp f 4 (volume.restrict cylinderDomain)) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℂ → ℂ, ContDiff ℝ ∞ G ∧ (∀ w, G (w + 1) = G w) ∧
      eLpNorm (fun w => f w - G w) 4 (volume.restrict cylinderDomain)
        ≤ ENNReal.ofReal ε
```

这就是延拓定理要吃的"光滑 1-周期类在圆柱 `L⁴` 中稠密"，形式上已经干净：
任意 `L⁴(D)` 函数，不带支撑假设。桥接靠 mathlib 的
`memLp_indicator_iff_restrict` 与 `eLpNorm_indicator_eq_eLpNorm_restrict`。

### 仍欠

`B_per` 的定义与有界性（#8b→#8c→#8d），以及最后的有界线性延拓
（`Lp` 空间上的标准论证，届时是常规工作）。

**关键路径未变：#8b → #8c → #8d → #8e。**


## 13. #8b 已完成（2026-09-17）

`Kneser/TruncatedRepetition.lean`，**8 条定理**，全项目 **91 条 / 13 模块**审计通过，48041 job。

**核心是"周期数"的精确记账**——§2 里"除以内部周期数"所除的正是这个数：

```lean
theorem lintegral_truncDomain_of_periodic {f : ℂ → ℝ≥0∞}
    (hper : ∀ w : ℂ, f (w + 1) = f w) (M : ℕ) :
    ∫⁻ w in truncDomain M, f w = (2 * M : ℕ) * ∫⁻ w in cylinderDomain, f w
```

其中 `truncDomain M = ⋃_{n=−M}^{M−1} (基本域 + n)`。证法：不交并的可加性
（`lintegral_biUnion_finset`）＋ `lintegral_cylinderTranslate_of_periodic`
（周期函数在每个平移基本域上积分相同）＋ `Int.card_Ico` 数出 `2M` 项。

配套给出截断重复 `truncRepeat v M = (truncDomain M).indicator v` 及其平面 `L⁴` 预算：

```lean
theorem lintegral_truncRepeat_rpow {v : ℂ → ℂ} (hper : ∀ w, v (w + 1) = v w) (M : ℕ) :
    ∫⁻ w, ENNReal.ofReal ‖truncRepeat v M w‖ ^ (4 : ℝ)
      = (2 * M : ℕ) * ∫⁻ w in cylinderDomain, ENNReal.ofReal ‖v w‖ ^ (4 : ℝ)
```

**这就是 §2 把平面界搬到圆柱时两边都出现的那个 `2M`**：平面 `L⁴` 界给
`‖B v_M‖₄ ≤ C‖v_M‖₄`，两边各带一个 `(2M)^{1/4}`，相消后剩下圆柱上的界。

**下一格 #8c `InnerStripComparison`**：在距两端 `≥ εM` 的内部条带上，
`B(截断)` 与 `B_per v` 之差被 **#8a 的尾部界**控制。#8a 与 #8b 的产物在那里汇合。


## 14. #8c 已完成，并修正了 #8a（2026-09-17）

`Kneser/InnerStripComparison.lean`，**3 条定理**，全项目 **94 条 / 14 模块**审计通过，48042 job。

### ⚠ 先说修正：#8a 的假设对实际几何太强

`KernelTailBound` 的假设是 **`2R ≤ N`**。代入 §2 的实际几何——
内部条带 `|Re| ≤ (1−ε)M`、截断在 `N = M`——需要

    2(1−ε)M ≤ M  ⟺  ε ≥ 1/2。

**而 §2 要的正是 `ε → 0`。** 所以 #8a 那条形式**用不到主论证里**，
它只是 `ε = 1/2` 的特例。

### 正确的形式

假设改成 **`R ≤ (1 − ε)·N`**：此时 `m > N` 蕴含

    |x − m| ≥ m − R ≥ m − (1−ε)N ≥ m − (1−ε)m = εm，

故核被 `(1/ε²)(1/m²)` 控制，尾部和为 `2/(ε²(N+1))`。

```lean
theorem kernel_tail_right_le {u : ℂ} {ε : ℝ} {N K : ℕ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hu : |u.re| ≤ (1 - ε) * N) :
    ∑ m ∈ Finset.Ioo N K, ‖(1 : ℂ) / (u - (m : ℂ)) ^ 2‖
      ≤ 2 / (ε ^ 2 * ((N : ℝ) + 1))
```

**与截断位置 `K` 无关**——这就是 §2 的"遗漏核的作用**一致**趋于零"。
复核经 `‖ζ‖ ≥ |Re ζ|`（`Complex.abs_re_le_norm`）归约到实的情形。

⚠ 边界情形：`ε = 1` 时原本想写的严格不等号 `x − m < −εm` **不成立**
（此时 `R = 0`、`x = 0`，两边都是 `−m`），必须用 `≤`，再由 `εm > 0` 得 `x − m < 0`。

### 现状

**#8 只剩 #8d 与 #8e。** #8a/#8b/#8c 的产物已就位：
尾部界（`2/(ε²(N+1))`，与 K 无关）、周期数记账（`2M` 因子）、以及两者的几何衔接。
**#8d 的三重极限（`M → ∞` 得 `(1−ε)^{−1/4}`、`ε → 0`、单调收敛放开高度）是仅剩的长活**；
#8e 的稠密性输入已备好，主体依赖 #8d。


## 15. #8d：极限骨架已完成（2026-09-17）

`Kneser/TransferLimits.lean`，**6 条定理**，全项目 **100 条 / 15 模块**审计通过，48043 job。

§2 最后一段的三步记账，每步一条独立引理：

| §2 的话 | Lean 定理 |
|---|---|
| "**除以内部周期数**" | `le_of_period_count_cancel`（`c ≠ 0, ≠ ⊤` 时 `c·a ≤ c·b ⟹ a ≤ b`）＋ `period_count_ne_zero` / `_ne_top` |
| "得到多一个 `(1−ε)^{−1/4}` 因子……再令 **`ε → 0`**" | `le_of_forall_one_sub_mul_le`（`∀ ε ∈ (0,1), (1−ε)·a ≤ K ⟹ a ≤ K`） |
| "用**单调收敛放开输出高度**" | `lintegral_cylinderDomain_le_of_forall_trunc`（靠 #1 的 `iSup_lintegral_cylinderTrunc`） |

合成：

```lean
theorem transfer_skeleton {f : ℂ → ℝ≥0∞} {K : ℝ≥0∞}
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ n : ℕ,
      ENNReal.ofReal (1 - ε) * ∫⁻ w in cylinderTrunc n, f w ≤ K) :
    ∫⁻ w in cylinderDomain, f w ≤ K
```

**带 `(1−ε)` 折扣的截断界 ⟹ 圆柱上的干净界。** 两重极限一次打完。

### ⚠ 仍欠：算子层面

骨架的假设要由"平面界 ＋ #8c 的尾部 ＋ #8b 的周期数"喂出来，而这一步**需要
`B_per` 与平面 `B` 的定义**——目前项目里都还没有。而 `B_per` 的可用性又依赖
**#7 的显式常数**（施工计划 §8/§9，正等 Zulip 回复）。

所以 **#8 剩余的真正瓶颈不是极限论证，而是算子的定义与 #7**。
极限记账这块——我一开始判定为"#8 里最长的活"——现在已经不是障碍了。


## 16. 算子已定义（2026-09-17）

`Kneser/BeurlingOperators.lean`，**4 条定理**，全项目 **104 条 / 16 模块**审计通过，48044 job。

此前十五个模块做的全是核估计、几何与测度记账，**项目里一个算子都没有**。本模块补上。

### 两个核

```lean
noncomputable def planeBeurlingKernel (u : ℂ) : ℂ := (-(1 : ℂ) / (π : ℂ)) * (1 / u ^ 2)
noncomputable def perBeurlingKernel  (u : ℂ) : ℂ := -(π : ℂ) / (Complex.sin ((π : ℂ) * u)) ^ 2
```

### ⭐ #6 在这里兑现：周期化核有闭式

```lean
theorem tsum_planeBeurlingKernel {u : ℂ} (hu : u ∈ ℍₒ) :
    ∑' n : ℤ, planeBeurlingKernel (u + (n : ℂ)) = perBeurlingKernel u
```

即 `∑_n −1/(π(u+n)²) = −π/sin²(πu)`。**周期化不必带着无穷和走**——
`B_per` 的核就是一个初等闭式。这是 #6 那条 cot 恒等式的直接付现。

### 两个截断算子

奇异积分取 `czOperator` 式截断（挖掉 `ball z r`），每个 `r > 0` 都是普通积分，
主值极限 `r → 0⁺` 留到用时再取——与 RiemannDynamics 的做法一致：

```lean
noncomputable def planeBeurlingTrunc (r : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ w in (Metric.ball z r)ᶜ, planeBeurlingKernel (z - w) * f w

noncomputable def perBeurlingTrunc (r : ℝ) (v : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ w in cylinderDomain \ Metric.ball z r, perBeurlingKernel (z - w) * v w
```

注意 `perBeurlingTrunc` 的积分**只在一个基本域上跑**——周期性已经吸进核里了。

附 `planeBeurlingKernel_neg`（核是偶的）、`perBeurlingKernel_periodic`（周期化核 1-周期，
由 `Complex.sin_add_pi` 得）、`norm_planeBeurlingKernel`（`= 1/(π‖u‖²)`）。

### 剩余

算子已在，#8a/#8b/#8c/#8d 的零件也都在。**把它们接起来所缺的只剩 #7 的显式常数**
——没有平面 `L⁴` 界，转移论证无从起步。#7 的路线明确（施工计划 §9），
但改动在 RiemannDynamics 代码里，**正等 Zulip 回复**。
