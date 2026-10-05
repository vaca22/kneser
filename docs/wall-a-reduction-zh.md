# 墙 A 的归约：负模方程组不是障碍

2026-09-16。本文记录一轮形式化工作的结论：几何路线（[§2–§8](theta-canonical-identity.md)）
此前被记为唯一实质障碍的"墙 A"——`Kneser.ThetaExactGluing`，θ 算子边界数据的**全部负
Fourier 模为零**——**不是一个需要求解的无限方程组**，也**不是构造 §1 表示式的必要输入**。

三条归约、一条合成，以及把结构假设 `hlink` 消除的那一步，全部在 Lean 4 内证成，并通过公理审计（无 `sorry`、无自定义公理、无 `native_decide`，
只用 `propext` / `Classical.choice` / `Quot.sound`）：

> **74 条定理、14 个模块，全部通过。**
> 审计记录：`formal/audit/wall-a-reduction-result.json`。

这些归约**没有**证明 Kneser 身份定理，**没有**构造出所需的解析对象。它们改变的是障碍的
**形状**：从"一族无穷多个积分方程"变成"一条关于单个函数的解析性陈述"。第 6 节逐条写明
本文**不**主张什么。

---

## 0. 与 mathlib 已有结果的关系（**先读这一节**）

本文第 3 节与第 7.2 节的内容，**mathlib 已经有了**，只是坐标系不同。必须先讲清楚，
否则容易把标准结果当成新东西：

| 本文 | mathlib 已有 |
|---|---|
| `theta_eq_reconstruct`（上半平面周期全纯有界 ⟹ 等于自己的非负重建） | `UpperHalfPlane.hasSum_qExpansion`（`Mathlib/NumberTheory/ModularForms/QExpansion.lean`）——**同一条定理**，即模形式的 q-展开 |
| `boundaryCoefficient_height_shift`（正模的高度缩放） | `UpperHalfPlane.qExpansion_coeff_eq_intervalIntegral` 对**任意**高度 `t > 0` 成立，缩放已含在 `1/𝕢ⁿ` 因子里 |
| `periodic_band_negative_fourier_zero`（半带上负模全零） | 是 `hasSum_qExpansion` 的直接推论——q-展开只含**非负**幂 |
| q-圆盘下降的基础设施 | `Mathlib/Analysis/Complex/Periodic.lean`：`qParam`、`cuspFunction`、`eq_cuspFunction`、`differentiableAt_cuspFunction_zero` |

`formal/Kneser/QExpansionBridge.lean` 把本文的陈述**从 mathlib 的陈述推导出来**，验证了这种等价：
取 `f τ := h(τ + c·I)`、周期 1、`t := δ − c`，则系数差一个 `e^{2πnt}`、相位差一个 `e^{−2πnt}`，
**逐项抵消**。桥接版 297 行 vs 手工版 424 行，而且**假设少一条**（mathlib 的 `HasSum` 自带收敛性，
`hsum` 根本不用提）。主链（`RepresentationComplete`）现已改走桥接，手工版不再是任何东西的依赖。

**没有重复的部分**：mathlib **没有** Hardy 空间，也没有"负模全零 ⟺ 圆盘全纯延拓"这条刻画，
所以第 2 节与 2.1 节（`DiscBoundaryModes` + `DiscBoundaryConverse`）相对 mathlib 是新的；
第 4、5 节与全部装配是项目专有的。

**教训**：动手前先搜库。本轮在半带那一半付出的证明工作量，本可以省掉一个数量级。

---

## 1. 原来的记法

`formal/Kneser/ThetaClosure.lean` 末尾把障碍写成可检查的命题：

```lean
noncomputable def thetaBoundaryNegativeMode (a : WienerCoeffs) (n : ℕ) : ℂ :=
  ∫ t in (0:ℝ)..1, thetaCircleBoundary certifiedAbel certifiedRegular (11/20) (1/10) a t
    * Complex.exp (((2*Real.pi*((n:ℝ)+1)*t:ℝ):ℂ)*Complex.I)

def ThetaExactGluing (a : WienerCoeffs) : Prop := ∀ n : ℕ, thetaBoundaryNegativeMode a n = 0
```

理由是：θ 算子的 Cauchy 投影只保留非负 Fourier 模，所以它的固定点只在"差一堆负模"的意义下
重现自己的边界数据；要让函数方程 `F(z+1)=exp F(z)` 真正成立，负模必须全为零。
该文件的注释把它称为"和 [负模判据](theta-negative-modes.md) 留下的同一个无限方程组"。

`formal/GEOMETRIC-ROUTE-STATUS.md` 据此把墙 A 记为
"`UpperRepresentation` 没有实例，追到底是公开未解决的 `ThetaExactGluing`"。

---

## 2. 归约一：负模全零 ⟸ 圆盘全纯延拓

**这不是一族方程，而是一个经典二分法的一半。**
`thetaCircleBoundary` 是单位圆上的边界数据，以 `z = exp(2πit)` 参数化。若它是某个在**闭单位
圆盘上连续、开圆盘内全纯**的函数 `G` 的边界值，则全部负模一次性为零——这只是柯西定理作用在
`z ↦ G(z)·zⁿ` 上。

模块 `formal/Kneser/DiscBoundaryModes.lean`（只依赖 mathlib，与 θ 无关）：

```lean
theorem circle_boundary_negative_mode_zero
    {G : ℂ → ℂ} {B : ℝ → ℂ} {n : ℕ}
    (hc : ContinuousOn G (Metric.closedBall 0 1))
    (hd : ∀ z ∈ Metric.ball (0:ℂ) 1, DifferentiableAt ℂ G z)
    (hB : ∀ t : ℝ, B t = G (Complex.exp (((2*Real.pi*t:ℝ):ℂ)*Complex.I))) :
    (∫ t in (0:ℝ)..1, B t * Complex.exp (((2*Real.pi*((n:ℝ)+1)*t:ℝ):ℂ)*Complex.I)) = 0
```

证明路线：mathlib 的 `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable`
给出 `∮_{|z|=1} G(z)zⁿ dz = 0`，再把 `circleIntegral` 展开成角变量积分、作 `θ = 2πt` 换元。

模块 `formal/Kneser/ThetaGluingBridge.lean` 把它接到项目的命题上，并给这条解析假设起名：

```lean
def ThetaDiscExtension (a : WienerCoeffs) : Prop :=
  ∃ G : ℂ → ℂ, ContinuousOn G (Metric.closedBall 0 1) ∧
    (∀ z ∈ Metric.ball (0:ℂ) 1, DifferentiableAt ℂ G z) ∧
    ∀ t : ℝ, thetaCircleBoundary certifiedAbel certifiedRegular (11/20) (1/10) a t
      = G (Complex.exp (((2*Real.pi*t:ℝ):ℂ)*Complex.I))

theorem thetaExactGluing_of_discExtension {a : WienerCoeffs}
    (h : ThetaDiscExtension a) : ThetaExactGluing a
```

**结论**：整个无限族一次性被一条假设打发。障碍从"逐模验证"变成"一个圆盘上的一个函数"。

### 2.1 这条归约是**充要**的

只证充分性还留着一个口子："会不会有更弱的假设也够？"——不会。模块
`formal/Kneser/DiscBoundaryConverse.lean` 证了逆方向，于是得到**精确刻画**：

```lean
theorem disc_extension_iff_negative_modes_zero
    {B : ℝ → ℂ} (hcont : Continuous B) (hper : Function.Periodic B 1)
    (hsum : Summable (fun n : ℕ => ‖boundaryCoefficient B n‖)) :
    (∃ G : ℂ → ℂ, ContinuousOn G (Metric.closedBall 0 1) ∧
        (∀ z ∈ Metric.ball (0:ℂ) 1, DifferentiableAt ℂ G z) ∧
        ∀ t : ℝ, B t = G (Complex.exp (((2*Real.pi*t:ℝ):ℂ)*Complex.I)))
      ↔ ∀ n : ℕ, (∫ t in (0:ℝ)..1,
          B t * Complex.exp (((2*Real.pi*((n:ℝ)+1)*t:ℝ):ℂ)*Complex.I)) = 0
```

逆方向的见证是显式的：`G z := ∑' n, c n · zⁿ`（`c n = boundaryCoefficient B n`），
由 `hsum` 得闭圆盘上一致收敛故连续、开圆盘内全纯；边界值等于 `B` 这一步走完了
mathlib 的 `has_pointwise_sum_fourier_series_of_summable`（**没有**退化成"把 Fourier
反演当假设"），负模为零正好消掉级数的负半支。

三条正则性假设都是必要的，不是为了编译凑上去的：`hper`（1-周期）因为结论右边关于 `t`
本来就 1-周期，`B` 不周期则等式在 `ℝ` 上不可能成立；`hsum` 是 Fourier 反演所需；
`hcont` 是把 `B` 提升到 `AddCircle 1` 所需。

**所以"墙 A"就是圆盘全纯延拓，一分不多一分不少。**

---

## 3. 归约二：周期半带上的负模自动为零

采样水平线上的版本同样是一条标准事实，而且正是
[§8](theta-qc-global-existence.md) 最后那段论证的内容。

模块 `formal/Kneser/PeriodicBandFourier.lean`（只依赖 mathlib）：

```lean
theorem periodic_band_negative_fourier_zero
    {h : ℂ → ℂ} {c δ M : ℝ} {n : ℕ}
    (hcδ : c < δ) (hn : 1 ≤ n)
    (hd : DifferentiableOn ℂ h {z : ℂ | c < z.im})
    (hper : ∀ z : ℂ, c < z.im → h (z+1) = h z)
    (hb : ∀ z : ℂ, δ ≤ z.im → ‖h z‖ ≤ M) :
    (∫ t in (0:ℝ)..1, h (↑t+↑δ*Complex.I) *
        Complex.exp (((2*Real.pi*(n:ℝ)*t:ℝ):ℂ)*Complex.I)) = 0
```

即：**上半带上全纯、1-周期、有界的函数，全部负 Fourier 模为零。** 证明三步，全部在 Lean 内：

1. 对 `f z = h z · exp(2πi n z)` 在矩形 `[0,1] × [δ,Y]` 上用 mathlib 的
   `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`；
2. 两条竖边逐点相消——`h(1+iy) = h(iy)`（周期性）且 `exp(2πin) = 1`（`n` 为整数）；
3. 上边的模 ≤ `M·exp(−2πnY)`，令 `Y → ∞`；底边的值与 `Y` 无关，故为零。
   最后约掉非零常数 `exp(−2πnδ)`。

不需要 Phragmén–Lindelöf，不需要 Fourier 级数收敛理论，只用矩形柯西定理。
`periodic_band_sample_negative_fourier_zero` 给出下游要用的"采样函数 `g : ℝ → ℂ`"形式。

---

## 4. 归约三：§1 的表示式根本不需要 θ 算子

这一条改变的东西最多。

`formal/Kneser/MidSegment.lean` 把 §1 的表示式装成结构 `UpperRepresentation F`，
其实质字段是

```lean
repr : ∀ u : ℂ, 3/10 < u.im → F (chart u) = certifiedRegular (u + theta u)
```

状态图把"这个结构没有实例"追溯到 θ 算子固定点那条线，因而追到 `ThetaExactGluing`。
**这个追溯不是必然的。** 结构里没有任何字段要求 `theta` 来自 Fourier 固定点。对**任意**
chart，令

    theta u := A (F (chart u)) − u,                                    (★)

其中 `A` 是正则超函数 `S` 沿 `F ∘ chart` 的值的任一右逆，则

    S(u + theta u) = S(A(F(chart u))) = F(chart u),

`repr` **由构造成立**。模块 `formal/Kneser/RepresentationFromInverse.lean`：

```lean
theorem inverse_theta_repr {F A chart : ℂ → ℂ} {u : ℂ}
    (hinv : certifiedRegular (A (F (chart u))) = F (chart u)) :
    F (chart u) = certifiedRegular (u + inverseTheta F A chart u)

theorem nonempty_upperRepresentation_of_inverse ... : Nonempty (UpperRepresentation F)
```

于是 `UpperRepresentation` 剩下的全部内容是三条**定量**字段。而其中的导数界还能再消掉一条：

模块 `formal/Kneser/HalfPlaneDerivBound.lean` 用 Schwarz 引理形式的柯西估计
（mathlib 的 `Complex.norm_deriv_le_div_of_mapsTo_ball`）证明：

```lean
theorem norm_deriv_le_of_bounded_on_upperHalfPlane {θ : ℂ → ℂ} {base : ℂ} {c ρ bound : ℝ}
    (hρ : 0 < ρ) (hd : DifferentiableOn ℂ θ {z : ℂ | c < z.im})
    (hclose : ∀ z : ℂ, c < z.im → ‖θ z - base‖ ≤ bound)
    {u : ℂ} (hu : c+ρ ≤ u.im) :
    ‖deriv θ u‖ ≤ 2*bound/ρ
```

在 `Im z > 0.08` 上全纯且与均值相差不超过 `bound`，则在 `Im u > 0.3` 上
`‖θ′‖ ≤ 2·bound/0.22`，只要 `bound < 0.11` 就自动 `< 1`。合起来：

```lean
theorem nonempty_upperRepresentation_of_bounded_inverse ... : Nonempty (UpperRepresentation F)
```

**§1 的表示式因此只需要两条定量输入**（半平面上的解析性 + 一条一致界），
加上逆支恒等式，与负模方程组无关。

---

## 5. 合成：逆支修正项的负模自动为零

(★) 定义的修正项有一条白给的性质：**它自动 1-周期**。因为

    theta(u+1) = A(F(chart(u+1))) − (u+1) = A(F(chart u)) + 1 − u − 1 = theta(u),

只要逆支沿函数方程平移一格（`chart` 与单位平移交换、`F(w+1)=exp F(w)`、`A` 跨 `exp` 加一）。
对比之下，θ 算子那条线里周期性是靠"只求和非负 Fourier 模"**硬造**出来的。

把归约二接上去，模块 `formal/Kneser/InverseThetaModes.lean`：

```lean
theorem inverse_theta_negative_fourier_zero {F A chart : ℂ → ℂ} {c δ M : ℝ} {n : ℕ}
    (hcδ : c < δ) (hn : 1 ≤ n)
    (hd : DifferentiableOn ℂ (inverseTheta F A chart) {z : ℂ | c < z.im})
    (hshift : ∀ z : ℂ, c < z.im → A (F (chart (z+1))) = A (F (chart z)) + 1)
    (hb : ∀ z : ℂ, δ ≤ z.im → ‖inverseTheta F A chart z‖ ≤ M) :
    (∫ t in (0:ℝ)..1, inverseTheta F A chart (↑t+↑δ*Complex.I) *
        Complex.exp (((2*Real.pi*(n:ℝ)*t:ℝ):ℂ)*Complex.I)) = 0
```

以及把两个结论收在同一组假设下的

```lean
theorem upper_representation_and_modes_of_inverse ... :
    Nonempty (UpperRepresentation F) ∧ ∀ n : ℕ, 1 ≤ n → (... = 0)
```

**这就是墙 A 归约的落点**：在**足以产生表示式的那组假设下，负模自动全为零**。
它不是一项额外义务，而是柯西定理的推论。

---

## 6. 本文**不**主张什么

必须写清楚，否则就是夸大：

1. **没有证明 Kneser 身份定理。** 最终身份仍未在 Lean 内闭合。
2. **没有构造 `ThetaDiscExtension` 的 `G`**，也没有构造 (★) 里的逆支 `A`。
   两者都仍是假设。归约改变的是障碍的形状，不是它的存在性。
3. **没有证明负模确实为零**——证明的是"在某某条件下为零"。条件仍待兑现。
4. **`UpperRepresentation` 本来就不是空结构**：取 `F = S`、`chart = id`、`theta = 0`
   即是平凡实例。第 4 节的内容不是"从无到有造出实例"，而是
   **`repr` 字段不含负模方程组的内容**——针对真正的 Kneser `F`，剩下的义务是定量估计。
5. 归约二**不是** §8 的全部，只是它最后那步。§8 前面的构造（周期 Beltrami / 可测黎曼映射）
   完全没有形式化，mathlib 里也没有这些定理。

---

## 7. 真正剩下的缺口

按现在的形状，欠的东西是下面三样，**没有一样是无限方程组**：

| 缺口 | 精确内容 | 现状 |
|---|---|---|
| `F` 本身的存在 | 整条链的起点：Re z > −2 上的解析实对称解 | [§3–§6](theta-qc-global-existence.md) 用周期 Beltrami 修正构造，**依赖可测黎曼映射定理（Ahlfors–Bers）**；mathlib 无此定理，故 Lean 内没有 `F` 的实例 |
| `θ_F` 的定量界 | **已压缩到终点**（见 §7.1）：只需采样线上一条**中心化 sup 界** `‖g t − b‖ ≤ 1/50` | 与已认证的 `\|θ_p − a₀\| < 0.02` 形状一致。仍需把它从**中心多项式**传到真正的 `θ_F`（`inverseTheta_close_of_lipschitz` 已备好骨架，代入 `L_A<2.343`、`‖F−p‖<2.878e-30`） |
| ~~`hlink`~~ | ~~逆支修正项等于它自己的非负重建~~ | **已消除**，见 §7.2 |
| `StripHighChartCover` | χ 把 u-条带的高处映满条带高处 | §7 仅剩的几何义务，见状态图 |

**一处需要澄清（本文早先版本写错过）**：解析性那一条**不是**缺口。§8 已经把 `θ_F` 延拓到
整个 `Im z > 0.08`：水平方向靠周期性（`R_A=(−0.51,0.51)+i(0.08,0.325)` 宽度 1.02 > 1，
整数平移即铺满水平带），上方靠 `W(z)=χ⁻¹(z)+θ_p(χ⁻¹(z))` 在 `Im z > 0.3+D` 上接住，
两者在重叠区由恒等定理相等。所以第一条定量输入（半平面解析性）在纸面上**已经有了**；
真正欠的是第二条，那个**带显式常数的一致界**。

### 7.1 这条定量缺口已被压到**一条线上的一个数**

"整个半平面上的一致界"听起来很强，但它**不需要被直接认证**。关键是：
修正项若是它自己在高度 `δ` 处采样的非负 Fourier 重建，则几何因子
`‖thetaPhase δ z‖ = exp(−2π(Im z − δ))` 随高度指数衰减，于是**一条线上的系数界自动传遍整个半平面**。

模块 `formal/Kneser/ReconstructionBounds.lean`：

```lean
theorem theta_reconstruct_close_of_height {g : ℝ → ℂ} {δ c M₁ Q : ℝ} {z : ℂ}
    (hδc : δ < c) (hQ : Real.exp (-2*Real.pi*(c-δ)) ≤ Q) (hQ1 : Q < 1)
    (hc : ∀ n : ℕ, ‖thetaFourierCoefficient g (n+1)‖ ≤ M₁) (hz : c ≤ z.im) :
    ‖thetaReconstruct g δ z - thetaFourierCoefficient g 0‖ ≤ M₁*Q/(1-Q)
```

注意这里的 `M₁` 只约束**非常数**系数——丢掉常数项白赚一个 `‖q‖` 因子，正是问题的正确形状
（`theta_close` 要的本来就是"与自身均值的偏差"）。

模块 `formal/Kneser/ReconstructionRepresentation.lean` 把它接到底，**常数全部是有理数、`norm_num` 可查**：

取采样高度 `δ = 1/10`、判据高度 `c = 1/5`、柯西半径 `ρ = 1/10`，则

| 量 | 值 | 来源 |
|---|---|---|
| `Q`（几何因子上界） | `62/100` | `exp(−π/5) ≤ 1/(1+π/5) < 0.62`，只用 `Real.add_one_le_exp` + `Real.pi_gt_d2` |
| `bound` | `33/1000` | `(1/50)·Q/(1−Q) = 62/1900 < 0.033` |
| `rate` | `67/100` | `2·bound/ρ = 0.66`，由 `HalfPlaneDerivBound` |
| `radius` | `1/8` | 预算 `0.033 + 0.67·0.125 = 0.11675 ≤ 0.125` |

```lean
theorem nonempty_upperRepresentation_of_reconstruction {F A chart : ℂ → ℂ} {g : ℝ → ℂ} {Mg : ℝ}
    (hg : ∀ t ∈ Set.Icc (-1/2:ℝ) (1/2:ℝ), ‖g t‖ ≤ Mg)
    (hcoeff : ∀ n : ℕ, ‖thetaFourierCoefficient g (n+1)‖ ≤ 1/50)
    (hlink : ∀ z : ℂ, (1:ℝ)/10 < z.im → inverseTheta F A chart z = thetaReconstruct g (1/10) z)
    (hinv : ∀ u : ℂ, 3/10 < u.im → certifiedRegular (A (F (chart u))) = F (chart u)) :
    Nonempty (UpperRepresentation F)
```

再往前一格：连"系数界"都不必单独认证。模块 `formal/Kneser/CentredCoefficient.lean` 证了
非零模的核在采样区间上积分为零（`theta_kernel_integral_eq_zero`，走
`integral_exp_mul_complex` ＋ `exp α·exp(−α) − exp α·exp α = 1 − 1 = 0` 的消去），
于是中心化的 **sup 界**直接给出全部非常数系数的界。最终形态：

```lean
theorem nonempty_upperRepresentation_of_centred_sample {F A chart : ℂ → ℂ} {g : ℝ → ℂ} {b : ℂ}
    (hint : IntervalIntegrable g MeasureTheory.volume (-1/2) (1/2))
    (hcentred : ∀ t ∈ Set.Icc (-1/2:ℝ) (1/2:ℝ), ‖g t - b‖ ≤ 1/50)
    (hlink : ∀ z : ℂ, (1:ℝ)/10 < z.im → inverseTheta F A chart z = thetaReconstruct g (1/10) z)
    (hinv : ∀ u : ℂ, 3/10 < u.im → certifiedRegular (A (F (chart u))) = F (chart u)) :
    Nonempty (UpperRepresentation F)
```

**这就是定量侧的终点形态**：整条链的数值输入退化成**一条线上的一个 sup 界**
`‖g t − b‖ ≤ 1/50`，与已认证的 `|θ_p − a₀| < 0.02` **形状完全一致**；
常数 `b` 不必是均值，也不需要对 `g` 本身的任何界。
这套常数下 `rate = 32.63·M₁`，所以只要采样线上的中心化界满足 `M₁ < 0.0306` 就够；
相对已认证的 `0.02` 约有 **1.5 倍余量**。（不要夸大成"差几倍都行"：`Q` 用的是粗糙的
`exp(−t) ≤ 1/(1+t)`；换更紧的指数下界可放宽到 `M₁ < 0.0437`，也就到此为止。）

最后再把"从中心多项式传播到真正的 `F`"这一步也接进去，得到端到端的形态
（`nonempty_upperRepresentation_of_model_sample`）：它直接吃证书交付的**三元组**——
模型界 `boundP`（即 `|θ_p − a₀|`）、逆支位移预算 `Lε`（即 `L_A·‖F−p‖`），
以及"两者之和仍在 `1/50` 之内"。除这三项外不再假设任何数值。

### 7.2 `hlink` 不是额外假设——它被证掉了

`hlink`（"修正项等于它自己的非负重建"）写成那样看着像循环论证：它就是精确拼接换了身衣服。
**但它不必假设。** 模块 `formal/Kneser/ReconstructionIdentity.lean` 证了：

```lean
theorem theta_eq_reconstruct {h : ℂ → ℂ} {c δ M : ℝ}
    (hcδ : c < δ) (hd : DifferentiableOn ℂ h {z : ℂ | c < z.im})
    (hper : ∀ z : ℂ, c < z.im → h (z + 1) = h z)
    (hb : ∀ z : ℂ, δ ≤ z.im → ‖h z‖ ≤ M)
    (hsum : ∀ y : ℝ, δ ≤ y → Summable (fun n : ℕ =>
      ‖thetaFourierCoefficient (fun t => h (↑t + ↑y * Complex.I)) n‖))
    {z : ℂ} (hz : δ < z.im) :
    h z = thetaReconstruct (fun t => h (↑t + ↑δ * Complex.I)) δ z
```

**上半平面上全纯、1-周期、有界的函数，等于它自己从任一采样高度作出的非负 Fourier 重建。**
三步：区间搬移（`[−1/2,1/2] ↔ [0,1]`，靠 1-周期）、正模的高度缩放
（`c_n(y) = c_n(δ)·exp(−2πn(y−δ))`，又是矩形柯西 + 竖边周期相消，只是核取共轭）、
以及逐高度的 Fourier 反演（走 §2.1 那套 `AddCircle` 机器，**没有**退化成假设）。

而 §4 已证修正项**自动 1-周期**。于是 `hlink` 完全被消掉，模块
`formal/Kneser/RepresentationComplete.lean` 给出**没有任何循环假设**的形态：

```lean
theorem nonempty_upperRepresentation_of_analytic_data ... : Nonempty (UpperRepresentation F)
```

它的假设只剩**六条**：`c < 1/10`、采样线下方的解析性、逆支沿函数方程平移一格
（`A(F(χ(z+1))) = A(F(χz)) + 1`）、采样线上方有界、一条中心化 sup 界 `‖θ − b‖ ≤ 1/50`、
以及逆支恒等式 `S(A(F(χu))) = F(χu)`。**没有一条提到负模、精确拼接或 θ 算子固定点。**

原本还挂着的两条技术假设也被消掉了：Fourier 系数的**可和性**由有界性推出
（`thetaFourierCoefficient_sample_summable`——高度缩放使系数在采样线上方几何衰减），
采样的**可积性**由解析性推出（`sample_continuous`）。
再套上传播即得 `nonempty_upperRepresentation_of_model_data`，直接吃证书三元组。

至于"Lean 内为什么仍不能闭合"：真实原因是第一行——**可测黎曼映射定理**
（[theta-periodic-beltrami.md](theta-periodic-beltrami.md)）mathlib 没有，
可预见的时间内也不会有。**不是**负模方程组。

---

## 8. 对 §8 解析链条的对抗性复核

归约把障碍指向了 [§8](theta-qc-global-existence.md)，所以 §8 本身值不值得信必须单独查。
本轮对 §8 及其三份姊妹文档做了一次逐句对抗性复核，结论如下（这是**文档层面的复核**，
没有逐条重算区间证书）：

**没有发现逻辑缺口。** 特别是 §8 第 220–232 行那段乍看像"数值上很接近所以相等"的论证，
**不是**非法推理。它的实际结构是：证书验证 `S′` 在半径 `10⁻⁴` 的参数圆盘上值域落在不含零的
圆盘内、旋转后实部严格为正，故 **S 在该圆盘上单叶**；再验证 `A_F(z₀)` 与 `W(z₀)` 都落在距
`A_p` 不超过 `10⁻⁴/4` 处，即同在该圆盘内；两者经 S 映射同为 `F(z₀)`；由单叶性得相等。严密。

**非初等输入**（引用而未证，Lean 内也无对应物）：

| 输入 | 出处 | 状态 |
|---|---|---|
| 可测黎曼映射定理（Ahlfors–Bers） | [theta-periodic-beltrami.md](theta-periodic-beltrami.md) §4 | **引用** |
| Beurling 变换的 `‖B‖_{L⁴} < 12`（Bañuelos–Janakiraman） | 同上 §2 | **引用** |
| 平面 Stoïlow 分解（Luisto–Pankka） | 同上 §4 | **引用** |
| Beurling 核的圆柱周期化、势的一致界、定量 Banach 收缩 | 同上 §2–§4 | **已证** |

**两处表述值得收紧**（不影响正确性，但会误导读者）：

1. 负模消失论证需要 **θ_F 在带的上端有界**，§8 没有把这句直接写出来，是从 §5 的高端极限
   隐含推得的。既然这一步现在已是 Lean 定理
   （`periodic_band_negative_fourier_zero` 明确要求 `hb`），这条假设应当在纸面上也显式化。
2. §8 定义 `W(z)` 时把 `S(W(z)) = F(z)` 当作已知，实际推导链在
   [theta-canonical-identity.md](theta-canonical-identity.md) §1（QC 分段定义 + 恒等定理），
   §8 未写出该链。

**一处必须区分清楚**：§8 给出的 `|θ_p − a₀| < 0.02`、`|θ_p′| < 0.1` 是对**中心多项式 p** 的
`θ_p`，**不是**对真正 Kneser `F` 的 θ，而且只覆盖一段高度。第 7 节表格里要的一致界是后者，
两者不能混用——这正是"从矩形推到整个半平面"这条缺口的具体内容。

**关于形式化风格的一点纪律**：不要用 `axiom` 把上述缺口写进 Lean。本仓库
`audit_modules.py` 明文拒绝 `axiom`（与 `sorry`/`native_decide` 同列），加公理会直接破坏
审计的意义。正确做法是本文自始至终采用的那种——写成**具名假设**（`Prop` 定义或结构字段），
让依赖关系出现在定理的类型里、可被 `#print axioms` 检验。

## 9. 复现

编译（galic 容器，Lean 4.32 / mathlib 26d1c9d）：

```sh
ssh galic 'docker exec -u lean lean-build bash -lc \
  "cd ~/projects/kneser-formal && LEAN_NUM_THREADS=16 lake build"'
```

全项目 48000 job 通过。公理审计：

```sh
ssh galic 'docker exec -u lean lean-build bash -lc \
  "cd ~/projects/kneser-formal && python3 audit_modules.py --name wall-a-reduction \
     --module DiscBoundaryModes --module DiscBoundaryConverse --module ThetaGluingBridge \
     --module PeriodicBandFourier --module ReconstructionBounds \
     --module CentredCoefficient --module ReconstructionRepresentation \
     --module ReconstructionIdentity --module QExpansionBridge --module RepresentationComplete \
     --module HalfPlaneDerivBound --module RepresentationFromInverse --module InverseThetaModes"'
```

输出 `PASS: 74 theorems in 14 selected modules; allowed axioms only.`

十四个模块都不含任何数值证书，全部是一般定理（矩形柯西、圆周柯西、Schwarz 型导数估计、
结构装配）。
