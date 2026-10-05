# 几何路线（§2–§8）的 Lean 状态地图

2026-09-17 修订（原 2026-09-16 / 2026-09-15）。本文只回答一个问题：**离「F = F_K 的内核验证」还差什么，差在哪。**

> **2026-09-16 修订的要点**：墙 A 不再是 `ThetaExactGluing` 那条"公开未解决的无限方程组"。
> 见 §2 与 [docs/wall-a-reduction-zh.md](../docs/wall-a-reduction-zh.md)。
>
> **2026-09-17 修订的要点**（三条）：
> 1. 修掉 §4 相对 §2 未同步造成的两处自相矛盾——(a) `hlink` §2 说已消除而 §4 仍列为待办；
>    (b) 能否闭合 §2 说应撤回而 §4 仍说不可能。
> 2. 对 mathlib 侧实查：经典 RMT **不在 mathlib 里**，PR #33505 仍是 draft、停滞四个月，
>    原文"在途并入"的说法已改。见 §4。
> 3. ⚠ **最要紧的一条**：原文"可测 RMT……可预见的时间内也不会有"**是错的，已删**。
>    MRMT 已由 [will1491/RiemannDynamics](https://github.com/will1491/RiemannDynamics)
>    在 Lean 里证完且 sorry-free；经典 RMT 另有 [vbeffara/RMT4](https://github.com/vbeffara/RMT4)。
>    两者都不在 mathlib 里但都可依赖。见 §2 的"外部已有的 Lean 资产"。
>    **此后凡要写"mathlib 没有 X ⟹ 路线走不通"，先查那一节。**
>    该节末尾附 `mrmt_exists` 与 §5 所需 χ 的**逐条签名对照**：MRMT 本身可直接用，
>    周期性与实对称须另补证明（周期性不能直接套归一化唯一性，见下文 2026-09-26 更正），而**显式常数预算（`‖B‖_{L⁴} < 12`、`D = 40k/(1−12k)`）
>    与圆柱算子拿不到，仍须自建**。

所有"已证"都指在 galic 上 `lake build` 通过且 `audit_modules.py` 公理审计通过
（无 `sorry`、无自定义公理、无 `native_decide`，只允许 `propext`／`Classical.choice`／`Quot.sound`）。

## 0. 链条

```
LiftedEdge F L          §3 低段 + §4 中高段 + §5 端点 + 反射 + 重参数化
        +
StripBijection F L g    §6 横截面一致极限 + §7 辐角原理
        ↓  canonicalRouteChart
GraphAbelChart (standardRegion L) exp 1
        ↓  canonical_identity_of_routes   （已证，`Kneser/CanonicalRoute.lean`）
EqOn F F_K slitDomain
```

末端两步（图册 → 身份）**已经证完**：`canonicalRouteChart`、`canonical_identity_of_routes`，
外加仓库原有的 `graphAbelChart_unique`、`closed_graph_strip_rigidity`、`Automorphism`、`Atlas`。

**2026-09-15 起，`StripBijection` 也整体不再是假设**：`RouteAssembly.stripBijection_of_boundary_data`
从边界数据把它构造出来（见 §2 的"墙 B"一节）。链条现在是

```
LiftedEdge F L          §3 低段 + §4 中高段 + §5 端点 + 反射 + 重参数化
        +
边界数据（左边界严格内部性、两端极限、闭条带单叶、割线域解析、F(0)=1）
        ↓  canonicalRoute_of_boundary_data
CanonicalRoute F L  →  GraphAbelChart  →  EqOn F F_K slitDomain
```

## 1. 逐节状态

| 节 | 内容 | 状态 | 模块 |
|---|---|---|---|
| §3 低段 t∈[0,0.32] | 提升存在、唯一、连续、Lipschitz、虚部严格单调（斜率 ≥1） | **已证，且只依赖缝合界 α** | `RootDisc`, `LowSegment`, `LowSegmentCells`, `LowCell000–063`, `LowSegmentAll`, `LowSegmentChain`, `LowSegmentMonotone`, `CenterUnivalent` |
| §3 附带 | F 在 \|z\|≤0.46 单叶（原文列为"已知"） | **已证**（不再是假设） | `CenterUnivalent.center_ball_injOn` |
| §3 附带 | ζ(0) 为实（原文列为"已知"） | **已证**（由实对称＋单叶） | `LowSegmentReflect.low_segment_lift_zero_real` |
| 反射 t∈[−0.32,0] | ζ(−t)=conj ζ(t)，连续性与单调性延拓 | **已证**（给定 F 实对称） | `EdgeSplice`, `LowSegmentReflect` |
| §4 中高段 t∈[0.31,1.32] | 目标属于 Abel 域 ＋ 高度下界 −3/5 | **已证（202 格数值证书）** | `MidSegment`, `MidCell000–201`, `MidSegmentAll` |
| §4 存在唯一 | 修正坐标方程 (4) 的唯一解，`F(χu)=w` 精确 | **已证，但条件于 `UpperRepresentation`** | `MidSegment.mid_segment_unique_solution` |
| §4 单调性 (6) | `t′−t ≤ (ζ′−ζ).im` | **已证，条件于每格 (κ₀,K₁)** | `MidSegmentDerivative` |
| §4 的 (κ₀,K₁) | Abel 值沿左边界的增量速率 | **已证（202 格数值证书）**：导数恒等式 `dβ/dt = i·χ′(v)/(χ(v)·L·∏w_k)` 是**证出来的**；κ₀∈[1.0006, 31.68]、K₁∈[1.113, 46.36]；格内 κ=1/2 成立（最大可取 0.7945，κ=1 不可达） | `MidDerivative`, `MidDerivCell000–201`, `MidDerivAll` |
| §5 端点 t→b⁻ | `Im Ψ<0`、目标属于 Abel 域、`Im B → +∞` | **已证，完全无条件** | `EndSegment` |
| §6 横截面极限 (8) | `F(ζ(t)+r) → L` **一致于 r** | **已证**（条件于表示结构；δ 与 r 无关的定量形式） | `CrossSection` |
| §6 附带 | `MapsTo F strip (standardRegion L)` | **已证**（2026-09-15）：截断 + mathlib 普通极大模原理，不需要曲边条带的 Phragmén–Lindelöf。条件于左边界数据（`Re F = Re L`、`\|Im F\| < \|Im L\|`）与两端极限 | `StripMaximum`, `StripRegion`, `StripRegionBridge` |
| §7 辐角原理 | 条带 → 标准区域的双全纯 | **墙**（见 §2） | `StripBijectionTools` 已把它归约为一条 `∃!` |
| §7 开映射排除 | 内部点不映到边界 | **已证** | `StripBijectionTools.openStrip_image_notMem_frontier` |
| §7 逆支解析性 | 由 `deriv F ≠ 0` 得逆解析 | **已证**（转移引理） | `StripBijectionTools.inverse_analyticAt_of_deriv_ne_zero` |
| §7 `StripDerivNeZero` | 单叶解析 ⟹ 导数处处非零 | **已证**（开集上）——mathlib 没有这条，值得上游 | `InjectiveDeriv.analytic_injOn_deriv_ne_zero` |
| §7 单叶性（上半部） | 由表示式 `F=S∘W∘χ⁻¹` 得 `InjOn F`，**不需要 χ 单叶** | **已证** | `RepresentationBijection.representation_injOn_region` |
| §7 覆盖假设 | "χ 把 u-条带映满 z-条带" | **已证不可能**：`‖χ−id‖≤D` 时条带里 `g(y)−(D+1)` 处的点没有原像 | `RepresentationBijection.chart_covers_impossible_of_bounded` |
| 装配 | 三段数据（在 (−b,b) 上）⟹ `LiftedEdge` | **已证** | `EdgeAssembly.liftedEdge_of_interval_data` |
| 装配附带 | 左边界字段 `Re F(ζt)=Re L` 无需定分支（2πik 是纯虚） | **已证** | `EdgeAssembly.left_edge_re_of_functional_equation` |
| 低段全字段 | 在 t∈[−0.32,0.32] 上 `LiftedEdge` 的**每一条**都成立 | **已证，无条件** | `LowSegmentReflect.low_segment_edge_fields` |
| §8 规范判据 | Abel 方程实例 → 图册 → 身份 | **已证** | `Geometry`, `AbelUniqueness`, `CanonicalRoute` |

### 低段的最强表述

`low_segment_edge_fields`：只要 F 满足下面四条——**没有别的输入**——

1. 在 \|z\|<0.61 上解析；
2. 被 150 项中心多项式控制到缝合界 α ≤ 10⁻³⁰；
3. 实对称 `F(conj z) = conj F(z)`；
4. 函数方程 `F(z+1) = exp F(z)`；

则曲线 `ζ t = lift t − 1` 在 `t ∈ [−0.32, 0.32]` 上满足 `LiftedEdge` 的**每一条**：
连续、虚部严格单调（斜率 ≥1）、`Re F(ζt) = Re L`、指数边界恒等式、
基点 `ζ(0)` 为实且落在 (−1,0)。其中原文列为"已知"的单叶性与基点实性都是**证出来的**。

差的只是把曲线从 [−0.32, 0.32] 延到整个 (−b, b)——那需要 §4 的提升（条件于墙 A）
与 §5 的提升高度。

## 2. 两堵墙

### 墙 A（解析侧）：`UpperRepresentation` 未构造——但**不再是负模方程组**

§1 把 `F(χ(u)) = S(u + θ(u))`（Im u > 0.3）列为已有结论。Lean 侧它是结构
`UpperRepresentation` 的字段，**仍然没有针对真正的 Kneser F 的实例**。

**2026-09-16 起，这堵墙的描述变了。** 原判断是："追到底是 θ 算子固定点那条线：
Cauchy 投影只保留非负 Fourier 模，固定点要真正取到边界数据必须'负模全为零'，即
`ThetaExactGluing`——公开未解决的无限方程组。" **这个追溯被推翻了**，
见 [docs/wall-a-reduction-zh.md](../docs/wall-a-reduction-zh.md)（74 条定理，已审计）：

1. **负模族不是方程组。** `ThetaExactGluing` 的整个无限族由一条假设一次性打发：
   边界数据是闭单位圆盘上连续、内部全纯的函数的边界值。
   `ThetaGluingBridge.thetaExactGluing_of_discExtension`，靠的是圆周柯西定理
   （`DiscBoundaryModes.circle_boundary_negative_mode_zero`）。而且这条归约是**充要**的：
   `DiscBoundaryConverse.disc_extension_iff_negative_modes_zero`——所以"墙 A 就是圆盘全纯延拓"，
   不多不少。
2. **采样线上的版本同样是标准事实。** 上半带上全纯、1-周期、有界 ⟹ 全部负模为零：
   `PeriodicBandFourier.periodic_band_negative_fourier_zero`，矩形柯西 + 竖边周期相消 +
   上边 `exp(−2πnY)` 衰减。这正是 §8 最后那步，现已是内核检查过的定理。
   ⚠ **但这一半 mathlib 早已有**：它就是模形式的 q-展开
   （`UpperHalfPlane.hasSum_qExpansion` / `qExpansion_coeff_eq_intervalIntegral`）。
   `QExpansionBridge` 已把我们的陈述从 mathlib 的推出（少一条假设），主链改走桥接。
   详见 [docs/wall-a-reduction-zh.md](../docs/wall-a-reduction-zh.md) §0。
3. **`repr` 字段根本不需要 θ 算子。** 对**任意** chart，取 `θ u := A(F(χ u)) − u`
   （`A` 为 `S` 沿 `F∘χ` 的任一右逆），则 `S(u+θu) = S(A(F(χu))) = F(χu)`，
   `repr` 由构造成立：`RepresentationFromInverse.inverse_theta_repr`。
   剩下的三条定量字段里，导数界又能由一致界经半平面柯西估计推出
   （`HalfPlaneDerivBound`），故只剩**两条**定量输入。
4. **合成**：这样得到的 θ **自动 1-周期**，于是它的负模自动为零
   （`InverseThetaModes.upper_representation_and_modes_of_inverse`）。
   即：**在足以产生表示式的那组假设下，精确拼接是推论而非义务。**

**因此墙 A 的正确表述是**：缺的不是无限方程组的解，而是

1. **`F` 本身在 Lean 内没有实例**——[§3–§6](../docs/theta-qc-global-existence.md) 的构造
   依赖**可测黎曼映射定理（Ahlfors–Bers）**，**mathlib 至今没有这条**。
   ⚠ **2026-09-17 更正：原文"可预见的时间内也不会有"是错的，已删。**
   MRMT 不在 mathlib 里，但**在 Lean 里已经有了**，且是 sorry-free 的：
   见下面"外部已有的 Lean 资产"。这一条不应再作为"路线不可行"的依据。
   ⚠ **2026-09-16 更正：这是本项目所选路线的障碍，不是 Kneser 定理的障碍。**
   [Kneser 1950 原证](../docs/kneser-classical-route-zh.md) 第六步用的是**经典** RMT，
   而经典 RMT 的完整 Lean 证明已存在于 mathlib PR #33505——但**该 PR 仍是 draft、未合并、
   已停滞四个月**（详见 §4 的实查记录，2026-09-17）。
   第六步所需的"把诱导平移识别成 Möbius 自同构"本轮已补齐
   （`BlaschkeFactor`/`DiscRotation`/`CayleyTransform`/`DiscAutomorphism`，35 条定理已审计），
   **其后半"把无内点不动点的自同构归一化成 `ζ↦ζ+1`"也已补齐**
   （`RealMoebiusMap`/`MoebiusFixedPoint`/`ParabolicNormalForm`/`HyperbolicNormalForm`/
   `UpperHalfNormalForm`，25 条定理已审计，见
   [docs/upper-half-normal-form-zh.md](../docs/upper-half-normal-form-zh.md)）；
   第六步的"排除双曲情形"**其解析核心本轮也已补齐**——Kneser 那句
   "Da es eine solche nicht gibt"（有界全纯、在圆周除两点外边界极限为零 ⟹ 恒零）
   由 `DiscTwoPointVanishing`/`UpperHalfTwoPointVanishing`/`HyperbolicExclusion`
   证出（19 条定理已审计，`audit/hyperbolic-exclusion-result.json`），
   走的是"乘 `(z−p)(z−q)` 后闭圆盘上连续、普通极大模原理以 C=0 打完"，
   **不需要任何边界唯一性理论**（Fatou/Privalov/F.&M. Riesz，mathlib 全无）。
   第六步只剩**见证函数的构造**（把 `e^{w/c}` 沿黎曼映射搬过来，要 𝔅 与 RMT 本身），
   它留在上述定理的假设位置上，没有被公理化。
   **所以"Lean 内不可能闭合"这个说法应当撤回**，改为"卡在一个停滞的 draft PR 加一批常规工作"
   ——注意是"停滞的 draft"而不是"在途"，且合并时间表不受本项目控制。§4 给出对外表述的完整措辞。

   ### 外部已有的 Lean 资产（2026-09-17 查证）

   下面两个仓库都**不在 mathlib 里**，但都是可直接依赖的 Lean 代码。
   任何"mathlib 没有 ⟹ 路线走不通"的推理在写下之前都要先看这一节。

   | 仓库 | 内容 | 状态 |
   |---|---|---|
   | [will1491/RiemannDynamics](https://github.com/will1491/RiemannDynamics) | **可测黎曼映射定理（MRMT）**、Uniformization、No Wandering Domain、拟共形映射、Teichmüller 基础 | Lean v4.33.0，下游于 mathlib v4.33.0 + RMT4 + Carleson；作者自述 sorry-free、只用三条标准公理；2026-08-17 仍在推送 |
   | [vbeffara/RMT4](https://github.com/vbeffara/RMT4) | **经典**黎曼映射定理 | 独立于 mathlib PR #33505 的另一份实现；2026-01-10 最后推送 |

   MRMT 那部分已核到文件级，不是口头声明：

   - `RiemannDynamics/QC/MRMT/Existence.lean`——921 行，**0 个 `sorry`**，含 `mrmt_exists`、
     `mrmt_exists_of_support`、`IsPrincipalSolution.{injective,isHomeomorph,ae_det_pos,isQCAnalytic}`
   - `RiemannDynamics/QC/MRMT/Uniqueness.lean`——542 行，**0 个 `sorry`**，含 `mrmt_unique_normalized`
   - 另有 `AnalyticDependence.lean`、`NeumannSeries/{CauchyTransform,PrincipalSolution}.lean`、
     `SmoothCase/{Solution,Regularity,Inverse,Stability}.lean`、`QC/Defs/BeltramiCoeff.lean`

   **对本项目的后果**：§3–§6 的 qc 构造不再因为"Lean 里没有 MRMT"而不可行。
   工具链距离很近——本项目 `lean-toolchain` 是 `leanprover/lean4:v4.32.0`，
   RiemannDynamics 是 `v4.33.0`，差一个小版本。
   代价是要依赖第三方仓库（单个小组维护、star 个位数），不是 mathlib 的稳定性保证。

   **来源**：`#mathlib4 > Geometry and complex dynamics formalization`，
   Will (Ziang) Li 2026-08-10 发帖（message id 615696635）宣布上述三条定理已形式化并希望上游；
   Junyan Xu 2026-08-11 回复讨论 Riemann sphere 的实现方式。
   本项目已在该话题下追问 MRMT 能否直接依赖（message id 624822047，2026-09-17，待回复）。

   #### 签名对照：`mrmt_exists` vs §5 实际需要的形式（2026-09-17 逐条核对）

   对方的接口：

   ```lean
   theorem mrmt_exists (b : BeltramiCoeff) : ∃ f : ℂ → ℂ, IsQCAnalytic f b
   theorem mrmt_unique_normalized (b : BeltramiCoeff) :
       ∃! f : ℂ → ℂ, IsQCAnalytic f b ∧ f 0 = 0 ∧ f 1 = 1

   structure BeltramiCoeff where
     μ : ℂ → ℂ ; measurable : Measurable μ ; bound : eLpNormEssSup μ volume < 1

   def IsQCAnalytic (f : ℂ → ℂ) (b : BeltramiCoeff) : Prop :=
     OrientationPreservingHomeo f ∧ MemW12loc f ∧ ∀ᵐ z, dzbar f z = b.μ z * dz f z
   ```

   [docs/theta-qc-global-existence.md](../docs/theta-qc-global-existence.md) §5 要的 χ，
   其规格在 [docs/theta-periodic-beltrami.md](../docs/theta-periodic-beltrami.md) §1，共六条：

   | §5 需要 χ 满足 | RiemannDynamics 是否提供 | 判定 |
   |---|---|---|
   | QC 同胚解 μ 的 Beltrami 方程 | `mrmt_exists` | ✅ 直接可用 |
   | 固定 0、1、∞ | `mrmt_unique_normalized`（∞ 对 ℂ 同胚自动，其 docstring 明说） | ✅ 直接可用 |
   | `χ(z+1) = χ(z)+1` | 无 | ⚠️ 尚须周期性证明，不能直接套归一化唯一性 |
   | 实对称 `χ(conj z) = conj χ(z)` | 无 | ⚠️ 可由唯一性推出 |
   | `sup_ℂ ‖χ − id‖ ≤ 40k/(1−12k)` | 无 | ❌ 拿不到，必须自建 |
   | `χ−z` 两端趋常数、高半平面解析 | 无 | ❌ 拿不到，必须自建 |

   **第 3 条仍有证明义务**（2026-09-26 更正）：μ 为 1-周期时，
   `z ↦ χ(z+1)−1` 虽在 `0` 处取值 `0`，但在 `1` 处的值是 `χ(2)−1`；
   要证明它等于 `1` 就已经需要尚未证明的周期性。因此不能声称两个解有同一归一化，
   再直接套 `mrmt_unique_normalized`。一条可行的数学路线是：先证明
   `χ ∘ (z ↦ z+1) ∘ χ⁻¹` 为平面的共形自同构，因而为仿射映射；
   它无不动点，故线性系数为 `1`，再由 `χ(0)=0`、`χ(1)=1` 确定平移量为 `1`。
   共形共轭、仿射分类及其接口仍须接入 Lean，不能记作 MRMT 已提供的结论。
   **第 4 条**在系数满足所需共轭对称时可走归一化唯一性：
   `z ↦ conj (χ (conj z))` 确实同时固定 `0` 和 `1`，但方程在共轭下的变换也仍须验证。

   **吻合点是承重的**：theta-periodic-beltrami.md §4 证 χ 是同胚时明写"取可测 Riemann
   映射定理给出的平面拟共形坐标 q，具有同一系数 μ"，再走 Stoïlow 分解 + Weyl 引理。
   那个 `q` 就是 `mrmt_exists b` 的产物，签名一字不差——这一步可以直接
   `obtain ⟨q, hq⟩ := mrmt_exists b`。

   **但定量核心拿不到。** §2–§4 的预算链是独立工程，对方没有：

   - **圆柱算子 `B_per`**（平面 Beurling 核按整数平移周期化）——只有平面版
   - **周期 Cauchy 势**（`cot(π(z−w))` 核，`∂̄P = v`、`∂P = B_per v`）——无
   - **`‖cot 核‖_{L^{4/3}} < 10 ⟹ ‖Pv(z) − Pv(0)‖ ≤ 20‖v‖₄`**——无

   ⚠ **最要紧的一条：显式常数拿不到。** 对方的
   `beurling_lp_bound (hp : 1 < p) (hp' : p ≠ ⊤) : ∃ C : ℝ, IsCalderonZygmundBound beurling p C`
   里 **C 是存在量词**（p>2 那支还要再 `obtain` 一次 `eLpNorm_beurling_Lp_le_high` 的存在常数）。
   而 §2 要的是 Bañuelos–Janakiraman 的显式 `‖B‖_{L⁴} < 12`，整条 `12k < 1` 收缩与
   `D = 40k/(1−12k)` 全靠它。**存在性常数喂不进这条链。**

   ⚠ **指数错配**：`IsQCAnalytic` 打包的是 `MemW12loc`（**L²**），
   而周期引理与 §4 的 `F_hat` 走局部 **W^{1,4}**。对方有 L⁴ 机器
   （`beurling_ae_tendsto_neg_pi_two_four` 的插值端点就是 p₀=2、p₁=4），
   但没打包进 `IsQCAnalytic`，接的时候要自己补一层。

   **净结论**：依赖 RiemannDynamics 省掉的是 **MRMT 本身**——整条链里最重、
   最不想自己证的一块，且接口正好。省不掉的是周期化与全部显式常数预算，
   那本来就是本项目自己的贡献（theta-periodic-beltrami.md 明写"本文的周期化、
   显式核预算和 proper 次数论证如上给出"）。
   所以"抬工具链到 v4.33.0 换 MRMT"划算，但**不要指望它把 §5 交钥匙**：
   周期 Beltrami 定理仍要自己形式化，MRMT 只进去当其中一个引理。

   #### 施工计划已单列

   周期 Beltrami 定理的形式化拆成 **18 个模块**（＋1 个下游应用），
   见 [docs/periodic-beltrami-formalization-plan.md](../docs/periodic-beltrami-formalization-plan.md)：
   L0 基础设施 2 格、L1 cot 核估计 3 格、L2 周期 Beurling 算子 4 格、
   L3 不动点 2 格、L4 同胚性 3 格、L5 附加性质 4 格。

   该计划的三条要点：

   1. ⚠ **不要去证 `‖B‖_{L⁴} < 12`。** 那个 12 是宽松常数，在链里只出现于 `12k < 1`
      与 `‖v‖₄ ≤ ‖μ‖₄/(1−12k)`；换成任意显式 `C` 只是把结论变成
      `sup‖χ−id‖ ≤ 40k/(1−Ck)`。而实际 `k = 100000ε`、`ε < 10⁻³⁰`，即 `k ~ 10⁻²⁵`，
      要 `Ck < 1` 只需 `C < 10²⁵`。**目标是"任何显式可算的 C"**，余量大到可以用最笨的证法。
   2. **仅有两道门**：#7 `PlaneBeurlingLpExplicit`（显式常数）与
      #8 `BeurlingTransfer`（平面界→圆柱界的三重极限论证）。其余十六格是常规工作量。
   3. **外部收益只有两格**：#12 `StoilowFactorization` 用 `mrmt_exists` ＋ 对方的
      `QC/Calculus/Weyl.lean`，#15 `ChiUniqueness` 用 `mrmt_unique_normalized`。

   建议次序：先做 L1（#3–#5，纯不等式、零外部依赖、独立可交付），
   再 #1/#2/#6，然后攻 #7、#8，最后 L4/L5。

   **#3 `CotKernelBound` 已完成**（2026-09-17，本计划的第一格）：
   `Kneser/CotKernelBound.lean`，**8 条定理**，`lake build` 通过，
   `audit_modules.py --name cot-kernel-bound --module CotKernelBound` 通过
   （`audit/cot-kernel-bound-result.json`，无 `sorry`、无自定义公理、无 `native_decide`）。
   主定理 `norm_cot_pi_mul_le`：`|x| ≤ 1/2`、`0 < x²+y²` ⟹
   `‖cot(π(x+iy))‖ ≤ 1 + 1/(2√(x²+y²))`。
   其中 `norm_sq_sin_ofReal_add_mul_I` / `norm_sq_cos_ofReal_add_mul_I`
   （`‖sin(x+iy)‖² = sin²x + sinh²y` 等）与 `abs_sinh_eq_sinh_abs`
   是 **mathlib 没有的**，可考虑上游。
   已并入根导入，全项目 `lake build` 由 48028 升至 **48029 job**，整体仍通过。

   **#4 `CotKernelL43` 的数学内容已全部形式化**（2026-09-17）：
   `Kneser/CotKernelL43.lean`，**14 条定理**，`lake build` ＋
   `audit_modules.py --name cot-kernel-l43` 均通过，全项目 **48030 job**。三条主结论：

   - `lintegral_ball_norm_rpow_le`：`∫_{ball 0 1} ‖w‖^{-4/3} ≤ 3π`
     ——原文那个 `3π`，由 **layer cake** 精确复现
     （`∫₀^∞ vol{‖w‖^{-4/3} > t} dt`，`(0,1]` 用全局界 `π`、`(1,∞)` 用 `π t^{-3/2}`，合 `π(1+2)`）。
   - `lintegral_kernel_rpow_le`：在**任何**面积 ≤ 2 的可测域 `S` 上
     `∫_S (1 + 1/(2‖w‖))^{4/3} ≤ (3/2)^{4/3}(3π + 2)`。刻意写成域无关形式，
     故不必等 #1/#2。
   - `closing_arith`：`(3/2)(3π+2)^{3/4} < 10`——**原文那个 `10` 已验算成立**，
     实际值约 9.32，有余量。

   顺带补了三条 mathlib 空白：`volume_complex_ball`、`superlevel_set_norm_rpow`、
   `lintegral_Ioi_one_rpow`。

   **#5 `PotentialUniformBound` 已完成**（2026-09-17）：`Kneser/PotentialUniformBound.lean`，
   **4 条定理**，`lake build` ＋ `audit_modules.py --name potential-uniform-bound` 通过。
   主结论 `potential_difference_bound`：两核的 `L^{4/3}` 范数各 ≤ 10 时
   `∫_S (‖K₁‖+‖K₂‖)‖v‖ ≤ 20·‖v‖₄`——**那个 `20` 就是 `2 × 10`**。
   另有 `l43_norm_le_ten`（把 #4 的积分预算转成范数界，关键是 `closing_arith`）、
   `lintegral_norm_mul_le_holder`（Hölder，共轭指数 4/3 与 4）、
   `holderConjugate_four_thirds`。全程在 `ℝ≥0∞` 里做，**不需要任何可积性副条件**。

   ### ✅ L1 整层已完成（2026-09-17）

   #3 ＋ #4 ＋ #5 共 **26 条定理**（8 + 14 + 4），全部审计通过，全项目
   `lake build` 由 48028 升至 **48031 job**，整体仍通过。
   **theta-periodic-beltrami.md §3 的每个常数都已验算成立**：
   逐点界 `1 + 1/(2d)`、圆盘积分 `3π`、核范数 `10`（有余量，实际约 9.32）、
   势差界 `20`。顺带补了 **6 条** mathlib 空白。
   ### ✅ L0 第一阶段也完成了（2026-09-17）

   `Kneser/PeriodicSupport.lean`（6 条）＋ `Kneser/CylinderLp.lean`（8 条），
   共 **14 条定理**，`audit_modules.py --name l0-layer` 通过，全项目 **48033 job**。

   - **#2 全部完成**：`fundamentalStrip`、面积恰为 `2Y`、`Y ≤ 1` ⟹ 面积 ≤ 2、
     `‖μ‖₄ ≤ k(2Y)^{1/4}`；并由 **`lintegral_kernel_rpow_le_strip`
     兑现了 #4 遗留的末端打包——#4 至此完全闭合**。
   - **#1 第一阶段**（铺砌与周期不变性，#8 真正要用的那块）：
     `stripTranslate_disjoint` ＋ `iUnion_stripTranslate`（整数平移铺满整条带）、
     `periodic_int`、`lintegral_stripTranslate_of_periodic`。
     mathlib 只有 ℝ 上的 `isAddFundamentalDomain_Ioc`，**没有 ℂ 沿实轴方向的版本**，故自建。
   - **#1 仍欠**：光滑紧支撑周期函数在圆柱 `L⁴` 中稠密。

   ### 周期 Beltrami 形式化的当前总账

   **已证 43 条定理**：L1 26 条（#3/#4/#5）＋ L0 14 条（#1 第一阶段/#2）
   ＋ #6 第一阶段 3 条。
   theta-periodic-beltrami.md **§3 整节的常数链已全部验算成立**
   （`1+1/(2d)` → `3π` → `10` → `20`），§1 的基本条带与面积预算也已就位，
   §2 的"周期化 Beurling 核 ＝ 周期 Cauchy 势的 `∂` 导数"这条关系亦已证
   （`tsum_inv_sq_add_int`：`∑' n:ℤ, 1/(z+n)² = π²/sin²(πz)`，上半平面）。
   顺带补的 mathlib 空白升至 **7 条**（新增 `hasDerivAt_cot`）。

   **2026-09-17 再更新：已证 47 条定理**（7 个模块一次性审计通过，全项目 **48035 job**）。
   新增 **#8a `KernelTailBound`**（4 条）——§2 那句"核的远端绝对积分为 `O(1/(εM))`"
   的定量形式，主结论 `tail_sum_right_le`：`∑_{m ∈ Ioo N K} 1/(x−m)² ≤ 8/(N+1)`，
   **与截断位置 `K` 无关**（这正是"一致趋于零"的含义）。

   **2026-09-17 再更新：已证 58 条定理**（8 个模块一次性审计通过，全项目 **48036 job**）。
   新增 **`CylinderDomain`**（11 条）：圆柱的**完整**基本域 `Re ∈ (−1/2,1/2]`
   （`CylinderLp` 那个是有限高度的条带，承载 μ 支撑用），
   `iUnion_cylinderTranslate`（整数平移**铺满整个 ℂ**）、
   `iSup_lintegral_cylinderTrunc`（高度截断单调上升到全积分，**稠密性论证的第一步**）。
   **再增 `CylinderTruncDense`（5 条）：已证 63 条定理 / 9 模块，全项目 48037 job。**
   `tendsto_lintegral_cylinderTrunc_compl` 完成稠密性的**第 1 步**（高度截断收敛）；
   `periodization_translate_eq_zero` 把**周期化陷阱的解药形式化**了
   （支撑限在一个周期宽度内 ⟹ 逐点只剩 ≤3 个平移，误差只放大常数倍）。
   **装配再进（同日）：已证 66 条定理 / 9 模块。** 新增
   `tsum_periodization_eq`（周期化在基本域上**塌成三项有限和**）、
   `norm_tsum_periodization_le`、`lintegral_translate_cylinderDomain_le`，
   三条合起来即 `‖周期化‖_{L⁴(D)} ≤ 3‖h‖_{L⁴(ℂ)}`——**§11 的陷阱完全解决**。
   **光滑截断已装完（`CylinderCutoff`，9 条）：已证 75 条定理 / 10 模块，全项目 48038 job。**
   `cutoff w = reBump w.re`（`rIn=1/2`、`rOut=3/4`），
   `cutoff_mul_eq_self`（截断不改变支撑在基本域内的函数）＋
   `tsum_periodization_cutoff`（截断后周期化在基本域上塌成三项）**两头都接上了**。
   ### ✅ **#1 的稠密性已完成**（2026-09-17）

   `PeriodizationSmooth`（4 条）＋ `CylinderDense`（3 条）补齐最后两块，
   全项目 **82 条定理 / 12 模块**审计通过，**48040 job**。
   主结论 `exists_periodic_smooth_approx`：支撑在基本域内的 `L⁴` 函数
   可被**光滑 1-周期**函数在圆柱 `L⁴` 中任意逼近——正是 §2 末尾延拓 `B_per` 所需的那条。
   ε/3 链：`‖f−G‖_{L⁴(D)} ≤ 3‖f−cutoff·g‖ ≤ 3‖f−g‖ ≤ 3·(ε/3)`。
   光滑性靠**局部有限**（`1/4` 邻域内只剩 `|m−⌈−Re w₀⌉| ≤ 2` 的项）。
   **#8e 的稠密性输入已备好**：`exists_periodic_smooth_approx_restrict`（无支撑侧条件）。
   ⚠ 但 **#8e 的主体依赖 #8d**——要延拓的是 `B_per`，其有界性正是 #8d 的结论。
   关键路径仍是 **#8b → #8c → #8d → #8e**。

   **#8b 已完成**（2026-09-17，8 条定理）：`TruncatedRepetition`，
   核心是 `lintegral_truncDomain_of_periodic`——**1-周期函数在 `2M` 个基本域的并上
   的积分恰为基本域上的 `2M` 倍**，即 §2 里"除以内部周期数"所除的那个数。
   配套 `truncRepeat` 与其平面 `L⁴` 预算 `lintegral_truncRepeat_rpow`。
   全项目 **91 条定理 / 13 模块**，48041 job。
   **#8c 已完成**（2026-09-17，3 条定理），并**修正了 #8a 的形式**：
   #8a 的假设 `2R ≤ N` 代入实际几何需要 `ε ≥ 1/2`，而 §2 要的是 `ε → 0`——
   正确假设是 `R ≤ (1−ε)N`，此时尾部和为 `2/(ε²(N+1))`，**与截断位置无关**。
   主结论 `kernel_tail_right_le` 给的是复核形式（经 `Complex.abs_re_le_norm` 归约）。
   全项目 **94 条定理 / 14 模块**，48042 job。
   **#8d 的极限骨架已完成**（2026-09-17，6 条定理）：§2 那三步记账
   （除以周期数 / `ε → 0` / 放开高度）各一条引理，合成 `transfer_skeleton`——
   **带 `(1−ε)` 折扣的截断界 ⟹ 圆柱上的干净界**。
   全项目 **100 条定理 / 15 模块**，48043 job。
   **算子已定义**（2026-09-17，`BeurlingOperators`，4 条）：`planeBeurlingKernel`、
   `perBeurlingKernel`，以及 ⭐ **`tsum_planeBeurlingKernel`——#6 的兑现**：
   `∑_n −1/(π(u+n)²) = −π/sin²(πu)`，**周期化核有初等闭式，不必带无穷和**。
   两个截断算子 `planeBeurlingTrunc` / `perBeurlingTrunc` 取 `czOperator` 式截断。
   全项目 **104 条定理 / 16 模块**，48044 job。

   ⚠ **零件已齐，接起来所缺的只剩 #7 的显式常数**——没有平面 `L⁴` 界，
   转移论证无从起步。#7 路线明确但改动在 RiemannDynamics 代码里，正等 Zulip 回复。

   剩：#1 的稠密性、#6 的下半平面与核定义、#7、以及 #8 的其余四块。
   **#7 已不再是门**（见上，有明确路线且数字清过 10 个数量级）。
   **#8 `BeurlingTransfer` 是唯一剩下的门**，已拆成 #8a–#8e
   （见 [施工计划 §10](../docs/periodic-beltrami-formalization-plan.md)）：
   #8a 已证；#8b/#8c 是常规工作量；**#8d 的三重嵌套极限是真正的长活**；
   #8e 卡着 #1 的稠密性。关键路径 = **#1 稠密性 → #8b → #8c → #8d → #8e**。

2. **一条线上的一个数**（2026-09-16 已压缩）。原先写成"半平面上的显式一致界"，
   其实**不必单独认证**：修正项若是自己在高度 δ 处采样的非负 Fourier 重建，几何因子
   `exp(−2π(Im z − δ))` 会把一条线上的系数界自动传遍整个半平面。
   `ReconstructionBounds.theta_reconstruct_close_of_height` ＋
   `ReconstructionRepresentation.nonempty_upperRepresentation_of_reconstruction` 给出全有理常数的链条：
   δ=1/10、c=1/5、ρ=1/10 ⟹ Q=62/100、bound=33/1000、**rate=67/100 < 1**、radius=1/8。
   再经 `CentredCoefficient`（非零模的核积分为零），输入退化成**一条线上的一个中心化 sup 界**
   `‖g t − b‖ ≤ 1/50`（`nonempty_upperRepresentation_of_centred_sample`），
   正是 `docs/certify_theta_fourier.py` 计算的量；rate 离 1 还有三分之一余量，常数差几倍也不影响。
   仍需把已认证的 `|θ_p − a₀| < 0.02` 从**中心多项式**传到真正的 θ_F
   （`inverseTheta_close_of_lipschitz` 已备好骨架）。
3. ~~**`hlink`**~~ —— **已消除**（2026-09-16）。`ReconstructionIdentity.theta_eq_reconstruct`
   证了"上半平面上全纯 ＋ 1-周期 ＋ 有界 ⟹ 等于自己从任一高度作出的非负重建"，
   而修正项的 1-周期性由 §2 的第 3 点白给。于是
   `RepresentationComplete.nonempty_upperRepresentation_of_analytic_data` 给出**无循环假设**的形态，
   假设只剩**六条**：`c < 1/10`、解析性、逆支沿函数方程平移一格、有界、
   一条中心化 sup 界 `‖θ − b‖ ≤ 1/50`、逆支恒等式。
   （系数可和性由有界性推出，采样可积性由解析性推出，都不再是假设。）

注意**解析性那一条不是缺口**：§8 已把 θ_F 延拓到整个 `Im z > 0.08`——水平方向靠周期性
（`R_A=(−0.51,0.51)+i(0.08,0.325)` 宽 1.02 > 1，整数平移铺满水平带），
上方靠 `W(z)=χ⁻¹(z)+θ_p(χ⁻¹(z))`（`Im z > 0.3+D`）接住，重叠区由恒等定理相等。

后果：§4、§5 的**提升**（而非 §5 的 Abel 高度结论）以及最终身份仍条件于上述两条定量输入。
§3 不受影响：低段只用缝合界 α。

### 墙 B（几何侧）：**已拆除**

原判断是："mathlib 完全没有 winding number／辐角原理／Rouché／黎曼映射定理，
§7 的绕数计数无法照搬，只能自建 winding number（月级工程）"。

**这个判断被推翻了。** `Kneser/StripCovering.lean`（34 条定理，已审计）
**直接证出了 `StripPreimageUnique`**，而且用的路子比覆叠空间还短：

1. 单叶 ⟹ 开条带的像是**开集**（`InjectiveDeriv` ＋ 已有的开映射引理）；
2. 真正性（properness）⟹ 像在目标里**相对闭**；
3. 目标 `openStandardRegion L`＝"开半平面 ∩ 开圆盘"是**凸集**，故连通，且像非空；
4. 开 ＋ 相对闭 ＋ 非空 ⟹ 像就是全部 ⟹ 满射；配上单叶即 `∃!`。

**绕数、覆叠映射、单连通性一个都没用上**——纤维有限、均匀覆盖邻域、单值性、道路提升全部蒸发。
（顺带查清：mathlib 其实**有** `IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn`，
即"真正的局部同胚 ⟹ 覆叠映射"，之前判断它缺失是错的；但这条路线用不上它。）

`StripEscape` 随后也被 `StripEscapeProof`（14 条定理）**证成了定理**：
`stripEscape_of_limits`（纯度量拓扑）＋ `stripLowerLimit_of_upper`（实对称反射）
＋ `stripUpperLimit_of_highChartCover`（就是 `CrossSection` 的一致极限沿 χ 搬运）。

### 墙 B 的第二块砖：`StripValuesInStandardRegion` 也已拆除（2026-09-15）

原判断是："条带整体映入标准区域缺曲边条带的极大值原理，mathlib 的 Phragmén–Lindelöf
几何不适用"。**这个判断同样被推翻了——根本不需要 Phragmén–Lindelöf。**

`Kneser/StripMaximum.lean`（9 条定理）＋ `Kneser/StripRegion.lean`（5 条）＋
`Kneser/StripRegionBridge.lean`（6 条，共 24 条，已审计）走的是截断路线：

1. 在高度 `|Im z| < Y` 处截断，得到**有界开集** `truncStrip g Y`；
2. 其边界只有四段：两条长边（由边界恒等式 (7) 定死）＋ 高度 `±Y` 的两条横截面
   （由 `StripUpperLimit` / `StripLowerLimit` 控到 `‖L‖+ε`）；
3. 对有界集用 mathlib 的普通极大模原理 `Complex.norm_le_of_forall_mem_frontier_norm_le`，
   再令 `Y → ∞`、`ε → 0`，得 `‖F‖ ≤ ‖L‖`；
4. **实部下界是同一条定理作用在 `exp (-F)` 上**：`‖exp(-F z)‖ = exp(-Re F z)`，
   极大模界就是实部的极小界。不需要单独的调和函数极小原理。
5. 两条 `≠`（`F z ≠ L`、`F z ≠ star L`）由开条带上的**严格**极大模原理
   （`Complex.eqOn_closure_of_isPreconnected_of_isMaxOn_norm`，配开条带的连通性
   `openGraphStrip_isPreconnected`）＋ 边界上的严格不等式给出；非常值性由
   `InjOn F (graphStrip g)` 白给。

代价是把一条隐含的 §2 数据写成显式假设：左边界的像**严格落在**标准区域的直边内部，
即 `|Im F(ζ t)| < |Im L|`（文档 §2 的 γ(t)=a+it, t∈(−b,b) 正是这条）。右边界随即由
`F(z+1)=exp F(z)` 落在圆弧 `‖w‖=‖L‖` 上且 `Re > Re L`（用到 `|Im L| ≤ π`，
对认证不动点由 `certified_exp_fixed_point_abs_im_le_pi` 证出）。

### 墙 B 的第三、四块砖：闭条带导数与逆支解析性（2026-09-15）

`ArgumentPrincipleCertificate` 还有两个字段原本没有证明：`StripDerivNeZero`
（闭条带上 `deriv F ≠ 0`，原只证了开条带）与 `StripAbelAnalytic`（逆支跨过两条边解析延拓）。
两条都已证掉，关键是同一个观察：**F 在三倍条带上单叶**。

`Kneser/StripDeriv.lean`（双条带 `S ∪ (S+1)`）先给出：`exp` 在标准区域上单叶
（区域含于半径 `‖L‖` 的圆盘且 `Re ≥ Re L ≥ 0`，故 `|Im| ≤ |Im L| < π`），于是 `S+1` 上的
`F = exp ∘ F ∘ (·−1)` 也单叶；两半只能在缝上相碰，因为模界只在右边界取到、实部界只在左边界取到。

`Kneser/StripInverse.lean` 把它推到 **三倍条带** `Ω = {g−1 < Re z < g+2}`，靠值的三分离：

- 左边（`Re z < g`）：`F(z+1) = exp F(z)` 的模 `< ‖L‖`，故 `Re F z < Re L`；
- 条带上：`Re F z ≥ Re L`；
- 右边（`Re z > g+1`）：`F z = exp u`、`u` 在标准区域，
  `Re(exp u) = e^{Re u} cos(Im u) ≥ e^{Re L} cos(Im L) = Re L`（用到 `Re L > 0` 使 `cos Im L > 0`）。

因为闭条带含于 `Ω` 的内部，`invFunOn F Ω` 一步就是标准区域某个开邻域上的解析函数——
**不需要沿两条边粘接局部逆支，也不需要同一性定理**。于是
`tripleAbel_analytic` 给出 `StripAbelAnalytic`，`openTripleStrip_deriv_ne_zero` 给出
`StripDerivNeZero`，`stripBijection_of_boundary_data` 直接产出完整的 `StripBijection`。

### §7 现在需要什么

§7 一条独立几何义务都不剩了。`StripBijection` 的输入退化为下面这些（`RouteAssembly`）：

| 输入 | 内容 | 来源 |
|---|---|---|
| `StripUpperLimit` / `StripLowerLimit` | 两端一致极限 | 由 `StripHighChartCover` ＋ 反射得到（`StripEscapeProof`）；`StripHighChartCover` 仍开放，且条件于墙 A |
| `InjOn F (graphStrip g)` | 闭条带单叶 | 上半部 `representation_injOn_region`、下半部反射、中间带需缝合 |
| `AnalyticOnNhd ℂ F slitDomain` ＋ `F(z+1)=exp F(z)` | 解析性与函数方程 | 解析构造（qc 那篇）的结论，Lean 侧无实例 |
| `\|Im F(ζ t)\| < \|Im L\|` | 左边界像严格落在直边内部 | §2 的 γ(t)=a+it, t∈(−b,b)；建议加成 `LiftedEdge` 的字段 |
| `exp L = L`、`0 < Re L`、`\|Im L\| < π` | 不动点事实 | 认证不动点已证：`certified_exp_fixed_point_equation`／`_re_pos`／`_abs_im_lt_pi` |
| `F 0 = 1` | 归一化 | 构造给出 |

`StripEscape`、`StripEdgeExterior`、`StripDerivNeZero`、`StripValuesInStandardRegion`、
`StripAbelAnalytic`、`StripPreimageUnique` 全部是定理。

端到端：`canonicalRoute_of_boundary_data`（上述输入 ⟹ `CanonicalRoute`）、
`identity_of_boundary_data`（两边各有这套数据 ⟹ 割线平面上 `F = K`）。

`StripEdgeExterior` 不是独立假设（由 `StripValuesInStandardRegion` ＋ 函数方程导出）；
`StripDerivNeZero` 已由 `InjectiveDeriv` 证掉；`StripAbelAnalytic` 只剩边界延拓。

## 3. 数字

一次性审计（`audit/geometric-route-grand-result.json`）：

> **24941 条定理、492 个模块，全部通过；只用 `propext`／`Classical.choice`／`Quot.sound`。**

构成：§4 的 202 格域/高度证书 15157 条、202 格 Abel 增量证书 8713 条、
§3 的 64 格与链条约 900 条、其余骨架与工具（§5 端点、§6 横截面、§7 条带、
单叶⟹导数非零、表示式单叶性、拼接装配）约 200 条。
生成代码合计约 30 MB，全部为**候选**——每条不等式都由 Lean 内核在精确有理数上重算。

整个项目（`lake build` 默认目标，42811 个 job）现已包含本轮全部模块。

2026-09-15 新增的六个条带模块单独审计（`audit/strip-region-result.json`）：
**61 条定理、6 个模块（`StripMaximum`、`StripRegion`、`StripRegionBridge`、`StripDeriv`、
`StripInverse`、`RouteAssembly`），无 `sorry`、无自定义公理、无 `native_decide`**，
复现：`lake build Kneser.RouteAssembly` 后
`python3 audit_modules.py --name strip-region --module StripMaximum --module StripRegion --module StripRegionBridge --module StripDeriv --module StripInverse --module RouteAssembly`。
这六个模块不含任何数值证书，全部是一般定理（截断集拓扑、极大模原理、区域几何、逆函数定理）。

2026-09-16 新增的**墙 A 归约**六个模块单独审计（`audit/wall-a-reduction-result.json`）：
**74 条定理、14 个模块（`DiscBoundaryModes`、`DiscBoundaryConverse`、`ThetaGluingBridge`、`PeriodicBandFourier`、
`ReconstructionBounds`、`CentredCoefficient`、`ReconstructionRepresentation`、
`ReconstructionIdentity`、`QExpansionBridge`、`RepresentationComplete`、
`HalfPlaneDerivBound`、`RepresentationFromInverse`、`InverseThetaModes`、`WallAReductionWitness`），
无 `sorry`、无自定义公理、无 `native_decide`**，复现：

```sh
python3 audit_modules.py --name wall-a-reduction \
  --module DiscBoundaryModes --module DiscBoundaryConverse --module ThetaGluingBridge \
  --module PeriodicBandFourier --module ReconstructionBounds --module CentredCoefficient \
  --module ReconstructionRepresentation --module ReconstructionIdentity \
  --module QExpansionBridge --module RepresentationComplete \
  --module HalfPlaneDerivBound --module RepresentationFromInverse --module InverseThetaModes \
  --module WallAReductionWitness
```

同样不含数值证书，全部是一般定理（圆周柯西、矩形柯西与围道上移、Schwarz 型导数估计、
结构装配）。并入根导入后全项目 `lake build` 为 **48000 job**（新增的 mathlib 依赖
`Analysis.Complex.CauchyIntegral` / `Analysis.Complex.Schwarz` 抬高了 job 数）。
2026-09-16 再并入经典路线第六步的正规形五模块后为 **48025 job**，
并入"排除双曲情形"的三模块后为 **48028 job**。

## 4. 下一步（按性价比）

1. **`StripHighChartCover`**——两端极限的唯一来源，形式是"χ 把 u-条带的高处映满条带高处"。
   与 `chart_covers_impossible_of_bounded` 的反例不冲突（那条用的是负高度点）。
2. **闭条带单叶 `InjOn F (graphStrip g)` 的中间带**——上下半部已有，缝合段缺。
3. **三段拼接成 `LiftedEdge`**——`EdgeSplice.liftedEdge_curve_fields` 已备好接口，
   等 §4 单调性与 §5 的提升高度就位；同时应把左边界的严格内部性
   `|Im F(ζ t)| < |Im L|` 作为字段加进 `LiftedEdge`（现在是 `RouteAssembly` 的外部假设；
   注意它会否掉 `constantLiftedEdge` 这个平凡例子，这正说明它有内容）。
3. **墙 A 的新形状**——不再是 `ThetaExactGluing`（见 §2 与
   [docs/wall-a-reduction-zh.md](../docs/wall-a-reduction-zh.md)）。
   定量侧已压缩成**采样线上一个数**（`‖c_{n+1}‖ ≤ 1/50`），全有理常数链条已在
   `ReconstructionRepresentation` 里跑通（rate=67/100 < 1）。
   **当前性价比最高的一步**是把 `|θ_p − a₀| < 0.02` 从中心多项式传到真正的 θ_F
   （骨架 `inverseTheta_close_of_lipschitz` 已备好，代入 `L_A<2.343` 与 `‖F−p‖<2.878e-30`）。
   ~~(ii) 兑现 `hlink`~~ —— **2026-09-16 已消除**，见 §2 第 3 点：
   `ReconstructionIdentity.theta_eq_reconstruct` ＋ 修正项的 1-周期性给出
   `RepresentationComplete.nonempty_upperRepresentation_of_analytic_data`，
   无循环假设，假设只剩六条。
   §4、§5 的提升与最终身份仍条件于上面那一步。

   **关于最终身份能否在 Lean 内闭合**（2026-09-17 与 §2 同步并实查 mathlib）：
   按 §2 的 2026-09-17 查证，§8 所依赖的**可测**黎曼映射定理（Ahlfors–Bers）
   不在 mathlib 中，但第三方 RiemannDynamics 已有实现；本项目仍须接入依赖并补齐
   周期化与定量估计。这是**本项目所选路线**的接入工作，不是 Kneser 定理的障碍——Kneser 1950 原证第六步用的是
   **经典** RMT（见 [docs/kneser-classical-route-zh.md](../docs/kneser-classical-route-zh.md)）。
   **所以"最终身份定理不可能在 Lean 内闭合"这个说法已撤回**，与 §2 一致。
   但撤回后的准确表述不是"卡在一个在途 PR"，实查如下：

   - mathlib master 有 `Mathlib/Analysis/Complex/RiemannMapping.lean`，但仅 6.5 KB，
     只含 step 1（`exists_injective_not_dense_image_deriv_ne_zero`）与
     step 2（`exists_mapsTo_unitBall_injOn_deriv_ne_zero`），两条都标 `private`，无 `sorry`。
   - 该文件 docstring 原文：完整证明在 PR #33505，
     *"though it may fail to compile with the latest Mathlib"*，正拆成一系列小 PR 合并。
   - **PR #33505 仍是 draft、未合并**。作者 urkud，开于 2026-01-03，
     最后更新 **2026-05-20**——已停滞四个月。

   即：经典 RMT **不在 mathlib 里**，其面向 mathlib 的完整证明存在于一个停滞四个月、
   作者自陈可能已无法对当前 mathlib 编译的 draft PR 中。对外表述应当这样写，
   既不说"不可能闭合"，也不说"在途并入"。

   ⚠ 但**不要因此认为 Lean 里没有 RMT**：mathlib 之外另有
   [vbeffara/RMT4](https://github.com/vbeffara/RMT4)（经典 RMT）与
   [will1491/RiemannDynamics](https://github.com/will1491/RiemannDynamics)（**可测** RMT，
   sorry-free），见 §2 的"外部已有的 Lean 资产"。PR #33505 的死活只决定
   **mathlib 内**何时有这条，不决定本项目能否推进。
   第六步所需的其余成分（Möbius 自同构识别、上半平面正规形、排除双曲情形）本轮已补齐，
   只剩见证函数的构造，它留在假设位置上，没有被公理化。

墙 B（"缺绕数／缺曲边条带的极大值原理"）作为**方法论障碍**已经消失：
`StripPreimageUnique`、`StripEscape`、`StripEdgeExterior`、`StripDerivNeZero`、
`StripValuesInStandardRegion` 全是定理，绕数、覆叠映射、Phragmén–Lindelöf 一个都没用上。
剩下的 `StripHighChartCover` 不是"缺工具"，而是一条关于 χ 的具体覆盖事实，
且它本身条件于墙 A 的 `UpperRepresentation`。
