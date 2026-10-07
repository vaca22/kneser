# 实际指数族、全局 horn 与 Fourier 缝合的 Lean 证明

本工程从论文的实际指数族

\[
f_s(u)=\exp(-s+(1-s)u)-1
\]

构造两侧轨道坐标、同一个移动逆映射、实际基点 `e⁻¹−1`、规范全局上端
horn、Koenigs 转移和 Fourier 缝合。缝合的真实积分系数除以实际指数尺度后，
具有同一乘子参数的任意阶展开；一阶系数由抛物轨道上的绝对收敛级数显式给出。

审计统计与源码指纹以 [审计记录](audit/first-order-result.json) 为准。
2026-10-07 的最终全工程检查通过：323 个模块、1994 条命名定理及引理；
源码与配置指纹一致，9 个锁定依赖的跟踪文件均干净。
`Kneser.lean` 导入全部模块，`check.py` 构建整个工程并逐条检查命名定理及引理的
公理依赖。最终存在性入口从实际指数函数构造数据，不要求用户提供坐标存在性、
级数收敛、逆图、Fourier 衰减或缝合误差。**对数和模式比值只在相应零参数
系数非零时断言；本工程尚未认证论文的 `B₁≠0` 数值证书。**

## 可读入口

底层终点量化约三十个辅助对象，难以直接阅读。[Interface.lean](Kneser/Interface.lean)
把同一个实际构造打包为结构 `Kneser.Interface.SewnTetrationFamily`：参数区间 `(0,s₀)`、
底数 `b(s)=exp((1-s)/e)`、实不动点 `L₁<e<L₂` 与乘子 `λᵢ=log b·Lᵢ`、
`p(s)=-log λ₁ log λ₂`（解析芽，`p(0)=0,p'(0)=2`）、两侧粘合函数 `K_s` 及其开放域、
周期线积分 `τₙ(s)`、尺度 `Λ(s)=exp(4π²/log λ₁)`（在零点平坦）、规范 horn `G` 与基线 `Bₙ`、
显式一阶系数 `κₙ=dₙ/(2tₙ)-πi n d₀` 和一致的任意阶展开。字段 `realized` 记录这些可读对象
就是 `GluedResultData` 中的同一组对象，不另选。主定理：

```lean
theorem exists_sewn_tetration :
    ∃ F : SewnTetrationFamily,
      (∀ s ∈ Ioo 0 F.s₀, F.K s 0 = 1 ∧
        ∀ z ∈ F.domain s, z + 1 ∈ F.domain s ∧ F.K s (z + 1) = (tetrationBase s : ℂ) ^ F.K s z) ∧
      F.p 0 = 0 ∧ HasDerivAt F.p 2 0 ∧
      ∀ n : ℕ, 1 ≤ n → F.B n ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
        ‖log (F.τ s n / (F.Λ s : ℂ) ^ n / F.B n) - F.κ n * F.p s‖ ≤ C * ‖F.p s‖ ^ 2
```

任意阶版本为 `exists_sewn_tetration_all_orders`，结构存在性为 `exists_sewnTetrationFamily`。
模块文档同样写明未覆盖的内容：经典 Kneser 身份、完整复参数续接、`B₁≠0` 等数值证书；
修正 `D` 的显式轨道级数未在接口中重述，只通过 `realized` 钉到 `physicalCorrection`。

## 主结果与核对入口

原变量主入口是 [OriginalMainResult.lean](Kneser/OriginalMainResult.lean) 中的
`exists_actual_original_first_order_result`。它使用真实底数
`b(s)=exp((1-s)/e)`，并在包含零点的实际开放域证明
`K(0)=1`、`K(z+1)=exp(log(b(s))*K(z))`，以及同一组见证的真实积分系数、
一阶修正和所有有限阶展开。全纯性、定义域和积分线均随同保留。
完整两侧粘合及其原变量积分见
[ActualGluedPhysicalSewing.lean](Kneser/ActualGluedPhysicalSewing.lean) 与
[GluedOriginalResult.lean](Kneser/GluedOriginalResult.lean) 的无前提终点
`exists_actual_glued_original_result`。下图包含整个下半平面，
上图保留真实 Koenigs 逆域的切口；重叠区函数精确相等。

归一化物理函数入口是 [PhysicalMainResult.lean](Kneser/PhysicalMainResult.lean) 中的
`exists_actual_physical_first_order_result`。它保留同一组实际准备、根、逆映射、
缝合函数和真实积分线，同时给出规范 horn 基线、真实乘子参数及一阶公式。
非零条件精确等价于规范全局 horn 的模式非零。
任意阶版本为 [ActualPhysicalSewnCoefficients.lean](Kneser/ActualPhysicalSewnCoefficients.lean) 的
`exists_actual_physical_sewn_coefficients`。时间坐标的终点另见
[MainResult.lean](Kneser/MainResult.lean) 与 [ActualSewnAllOrders.lean](Kneser/ActualSewnAllOrders.lean)。

| 入口 | 已证明的连接 |
|---|---|
| [ActualFourierExpansion](Kneser/ActualFourierExpansion.lean) | 两侧与真实基点的绝对收敛轨道级数，完整积分门区，所有整数模式的显式一阶修正 |
| [ActualAllOrderHornParameter](Kneser/ActualAllOrderHornParameter.lean) | 同一归一化转移、同一移动逆图的全阶展开及一致的系数序列 |
| [ActualAllOrderUpperHornBaseline](Kneser/ActualAllOrderUpperHornBaseline.lean) | 零参数转移与规范全局 upper horn 的精确识别 |
| [ActualUpperHornCoefficientIdentification](Kneser/ActualUpperHornCoefficientIdentification.lean) | 真实积分系数等于规范 horn 的 Fourier 系数及其实际基点相位 |
| [ActualGlobalHornFamily](Kneser/ActualGlobalHornFamily.lean) | 同一局部全阶族与正参数 Koenigs 规范化的增长条带转移完全一致 |
| [NormalizedGrowingFourier](Kneser/NormalizedGrowingFourier.lean) | 实际增长条带的全纯性、周期性、全部模式指数衰减与 Fourier 重构 |
| [ActualNormalizedSewing](Kneser/ActualNormalizedSewing.lean) | 真实 Fourier 收缩、缝合修正、规范平移及真实积分系数的 `O(Λ)` 比较 |
| [ActualGlobalSewingIdentification](Kneser/ActualGlobalSewingIdentification.lean) | 同一缝合与局部全阶族的全部非零规范系数精确相等，尺度等于真实乘子定义的 Λ |
| [ActualOrderedLambdaFlatness](Kneser/ActualOrderedLambdaFlatness.lean) | 每个实际有序根对的 Λ 小于任意参数幂 |
| [FlatSewingLogTransfer](Kneser/FlatSewingLogTransfer.lean) | 指数小误差保留整个一致的对数系数序列；极限及正确对数分支均推导 |
| [ActualSewnModeRatios](Kneser/ActualSewnModeRatios.lean) | 模式比值中的尺度精确消去，全阶系数相容，一阶的均值项消去 |
| [ActualSewingTimeAtlas](Kneser/ActualSewingTimeAtlas.lean) | 同一组缝合修正的两侧单射、解析逆图、覆盖、平移与真实接缝 |
| [ActualRegularKoenigsInverse](Kneser/ActualRegularKoenigsInverse.lean) | 真吸引盆地上的单叶 Koenigs 坐标、实际逆域、周期、Abel 方程、锚点与镜头识别 |
| [ActualEntireRepellingCoordinate](Kneser/ActualEntireRepellingCoordinate.lean) | 真逆迭代 Koenigs 级数生成整函数 S，并与同一镜头逆图精确一致；真实 Abel 方程和虚周期 |
| [ActualPhysicalSewnCoefficients](Kneser/ActualPhysicalSewnCoefficients.lean) | 同一物理函数的规范 Koenigs–Abel 升举积分精确等于缝合系数；显式一阶与全部阶数均传递 |
| [ActualBaseTetration](Kneser/ActualBaseTetration.lean) | 真实底数与仿射共轭，还原原变量的锚点 1 和迭代方程；原变量规范升举与全部 Fourier 积分精确相等 |
| [ActualGluedPhysicalSewing](Kneser/ActualGluedPhysicalSewing.lean) | 同一实际 R 与整函数 S 的两侧物理粘合；开放域、锚点、全纯性和 Abel 方程，原积分域上的身份不变 |
| [GluedOriginalResult](Kneser/GluedOriginalResult.lean) | 同一两侧原变量函数的真实周期积分、规范 horn 基线、乘子参数、显式一阶和一致任意阶展开 |

## 参数、显式系数与任意阶余项

实际有序不动点记为 `aₛ<0<bₛ`，乘子为 `λ₁,λ₂`。同一参数满足

\[
p(s)=-\log\lambda_1\log\lambda_2,\qquad p(0)=0,\quad p'(0)=2.
\]

准备中的参数与选定缝合族的真实根乘子精确一致，见
[ActualOrderedParameterIdentification](Kneser/ActualOrderedParameterIdentification.lean)。

令 `tₙ(s)` 是同一个转移的水平积分系数，`dₙ` 是其显式修正的积分系数。
在同一坐标原点下写 `Bₙ=tₙ(0)`。对 `Bₙ≠0`，

\[
\tau_n(s)=t_n(s)e^{-2\pi i n t_0(s)},\qquad
\kappa_n=\frac{d_n}{2B_n}-\pi i n d_0.
\]

显式空间修正保留排斥坐标的真实基点项：

\[
D(w)=\dot A(v)-\dot A(u_*)-T'_0(w)\bigl(\dot S(v)-\dot S(p')\bigr).
\]

两侧导数和实际锚点运输值均由绝对收敛的真实轨道级数给出；逐项微分、参数估计
与导数尾界已证明。见 [ActualRealNormalizedFirstCoefficient](Kneser/ActualRealNormalizedFirstCoefficient.lean)。

令 `cₙ(s)` 是规范化后缝合时间坐标的真实 Fourier 积分，`ĉₙ=cₙ/Λⁿ`；
零参数值取其已证明的规范 horn 极限。存在同一个系数序列 `αₙ,j`，任意有限 `m` 满足

\[
\log\frac{\widehat c_n(s)}{\widehat c_n(0)}
=\sum_{j=1}^{m}\alpha_{n,j}p(s)^j+O(|p(s)|^{m+1}),\qquad
\alpha_{n,1}=\kappa_n.
\]

一阶终点因此具有 `O(|p|²)` 余项。常数可依赖于模式；没有断言所有模式的对数余项
共用一个常数。模式比值的一阶系数为

\[
\kappa_n-n\kappa_1=\frac{d_n}{2B_n}-\frac{n d_1}{2B_1}.
\]

## 物理函数与论文完成范围

真实物理逆映射只在已证明的开放逆域使用，保留切口。实际 R 满足
`R(0)=e⁻¹−1`、真实虚周期和水平 Abel 方程，并与增长镜头中的逆图精确一致。
同一缝合族的接缝由物理坐标证明；时间坐标在零点为零本身不足以推出物理锚点值。

工程从真正的有限迭代构造 [Poincare 整延拓](Kneser/PoincareEntireExtension.lean)，
并已用真实逆迭代 Koenigs 级数实例化，得到整个复平面上的实际排斥函数 S。
它与增长镜头逆图精确一致，不需要假设该身份。泛型模块的局部解析图与局部方程
前提，在 [ActualEntireRepellingCoordinate](Kneser/ActualEntireRepellingCoordinate.lean) 的链中证明。

实际 R 的逆域包含完整右半平面，因此存在一个真正可用的整数周期积分线。
在这条线上，物理函数的主值 Koenigs–Abel 升举精确等于同一缝合时间坐标，
全部整数模式的积分也精确相等；不把指数身份的模虚周期歧义留作假设。

最后通过已证明的仿射共轭 `x=e(1+u)` 还原论文的原变量。对足够小的正参数，
`1<b(s)<exp(1/e)`；原变量的 Koenigs 坐标归一化于 `x=1`。
新主终点的系数是这个实际 `K` 的升举积分，和前述物理系数作为整个参数函数
精确相等，没有另选 Fourier 家庭或在证明中代换对象。
实际两侧粘合进一步把上侧函数接到整函数 S 的下侧图，在两图并域证明全纯与
迭代方程。同一完整粘合函数的升举积分在已证明的周期线上精确等于原积分，
所以其显式一阶及所有有限阶展开也保留同一系数序列。

**当前结果尚不等于整篇论文已经形式化。** 尚需闭合经典 Kneser uniformization 的独立身份、
完整复参数续接与全局单值性，以及指定模式的非零性和计算机辅助数值证书。
审计中的 `full_kneser_identity_formalized` 与 `full_paper_first_order_formalized`
保持 `false`，直到完整命题真的证明。当前实际缝合采用充分常数 `ρ=1,M=4,D=64`；
不把它说成论文 W2 的字面常数 `ρ=1/4`。

## 复现与公理审计

安装 `elan`、Git 和 Python 3，在本目录执行：

```bash
lake exe cache get
python3 check.py
```

Lean 固定为 `v4.34.0-rc2`，全部 9 个依赖由清单锁定；mathlib 提交为
`7d4b13faab401bc39c856208befd63c5bb7b3615`。缓存仅用于构建加速。

审计扫描全部源码，拒绝 `sorry`、`admit`、自定义 `axiom`、`native_decide` 与 `unsafe`；
逐条执行 `#print axioms`，只允许 `propext`、`Classical.choice`、`Quot.sound`。
它检查完整入口清单、源码与配置指纹、编译器版本、依赖提交与依赖跟踪文件干净状态。
审计期间源码变化或任何失败都不会留下本轮 PASS。

本工程独立于仓库忽略的旧 `formal/`。本轮未修改 LaTeX 原稿；对象身份、定义域
和真实前提实例化均在 Lean 源码中核对。
