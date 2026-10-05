# 超运算研究的领域规模与价值评估

核对日期：2026-09-17 · 引用数据来自 OpenAlex 与 Semantic Scholar API 实时查询

---

## 领域规模：作为独立方向，人极少

全球认真做超运算/迭代半群的大概只有几十人量级。以下数字均为本次实查，不是估计。

### 引用量

| 文献 | 年 | 发表处 | OpenAlex | Semantic Scholar |
| --- | --- | --- | --- | --- |
| Kneser, *Reelle analytische Lösungen der Gleichung ϑ(ϑ(x))=eˣ* | 1950 | J. reine angew. Math. 187, 56–67 | 26 | 44 |
| Kouznetsov, *Solution of F(z+1)=exp(F(z)) in complex z-plane* | 2009 | Math. Comp. | 14 | 无记录 |
| Kouznetsov & Trappmann, *Portrait of the four regular super-exponentials to base √2* | 2010 | Math. Comp. 79, 1727–1756 | 9 | — |
| Kouznetsov & Trappmann, *Computation of the two regular super-exponentials to base exp(1/e)* | 2012 | Math. Comp. | 7 | — |
| Paulsen & Cowgill, *Solving F(z+1)=b^F(z) in the complex plane* | 2017 | **Adv. Comput. Math. 43(6), 1261–1282** | 3 | 0 |
| Paulsen, *Tetration for complex bases* | 2018 | Adv. Comput. Math. 45(1), 243–267 | 2 | — |

Kneser 1950 距今 76 年，引用量仍停在两位数。这是整个领域的奠基文献。

> **更正**：Paulsen–Cowgill 2017 发表在 *Advances in Computational Mathematics*
> (DOI [10.1007/s10444-017-9524-1](https://doi.org/10.1007/s10444-017-9524-1))，
> 不是 *Aequationes Mathematicae*。该文的结果是：对任意 b > e^(1/e)，
> 找到迫使 Kneser 解唯一的自然条件，回答了 Trappmann–Kouznetsov 的猜想。

### 文献总量

OpenAlex 全库中标题含 "tetration" 的著作共 **75** 篇（有史以来全部，含误命中，例如 1965 年一篇化学论文 "Microanalytical Redox Tetrations" 是拼写错误）。含 "hyperoperation" 的 117 篇。注意 OpenAlex 的 `title.search` 是分词匹配不是短语匹配，这两个数字是上界。

### 社区

tetrationforum（`math.eretrandre.org/tetrationforum` 现 301 重定向到 `tetrationforum.org`）：

- 注册成员 **224**
- 主题 **1,434**，帖子 **10,604**
- 最新帖 **2026-09-14**（Computation 版，用户 bo198214）

论坛还活着，但注册总量 224 人已经是这个领域线上聚集的天花板。

#### 成员构成与该怎么用它（2026-09-17 补）

⚠ 人员身份与职业背景一段是**转述**，未逐条核实；标注「✔ 已核」的是本次实查。

| 人 | 位置 |
|---|---|
| Henryk Trappmann（ID `bo198214`） | 论坛创办者；与 Kouznetsov 合作的正式论文见上表 |
| Dmitrii Kouznetsov | 物理背景；Math. Comp. 2009/2010/2012 |
| Sheldon Levenson（`sheldonison`） | 工程师出身，PARI/GP 复底数 Kneser 型实现，被正式论文引为参考 |
| Gottfried Helms | 矩阵（Carleman）方法的大量数值探索 |
| James Nixon（`JmsNxn`） | 分析方向，arXiv 有系列文章 ✔ 已核，见下 |
| `MphLee` | 超版主，结构/算子视角（层数延拓的归约就出自他）✔ 已核 |
| **William Paulsen**（Arkansas State University） | **唯一的学院派主力**；与 Cowgill 2017 的唯一性定理是本领域最硬的定理之一 |

**真正的大数学家在隔壁，不在论坛里。** 核心工具——Écalle 的抛物迭代、
Lavaurs/Shishikura 的抛物内爆、Milnor 的复动力系统教材、Baker 的迭代理论——
全部出自复动力系统主流。那些人研究 `e^z` 的迭代，但不关心「幂塔」这个名字。
**论坛的位置是：拿主流复动力系统的工具，去啃一个主流圈子没兴趣专门啃的问题。**

**长处**：近二十年的数值实验、构造、图像、猜想积累，对入门者极友好。
**短处**：严格证明少，大量结论停在「数值上看起来成立」；至今没有统一各家技术的综合。

**结论性的用法**：把论坛当**矿区地图与同好聚集地**——查别人试过哪些路、
提问、交流数值；但**判断标准与证明工具向正规复动力系统文献看齐**，
真做出结果投正规期刊，不是只发在论坛里。

---

## 三条有分量的外部连接

超运算的价值全部来自它接入的三个成熟领域。

| 连接 | 具体接口 | 对 halfexp 的含义 |
| --- | --- | --- |
| 复动力系统 | Abel 函数、Fatou 坐标、抛物型不动点的 implosion；Écalle / Shishikura / Douady–Hubbard 的核心机器 | 墙 A 归约到可测黎曼映射定理，说明这不是民科趣味，是复动力学里一个具体而困难的边界问题 |
| 增长率 / Hardy 域 / transseries | Aschenbrenner–van den Dries–van der Hoeven, *Asymptotic Differential Algebra and Model Theory of Transseries* (Princeton UP, 2017)，OpenAlex 引用 54；接壤 o-minimality 与模型论 | 半指数函数不在 log-exp 类里是定理级事实；halfexp 要造的正是域外的对象 |
| 复杂性理论 | Miltersen–Vinodchandran–Watanabe, COCOON 1999，OpenAlex 53 / S2 66 | 电路下界文献里 half-exponential 是**形式占位符**：只要求 f(f(n)) ≈ 2ⁿ，从不指定是哪一个 f |

### Hardy 域那条，已核实

标准结论：若 f 由四则运算、指数、对数和实常数构成（即 Hardy 的 log-exp 类 H^LE），则 f∘f 要么次指数要么超指数增长——Hardy L-函数不可能是半指数的。使这个不可能性证明成立的关键刚性是 Hardy 域的增长率三分律：同一 Hardy 域中两个最终为正的函数必居 f ≺ g、f ∼ g、f ≻ g 之一，这迫使候选 f 落在确定的"指数深度"上，自复合必然过冲或欠冲。

transseries 语言下的对应陈述：解 E(x+1) = exp E(x) 需要把 𝕋 扩张到含 exp 的迭代子 exp_ω x 的带复合 transseries 域——整个迭代层级住在 𝕋 之外。

Kneser 构造本身反而给出一个高一层的真正 Hardy 域对象：实解析的 e_ω 满足 e_ω(x+1) = exp e_ω(x)，其在 +∞ 的芽落在某个 Hardy 域中，但增长快于任何迭代指数。

### 复杂性理论那条值得展开

复杂性理论避开具体选取，正是因为大家知道自然的选取问题没解决。这是一个真实存在、被明确回避的缺口。如果 halfexp 能给出典范选取加上好的解析性质，那不是补充美感，是补一个被写进论文脚注的洞。

---

## 对 halfexp 项目的价值排序

三个已有部分的价值差距很大，从高到低：

1. **Lean 形式化是唯一一个稀缺性明确的方向**。mathlib 里 Abel 方程、迭代半群、拟共形映射几乎是空白。形式化 Kneser 这种量级的复分析定理，价值不在超运算圈子（那里没人看 Lean），在形式化数学圈子（那里正缺硬的复分析样例）。**具体要形式化什么，见下一节**——初稿这条写得太笼统，项目实际已有 24,941 条已审计定理，问题不是"要不要形式化"而是"还剩什么、哪些能上游"。

2. **结构性分离结论价值次高**。例如"(1,η) 不是自然边界，但 Kneser 延拓的边界值也不是正则解"。这是关于构造本身的事实，是别人没说过的话。Λ = exp(4π²/logλ) 这种"尺度是被逼出来的"陈述，如果能证明，能写进论文。

3. **纯数值/实验部分价值最低**。Kouznetsov 早就把 tetration 的高精度计算做完了（Math. Comp. 2009 / 2010 / 2012 三篇），再算一遍不构成贡献。已修掉的 dps=30 bug、残差 5e-22、f'(0)=0.8763 这些是工具不是成果。

第 1 条和第 2 条的受众不重叠。这意味着实际上有两个可投的方向，而不是一个。

---

## Lean 形式化：具体要形式化什么

依据 `kneser/formal/GEOMETRIC-ROUTE-STATUS.md`（2026-09-16 修订）逐条核对，外加对 mathlib 侧的实查。

### 现状基线

一次性审计 `audit/geometric-route-grand-result.json`：**24,941 条定理、492 个模块全部通过**，只用 `propext` / `Classical.choice` / `Quot.sound`，无 `sorry`、无自定义公理、无 `native_decide`。`lake build` 默认目标 48,028 个 job。

但这个数字要拆开看：其中 §4 的 202 格域/高度证书 15,157 条、202 格 Abel 增量证书 8,713 条，加 §3 的 64 格约 900 条——**约 24,700 条是生成的数值证书，约 30 MB**。真正可复用的一般定理在 200 条量级，加上几个专题模块（条带几何 61 条、墙 A 归约 74 条、正规形 25 条、双曲排除 19 条、Möbius 自同构 35 条）。

这个拆分决定了后面所有判断：对 mathlib 有价值的是那几百条，不是那两万多条。

### 还剩什么（项目内部义务）

链条现在是：

```
LiftedEdge F L  +  边界数据
      ↓  canonicalRoute_of_boundary_data
CanonicalRoute F L → GraphAbelChart → EqOn F F_K slitDomain
```

末端两步已证。剩下四项：

| # | 义务 | 现状 | 卡在哪 |
| --- | --- | --- | --- |
| 1 | `StripHighChartCover` | 开放 | 两端极限的唯一来源，形式是"χ 把 u-条带高处映满条带高处"。与 `chart_covers_impossible_of_bounded` 的反例不冲突（那条用负高度点）。**条件于墙 A** |
| 2 | `InjOn F (graphStrip g)` 中间带 | 上下半部已证 | 上半部走 `representation_injOn_region`，下半部靠实对称反射，缝合段缺 |
| 3 | 三段拼接成 `LiftedEdge` | 接口已备 | `EdgeSplice.liftedEdge_curve_fields` 等 §4 单调性与 §5 提升高度就位；同时应把 `\|Im F(ζt)\| < \|Im L\|` 加成 `LiftedEdge` 字段（它会否掉 `constantLiftedEdge` 这个平凡例，正说明它有内容） |
| 4 | 墙 A 的定量输入 | 骨架已备 | 把 `\|θ_p − a₀\| < 0.02` 从中心多项式传到真正的 θ_F：`inverseTheta_close_of_lipschitz`，代入 `L_A < 2.343` 与 `‖F − p‖ < 2.878e-30` |

第 4 条是整个墙 A 压缩后的剩余物，值得单独说清楚：墙 A 曾被判为"`ThetaExactGluing` 那条公开未解决的无限方程组"，**这个判断已被推翻**。`ThetaGluingBridge.thetaExactGluing_of_discExtension` 用圆周柯西定理把整族负模条件一次性归约成"边界数据是闭圆盘上连续、内部全纯的函数的边界值"，而且 `DiscBoundaryConverse.disc_extension_iff_negative_modes_zero` 证明这个归约是**充要**的。经 `ReconstructionRepresentation` 与 `CentredCoefficient` 逐步压缩后，全部实数输入退化成**一条采样线上的一个中心化 sup 界** `‖g t − b‖ ≤ 1/50`，有理常数链条已跑通（δ=1/10、c=1/5、ρ=1/10 ⟹ rate=67/100 < 1，离 1 有三分之一余量）。

### 外部依赖：黎曼映射定理的真实状态（重要修正）

`GEOMETRIC-ROUTE-STATUS.md` §2 写"经典 RMT 的完整 Lean 证明已存在（mathlib PR #33505，在途并入）"，据此把"Lean 内不可能闭合"的说法撤回，改述为"卡在一个在途 PR 加一批常规工作"。

实查结果（2026-09-17）：

- mathlib master **确实有** `Mathlib/Analysis/Complex/RiemannMapping.lean`，但只有 6.5 KB，仅含 **step 1**（`exists_injective_not_dense_image_deriv_ne_zero`）与 **step 2**（`exists_mapsTo_unitBall_injOn_deriv_ne_zero`），两条都标了 `private`，无 `sorry`。
- 该文件的 docstring 原文说明：完整证明在 PR #33505，*"though it may fail to compile with the latest Mathlib"*，正在拆成一系列小 PR 合并。
- **PR #33505 仍是 draft，未合并**。作者 urkud（Yury Kudryashov），开于 2026-01-03，最后更新 **2026-05-20**——距今已停滞四个月。

所以"在途并入"偏乐观。准确表述是：**RMT 不在 mathlib 里；面向 mathlib 的完整证明存在于一个停滞四个月、且作者自陈可能已无法对当前 mathlib 编译的 draft PR 中；两个前置步骤已落地。**

### 但 mathlib 之外，Lean 里已经有了（2026-09-17 查证）

这条比上面那条重要得多，它推翻的是项目状态文档里"可测 RMT 可预见时间内也不会有"的判断：

| 仓库 | 内容 | 状态 |
| --- | --- | --- |
| [will1491/RiemannDynamics](https://github.com/will1491/RiemannDynamics) | **可测黎曼映射定理（MRMT）**、Uniformization、No Wandering Domain、拟共形映射、Teichmüller 基础 | Lean v4.33.0，下游于 mathlib v4.33.0 + RMT4 + Carleson；作者自述 sorry-free、只用三条标准公理；2026-08-17 仍在推送 |
| [vbeffara/RMT4](https://github.com/vbeffara/RMT4) | **经典**黎曼映射定理 | 独立于 PR #33505 的另一份实现；2026-01-10 最后推送 |

MRMT 已核到文件级：`QC/MRMT/Existence.lean` 921 行、**0 个 `sorry`**、含 `mrmt_exists`；`QC/MRMT/Uniqueness.lean` 542 行、0 个 `sorry`、含 `mrmt_unique_normalized`；另有 `AnalyticDependence.lean`、`NeumannSeries/`、`SmoothCase/`。

来源是 `#mathlib4 > Geometry and complex dynamics formalization`，Will (Ziang) Li 2026-08-10 发帖宣布并希望上游。

**后果**：§3–§6 的 qc 构造不再因为"Lean 里没有 MRMT"而不可行，原路线可能根本不必绕道经典路线。工具链距离很近（本项目 v4.32.0，RiemannDynamics v4.33.0）。代价是依赖第三方仓库（单个小组维护、star 个位数），不是 mathlib 的稳定性保证。

### 状态文档内部有两处自相矛盾

对外表述前应当先修掉：

1. **`hlink`**：§2 第 3 点写"已消除（2026-09-16）"，理由是 `ReconstructionIdentity.theta_eq_reconstruct` 加上修正项的 1-周期性；§4"下一步"第 3 条却仍写"(ii) 兑现 `hlink`（负模全零已证，只差 Fourier 反演）"。
2. **能否闭合**：§2 写"'Lean 内不可能闭合'这个说法应当撤回"；§4 末尾仍写"最终身份定理目前仍不可能在 Lean 内闭合——这一点必须在任何对外表述里讲清楚"。

两处都是 §4 相对 §2 未同步。第 2 处尤其要紧，因为它正好是最容易被外部引用的一句话。

### 真正可上游 mathlib 的独立件

这些的价值不依赖 Kneser 最终身份是否闭合，是本项目对形式化数学圈子最直接的产出：

1. **`DiscTwoPointVanishing` / `UpperHalfTwoPointVanishing`**（19 条，`audit/hyperbolic-exclusion-result.json`）——有界全纯、在圆周除两点外边界极限为零 ⟹ 恒零。走"乘 `(z−p)(z−q)` 后闭圆盘上连续、普通极大模原理以 C=0 打完"，**不需要任何边界唯一性理论**（Fatou / Privalov / F.&M. Riesz，mathlib 全无）。这条独立价值最高：它给的是一条绕开 mathlib 空白的证法，不只是一个结论。
2. **`InjectiveDeriv.analytic_injOn_deriv_ne_zero`**——开集上单叶解析 ⟹ 导数处处非零。项目标注 mathlib 没有；我在 mathlib 代码搜索中未找到对应引理（非穷尽检索，上游前应再确认一次）。mathlib 的 RMT step 2 是存在性陈述 `exists_mapsTo_unitBall_injOn_deriv_ne_zero`，不是这条蕴涵。
3. **条带几何六模块**（`StripMaximum` / `StripRegion` / `StripRegionBridge` / `StripDeriv` / `StripInverse` / `RouteAssembly`，61 条，无数值证书）——用"截断成有界开集 + mathlib 普通极大模原理 + 令 Y→∞"替代曲边条带的 Phragmén–Lindelöf；实部下界由同一条定理作用在 `exp(−F)` 上得到，不需要单独的调和函数极小原理。手法通用。
4. **上半平面自同构正规形五模块**（`RealMoebiusMap` / `MoebiusFixedPoint` / `ParabolicNormalForm` / `HyperbolicNormalForm` / `UpperHalfNormalForm`，25 条）加 Möbius 自同构四模块（`BlaschkeFactor` / `DiscRotation` / `CayleyTransform` / `DiscAutomorphism`，35 条）——把无内点不动点的自同构归一化成 `ζ↦ζ+1`。这是标准教科书内容但 mathlib 缺。
5. **`DiscBoundaryConverse.disc_extension_iff_negative_modes_zero`**——圆盘全纯延拓 ⟺ 负模全零，充要形式。

注意第 5 条的"一半" mathlib 已有：上半带全纯 + 1-周期 + 有界 ⟹ 负模全零，就是模形式的 q-展开（`UpperHalfPlane.hasSum_qExpansion` / `qExpansion_coeff_eq_intervalIntegral`），项目已用 `QExpansionBridge` 改走桥接。上游时要把重叠部分剥干净。

### 建议的次序

按"不依赖外部 PR、且受众明确"排：

1. 先上游第 1 条（两点消失定理）。它完全独立，且填的是 mathlib 一个真实空白。
2. 同时推进内部义务 2 和 3（缝合段单叶 + `LiftedEdge` 拼接）——这两条不依赖墙 A，做完能把 §3 的"最强表述"从 `[−0.32, 0.32]` 延到整个 `(−b, b)`。
3. 内部义务 4（θ_F 的 Lipschitz 传递）是墙 A 的最后一步，性价比高但要等 2、3。
4. `StripHighChartCover` 排最后，因为它条件于墙 A。
5. RMT 那条**不要等 mathlib**。PR #33505 的死活只决定 mathlib 内何时有这条，不决定本项目能否推进——Lean 里已经有 RMT4（经典）和 RiemannDynamics（可测）。

   签名对照**已做**（2026-09-17，完整对照表见 `kneser/formal/GEOMETRIC-ROUTE-STATUS.md` §2）。结论：`mrmt_exists` 与 §5 的需求在一个点上精确吻合且承重——theta-periodic-beltrami.md §4 证 χ 是同胚时用的那个"平面拟共形坐标 q"就是它，可直接 `obtain`。周期性与实对称能从 `mrmt_unique_normalized` 推出。但**显式常数预算拿不到**：对方的 `beurling_lp_bound` 里 C 是存在量词，而 §2 要的是 Bañuelos–Janakiraman 的显式 `‖B‖_{L⁴} < 12`，整条 `12k < 1` 收缩与 `D = 40k/(1−12k)` 全靠它；圆柱算子 `B_per` 与周期 Cauchy 势对方也没有。另有指数错配（`IsQCAnalytic` 是 W^{1,2}，周期引理走 W^{1,4}）。

   **净结论**：抬工具链换 MRMT 划算——省掉的是整条链里最重的一块——但周期 Beltrami 定理仍要自己形式化，MRMT 只进去当其中一个引理。

> 已发出的两个询问（2026-09-17，待回复）：
> [PR #33505 comment](https://github.com/leanprover-community/mathlib4/pull/33505#issuecomment-5708040363)（问 PR 是否还活着）；
> Zulip `#mathlib4 > Geometry and complex dynamics formalization` message 624822047（问 MRMT 能否直接依赖）。

---

## 现实判断

如果目标是引用量和职位，这是一个糟糕的选择——看表就知道，领域内最高被引的自有文献是两位数。

如果目标是"做一件确定没人做完、且确实困难"的事，信噪比很好：因为人少所以没被扫荡过，而且困难是真困难（可测黎曼映射定理不是能绕过去的技术细节）。

当前位置：墙 B 已拆完，墙 A 已归约到一个有名字的定理。这比大多数进这个题目的人走得远。

待定的问题：两个受众的产出形式不同（形式化需要可编译的 Lean 库，复分析需要可审稿的论文），优先级尚未决定。

---

## 未能核实的项

- **arXiv 分类与篇数**：export.arxiv.org 的 API 从本机查询返回空响应，超时。原稿中"arXiv 上没有对应主分类、论文通常投 math.CA 或 math.DS"一句因此未经核实，已从正文移除。
- **Semantic Scholar 与 OpenAlex 的差异**：Kneser 1950 两库相差 18（26 vs 44），MVW 1999 相差 13（53 vs 66）。老文献的数字化引用覆盖不全是常态，Google Scholar 通常比两者都高。表中数字应读作下界。

## 来源

- [OpenAlex API](https://api.openalex.org/) — 全部引用数与文献计数
- [Semantic Scholar Graph API](https://api.semanticscholar.org/) — 交叉核对
- [Paulsen & Cowgill 2017, Adv. Comput. Math.](https://doi.org/10.1007/s10444-017-9524-1)
- [Kneser 1950, Crelle 187](https://doi.org/10.1515/crll.1950.187.56)
- [Miltersen–Vinodchandran–Watanabe 1999, COCOON](https://doi.org/10.1007/3-540-48686-0_21)
- [tetrationforum.org](https://tetrationforum.org/index.php) — 成员/帖子统计，读取于 2026-09-17
- [Half-exponential function, Wikipedia](https://en.wikipedia.org/wiki/Half-exponential_function) — Hardy 域不可能性的陈述
- [On Numbers, Germs, and Transseries (ADH)](https://arxiv.org/pdf/1711.06936)
