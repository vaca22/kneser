# 计划：把「迭代的双坐标理论」从一个内核加两个计划，整理成一套理论

2026-10-07。起因是对 [theory-framework-zh.md](theory-framework-zh.md) 的审美评估，结论是：
内核（双坐标、焊接、汇流到 `h⁻¹`）已经够优美；阻碍整体优美的有五处。本计划逐条处理，
每一项都写明交付物与验收标准。状态标记沿用 [证]/[证·机]/[推]/[数]/[猜]/[否]。

| # | 问题 | 交付物 | 验收标准 |
|---|---|---|---|
| P1 | 定位：tetration 被当成主角，其实它是一般理论的第一个例子 | 新的核心文档 [theory-core-zh.md](theory-core-zh.md)：以「实鞍结开折的参数化分数迭代」为题，一条主定理串起 A′–E′、命题 G 和 P2 的新结果；tetration 降为例子一章 | 主定理的陈述不超过一屏；每一条结论都带状态标记和出处 |
| P2 | 最关键的常数 `κ⁽ⁿ⁾` 只是一个数（Q3/Q11） | 一阶项的**变分公式**：`κ⁽ⁿ⁾` 拆成「芽的普适常数」加「horn 映射沿开折方向的 Melnikov 导数」。写出陈述、证明梗概和数值验证 | 在 tetration 与至少一个非指数族上，公式两边的数值吻合到 10 位以上；附可复现脚本 |
| P3 | 层数轴和高度轴硬挂在旁边 | 在核心文档里降为「应用与开放问题」；明确写出它们和内核之间**没有**定理联系，只有类比 | 核心文档中三根轴不再并列 |
| P4 | 记号一字多用（ε、τ、a、h、κ） | 核心文档使用一套一字一义的记号，附新旧对照表；同步到 [general-statements-zh.md](general-statements-zh.md) 的读法说明 | 核心文档中每个字母只有一个含义 |
| P5 | Lean 层的定理陈述一屏放不下（约 30 个参数） | 新模块 `lean/Kneser/Interface.lean`：把实际构造打包进一个结构，主定理的陈述在 10 行以内，证明直接调用现有终点；把未提交的 `GluedOriginalResult.lean` 简化构建通过 | 全工程构建通过；`check.py` 审计通过（无 sorry、无自定义公理）；新入口加入审计清单 |

## P2 的数学思路（实施前写下，便于事后对照）

设 `g(u) = u + a₂u² + a₃u³ + …` 是抛物芽，开折 `f_s = g − s·h + O(s²)`，`γ = h(0) > 0`。

1. **无穷小共轭不改变 Re κ。** 共轭 `u ↦ u + sφ(u)` 在一阶上把 `h` 换成 `h + Lφ`，
   其中 `Lφ = φ∘g − g′·φ`。它只移动基点，由命题 G，只改变 `κ` 的虚部。
   取 `φ ≡ c = h′(0)/(2a₂)`，可把 `h` 的一次项消掉：
   `h̃ = h + c(1 − g′) = γ + O(u²)`。
2. **两参数族。** 令 `X₁ = h̃ − γ = O(u²)`，考虑 `G_{s,t} = (g − t X₁) − sγ`。
   对每个 `t`，`g_t = g − t X₁` 仍是抛物芽（乘子 1），`G_{s,t}` 是它的平移开折。若展开对 `t` 一致，则沿对角线 `t = s`：
   ```
   4a₂γ · κ⁽ⁿ⁾[g; h] = 4a₂γ · κ⁽ⁿ⁾[g; 1] + ∂_t log(Bₙ e^{2πinα})(g_t) |_{t=0}   （Re 部分严格成立）
   ```
   其中 `α = Φ_att(u*)` 是基点的 Fatou 坐标值。
3. **右端第二项是 Melnikov 和。** 变分方程 `Φ̇(u) = Φ̇(g(u)) − Φ′(g(u)) X₁(u)` 沿轨道迭代，
   `X₁ = O(u²)` 时，每一项 `Φ′(u_{k+1}) X₁(u_k)` 是 `O(1)`，因此需要用形式 Abel 函数 `α_t` 的显式变分做正则化。
   `a₂`、`ρ` 随 `t` 变化，这一点由 `α̇_t` 精确承担。
4. **结论的形状**：`Re κ⁽ⁿ⁾` 是开折方向 `h` 的仿射函数，在上同调类上取值；
   它不可能只由芽的数据（`Bₙ`、`α`、`ρ`）给出闭式，因为同一个芽的不同开折给出不同的 `Re κ`。
   这在负面意义上回答了 Q3；Q11 则被约化为一个普适常数 `Kₙ(g) := κ⁽ⁿ⁾[g; 1]`。

数值检验用 tetration `g = eᵘ − 1`、`h = (1+u)eᵘ`，于是 `X₁ = (u−1)eᵘ + 1`；
并直接比较同一芽的两个开折 `g − s` 与 `g − s(1+u)eᵘ`。

## 执行顺序

1. P5 交给后台子代理（Lean 构建很慢，与其余各项独立）。
2. P2 先做数值，再写证明梗概。
3. P1、P3、P4 合并为一份核心文档，在 P2 有结论后写。
4. 收尾：更新 [theory-framework-zh.md](theory-framework-zh.md) 的开放问题表（Q3、Q11），在 README 中加入口，提交。

## 执行记录

**P2（完成）.** [kappa-variation-zh.md](kappa-variation-zh.md)，脚本 [kappa_variation.py](kappa_variation.py)。
变分公式 `κ⁽ⁿ⁾[g; X] = κ⁽ⁿ⁾_tr(g) + (𝓜_n(g)[X₁] − 2πincΦ′_att(u*))/(4a₂γ)` 在两个芽（`eᵘ−1`、`u+u²`）、
五个开折方向上，两条独立代码路径吻合到 1e−17（n=1）、1e−13（n=2）、1e−9（n=3），超过验收标准。
意外收获：tetration 的底数方向是上边界（`X₁ = −L(u)`），所以论文的 `Re κ` 就是指数芽的普适常数。
证明是梗概：「定理 E′ 关于芽参数一致」逐行核查过，但没有重写，列为开放问题 C2。

**P1、P3、P4（完成）.** [theory-core-zh.md](theory-core-zh.md)。主定理五条 (i)–(v) 写在一屏内；
层数与高度方向移到 §6「应用与开放问题」，并写明它们和核心之间缺哪一条定理；
§1.2 是一字一义的记号表，附旧写法对照（horn 映射 `h^{±1} → 𝔥^{±1}`，`κ_n → Ξ_n`，`κ_b → 𝒦_b`，层数 `s → ℓ`，`ε` 只表示 `1 − λ₁`）。
开放问题重新编号为 C1–C5（核心）、T1–T3（tetration）、A1–A5（应用）。
旧文 [theory-framework-zh.md](theory-framework-zh.md) 加了指向新入口的说明，Q3、Q11 更新；
[general-statements-zh.md](general-statements-zh.md) §2.7 加了后续链接；README 加了入口。
**P4b（完成，应作者要求）.** 投稿论文 [paper-submission/main.tex](paper-submission/main.tex) 与 [sec-general.tex](paper-submission/sec-general.tex) 的记号同步修改。
论文原先自列的六个一字多用（ε、τ、a、h、s、κ）全部消除，「Symbols with more than one use」一节换成「Conventions」：
`ε = 1 − λ`（W2–char 节原来的 `ε = |log λ|` 改为显式写 `|log λ|`）；排斥 Koenigs 映射 `τ → σ_rep`，`T − id − t₀` 记为 `T°`；
`log b` 由 `a` 改为 `ℒ`（双周期一节的 `−log b` 记为 `ℳ`）；horn 映射 `h^{±1} → 𝔥^{±1}`，其余局部的 `h`（qc 共轭 `h_λ, h_m → 𝒬`）改名；
`s(b) → s_*(b)`，尖点节的插值参数 `s → 𝗋`，全局节的 `s = Log λ → 𝔰`，接缝映射 `s_θ → 𝗌_θ`；`κ_b → 𝒦_b`，`κ_n → Ξ_n`。
用 tectonic 编译通过，警告与修改前相同（11 条 hyperref 书签警告）。`main-full.tex` 与 `main-general-draft` 未改。
核心文档的记号表随之与论文对齐（周期仍记 `h`，基点 Fatou 值仍记 `a`，变分方向记 `X₁`）。

**P5（完成）.** 新模块 [lean/Kneser/Interface.lean](../lean/Kneser/Interface.lean)：
结构 `SewnTetrationFamily` 用可读的名字打包实际构造（底数、不动点、`p`、粘合函数 `K`、`τ`、`Λ`、horn 基线 `B`、`κ`），
字段 `realized` 保证它们就是 `GluedResultData` 里的同一组对象，没有另选。
主定理 `exists_sewn_tetration`（一阶）和 `exists_sewn_tetration_all_orders`（任意阶）的陈述各约 8 行，
由现有终点直接推出。未提交的 `GluedOriginalResult.lean` 简化原本编译不过（`uIcc` 成员关系的写法），已最小修复，简化意图保留。
复核：`python3 check.py` 输出 `PASS: 1994 theorems/lemmas in 323 built modules; allowed axioms only.`
审计增加了标志 `readable_interface_bundles_same_glued_family`。

**第二轮：把一阶项做成严格定理（2026-10-07，目标「优美理论，完美」）.**
- **C2 解决。** 变分公式改用抛物层 `𝒫`（有二重不动点的映射）上的导数来表述和证明：
  `κ⁽ⁿ⁾ = κ⁽ⁿ⁾_tr(g) + 𝒟_n(g)[X − X(0)]/(4a₂X(0))`。`T_g𝒫 = {Y : Y(0)=0}`，定理 D 的导数公式对方向是线性的，
  在 `𝒫` 上它就是真导数，所以不再需要「关于芽参数一致」。写入论文 [sec-general.tex](paper-submission/sec-general.tex)
  §「The first-order term as a derivative on the parabolic stratum」（Lemma gen-banach、Proposition gen-linear、
  Theorem gen-variation、Corollary gen-variation、Remarks gen-cocycle 与 gen-variation）。
- **对抗审稿。** 结论是 0 个 FATAL、1 个 MAJOR（上游 (H3) 的符号应为 `γ = +∂_μ f`；论文和
  [general-statements-zh.md](general-statements-zh.md) 均已改正），十余个 MINOR 已全部落实。
- **C1 重新表述。** `κ_tr` 不是芽的不变量，在坐标变换下按上闭链变化（Remark gen-cocycle）。
  数值核对：`ψ(u)=u+0.3u²` 把 `Re κ⁽¹⁾_tr` 从 −0.0101990 变为 −2.8764956，公式的预测吻合到 3e−17
  （[kappa_cocycle.py](kappa_cocycle.py)，[data/kappa-cocycle.txt](data/kappa-cocycle.txt)）。
- **horn 变分的轨道级数**（原 §2.5 只有推导）已实现并验证：与有限差分吻合到 1e−16（n=1）。
