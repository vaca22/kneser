# 先行工作核查（2026-10-05）

目的：投稿前确认两件事。

1. arXiv:2208.05328 与本文是否重叠。
2. "开折模关于参数的正则性 / 一阶系数"是否已有人做过。

两项检索均由子代理完成，原始 PDF 未入库。

## 1. Nixon, arXiv:2208.05328

*Asymptotic Solutions of the Tetration Equation*，J. D. Nixon，2022，100 页，只有 v1，未发表。

**它做的事：**

- 用无穷复合构造 β 函数，再加修正项 τ，得到 Shell–Thron 内部周期为 2πi/λ 的非正则解族。
- 第 5 章用 1-周期的「θ 映射」比较这些解与正则解：F = tet_b(s+θ(s))。唯一性论证不完整，作者未写成定理。
- 对 b>η 时它与 Kneser 解的关系只停留在推测。
- Cor 4.4.7 指出 β 型构造在 b>η 时沿实轴处处不全纯。

**与本文的重叠：只有写法相同。** 两边都把解写成「正则解 ∘ (id + 1-周期函数)」，这个写法本来就是 tetration 论坛的通行做法。下列内容它全部没有：

- horn map / Écalle–Voronin；
- 两个不动点之间的转移映射（Glutsyuk 模）；
- b→η 的极限、尺度 Λ、系数 B_n；
- 底数方向的延拓、穿越 Shell–Thron 边界、与 Paulsen 族一致。

**处理：** 已在引言加一段引用并说明区别，参考文献新增 `Nixon2022`。

## 2. 开折模的参数正则性

### 必须更正的认识

我们以前说「MRR 2004 §11(1) 问的是可微性，定理 D/E 回答了它」，**这个说法不对**。

MRR 原文证明的是模在 ε=0 处连续，并**猜测**模关于 √ε 是 1-可和的。这个猜测已经被证明了：

- **Christopher–Rousseau**（IMRN 2014，arXiv:0809.2167，Cor 4.9）：在他们的规范 (4.25) 下，模关于 ε 是 1/2-可和的，不可和方向是 Glutsyuk 方向。
- **Ribón**（arXiv:1009.3518，2010）：对任意有限余维的开折，Fatou 坐标和 Écalle–Voronin 不变量关于参数多重可和。

所以「沿 Glutsyuk 方向存在任意阶渐近展开」本身不是新结果。

### 仍然是新的部分

检索范围是 2008–2026 年，重点查了 2024–2026 年，在这个范围内没有找到先例：

- 展开的**系数**，在 τ_n 规范下用抛物点上绝对收敛的级数给出（定理 D/E）；
- 这些系数的高精度数值，κ⁽¹⁾ 到 20 位；
- 一个不依赖可和性理论的直接证明；
- 对任何不可解的族给出 ∂_ε（模）在 ε=0 处的公式或数值。可解情形（Riccati、超几何）有 Γ 函数公式，不适用于 e^u−1。

一个旁证：Rousseau 2022 年的综述（Arnold Math. J.，arXiv:2011.12456）仍然只说模在 ε=0 有「连续极限」。

### 已经确认未预见本文结果的文献

| 方向 | 文献 | 它们做的事 |
|---|---|---|
| 汇流 | Glutsyuk 2001 | 只证明收敛 |
| 汇流 | MRR 2004 及 Addendum | 模在 ε=0 连续 |
| 汇流 | Rousseau–Teyssier 2008 | |
| 汇流 | Rousseau ETDS 2015 / 2025、Nonlinearity 2026 | 分类与实现问题 |
| 汇流 | Godin–Rousseau 2023 / 2025 | 分类与实现问题 |
| 抛物内爆（Lavaurs 侧） | Shishikura、Oudkerk、Chéritat、Buff–Chéritat、Kapiamba、Astorg–Bianchi、Astorg–López-Hernanz–Raissy 2026、Boc Thaler 2026、Zhang | 连续性、速率、几何估计；没有 ε 一阶系数公式 |
| 二次族 c→1/4⁻ | Jaksztas、Havard–Zinsmeister | 维数导数，不涉及模的系数 |
| 超运算 | Kouznetsov–Trappmann、Paulsen–Cowgill、Paulsen 2019/2026、Nesargi–Roudenko、Nixon | 没有一篇把 Kneser 解与 horn map / Glutsyuk 模联系起来 |

### 已对论文所做的修改

- 「Relation to the literature」这条 Remark 改成：
  - MRR 证明了连续性，并猜测 1-可和；
  - CR 证明了这个猜测，Ribón 推广到有限余维；
  - 这些结果给出展开的存在性，本文给出系数和直接证明；
  - 与 Dudko–Sauzin 用收敛数值级数表示 Écalle–Voronin 不变量的做法相对照。
- Open problem 里「不同规范」一句同时引用 CR 和 Ribón。
- 新增参考文献：`Ribon2010`、`DudkoSauzin2014`（CRAS 353 (2015)）、`Nixon2022`。

### 检索的局限

- Semantic Scholar 对 CR 没有返回数据，被引关系只用了 OpenAlex。OpenAlex 覆盖不全，例如 MRR 只列出 34 篇引用。
- MathSciNet、zbMATH、Google Scholar 无法访问。2025–2026 年正式刊出但没有 arXiv 版的论文可能漏检。
- Chéritat 的博士论文、Buff–Chéritat、Inou–Shishikura 中关于扰动 Fatou 坐标展开的细节没有逐页核查。如果存在 **Lavaurs 侧**的一阶公式，最可能出现在这些地方。审稿人可能会问到，届时需要补查。
- Ribón 的论文只读了导言和 §6 的定理陈述。

## 对外表述建议

> 把 Glutsyuk 的汇流理论应用到 Kneser 构造上：证明 Kneser 解与正则解的分离由两图转移映射（Glutsyuk 模）决定，其极限是 e^u−1 的反向 horn map；并给出模沿 Glutsyuk 方向渐近展开的系数公式（展开的存在性由 Christopher–Rousseau / Ribón 的可和性给出）。

**不要说**「发现了转移映射不变量」，也**不要说**「回答了 MRR 的开放问题」。

## 3. Lavaurs 侧补查（同日）

逐页或按关键词核查了以下文献：
- Chéritat 博士论文（207 页全文）
- Buff–Chéritat Annals 2012
- Inou–Shishikura 草稿（2008-12 版）
- Bedford–Smillie–Ueda、Bianchi JEMS 2019
- Astorg–Bianchi 2026（arXiv:2603.27686）
- Kapiamba arXiv:2210.06647 / 2103.03211
- Jaksztas 系列
- Buff–Écalle–Epstein GAFA 2013
- Gelfreich–Brännström arXiv:0806.2403

**结论：Lavaurs 侧没有人给过一阶系数。** 但有三件事要在论文里交代：

1. **存在性在 Lavaurs 侧也已知。** Shishikura 2000 与 Inou–Shishikura（Thm 1.3/2.1）、Kapiamba（Prop 2.13）证明了规范化后的扰动 Fatou 坐标与 horn map 关于扰动全纯依赖，所以展开必然存在。Chéritat 论文里只有周期点"爆炸速度"的一阶量，不是模的一阶量。Buff–Chéritat 2012 只有 O(1/α) 的误差界。Astorg–Bianchi 2026 只有经典 Lavaurs 相位加 o(1)。
2. **最近的类比在保面积映射的分界线分裂文献里。** 这是我们之前没注意到的近邻领域。
   - Gelfreich–Brännström 证明鞍-中心分岔附近的 homoclinic invariant 形如 e^{−2π²/log λ}·Σ a_k δ^{2k}，a₀ 是抛物极限下的 Stokes 常数（Gelfreich–Sauzin 2001 对 Hénon 证明 a₀≠0）。指数小因子与我们的 Λ 同型，级数结构就是"log(τ/τ(0)) 关于参数展开"。
   - Gelfreich–Simó（DCDS-B 10, 2008）用数千位高精度**数值提取**了高阶 a_k。
   - 1:3 共振展开（arXiv:1612.04752）也是同一种形式。
   - 区别：那里只有一个 Fourier 模，对象是二维保面积映射；a_k（k≥1）由辅助问题定义（核对 gb.txt 确认没有显式公式），或者靠数值拟合，不是收敛的轨道级数。
3. **方法上最相近的是 Buff–Écalle–Epstein Prop 9.1。** 它沿轨道逐阶递推，得到 horn map 关于参数的显式展开（系数用 multitangent / 多重 zeta 值表示）。但那里的参数在抛物族内部变动，不把不动点分裂开。

**已对论文所做的修改：** 在"Relation to the literature" Remark 中加了一段，说明 Lavaurs 侧有存在性、分界线分裂的类比、BEE 的方法，以及我们的区别。新增参考文献 InouShishikura、GelfreichBrannstrom、GelfreichSauzin2001、GelfreichSimo2008、BuffEcalleEpstein2013。

**对外表述再收紧一步：** 展开的**存在性**两侧都已知，指数小因子乘以参数级数这种结构在分界线分裂里也有先例。我们新的地方是：
- 对 1 维全纯开折的**所有 Fourier 模**，系数在抛物点上由**绝对收敛的轨道级数**显式给出，并有直接证明；
- 把这些结果用于 Kneser 构造。

**仍未取得全文的：** Shishikura 2000 原文、Lavaurs 与 Oudkerk 的博士论文、Douady 1994、Buff–Chéritat 2004/2006、Jaksztas TAMS 2011、Gelfreich–Simó 2008（只看了摘要）。
