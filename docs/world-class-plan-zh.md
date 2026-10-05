# 通往世界级结果的四条线：计划书

> **2026-09-12 接手审计更新：以下保留原研究计划，不代表其中的猜想或“已有”论断已获验证。**
> 目标 1 的共同半直线全阶正性条件已被严格反证；目标 4 的 Hardy 域唯一性方向也有明确反例。
> 目标 2 尚未建立自然边界；目标 3 已进一步完成 base-e 非线性有限维球收缩证书，
> 但到真正 Kneser 解的误差界仍未完成，见 [新证书](theta-nonlinear-certificate.md)。
> 结论、验证和下一步见 [接手结果总览](world-class-results-zh.md)，不要再把原计划的成功判据当作既成定理。

> 起点（2026-09-12）：kneser 0.3.3——全基底平面的 tetration 计算库（Kneser θ-映射 / 实正则 /
> 抛物 Fatou / 复正则 / 双不动点延拓），η 接合定理（凸性证明，docs/proof-eta-junction.md），
> 区间算术证书（docs/error-certificate.md），基底延拓数值（docs/paulsen-continuation-zh.md）。
> 这些是可靠的起跳点，但每条都还差决定性一步。本计划书给出四个目标、里程碑、成功判据和
> **放弃判据**。所有数值在 galic 上跑；证明文档分段写。

## 目标 1：Kneser tetration 的 Bohr–Mollerup 型刻画

**问题。** Γ 由对数凸性唯一选出（Bohr–Mollerup 1922）。Kneser 的 sexp 至今只有复平面刻画
（Trappmann–Kouznetsov：上下半平面趋向共轭不动点）。是否存在只用实轴条件的刻画？

**已有。** a < η 时我们证明了：凸 Abel 函数唯一到常数（proof-eta-junction.md 引理 4.1）。
a > η 时凸性不够：任意小的 1-周期 θ 给出 F(z+θ(z))，仍凸、仍解析、仍满足方程。

**猜想 1.1。** a > η 时，sexp 是满足 sexp^{(n)}(z) > 0（∀ n ≥ 1，z > −2 的某个半直线上）的唯一解，
且它就是 Kneser 解。（"完全单调型"条件排除周期扰动：θ 的任何非零 Fourier 模最终会让某阶导数变号。）

**里程碑。**
- M1.1（数值，判生死）：用 50 位表检验 base e、2 与 17 位表 base 3、10 的 sexp^{(n)}，n ≤ 30，
  在 [−1.5, 3] 上的符号；再检验扰动解 F(z + ε sin 2πz) 在哪一阶变号。若 Kneser 解本身在低阶就变号，
  猜想死，改找替代条件（如 slog 的完全单调、或 log-convexity 的高阶版本）。
- M1.2（理论）：证明"任意非零周期扰动破坏条件"（扰动方向）；这是 Bohr–Mollerup 证明的
  对应部分，应可做。
- M1.3（理论，难）：证明 Kneser 解本身满足条件——需要上半平面表示（Cauchy 积分或
  Kouznetsov 的积分表示）推出导数正性。
- **成功判据**：M1.2 + M1.3 ⇒ 定理。**放弃判据**：M1.1 显示 Kneser 解在 n ≤ 30 内变号且找不到
  替代条件。

## 目标 2：基底方向的解析性：Shell–Thron 边界是延拓还是自然边界

**问题。** 延拓实验（paulsen-continuation-zh.md）给出张力：差 D(b) = K(b) − R(b) 在 1.3+0.3i
非零、沿 Im b → 0 以 exp(−6/Im b) 塌缩、在实点各阶为零。若 D 在 b 上解析，反射原理迫使 D ≡ 0。
所以要么 K(b) 在基底方向不解析，要么 (1, η) 是自然边界。哪个成立是新结果。

**里程碑。**
- M2.1：在区内一个圆 |b − b₀| = r（b₀ = 1.3+0.5i, r = 0.15）上取 N 个基底建 12 位表，
  对固定 z 用 Cauchy 积分检验 K(b; z) 的解析性（∮ K db = 0，∮ K/(b−b₁) db = 2πi K(b₁)）。
- M2.2：把圆推向实轴（b₀ = 1.3+0.2i, r=0.15 触及 Im b = 0.05），看 Cauchy 恒等式何时失效。
- M2.3：沿 Im b → 0 拟合 D 的衰减律 exp(−c/Im b)，c 是否与 b₀ 无关；给出自然边界假说的
  精确表述（K 在 Shell–Thron 区内解析、在 (1, η) 上有边值 = R，但不能越过）。
- M2.4（理论）：若数值支持自然边界：证明 D 在区内非零但沿实轴平坦，与解析性相容的唯一可能是
  区外与区内的 K 不是同一解析函数（θ-映射在越过边界时换了不动点分支）。写成命题。
- **成功判据**：M2.1–2.3 给出一致图景 + M2.4 的命题。**放弃判据**：区内 Cauchy 检验失败
  （K 本身在区内不解析，说明双不动点构造在吸引情形不是解析族）。

## 目标 3：θ-迭代的显式收缩常数（把数字变成定理）

**问题。** 证书证明了残差 ≤ 7e-52，但残差不能约束到真解的距离（θ 自由度）。缺的是：
θ-迭代算子 T 在合适的范数下是压缩映射，压缩常数 κ 有显式上界，从而 |表 − Kneser 解| ≤ 残差/(1−κ)·C。

**里程碑。**
- M3.1：把 T 写成算子：θ ↦ 由 superf(z+θ) 经 Cauchy 积分再经 isuperf 得到的新 θ；写出线性化 DT。
- M3.2：数值估计 DT 的谱半径（base e），与经验律 κ ≈ 0.017 + δ/2π 对照；用 galic 做 DT 的
  有限维近似（Fourier 模截断）。
- M3.3：理论上界：|DT| ≤ C·e^{−2π δ}·(线性化误差) 型的估计；哪怕只在 Fourier 模截断的有限维
  空间里严格，也把"表到真解的距离"变成可证的数。
- **成功判据**：M3.3 的一个严格不等式 + 区间算术验证。**放弃判据**：DT 的谱半径数值上不小于 1
  （说明收敛靠的是别的机制，压缩论证不成立）。

## 目标 4：接到 Hardy 域 / transseries

**问题。** Aschenbrenner–van den Dries–van der Hoeven 的 transseries 理论没有 exp^{1/2}；
Boshernitzan (1986) 证明存在 Hardy 域含超指数函数，但没说哪一个是"自然"的。问：Kneser 的
sexp（或 half_exp）的实轴芽是否生成一个 Hardy 域？若是，Kneser 解是否是唯一使之成立的 tetration？

**里程碑。**
- M4.1（文献）：精确写出 Hardy 域定义、Boshernitzan 定理、ADH 关于超指数的结论；找出
  "Kneser 解在 Hardy 域中"需要什么（由 sexp 及其导数生成的微分域中每个元素最终单调/非零）。
- M4.2：证明部分结果：例如 ℝ(z, sexp, sexp', …) 中的元素在 +∞ 附近最终非零——这需要
  sexp 的导数的渐近展开（超指数增长下多项式关系最终由最高增长项主导）。
- M4.3：唯一性方向：若 F = sexp∘(id+θ) 且 θ 非零周期，则由 F 生成的域不是 Hardy 域
  （周期扰动产生无穷多零点）——这个方向与目标 1 的 M1.2 同源，可共用。
- **成功判据**：M4.2 + M4.3 ⇒ "Kneser 解是唯一生成 Hardy 域的 tetration"。
  **放弃判据**：M4.2 的最终非零性有反例（某个多项式关系在 sexp 的导数间无穷次为零）。

## 执行

四条线同时开，各自独立文件：
- 目标 1 → docs/bohr-mollerup-zh.md + docs/demo_derivative_signs.py（+ 证明 docs/proof-bohr-mollerup.md）
- 目标 2 → docs/base-analyticity-zh.md + docs/demo_base_cauchy.py
- 目标 3 → docs/theta-contraction.md + docs/demo_theta_operator.py
- 目标 4 → docs/hardy-field.md
每条线的报告必须先写"证了什么 / 没证什么 / 数值说了什么"，再写过程。
