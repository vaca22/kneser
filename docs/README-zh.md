# 研究笔记与随笔（中文）

这里是 `kneser` 库背后的研究记录。**它们不是库的使用文档**——库怎么用见
根目录的 [README.md](../README.md)。这些文件回答的是另一个问题：为什么要
造这个东西，以及用它算出了什么。

所有数值都可由同目录下的 `demo_*.py` 复现，关键恒等式锁在
`tests/test_research.py` 与 `tests/test_research_extensions.py` 里。
运行依赖 FLINT 的区间检查器前，可在项目根目录执行
`python3 -m pip install -e '.[research]'`。

## 研究纲领与实验记录

- [2026-09-26 复现与证据审计](research-audit-2026-09-26.md) —
  一阶模输入快照、二次亏损律的拟合与留一预测、底数精度修复，以及论文与 Lean 审计的纠错。
  附可在干净检出上运行的脚本；二次律仍是数值猜想。
- [Lean 4 形式化](../formal/README-zh.md) —
  5597 条定理已编译并通过公理审计：图形条带类 Abel 唯一性、边界解析拼接、
  曲线几何、圆盘规则、无限尾界、固定点、具体多项式区域界和 Cauchy 范数推导。
  完整 Kneser 身份尚未形式化；
  解析构造和区间包络正确性仍需补齐，不以无 `sorry` 代替前提实例化。
- [mixed-base-lie-algebra-zh.md](mixed-base-lie-algebra-zh.md) —
  混合 e 与 2 的连续迭代：交换子二阶漂移的两个数值零点、零点处仍存的
  三阶漂移，以及由左尾渐近证明的“两个不同 Kneser 底数生成无穷维实李代数”。
  附可复现脚本、原始数据和图；不声称文献首创或全局零点分类。
- [research-program-zh.md](research-program-zh.md) —
  把 Kneser 连续迭代变成一个可做的课题的纲领：迭代几何、连续运算阶、
  复时间、无穷复合方程、Kneser 常数。
- [research-findings-zh.md](research-findings-zh.md) —
  对该纲领的第一轮实验：流生成元 `V` 及其最小值（三个新常数）、
  运算路径 `x +_t y` 的端点斜率证书、虚时间轨道以 `(Re L, Im L)` 速率
  内旋到不动点（15 位吻合）、Carleman 截断开方缓慢收敛到 Kneser 分支、
  theta 迭代收缩率的模型对比、80 位下的 PSLQ 阴性结果。
  六个可运行 demo：`demo_flow_generator.py`、`demo_operation_path.py`、
  `demo_complex_time.py`、`demo_carleman_sqrt.py`、
  `demo_build_contraction.py`、`demo_constants_pslq.py`。
- [lemmas-round2-zh.md](lemmas-round2-zh.md) —
  第二轮：弱猜想 B 写成定理（V 不可加；自对偶对 `(2,2)` 强迫内部极值；
  `(2,3)` 的符号证书）；V 的凸性归约为 `sexp'` 的对数凸性加移位递推；
  虚时间余项界 `O(e^{-2 t Im L})`，由此 `I` 的存在刻画 Kneser 解；
  Carleman 主支开方在 `λx` 与 `e^x-1` 两端标定；收缩率 `κ(δ)` 定位到
  单位圆界面跳跃。Demo：`demo_lemma_b.py`、`demo_v_convex.py`、
  `demo_lemma_i.py`、`demo_kappa_mechanism.py`、`demo_carleman_calibrate.py`。
- [repository-insights-zh.md](repository-insights-zh.md) —
  跨仓库回顾：架构、生产库与历史实验之间的可靠性边界、float64 精度包络、
  已完成的工程加固，以及 `V`、`D_t`、复时间、`f∘f = g` 的有限域可复现实验。

> ⚠️ **术语提醒（2026-08 文献核查结论）**：这些笔记里的"流生成元 V"
> 在文献中的标准名字是 **Julia 方程**（又称 Jabotinsky 方程）的解，
> 即 exp 的**迭代对数** `itlog(exp)`。相关前人工作：Szekeres（对数凸性
> 作为分数次迭代的实变量选择判据）、Kuczma（Abel 方程的凸解）、
> Aschenbrenner–Bergweiler（itlog 的微分超越性——这比本仓库的猜想 D
> 强且已证）。任何对外发表都必须改用这套术语并引用它们。

- [proof-eta-junction.md](proof-eta-junction.md)（英文）— 定理：a ↑ η 时正则超函数 S_a 在 (−2, ∞) 的紧集上一致收敛到抛物解 S_η。
  路线：S_a 在整个定义域上凹（从不动点附近的 Koenigs/Fatou 渐近向左传播）⇒ Abel 函数凸 ⇒ 等度 Lipschitz、Arzelà–Ascoli ⇒
  极限是 E_η 的凸 Abel 函数 ⇒ 由"凸 Abel 函数唯一到常数"引理等于 A_η。仅引用 Koenigs 线性化与 Fatou 坐标的存在/渐近展开。
- [paulsen-continuation-zh.md](paulsen-continuation-zh.md) — 把 Kneser 双不动点解从 base 3 经上半平面延拓回 (1, η)：
  极限是正则解（12 位），区内两者相差按 exp(−6/Im b) 塌缩；附 Schwarz 反射带来的理论张力。脚本 `demo_paulsen_continuation.py`。
- [theta-qc-global-existence.md](theta-qc-global-existence.md) — 周期拟共形修正与逆支桥接，证明完整解析解、全部负模为零及精确无限拼接，距离 <2.878e-30；该阶段留下的规范身份已由后续证明解决。
- [theta-canonical-identity.md](theta-canonical-identity.md) — 最终规范身份：标准直边的完整逆支提升、辐角原理和整数平移覆盖，证明 F=f*=F_K，并将 <2.878e-30 的界识别为真 Kneser 误差。
- [theta-canonical-uniqueness.md](theta-canonical-uniqueness.md) — 规范唯一性判据与先前缺口的历史审计；缺口已由上述标准区域证明补齐。
- [theta-slit-extension.md](theta-slit-extension.md) — 完整上条带符号证书推出割线平面的单值全纯延拓、导数无零点和实轴严格递增。
- [theta-uniqueness-counterexample-audit.md](theta-uniqueness-counterexample-audit.md) — 弱半平面唯一性的全局反例；严格排除复平移和小正弦扰动作为完整实规范反例。
- [theta-periodic-beltrami.md](theta-periodic-beltrami.md) — 完整的周期 Beltrami 无限维辅助定理，含显式全平面位移界、周期化和同胚证明。
- [theta-negative-existence.md](theta-negative-existence.md) — 证明普通 ℓ² 负模残差下的有界 Newton 障碍，将存在性归约为统一留球的有限可行性；附有限阶数值探索。
- [theta-negative-modes.md](theta-negative-modes.md) — 证明全部负 Fourier 模为零足以推出精确拼接，并给出前 16 个负模的区间诊断；无限方程的存在性仍待证明。
- [theta-identity-bridge.md](theta-identity-bridge.md) — 已验证固定点在半径 0.54 圆盘上的单叶与无零点，证明精确局部拼接条件下的全局延拓，并验证一个非主支归一化点；精确拼接和 Kneser 身份仍未闭合。
- [theta-continuous-ball.md](theta-continuous-ball.md) — 已验证连续 θ 算子的无限维整球收缩，q<0.141711、中心到局部理想固定点距离 <8.399e-21；全局 Kneser 身份仍待证明。
- [theta-continuous-consistency.md](theta-continuous-consistency.md) — 已验证中心处连续理想 θ 算子的完整点缺陷 <7.209e-21，覆盖正则深度、两次连续投影与无限 Fourier/Taylor 尾项；后续整球工作见上。
- [theta-regular-depth.md](theta-regular-depth.md) — 正则 Koenigs 极限的显式深度误差，含连续输入域证书与分支、Rouche 验证。
- [theta-infinite-discrete-certificate.md](theta-infinite-discrete-certificate.md) — 固定离散 θ 算子的无限 Taylor 尾部验证：函数球覆盖、四块导数界、完整缺陷与精确有理检查器；与真 Kneser 误差的区别。
- [error-certificate.md](error-certificate.md) — base e/2 系数表的严格误差证书（区间算术）：Horner 误差、接缝缺陷 ≤ 7e-52、
  半整数接缝跳跃、导出量的区间；以及为何残差不能证明与真解的距离。脚本 `demo_certificate.py`，测试 `test_certificate.py`。
- [external-validation.md](external-validation.md) — **对外交叉验证**：与 sheldonison 的 `fatou.gp`（PARI/GP，社区参考实现）
  的独立数值对比，base e/2 烘焙表吻合 52 位、base 10 按需表吻合 19 位——这是本仓库唯一约束 θ 自由度
  （"是不是 Kneser 解"）而非残差的证据。同时记录两件事：Shell–Thron 区内我们给的是正则解而非
  fatou.gp 的双不动点融合解（差 9.5e-5 … 0.14），以及上游参考集里 `sexp|2|0.5|1000` 从第 44 位起是错的。
  并据此新增 `solution="kneser"/"regular"/"auto"` 关键字（区内可取融合解，与 fatou.gp 吻合 1.2e-12）；
  §4 还自行运行 fatou.gp 为区外基底 3+2i / 2+2i / −1+i 生成参考值，第一次从外部验证 `_cbuild`（吻合 ~2e-10）；
  §5 汇总 fatou.gp 自身的边界（Im(base)<0 主动禁用、须用共轭包装；近 Shell–Thron 边界无 θ 映射只有 15–16 位——
  但 2+i 实测排除；`matrix_ir` 线性解法）以及 0.8+0.4i 不收敛的定位（下侧 θ 停在错误的叶，非调参问题）。
  数据 `tests/data/external_reference.json`，测试 `test_external_reference.py`。
- [properties-zh.md](properties-zh.md) — ↑↑ 的性质清单（定理 vs 本仓库数值）：函数方程、奇点、共轭对称、
  三种周期性（正则区精确纯虚周期、区内复基底复周期、Kneser 区只有渐近周期）、基底方向的接合与割线。脚本 `demo_periodicity.py`。
- [base-plane-zh.md](base-plane-zh.md) — 基底取遍全体复数：η 的抛物引擎（正则 → 抛物极限到 13 位吻合）、
  (0,1) 与复基底的复正则引擎（吸引情形规范归一化）、排斥情形为何无规范塔。脚本 `demo_base_plane.py`。
- [base-landscape-zh.md](base-landscape-zh.md) — 把 a ↑↑ b 推广到任意基底 a > 1（η 上方 Kneser、下方正则迭代），
  以及由此挖到的现象：η 处两种构造数值上光滑接合、半指数斜率为 1 的基底 a* = 3.92334123872694829、
  大基底 a↑↑½ ~ ln a。脚本：`demo_base_landscape.py`、`demo_eta_junction.py`；英文技术说明见 [general-base.md](general-base.md)。

## 随笔

- [essay-operation-ladder-zh.md](essay-operation-ladder-zh.md) —
  把运算阶梯延拓到分数与虚数迭代阶：`exp^[i](1)`、介于 + 与 × 之间的运算、
  以及 Aczél 分类如何堵死其余可能。
- [essay-hyperoperation-industry-zh.md](essay-hyperoperation-industry-zh.md) —
  超运算有没有工业应用（2026-10-02 文献核对）：四级及以上没有产线算术；
  分数次迭代有西门子轧钢专利 WO 99/42232 这一次工业试验；
  矩阵根、算子分数幂和 Koopman 模型是已经在跑的同族工具。
- [essay-rank-1000-zh.md](essay-rank-1000-zh.md) —
  「算到第 1000 层」的四种读法（物理禁令、末位数、递归/FGH、解析延拓），
  以及真正开着的方向：把**层数本身**延拓成复变量 `a[s]b`——
  判据五条、`s = 1…6` 锚点表（`e[s]½`，四/五/六级现算），
  以及第一轮筛选：Bennett 族 1:4 出局，定义域定律 `min(a,b) > sexp(s−3)`。
  含文献前置（2026-09-17 实查）：MphLee/bo198214 把层数延拓归约为后继算子 `Σ`
  的分数次迭代、Nixon 的有界解析超运算链（解析的是高度不是层数、底数限于 η 以下）、
  Crespo–Montáns 2016。
  脚本：[demo_rank_interpolation.py](demo_rank_interpolation.py)，
  数据：[rank-anchors.json](rank-anchors.json)。
  第二轮（2026-10-02）：Nixon 的链条就是正则族；底数 1.3 的正则阶梯建到 24 级。
  脚本：[demo_rank_regular.py](demo_rank_regular.py)，
  数据：[rank-anchors-regular.json](rank-anchors-regular.json)。
- [essay-tropical-limit-zh.md](essay-tropical-limit-zh.md) —
  阶梯热带极限的通读稿：折线 `min(1+z, b)`、速率 `(log 2)/L_s`、
  后继缺陷 `log 2·ΔL/L²`、跟踪误差 `u_0/L`、临界底数 `≤ 2`，
  以及速率律模型的 `b_∞ = 2`。解析阶梯的 `b_∞` 仍是 `[1.83976, 2]`。
- [rank-tropical-limit-zh.md](rank-tropical-limit-zh.md) —
  超运算的阶数极限是**热带化**：`1 < b < η` 时 `b[s]z → min(1+z, b)`，
  有限阶是其 log-sum-exp 光滑化（温度 `1/|log λ_s| ≈ (b−1)/log s`）；
  拐点斜率趋于 `1/2`，曲率满足 `−4 S''(b−1)/|log λ_s| → 1`（三个底数在第 24 级都是 `1.01`），
  四阶导数同期是 `0.997 × L^3/8`；离开 `1/2` 的整列导数是闭式对数在偏移 `u_0` 处的逻辑斯蒂（第 24 级 `u_0=0.145`，逐位对上），且 `s u_0 → 1/(b−1)`；
  速率律延到 `s+1/2` 和 `s+it` 后，后继缺陷与整数阶同量级，峰高是 `log 2·(L_s−L_{s−1})/L_s²`；
  速率律闭式对数的 `b_∞ = 2`（解析阶梯在 `b_c8` 以上仍是 `[1.83976, 2]`）；
  速率律 `s λ_s^{b−1} → (2−b)/(b−1)` 带两项对数修正；转折点缺口 `~ (b−1) log 2/log s`；
  离软化折线的距离是 `u_0/L ∼ 1/(s log(s/a))`（`s^{−1.3}` 已撤回）；
  凹不动点有一整族、`F_b` 是上包络（证明）。四个底数，最高 48 级。
  η 以上（`b = 1.5, 1.6`，四级 Kneser、五级起正则）是同一个极限。
  临界底数 `b_c(s)` 单调、`≤ 2`（对一切阶梯成立的证明）；极限 `b_∞` **不普适**。
  「不越过 `1+z`」不是判据（`b=1.65>b_c5` 时四级仍在线下，五级塔发散）。
  命题 D：`[1, 1/(2-b)]` 上的包络 `1+(b-1)x` 迫使下一级塔收敛；四级上它给出
  `b_c5 ≥ 1.62`（真值 1.6353）。**`b_c8 = 1.83976`**。
  脚本：[demo_rank_limit.py](demo_rank_limit.py)、[demo_rank_above_eta.py](demo_rank_above_eta.py)、
  [demo_critical_bases_seeded.py](demo_critical_bases_seeded.py)，
  数据：[rank-limit.json](rank-limit.json)、[rank-limit-above-eta.json](rank-limit-above-eta.json)、
  [critical-bases-seeded.json](critical-bases-seeded.json)。
- [essay-infinite-systems-zh.md](essay-infinite-systems-zh.md) —
  把 f(f(x)) = eˣ 泰勒展开得到无穷多项式方程组；哪些类可解，为什么。
  Demo：[demo_infinite_system.py](demo_infinite_system.py)。
- [essay-inventing-numbers-zh.md](essay-inventing-numbers-zh.md) —
  发明分母为零的数：数学给除以零开的四种价（射影直线、wheel、
  IEEE 754、零环）、分类墙（Frobenius/Hurwitz/Ostrowski），
  以及每个被发明出来的数系背后的泛性质方法。
  Demo：[demo_division_by_zero.py](demo_division_by_zero.py)。
- [essay-transcendence-keys-zh.md](essay-transcendence-keys-zh.md) —
  无理性与超越性的钥匙：已锻造的四把（逼近、辅助函数/Siegel 引理、
  函数方程、计数）、作为条件万能钥匙的 Schanuel 猜想
  （Macintyre–Wilkie 可判定性、Zilber 伪指数），以及本仓库的常数
  落在所有已知钥匙之外的位置。
  Demo（PSLQ 重新发现 π 的 BBP 公式）：[demo_transcendence_keys.py](demo_transcendence_keys.py)。
- [essay-iteration-evolution-zh.md](essay-iteration-evolution-zh.md) —
  迭代作为普遍的复杂性引擎，演化作为它的另一条分支：确定性迭代
  （运算之塔）对比 迭代 + 变异 + **选择棘轮**（适应性复杂度）；
  基质中立的达尔文主义、与 exp 无不动点的呼应。
  Demo（累积选择比盲搜快约 10³⁴ 倍）：[demo_iteration_evolution.py](demo_iteration_evolution.py)。

## 姊妹仓库

- `../../semi_exp` — 探索过程：四种数值方法、它们的失败模式，
  以及本库 builder 复用的经验缩放律（见其 `NOTES_half_iterate_exp.md`）。
  ⚠️ 其中若干已发表数值有勘误标注，引用前先看文件内的 ⚠️ 标记。
- `../../kneser1950-paper` — Kneser 1950 年 Crelle 原始论文（OCR）
  与中英文证明讲解。

## 其他文档

- [VALUES.md](VALUES.md) — 50 位参考数值表
- [precision-envelope.md](precision-envelope.md) — 精度包络与测试区间（英文）
