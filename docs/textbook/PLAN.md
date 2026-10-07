# 教科书计划：《鞍结开折的分数迭代》

2026-10-07。目标：把 [theory-core-zh.md](../theory-core-zh.md) 的理论写成一本**教科书**。
读者是学过复分析的研究生，不假定读者熟悉复动力系统。

## 体例（所有章节必须遵守）

1. **语言**：中文正文，数学用 LaTeX。句子短而准确，不用宣传性形容词（「优美」「深刻」「惊人」）。
   术语首次出现时加粗，并附英文，例如 **转移映射**（transition map）。
2. **结构**：每章包含以下部分。
   - `\chapter{…}\label{ch:xxx}`，紧接一段引言和 `goals` 环境（3–6 条本章要点）。
   - 若干 `\section`。每个定义、定理、例子都要有标签。
   - 至少一个**算例**：给出具体数值，并说明来自哪个脚本。
   - 章末 `\notes`（注记与文献：历史、出处、与论文的对应）。
   - 章末 `\exercises`（6–12 道，由易到难；难题附 `hint` 环境的提示）。
3. **证明标准**：
   - 经典结果（Koenigs、Fatou 坐标、Weierstrass 预备等）给出完整证明，或给出精确出处（书名、章节、定理号）并说明为什么不证明。
   - 本理论的结果，在**一般实鞍结开折**的设定下给出完整证明。来源是论文 `docs/paper-submission/main.tex`（以下简称 [KneserPaper]）的证明和 `sec-general.tex` 的改写清单。
     论文对指数族写死的常数（`1/2`、`1/3`、`−2/u`、`p′(0)=2`）一律换成 `a₂`、`ρ`、`−1/(a₂u)`、`4a₂γ`。
   - tetration 的整体延拓（论文定理 F、G 及区间证书）篇幅太大：第 10 章只讲结构和关键思想，并精确引用论文的节号。
   - **不得**写出任何源材料中没有证明的断言而不加标注。数值事实注明「数值」；猜想注明「猜想」。
4. **记号**：严格使用下表与 `preamble.tex` 中的宏。**不要修改 `preamble.tex`**（多人并行编辑会冲突）。本章需要的新宏写在章节文件开头，用 `\providecommand`，并在汇报中列出。
5. **交叉引用**：用 `\cref{…}`。引用其他章的结果时，只能使用下面「标签登记表」中的标签。本章内部标签用前缀 `chN:`（例如 `ch3:lem:petal`）。
6. **图**：需要图时，写一个 Python 脚本 `figures/figN_name.py`（matplotlib，输出同名 `.pdf`），运行生成后用 `\includegraphics` 引用。图要简洁，用黑白可辨的线型。
7. **文献**：用 `\cite{key}`，键只能取 `references.tex` 中已有的条目；需要新文献时在汇报里列出完整条目，不要自己改 `references.tex`。
8. **编译自检**：`./build_chapter.sh N`（只编译第 N 章，输出到 `/tmp/tb-chN/`），要求零错误，且本章内部没有未定义引用（登记表中其他章的标签未定义可以忽略）。

## 记号（一字一义）

| 记号 | 宏 | 含义 |
|---|---|---|
| `f_s`, `s` | | 开折与开折参数；`s>0` 一侧有两个实不动点 |
| `g` | | 抛物芽 `g(u)=u+a₂u²+a₃u³+…`，`a₂>0` |
| `a₂, a₃` | | 芽的 Taylor 系数 |
| `ρ` | | 迭代留数 `1−a₃/a₂²` |
| `X`, `γ` | | 开折方向 `f_s=g−sX+O(s²)`，横截性 `γ=X(0)>0` |
| `u₁<u₂` | | 吸引、排斥不动点（`u` 坐标） |
| `λ₁, λ₂` | | 对应乘子，`0<λ₁<1<λ₂` |
| `A_j` | | 留数 `1/log λ_j` |
| `p` | | 内蕴参数 `−log λ₁·log λ₂` |
| `h, h₂` | | 周期 `2π/|log λ₁|`、`2π/log λ₂` |
| `Λ` | `\Lam` | 强迫尺度 `exp(4π²/log λ₁)=e^{−2πh}` |
| `σ, σ_rep` | | 吸引、排斥 Koenigs（Schröder）坐标 |
| `R, S` | | 吸引、排斥正则解（Abel 坐标的逆），`R⁻¹(w₀)=0` |
| `T, t_n` | | 转移映射 `R⁻¹∘S`，`T(z)−z=Σ t_n e^{2πinz}` |
| `τ_n` | | 不变量 `t_n e^{−2πint₀}` |
| `T°` | | `T−id−t₀` |
| `K^W`, `c_n`, `ĉ_n`, `Ξ_n` | `\Ksew` | 缝合解、分离系数、`c_n/Λⁿ`、`c_n/c₁ⁿ` |
| `α` | | 形式 Abel 函数 `−1/(a₂u)+ρ log(−u)+Σd_k u^k` |
| `Φ_att, Φ_rep` | `\Phiatt`,`\Phirep` | Fatou 坐标（用 `α` 归一化） |
| `𝔥` | `\horn` | horn 映射；逆 horn 映射 `𝔥⁻¹=Φ_att∘Φ_rep⁻¹=z+ΣB_n e^{2πinz}` |
| `B_n` | | 逆 horn 映射的 Fourier 系数 |
| `w₀, u*` | `\ustar` | 基点；`u*` 是基点在 `u` 坐标中的位置 |
| `u` | | 以 `w*` 为中心的**仿射**坐标 `w=w*+c·u`（`c>0`）。一般情形取 `c=1`；**tetration 取 `w=e(1+u)`**，芽为 `eᵘ−1`，`u*=1/e−1`，`a=Φ_att(u*)=3.0292972144180…` |
| `a` | | 基点的 Fatou 值 `Φ_att(u*)` |
| `κ⁽ⁿ⁾_j`, `κ⁽ⁿ⁾` | | 展开系数，`κ⁽ⁿ⁾=κ⁽ⁿ⁾_1` |
| `κ⁽ⁿ⁾_tr` | `\ktr` | 平移开折 `g−s` 的一阶系数 |
| `𝒫` | `\Pstr` | 抛物层（有二重不动点的映射） |
| `𝒪_r` | `\Ocal` | `D_r` 上有界全纯函数的 Banach 空间 |
| `𝔏_n, 𝓘_n, 𝒟_n` | `\Lfun`,`\Ifun`,`\Dfun` | 第 9 章的线性泛函、不变量、抛物层上的对数微分 |
| `𝖫` | `\Lop` | 同调算子 `𝖫φ=φ∘g−g′φ` |
| `𝒦_b` | `\Kkn` | tetration 的 Kneser 解（底数延拓族） |
| `η` | | `e^{1/e}` |
| `ε` | | 仅第 10 章：尖点附近的复参数 `1−λ₁` |

## 章节与标签登记表

| 章 | 标题 | 文件 | 必须定义的标签 | 主要来源 |
|---|---|---|---|---|
| 0 | 前言 | `ch00.tex` | `ch:preface` | — |
| 1 | 分数次迭代问题 | `ch01.tex` | `ch:intro`；`thm:main-preview` | 论文引言；theory-core §0 |
| 2 | 双曲不动点与 Koenigs 坐标 | `ch02.tex` | `ch:koenigs`；`thm:koenigs`；`def:regular-solution`；`prop:regular-periodic` | 经典；论文 §3.1 |
| 3 | 抛物不动点：Fatou 坐标与 horn 映射 | `ch03.tex` | `ch:fatou`；`def:formal-abel`；`thm:fatou-coordinates`；`def:horn`；`prop:B1-nonzero` | 经典；论文 §2.2、附录 |
| 4 | 实鞍结开折 | `ch04.tex` | `ch:unfolding`；`def:unfolding`（含 H1–H5）；`prop:scales`；`lem:residues` | sec-general；论文 §2、§4 |
| 5 | 双坐标与转移映射 | `ch05.tex` | `ch:transition`；`def:transition`；`lem:realT`；`prop:base-point`；`cor:invariance`；`thm:welding` | 论文 §3；sec-general |
| 6 | 缝合解 | `ch06.tex` | `ch:sewing`；`thm:sewing`；`def:class`；`thm:characterization` | 论文 §3.3、§6–§8 |
| 7 | 汇流定理 | `ch07.tex` | `ch:confluence`；`thm:reduction`；`lem:petal`；`thm:confluence` | 论文 §3.4、§4 |
| 8 | 一阶项与全阶展开 | `ch08.tex` | `ch:first-order`；`lem:uniform-model`；`thm:first-order`；`thm:all-orders` | 论文 §5 |
| 9 | 变分公式 | `ch09.tex` | `ch:variation`；`thm:variation`；`cor:variation`；`rem:cocycle` | sec-general §9.4；kappa-variation-zh.md |
| 10 | 例：tetration 与其他族 | `ch10.tex` | `ch:examples`；`thm:cusp`；`thm:upper-half-plane` | 论文 §10、§11；quad-kneser-zh.md |
| 11 | 数值方法 | `ch11.tex` | `ch:numerics` | 脚本；论文 §11、附录 |
| 12 | 开放问题 | `ch12.tex` | `ch:open` | theory-core §6–§7 |
| A | 复分析工具 | `appA.tex` | `app:tools`；`thm:weierstrass-prep`；`thm:ahlfors-bers` | 经典 |
| B | 记号表 | `appB.tex` | `app:notation` | 本表 |

## 流程

1. 骨架：`preamble.tex`、`book.tex`、`build_chapter.sh`、`references.tex`。
2. 并行起草：7 个子代理分别负责 第1–2章、第3章、第4–5章、第6章、第7–8章、第9+11章、第10+12章+附录A。
3. 汇总编译：解决跨章引用、统一术语。
4. 对抗审读：每章一位审稿人，检查数学正确性、证明完整性、与源材料是否一致、教学顺序。
5. 修订、定稿、写入执行记录。

## 执行记录

**2026-10-07，初稿完成。** `book.pdf` 共 211 页：前言、12 章、附录 A（复分析工具）、附录 B（记号表），每章有本章要点、
算例、注记与文献、6–12 道习题；17 幅图由 `figures/*.py` 生成。全书编译零错误、零未定义引用。

- **起草**：7 个子代理并行，按本计划的体例与标签登记表写作；中途统一了坐标约定（`u` 是以 `w*` 为中心的仿射坐标，tetration 取 `w=e(1+u)`）。
- **对抗审读**：每章一位独立审稿人，逐条核对定义、证明、算例（重新运行脚本）与跨章引用，并直接修改。
  共修正 FATAL 级错误 6 处（如第 1 章对 Kneser 构造的描述、第 2 章关于 `K^W` 极限与实半迭代的论断）、MAJOR 级 40 余处
  （如第 3 章 `d₁` 公式的符号、第 6 章缝合解 `|c_n|` 的基点依赖、第 4 章留数收敛速率）。
- **反馈到论文**：写书过程中发现的论文问题记录在 [ERRATA-paper.md](ERRATA-paper.md)（20 项）。
  第 20 项（`|c_n|` 与基点无关的说法不成立）已改正论文；第 18 项（上半平面区间证书的独立复核未完成）需要作者处理；其余为可挽救的证明缺口、常数或表述问题。
- **全书统一**：引用论文一律用 PDF 中的印刷编号（如「命题~9.1」），不用 LaTeX 标签名；章号用阿拉伯数字。

**尚待改进**：第 8 章 `ch8:rem:local` 中「排斥坐标可由局部数据构造」只给了论证思路；第 7 章带引理中反向轨道一步的措辞偏松；
二次族 F、G 的结果来自未审稿的证明稿，书中如实标注。
