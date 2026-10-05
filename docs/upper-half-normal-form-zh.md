# 上半平面无内点不动点自同构的正规形（Kneser 第六步后半）

> 2026-09-16。5 个模块 / 25 条定理，galic 上 `lake build` 通过（全项目 48025 job），
> `audit_modules.py` 公理审计通过（`audit/upper-half-normal-form-result.json`）。
> 复现命令见文末 §6。

## 0. 这一轮补的是什么

[kneser-classical-route-zh.md](kneser-classical-route-zh.md) §4 的"剩下什么"表里有一行：

| 缺口 | 性质 |
|---|---|
| 抛物型 ⟹ 共轭于 `ζ↦ζ+1` | Kneser 特有论证的下游 |

本轮把它**连同它的孪生（双曲型 ⟹ 共轭于 `ζ↦λζ`）一起证掉了**，并且给出了
两者合起来的二分定理、接到抽象自同构上的桥、三个分支的非平凡性见证，
以及一条**尖锐性定理**（见 §4，这条是纸上推导最容易写错的地方）。

Kneser 1950 第六步（`kneser1950-paper/Kneser-half-exponential-proof-zh.md`）说：

> 平移 `T` 在上半平面中对应一个无内点不动点的自同构。Kneser 排除双曲情形，
> 得到它必为抛物型自同构。**于是可选择共形映射 `R`，使得 `R(w+c) = R(w)+1`。**

黑体那句"于是可选择"就是本轮形式化的内容。`R` 不是凭空选的，它是把
不动点搬到 `∞` 的那个具体 Möbius 映射，而且它存在的**理由**是抛物性。

## 1. mathlib 里没有什么（先搜库，见 §5 的教训）

mathlib 有：

* `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/FinTwo.lean`：
  `Matrix.IsParabolic`（`m ∉ range (scalar _) ∧ m.discr = 0`）、`IsHyperbolic`（`0 < discr`）、
  `IsElliptic`（`discr < 0`）——**只有判别式的定义，没有正规形**；
* `Mathlib/Analysis/Complex/UpperHalfPlane/FixedPoints.lean`：
  `gl_smul_eq_self_iff_quadratic`、`isElliptic_of_exists_smul_eq_self`、
  `fixedPt`、`gl_smul_eq_self_iff_eq_fixedPt`——**椭圆情形的完整不动点理论**；
* `Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean`：`GL(2,ℝ)` 在 `ℍ` 上的作用。

mathlib **没有**：抛物型共轭于平移、双曲型共轭于伸缩、以及
"无内点不动点 ⟹ 这两者之一"的二分。这三条正好卡在 Kneser 主线上。

椭圆那一半虽然 mathlib 有，但它是 `GL (Fin 2) ℝ` 作用在子类型 `ℍ` 上的陈述；
本项目下游（`upperHalf_aut_real_moebius`）交出来的是**四个裸实数**
`α β γ δ` 加 `αδ-βγ > 0`，两者之间的搬运工作量与直接证明相当，
所以椭圆存在性也重新直接证了（见 §2.2），代价是 15 行。

## 2. 五个模块

记 `F w = (αw+β)/(γw+δ)`，`D := αδ-βγ`，`τ := α+δ`。分类由 `τ² - 4D` 的符号决定。

### 2.1 `formal/Kneser/RealMoebiusMap.lean`（7 条）

把映射命名为 `rmoebius α β γ δ`，并给出后面处处要用的三件事：

* `rmoebius_denom_ne_zero`：`D ≠ 0` 时分母在 `ℍ` 上不为零
  （否则 `w = -δ/γ` 是实数；而 `γ = 0` 会逼出 `δ = 0`，把行列式打死）；
* `rmoebius_mem_upperHalf`：`D > 0` ⟹ 自映射（用 `RealMoebius.im_realMoebius` 的虚部公式）；
* `rmoebius_eq_self_iff`：`w` 是不动点 ⟺ `γw² + (δ-α)w - β = 0`。

另有 `sub_real_ne_zero`：`ℍ` 里的点不等于任何实数——琐碎，但在后面出现 6 次。

### 2.2 `formal/Kneser/MoebiusFixedPoint.lean`（3 条）

**椭圆 ⟹ 有内点不动点**（`exists_fixedPoint_of_elliptic`）。不动点被**显式写出**：

```
w = (α-δ)/(2γ) + i·√(4D - τ²)/(2|γ|)
```

分母里的**绝对值**是关键：它让 `Im w > 0` **不需要对 `γ` 的符号分情况**
（两个根里哪个在上半平面取决于 `sign γ`，而 `|γ|` 把这件事吸收掉了）。
验证是 `ℂ` 上一条 `linear_combination`，用 `2γx = α-δ`、`4γ²r² = 4D-τ²`
和 `Complex.I_mul_I`：

```lean
linear_combination (2*γ*x - α + δ + 4*γ*r*Complex.I) * hxC - hrC
  + 4*γ^2*r^2 * Complex.I_mul_I
```

⚠ `ring` 不知道 `I² = -1`（这条教训 `MoebiusConjRel` 里已经踩过一次）。
系数 `4γ²r²` 就是用来消掉 `I²` 项的。

**反向**（`no_fixedPoint_of_four_det_le_trace_sq`）：`D > 0`、`4D ≤ τ²`、`F` 不是恒等映射
⟹ `ℍ` 内无不动点。做法是取**共轭根**：对不动点方程作用 `conj` 再相减，得

```
(w - conj w)·(γ(w + conj w) + δ - α) = 0
```

`w ∉ ℝ` 逼出 `2γ·Re w = α-δ`；代回实部又得 `β = -γ(x²+y²)`，于是
`τ² - 4D = -4γ²y² < 0`，与 `4D ≤ τ²` 矛盾。`γ = 0` 那支恰好落到
`γ = 0 ∧ β = 0 ∧ α = δ`，即恒等映射——所以**恒等映射必须作为例外排除**，
它是退化的抛物型而不动点遍布 `ℍ`。

只需要 `four_det_le_trace_sq_of_no_fixedPoint`（上面那条的逆否）就能推动二分，
但把双向都证了，三分法才是诚实的。

### 2.3 `formal/Kneser/ParabolicNormalForm.lean`（3 条）

**`parabolic_conjugate_translation`**：`D > 0`、`τ² = 4D`、`F` 非恒等
⟹ 存在实 `a b c d`，`ad-bc ≠ 0`，使得

```
R (F w) = R w + 1        (∀ w ∈ ℍ,  R := rmoebius a b c d)
```

两种情形都完全显式：

* `γ = 0`：抛物性逼出 `(α-δ)² = 0`，于是 `F w = w + β/α` 是真平移，`R w = (α/β) w` 把步长缩成 1。
* `γ ≠ 0`：二重根 `w₀ = (α-δ)/(2γ)` 是实数，取 `b = (α+δ)/(2γ)`，则有两条结构恒等式

  ```
  γw + δ = γ(w - w₀) + γb                    （只用 w₀、b 的定义）
  (αw + β) - w₀(γw + δ) = γb(w - w₀)         （这一条**就是抛物性**）
  ```

  第二条等价于 `(α-δ)² + 4βγ = 0`。相除得 `F w - w₀ = γb(w-w₀)/(γw+δ)`，
  于是 `R w := b/(w - w₀)` 满足 `R(F w) = (γ(w-w₀) + γb)/(γ(w-w₀)) = R w + 1`。
  几何上：**把唯一的（实）不动点搬到 `∞`，抛物型就露出平移的本来面目**。

⚠ **坑**：`w₀` 和 `b` 必须用 `obtain` 引入成不透明的局部变量，**不能用 `set`**。
`set` 生成 let-绑定，`ring`/`linear_combination` 会 zeta 归约把 `(α-δ)/(2γ)`
展开回来，于是上面两条"为了避开除以 `2γ` 而存在"的恒等式全部失效。
第一次写用 `set`，`linear_combination` 直接 `ring failed`。

### 2.4 `formal/Kneser/HyperbolicNormalForm.lean`（3 条）

**`hyperbolic_conjugate_dilation`**：`D > 0`、`τ² > 4D` ⟹ 存在实 `a b c d`（`ad-bc ≠ 0`）
与实 `λ > 0`、`λ ≠ 1`，使得 `R(F w) = λ·R w`。

技巧：**平方根只在生成一对"乘子" `p, q` 时出现一次**，之后全是 `p, q` 的代数。
`p, q` 是特征多项式的两根，由三条对称关系刻画：

```
p + q = α + δ,     p·q = αδ - βγ,     q - p = √(τ² - 4D) > 0
```

取 `γw₁ = α - p`、`γw₂ = α - q`（两个实不动点），则**仅凭前两条对称关系**就有

```
(αw + β) - wᵢ(γw + δ) = pᵢ(w - wᵢ)
```

（验证：`(α-p)(p-δ) = p(α+δ) - αδ - p² = p(p+q) - αδ - p² = pq - αδ = -βγ`。
这一步是整个文件最省力的地方——不用碰 `σ`。）
于是交比 `R w = (w-w₁)/(w-w₂)` 被乘以 `λ = p/q`。正性是白给的：
`λ = p²/(pq) = p²/D > 0`；`λ ≠ 1` 恰是 `p ≠ q`。

`γ = 0` 那支的第二个不动点是 `∞`，单独用平移 `R w = w - β/(δ-α)` 处理，
乘子 `λ = α/δ = D/δ² > 0`。

### 2.5 `formal/Kneser/UpperHalfNormalForm.lean`（9 条）

* `rmoebius_normal_form_of_no_fixedPoint`：**二分定理**。
  由"无不动点"经 `four_det_le_trace_sq_of_no_fixedPoint` 得 `4D ≤ τ²`，
  再按 `<` / `=` 分派给上面两个正规形。抛物那支要的"非恒等"由
  `w = i` 处无不动点直接提供。
* `upperHalf_aut_normal_form`：**接到抽象自同构上**。前提是
  `F, G` 在 `ℍ` 上全纯、互逆、互为自映射，且 `F` 在 `ℍ` 内无不动点；
  经 `upperHalf_aut_real_moebius`（`Aut(ℍ) = PSL(2,ℝ)`，上一轮的成果）
  换成 `rmoebius` 再套二分定理。**这就是 Kneser 第六步要的那句话的完整形式。**
* 三个见证 `normal_form_witness_{parabolic,hyperbolic,elliptic}`：
  `w↦w+1`（`τ²=4D`）、`w↦2w`（`8 < 9`）、`w↦-1/w`（`0 < 4`，且 `i` 真的是不动点）。
  三个分支都非空，"无内点不动点"这个前提也不是真空的。
* `upperHalf_aut_normal_form_nonvacuous`：**顶层定理本身的前提可满足**——
  `w↦w+1` 连同逆 `w↦w-1` 满足全部六条前提且处处无不动点。
  （顶层定理若前提矛盾则真空真；这条把该风险关掉。）
* `translation_neg_not_positively_conjugate`：见下节。

## 3. 陈述形态的一个决定

正规形里写的是 `ad - bc ≠ 0`，**不是 `> 0`**。这不是偷懒。

`ζ ↦ ζ+1` 与 `ζ ↦ ζ-1` 在 `PSL(2,ℝ)` 里**不共轭**——它们是两个不同的抛物共轭类。
如果要求 `R ∈ Aut(ℍ)`（即 `ad-bc > 0`），定理对其中一个符号就是**假的**。
允许负行列式，`R` 就是 `ℍ` 到上半平面**或下半平面**的双全纯映射，
这对 Kneser 完全够用（后续的 Schwarz 反射对两侧对称）。

## 4. 尖锐性定理（本文件最该被复核的一条）

`translation_neg_not_positively_conjugate`：

> 不存在实 `a b c d` 满足 `ad - bc > 0` 且 `∀ w ∈ ℍ`，`R(w-1) = R(w) + 1`。

证明是纯代数的。把 `R(w-1) = R(w)+1` 通分，得对一切 `w ∈ ℍ`

```
c²w² + (2cd - c²)w + (d² - cd + (ad - bc)) = 0
```

在 `w = i` 与 `w = 2i` 处取值，分离实虚部（`real_imag_zero`），实部给出

```
-c² + K = 0,      -4c² + K = 0      (K := d² - cd + (ad-bc))
```

于是 `3c² = 0`，`c = 0`，`K = 0`；`c = 0` 时 `K = d² + ad`，而 `ad = ad - bc > 0`，
故 `d² = -ad < 0`——矛盾。

⚠ **这里有一个我第一次写错的地方**：我原本想用一条 `linear_combination`
从 `h1`（`w = i` 处的复方程）直接推出实部方程。**这是错的**——
`linear_combination` 是环恒等式推理，从**一条**复方程推不出它的实部方程，
必须真的取 `Complex.re` / `Complex.im`。Lean 当场拒绝；纸上很容易滑过去。

## 5. 不主张什么

1. **没有证明 Kneser 定理。** 本轮补的是第六步里"于是可选择 `R`"那一句。
2. **没有排除双曲情形。** 那是 Kneser 特有的论证（用 `e^{w/c}` 在左半平面的有界性，
   搬到圆盘上得到"两段边界弧上极限都为零的非零全纯函数"之矛盾），仍然欠着。
   本轮做的是：**把双曲情形整理成 `ζ ↦ λζ` 这个可攻击的形状**——
   Kneser 的反证法正是在这个正规形上进行的。
   ⚠ **2026-09-16 补记**：该反证法的**解析核心已经证掉了**——"这样的函数不存在"就是
   `DiscTwoPointVanishing.disc_eq_zero_of_boundary_limits` 与它在本正规形坐标下的搬运
   `UpperHalfTwoPointVanishing.upperHalf_eq_zero_of_real_limits`（两不动点 `0`、`∞`，
   两段弧即两条实半轴）。见 [kneser-classical-route-zh.md](kneser-classical-route-zh.md) §3.9。
   欠的改成只有**见证函数的构造**（`e^{w/c}` 沿黎曼映射的搬运，要 𝔅 与 RMT）。
3. 这二十五条是**经典复分析**，不是新数学。价值在于它们是 mathlib 的真实空白，
   且卡在关键路径上。（对照 [wall-a-reduction-zh.md](wall-a-reduction-zh.md) §0 记录的
   相反教训：那里的半带引理 mathlib 早已有，属于重复劳动。**动手前先 grep。**
   本轮开工前先 grep 了 `IsParabolic|IsHyperbolic|IsElliptic` 和
   `Analysis/Complex/UpperHalfPlane/`，确认只有判别式定义与椭圆理论。）
4. `upperHalf_aut_normal_form` 的前提里 `F` 的双全纯性是**假设**，不是从几何构造出来的；
   在 Kneser 主线上它将由 Riemann 映射定理提供（mathlib 的经典 RMT 在 PR #33505，在途）。

## 6. 复现

```sh
ssh galic 'docker exec -u lean lean-build bash -lc \
  "cd ~/projects/kneser-formal && python3 audit_modules.py --name upper-half-normal-form \
     --module RealMoebiusMap --module MoebiusFixedPoint --module ParabolicNormalForm \
     --module HyperbolicNormalForm --module UpperHalfNormalForm"'
```

输出 `PASS: 25 theorems in 5 selected modules; allowed axioms only.`
全项目 `lake build` 为 48025 job。
