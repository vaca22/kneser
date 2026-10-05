# 运算之梯:一个高中问题的现代结案报告

> 从加法到乘法,从乘法到乘方,继续推广下去;把迭代次数推到分数、小数、
> 甚至虚数——能不能发展出更复杂的结构、更高层的运算律?
>
> 这是一个少年时代的问题,也是本仓库(以及姊妹仓库 `semi_exp`、
> `kneser1950-paper`)背后真正的动机。这份笔记给它一个诚实的结案:
> **哪一半已经实现(并且可以当场算出数值),哪一半撞上了分类定理,
> 以及梦的幸存形态在今天的数学里叫什么名字。**

这个念头并不天真。Abel 在 1820 年代追问的就是同类问题(Abel 方程因此得名);
Goodstein、Ackermann 把整数阶的梯子搭了上去;Kneser 1950 年解决了
f(f(x)) = eˣ 的实解析解。本仓库的 `kneser` 库把 Kneser 解算到了 50 位精度——
下面所有数值都可以用它复现。

---

## 一、当年想要的两个东西,数值在这里

### 1. 虚数次迭代:exp^[i]

一旦有了全纯的超指数 sexp(Kneser 解),迭代次数就可以取任何复数:
exp^[τ](x) = sexp(slog(x) + τ)。取 τ = i,作用在 x = 1 上:

```
exp^[i](1) = sexp(i) = 0.7856963885801980… + 0.9163026210812892…·i
```

自洽性检验:|sexp(i+1) − e^{sexp(i)}| ≈ 1.1e−25 ✓(函数方程在复平面上成立)。

复现(直接对烘焙系数在 z = i 处求级数值):

```python
import mpmath as mp
from kneser import _coeffs

with mp.workdps(60):
    a = [mp.mpf(s) for s in _coeffs.COEFFS]
    def sexp_c(z):
        r = mp.mpc(0)
        for c in reversed(a):
            r = r*z + c
        return r
    print(sexp_c(mp.mpc(0, 1)))          # sexp(i)
    print(abs(sexp_c(mp.mpc(1, 1)) - mp.exp(sexp_c(mp.mpc(0, 1)))))
```

exp^[it] 构成一族真正的"流"(exp^[s]∘exp^[t] = exp^[s+t]),其轨道在
Schröder 坐标里是乘以 L^{it}(L ≈ 0.318+1.337i 为复不动点)——
沿着绕 L 的螺旋线运动。这族流线的整体几何,至今没有人完整画过。

### 2. 加法与乘法"正中间"的运算

取 f = exp^[1/2](本库的 `half_exp`),定义

```
x ∘ y = f( f⁻¹(x) + f⁻¹(y) )
```

它是"第 0.5 级运算":同样的构造在第 0 级共轭出加法本身,在第 1 级
(f = exp)共轭出乘法(e^{ln x + ln y} = xy)。数值:

```
2 ∘ 3   = 6.074570478639311     (对比 2+3 = 5,2×3 = 6)
e ∘ e   = 6.922745177059359
10 ∘ 10 = 39.245582209809506
```

它**交换、结合、有单位元**——一个带完整运算律的真实新运算:

- 结合律:(2∘3)∘4 与 2∘(3∘4) 之差 ≈ 2e−14(纯浮点舍入);
- 单位元:e_s = exp^[s](0) 随级别 s 连续滑动——s=0 时是 0(加法单位元),
  s=1 时是 1(乘法单位元),s=½ 时是 f(0) = 0.49856…,
  验证:2 ∘ 0.49856… = 2.0 ✓。

复现:

```python
import kneser
half  = lambda x: kneser.exp_iter(x,  0.5)
ihalf = lambda x: kneser.exp_iter(x, -0.5)
op    = lambda x, y: half(ihalf(x) + ihalf(y))
print(op(2, 3), op(2, kneser.half_exp(0)))
```

一个诚实的细节:2∘3 = 6.07 **略大于** 2×3 = 6。这族运算在"级别"上插值,
但函数值并不随级别在加法和乘法之间单调过渡——少年直觉在这里第一次被
数值修正。

---

## 二、墙在哪里:推不动不是功力问题,是分类定理

这是整件事最深的部分。

**Aczél 定理**(J. Aczél, 1949;专著 1966):实区间上任何连续、结合、
可消去的二元运算,必同构于加法——存在严格单调的 φ 使

```
x ∘ y = φ⁻¹( φ(x) + φ(y) ).
```

也就是说:**在一维实数上,所有"带运算律的"运算都是加法的化装。**
乘法是加法戴了 exp 的面具;上一节的 ∘ 是加法戴了 exp^[1/2] 的面具。
再要求新运算与已有运算满足分配律,实数域 (ℝ, +, ×) 的刚性便把
"第三个全法则成员"封死了。

于是从乘方往上,梯子必然分叉,**两样只能保一样**:

| | 保什么 | 失什么 | 代表 |
|---|---|---|---|
| **Goodstein 塔**(tetration) | 递归定义 a↑↑(b+1) = a^(a↑↑b) | 全部运算律:无结合、无交换、无任何 a^(b+c)=a^b·a^c 式恒等式 | 四则塔、Ackermann |
| **Bennett 塔**(1915) | 交换 + 结合 + 单位元 | 新意:每一级都同构于加法 | 上一节的 ∘ 即其分数阶版本 |

高中时觉得"应该能继续推出去"却推不动,与试图三等分角、求五次方程根式解
是同一种处境:前方有一块没人告诉你的不可能性定理。这反而是对那个梦最大的
尊重——**它精确地踩在了可能与不可能的边界上**。

---

## 三、梦的幸存形态:换载体,别硬来

数学史上"创造新运算"真正成功的几次,全都遵循同一个模式——
**不在 ℝ 上硬加第四个运算,而是换载体或放宽法则**:

- **李理论**:把"迭代小数次"搬到高维——流、单参数群、矩阵指数 e^{tA}。
  Baker–Campbell–Hausdorff 公式就是那里的"新运算律"
  (e^X e^Y = e^{X+Y+½[X,Y]+⋯})。连续迭代在 n 维空间里是现代几何的地基。
- **热带半环 (max, +)**:梯子往**下**延伸——max 是比加法更低一级的运算。
  放弃可减性,换来热带几何这门活跃学科。"新运算长成大理论"的最干净案例。
- **序数与超现实数**:Goodstein 塔的天然家园;Goodstein 定理在皮亚诺算术内
  不可证(Kirby–Paris 1982)——这架梯子在数理逻辑里长出了牙齿。
- **超级数 / Hardy 域**(模型论前沿):transseries 对 exp/log 封闭却装不下
  exp^[1/2]——增长率谱在第四层有缝。补这个缝正是 Aschenbrenner–
  van den Dries–van der Hoeven 纲领、hyperseries、超现实数导子这条
  活跃战线的动机之一。**半指数正在逼着主流数学发明新结构**,
  只是成果不挂在 tetration 名下。

---

## 四、仍然敞开的角落

1. **保递归那一支的分数阶**:非交换意义下的"第 2.5 级运算"
   (介于乘方与四则塔之间、且延续 Goodstein 递归)至今没有公认构造。
   → 展开成判据与可做的第一步:[essay-rank-1000-zh.md](essay-rank-1000-zh.md)。
2. **复数阶迭代的几何**:exp^[it] 流线的整体图景、其与复动力系统
   (Julia 集为全平面,Misiurewicz 1981)的关系,基本无人系统绘制。
3. **常数的算术性质**:sexp(½) = 1.64635…、f'(0) = 0.87633… 的无理性
   完全 open;本仓库的 PSLQ 实验(系数 ≤ 1000,基 {π, e, ln2, γ, √2, Ω,
   e^{1/e}})未发现任何整数关系——与"全新超越常数"一致。

这三个问题都在本仓库 50 位精度管线的射程之内。

---

## 结案陈词

对当年那个高中生,公平的结论是:**直觉对了一半,而且是重要的那一半。**

"更复杂的结构存在"——对。虚数次迭代存在,并且可以算到小数点后 25 位;
加法与乘法之间的运算存在,带着完整的运算律和一个会滑动的单位元。

"它长在 ℝ 的运算梯子上"——错。Aczél 定理关上了那扇门;
结构真正生长的地方,是换了载体之后的李群、热带半环、序数、超级数。

二十年前的问题,今天有了能按回车的形态。

---

## 参考

- N. H. Abel,关于迭代与函数方程的工作(1820s);Abel 方程 ψ(f(x)) = ψ(x)+1 由此得名
- A. A. Bennett, *Note on an Operation of the Third Grade*, Ann. of Math. 17 (1915) — 交换超运算塔
- J. Aczél, *Sur les opérations définies pour nombres réels* (1949);*Lectures on Functional Equations and Their Applications* (1966) — 结合运算的分类
- R. L. Goodstein, *Transfinite Ordinals in Recursive Number Theory*, J. Symbolic Logic (1947) — 超运算层级
- H. Kneser, *Reelle analytische Lösungen der Gleichung φ(φ(x)) = eˣ…*, J. reine angew. Math. 187 (1950)
- H. Trappmann, D. Kouznetsov,Kneser 解的唯一性(2010)
- L. Kirby, J. Paris, *Accessible independence results for Peano arithmetic* (1982)
- M. Aschenbrenner, L. van den Dries, J. van der Hoeven, *Asymptotic Differential Algebra and Model Theory of Transseries* (Ann. of Math. Studies, 2017);及其后的 hyperseries / 超现实数方向
- D. Maclagan, B. Sturmfels, *Introduction to Tropical Geometry* (2015)
- 数值来源:本仓库 `kneser` 库(50 位系数,构建残差 2.6e−52);
  探索史与缩放律见姊妹仓库 `semi_exp/NOTES_half_iterate_exp.md`
