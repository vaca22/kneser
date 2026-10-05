# 无限方程组:形式可解与解析可解的两道门

> 用泰勒级数去解 f(f(x)) = eˣ:把 f 设为一个泰勒级数代入,就要面对
> 无限多个未知数、每条都无限长的方程组——正面强攻没有出路。
> 但可以逆向思维:既然现有方法**确实**得到了 f,那它是不是顺手解决了
> **某一类**无限长、无限次的方程组?这一类的边界在哪里?
>
> 这是本仓库动机问题(见[《运算之梯》](essay-operation-ladder-zh.md))的
> 续篇。结论先行:是的——而且"能解的那一类"有精确的刻画,它的每一段
> 边界上都长出过一片真实的数学。

---

## 一、字典:函数方程 ⟺ 无限多项式方程组

Carleman 矩阵把这个观察变成精确的字典:函数复合等于无限矩阵乘法,

```
f∘f = exp   ⟺   C_f · C_f = C_exp .
```

于是"解函数方程"严格等价于"解一个无限维的矩阵方程"。但真正的难点
随之显形:C_exp 作为算子有**无穷多个**平方根,而其中几乎全部
**不是任何函数的 Carleman 矩阵**。"是某个函数的复合算子"是一个
弯曲的非线性流形,解必须留在流形上——这正是问题与普通线性代数的
本质区别。姊妹仓库 `semi_exp` 的 Carleman 实验取"主值平方根"恰好
逼近 Kneser 解,本质上是在截断世界里做了一次一致的特征值分支选择:
离散版的唯一性定理。

---

## 二、两道门:一个可以当场跑的实验

挑一个**有不动点**的目标函数 g(x) = eˣ − 1(不动点 0,g'(0) = 1),
解同样形式的无限方程组 f(f(x)) = g(x)。运行
[demo_infinite_system.py](demo_infinite_system.py)(纯标准库、
精确有理数算术):

```
exact check: f(f(x)) == e^x - 1  (mod x^33)  PASS

a[2] = 1/4        a[5] = 1/3840
a[3] = 1/48       a[6] = -7/92160
a[4] = 0          a[7] = 1/645120     a[8] = 53/3440640
```

### 第一道门(代数):分级三角化

为什么 30 行代码就解掉了"无限"方程组?因为不动点给整个系统一个
**分级结构**:第 k 级方程中,新未知数 a_k **线性地、首次**出现,
系数为 (μ + μᵏ)(μ = f'(0),此处 = 2)。只要该系数不为零,就可以
一步解一个未知数——无限方程组在这个分级下是**三角的**,
"无限"瞬间退化为"逐有限"。

### 第二道门(分析):收敛性,它可以独立地失败

同一份精确解的尾部:

```
|a[10]| = 8.282e-08      |a[26]| = 2.220e-05
|a[14]| = 1.775e-06      |a[30]| = 1.113e-04
|a[18]| = 2.419e-06      |a[32]| = 1.677e-03
```

系数在 k ≈ 10 之后掉头暴涨:这个形式上完美的级数**发散**
(收敛半径为零;经典结果,Erdős–Jabotinsky、Baker:eˣ−1 的分数次
迭代级数仅在整数次收敛)。但发散不是死刑——Borel–Écalle 重求和
能把它变回真正的函数,而且左、右两个侧向求和相差一个指数小量
(Stokes 现象):**级数发散的方式,编码了解的不唯一性**。
Écalle 的 resurgence 理论正是从"解这类发散的无限方程组"中诞生的——
这个问题已经孕育过一次大理论的铁证。

### 而 eˣ 在实轴上,连第一道门都没有

eˣ = x 无实数解:任何实展开点处,方程组都稠密耦合、没有三角结构。
`semi_exp` 的第一个失败方法(在 Ω = W(1) 处最小二乘拟合 Abel 级数,
高阶导数 Runge 振荡)就是硬闯无结构系统的典型症状报告。
Kneser 构造的全部智慧,用本文的语言重说一遍就是:

1. **绕到复不动点恢复三角化**(Koenigs/Schröder 坐标下,方程组重新
   变成三角的);
2. **修补边界**(Riemann 映射 / theta 修正,把复坐标里的解拉回实轴);
3. 数值上,theta 迭代是无穷维函数空间上的一个**压缩映照**——
   本仓库的构建日志实测了它的压缩常数:每轮约 1.4 个十进制位,
   即每步把误差缩小约 25 倍。

---

## 三、版图:已知的"可解无限方程组"类

把已知的成功案例摆在一起,口号只有一句:

> **能解的无限方程组,都是在某个范畴里伪装的有限对象。**

| 类 | "伪装的有限"结构 | 可解性判据 / 关键定理 |
|---|---|---|
| 复合结构类(本仓库所属) | 不动点处的分级三角化 | 三分法:双曲(Koenigs 1884,收敛)/ \|λ\|=1(Siegel 1942–Brjuno,小除数的 Diophantine 条件,KAM 之源)/ 抛物(形式可解+发散+可和,Écalle) |
| 同上,障碍侧 | — | Écalle–Voronin 模量(1981):存在**形式相容但解析不相容**的系统,障碍空间是函数维的——解不出的方式本身成为分类不变量 |
| 线性无限方程组 | 算子的谱结构 | 20 世纪泛函分析;数值截断 = Galerkin / 有限截面法(`semi_exp` 的 24×24 Carleman 即是) |
| Carleman/Koopman 线性化 | 非线性升维为无限线性 | 今日工业级工具:数据驱动动力系统(DMD,Schmid 2010;Mezić);量子算法解非线性 ODE(Liu–Kolden–Krovi–Childs 等,PNAS 2021) |
| 损失正则性的非线性系统 | 迭代格式自身 | Nash–Moser 隐函数定理、KAM:无穷维牛顿法,"每步丢一点导数"也能收敛 |
| 对称的无限变元代数系统 | 对称群作用 | 无限变元多项式环在 Sym 作用下 Noetherian(Draisma;Sam–Snowden) |
| D-finite / holonomic 类 | 关系组背后的有限维向量空间 | Stanley、Zeilberger:无限多恒等式由有限数据生成,可机器判定 |

本仓库方法所解的类的精确刻画:**复合算子的多项式方程**,可解性由
不动点的谱数据(λ 的位置)加数论条件(Brjuno)加可和性(Écalle)
逐段划定;在边界之外,障碍本身升格为不变量。

---

## 四、结案

把本仓库背后的两个少年问题并排放好,对照非常完整:

- **"创造新运算律"** —— 撞上 Aczél 分类定理,属于"不可能"一侧;
  梦的幸存形态在换了载体的李群、热带半环、序数里
  (见[《运算之梯》](essay-operation-ladder-zh.md))。
- **"解无限长、无限次的方程组"** —— 驶入 20 世纪分析的主航道,
  属于"已成真"一侧:迭代方程为它贡献了两片理论
  (Koenigs–Siegel–KAM 一脉,与 Écalle resurgence 一脉),
  Koopman/Carleman 线性化则把它做成了当代应用数学的基础设施。

`semi_exp` 的三次失败,事后看恰好是三种结构缺失的症状:
无三角化(Abel 最小二乘)、有三角化但选错分支(朴素 Schröder)、
有限截断的病态(高阶 Carleman)。亲手摸过这张地图边界之后,
`kneser` 库把可解区域中的一个点钉到了小数点后 51 位。

---

## 参考

- T. Carleman, *Application de la théorie des équations intégrales linéaires aux systèmes d'équations différentielles non linéaires* (1932)
- G. Koenigs, *Recherches sur les intégrales de certaines équations fonctionnelles* (1884)
- C. L. Siegel, *Iteration of analytic functions*, Ann. of Math. (1942);A. D. Brjuno (1971);J.-C. Yoccoz(Brjuno 条件的最优性,1995)
- P. Erdős, E. Jabotinsky, *On analytic iteration* (1960);I. N. Baker,关于 eˣ−1 分数次迭代级数发散性的工作
- J. Écalle, *Les fonctions résurgentes* I–III (1981–85);Écalle–Voronin 抛物芽的解析分类 (1981)
- B. O. Koopman (1931);P. J. Schmid, *Dynamic mode decomposition* (2010);I. Mezić 的 Koopman 谱理论
- J.-P. Liu, H. Ø. Kolden, H. K. Krovi, A. M. Childs 等, *Efficient quantum algorithm for dissipative nonlinear differential equations*, PNAS 118 (2021)
- J. Draisma, *Noetherianity up to symmetry* (2014);S. Sam, A. Snowden 的 FI-模理论
- R. P. Stanley, *Differentiably finite power series* (1980);D. Zeilberger 的 holonomic 方法
- H. Kneser, J. reine angew. Math. 187 (1950);数值实现与失败记录见姊妹仓库 `semi_exp/NOTES_half_iterate_exp.md`
- 演示代码:[demo_infinite_system.py](demo_infinite_system.py)(本目录,纯标准库)
