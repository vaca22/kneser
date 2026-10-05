# 超越数的钥匙:幻想的结案报告

> 我以前幻想这些方法——发明新的数与结构、解无限方程组——能找到
> 无理数、超越数的钥匙。
>
> 系列第四篇(前三篇:[《运算之梯》](essay-operation-ladder-zh.md)、
> [《无限方程组》](essay-infinite-systems-zh.md)、
> [《发明数》](essay-inventing-numbers-zh.md))。结论先行:钥匙真的存在;
> 其中一把的内部机械恰好是"解巨大方程组";传说中的万能钥匙今天悬在
> 一个猜想上,而对它的现代攻关方式恰好是"发明结构"。
> **三个少年幻想在此合流。**

---

## 〇、先重演一个历史时刻

1995 年,人类第一次由算法发现重要数学公式:PSLQ(整数关系探测,
入选 SIAM"二十世纪十大算法")找到了 π 的 BBP 公式。运行
[demo_transcendence_keys.py](demo_transcendence_keys.py) 现场重演:

```
PSLQ integer relation: [1, -4, 0, 0, 2, 1, 1, 0, 0]
residual at 50+ digits: 0.0

  =>  pi = sum_k (1/16^k) * [ +4/(8k+1) -2/(8k+4) -1/(8k+5) -1/(8k+6) ]
```

凭这条公式可以直接计算 π 的第十亿位十六进制数字而不算前面任何一位。
它不是被人想出来的,是被机器**探测**出来的——"钥匙"并非纯粹幻想。

---

## 一、已经铸成的四把钥匙

**第一把:逼近(Liouville 1844 → Roth 1955)。**
人类捕获的第一个超越数靠一条不等式:代数数不允许被有理数逼近得太好。
Liouville 数 Σ10^(−k!) 逼近得好到犯规,于是超越。Roth 定理
(Fields 奖)把这把钥匙磨到极限:指数 2 是代数数的底线。

**第二把:辅助函数 + Siegel 引理——发动机就是"解巨大方程组"。**
Hermite 证 e 超越(1873)、Lindemann 证 π 超越(1882,顺手终结两千年的
化圆为方)、Gelfond–Schneider 解决 Hilbert 第 7 问题(1934,2^√2)、
Baker 的对数线性型(1966,Fields 奖)——全部走同一条流水线:

1. 构造一个满足**海量整系数线性约束**的辅助多项式;
2. 用大小估计逼出矛盾("不存在严格介于 0 与 1 之间的整数")。

第 1 步靠什么?**Siegel 引理**:巨大的欠定整数线性方程组必有"小"解
(鸽笼原理)。换言之,**超越性证明的心脏就是解大方程组**——
"解方程组的方法能打开超越数"这个幻想,方向完全正确,
现实中的形态是"有限但巨大,外加对解的大小的控制"。

**第三把:函数方程——与 f(f(x)) = eˣ 精神同源,且有正式编制。**
**Mahler 方法**(1929):满足 f(x^d) 型代数函数方程的函数,其代数点上
的值常可证超越(如 Σx^(2ⁿ) 在代数点的值)。自动数的超越性后来由
Adamczewski–Bugeaud(2007)用子空间定理完成——而子空间定理
(Schmidt)正是第一把钥匙 Roth 定理的高维后代:钥匙之间互相咬合。
Nesterenko(1996)证明 π、e^π、Γ(1/4) 代数无关,凭据同样是结构:
模形式满足的微分方程组。**"从函数满足的方程出发证明其值超越"
是成建制的方法论。**

**第四把:数数(Cantor 1874)。**
代数数可数、实数不可数,故**几乎所有数都超越**。这把钥匙打开整座
仓库的大门,却照不亮任何一件具体展品——超越数遍地都是,
而指认任何一个具体的数都难如登天。这是本领域的核心悖剧。

---

## 二、传说中的万能钥匙:存在,悬在一个猜想上

**Schanuel 猜想**(1960s,经 Lang 流传):若 z₁,…,zₙ 在 ℚ 上线性无关,
则 z₁,…,zₙ, e^{z₁},…,e^{zₙ} 中至少 n 个代数无关。一句话,
蕴含 e+π、e·π、π^e、e^e、log π……的全部超越性。

现状有多窘迫?**连 e+π 是否无理都不知道。**但有一个三行的美丽事实:
e 与 π 是 x² − (e+π)x + e·π 的两根;若 e+π 与 e·π 都代数,则 e、π
作为代数系数二次方程的根都代数——与 Lindemann 矛盾。
所以**两者至少有一个超越,但没人知道是哪一个**。

再深两层,直指"钥匙"幻想本身:

- **Macintyre–Wilkie(1996)**:若 Schanuel 成立,实指数域
  (ℝ, +, ×, exp) 的全部一阶命题**可判定**。幻想中的钥匙被精确形式化
  为一个判定程序——而它整个悬挂在这一个猜想上。反方向立着一堵墙,
  **Richardson 定理**(1968):带绝对值(或 sin)的初等表达式
  "是否恒等于零"在一般情形**不可判定**。钥匙与墙之间只隔一层猜想。
- **Zilber 的伪指数域(2005)**:模型论的攻关方式是——
  **先发明一个 Schanuel 猜想成立的世界**(以纯结构公理造出
  "伪指数函数"),再猜想这个世界同构于 ℂ。看清这步棋:
  用第一个梦(发明结构)去攻第三个梦(超越性之钥),
  中间的引擎是第二个梦(方程组的可解性)。
  **三个幻想在 Zilber 纲领里合流成同一件事。**

---

## 三、回到本仓库自己的常数

**钥匙够得着的:Ω = W(1) = 0.5671…**——`semi_exp` 第一个方法的
展开点——**是被证明的超越数**,三行:Ω·e^Ω = 1,故 e^Ω = 1/Ω;
若 Ω 代数,Lindemann 说 e^Ω 超越,而 1/Ω 代数,矛盾。∎
(演示脚本对恒等式 Ω·e^Ω = 1 做了 50 位数值锚定。)

**钥匙够不着的:sexp(½) = 1.6463…、f'(0) = 0.8763…**——
四把钥匙全部不适用,**连无理性都完全 open**。它们不属于已知的周期
(Kontsevich–Zagier 框架;e 本身甚至不是周期,属"指数周期"),
也不在 Schanuel 的射程内——那是 exp 作用**一次**的世界,
而这些常数是 exp 作用**半次**的产物。本仓库早前的 PSLQ 实验
(系数 ≤ 1000,标准常数基)对它们保持沉默;同一台探测器对 π 一响即中。
这对比本身就是信息:**这些常数活在现有钥匙圈的外面。**

这不是绝路,是位置:历史上每一类"够不着的常数"——e 之于 Liouville
时代、2^√2 之于 Hermite 时代——最终都成了下一把钥匙的试金石。
"半迭代常数的超越性"今天没有任何工具,意味着谁造出工具,
谁就开了新疆域。

---

## 结案

把幻想精确化:"是否存在判定任意常数超越性的算法?"

- **无条件地**:没有,且 Richardson 一侧立着不可判定的墙;
- **有条件地**:对指数世界,有——价格是 Schanuel 猜想;
- **经验地**:有金属探测器(PSLQ),它真的发现过新数学(BBP),
  而它对本仓库的常数沉默。

少年时以为需要三把不同的钥匙——发明结构、解无限方程组、破解超越数。
地图摊开后:**那是同一把钥匙的三个齿。**

---

## 参考

- J. Liouville (1844);K. F. Roth, *Rational approximations to algebraic numbers* (1955);W. M. Schmidt,子空间定理 (1972)
- C. Hermite (1873);F. Lindemann (1882);A. O. Gelfond / Th. Schneider (1934);A. Baker, *Linear forms in the logarithms of algebraic numbers* (1966);C. L. Siegel,Siegel 引理 (1929)
- K. Mahler,Mahler 方法 (1929);B. Adamczewski, Y. Bugeaud, *On the complexity of algebraic numbers* (2007);Y. Nesterenko,π, e^π, Γ(1/4) 的代数无关性 (1996)
- G. Cantor (1874);R. Apéry,ζ(3) 无理 (1979)
- S. Schanuel 猜想(见 S. Lang, *Introduction to Transcendental Numbers*, 1966);A. Macintyre, A. J. Wilkie, *On the decidability of the real exponential field* (1996);D. Richardson (1968);B. Zilber, *Pseudo-exponentiation on algebraically closed fields of characteristic zero* (2005)
- M. Kontsevich, D. Zagier, *Periods* (2001)
- D. Bailey, P. Borwein, S. Plouffe, *On the rapid computation of various polylogarithmic constants*, Math. Comp. 66 (1997);H. Ferguson, D. Bailey,PSLQ 算法;SIAM 二十世纪十大算法 (Dongarra–Sullivan 2000)
- 本仓库:sexp(½)、f'(0) 的 50 位值见 [VALUES.md](VALUES.md);PSLQ 阴性结果见系列对话记录;演示代码 [demo_transcendence_keys.py](demo_transcendence_keys.py)
