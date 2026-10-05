# Schröder 方程如何找到解：从幂级数到 Koenigs 极限

## 摘要

Schröder 方程是：
$$
\phi(f(x))=\lambda\phi(x).
$$

它的目标是：在不动点附近换一个坐标，把复杂函数 \(f\) 变成简单缩放
$$
w\longmapsto \lambda w.
$$

但关键问题是：

> 这样的坐标 \(\phi\) 到底怎么找？

答案有两条非常重要的桥梁：

1. **幂级数法**：假设 \(\phi\) 是一个幂级数，把非线性项逐阶消掉。
2. **Koenigs 极限法**：观察点反复迭代靠近不动点的速度，把线性收缩因子除掉，极限就是线性化坐标。

这两条路都来自同一个直觉：

> Schröder 解是一把重新标尺的尺子，它把不动点附近的复杂迭代变成纯粹的乘法缩放。

阅读这篇文档时，可以把整件事看成四步：

$$
\text{找到不动点}
\longrightarrow
\text{把不动点移到原点}
\longrightarrow
\text{消掉非线性高阶项}
\longrightarrow
\text{得到精确缩放坐标}.
$$

也就是说，Schröder 方程不是第一步，而是最后被逼出来的目标形式。

## 1. 先把不动点搬到原点

设 \(c\) 是 \(f\) 的不动点：
$$
f(c)=c.
$$

记
$$
\lambda=f'(c).
$$

为了看清不动点附近的结构，先把 \(c\) 平移到 \(0\)。

令
$$
y=x-c,
$$
并定义
$$
F(y)=f(c+y)-c.
$$

于是
$$
F(0)=0,
$$
并且
$$
F'(0)=\lambda.
$$

这一步只是换了观察原点。

原来的点是 \(x\)，新坐标里的点是
$$
y=x-c.
$$

原来的函数是
$$
x\longmapsto f(x).
$$

新坐标里的函数变成
$$
y\longmapsto F(y)=f(c+y)-c.
$$

也就是说，先从 \(c+y\) 回到原坐标，作用 \(f\)，再减去 \(c\) 回到以不动点为中心的新坐标。

如果 \(f\) 在 \(c\) 附近解析，那么 \(F\) 在 \(0\) 附近可以写成：
$$
F(y)=\lambda y+a_2y^2+a_3y^3+a_4y^4+\cdots.
$$

这说明：\(F\) 的第一阶行为是线性的，但后面有很多高阶扰动。

Schröder 方程要做的事情就是：

> 找一个新坐标，把这些高阶扰动吸收掉，只留下 \(\lambda y\)。

如果 \(F(y)\) 本来就等于 \(\lambda y\)，那问题已经结束。

真正的困难全在：
$$
a_2y^2+a_3y^3+a_4y^4+\cdots
$$
这些非线性项里。

## 2. Schröder 方程在原点形式

在新变量 \(y\) 下，Schröder 方程写成：
$$
\psi(F(y))=\lambda\psi(y).
$$

这里 \(\psi\) 是新的坐标函数。

为什么写成这个样子？

因为我们希望新坐标 \(w=\psi(y)\) 中的运动尽可能简单。

如果
$$
w=\psi(y),
$$
那么作用一次 \(F\) 后，新坐标变成
$$
\psi(F(y)).
$$

而“最简单的缩放运动”应该是
$$
w\longmapsto \lambda w.
$$

由于 \(w=\psi(y)\)，这就要求
$$
\psi(F(y))=\lambda\psi(y).
$$

所以 Schröder 方程不是凭空写出来的，而是下面这个愿望的翻译：

> 我想让 \(F\) 在新坐标中精确等于乘以 \(\lambda\)。

如果找到了 \(\psi\)，那么在 \(\psi\)-坐标里：
$$
y\longmapsto F(y)
$$
就变成：
$$
w\longmapsto \lambda w.
$$

也就是说：
$$
\psi\circ F\circ \psi^{-1}(w)=\lambda w.
$$

这叫线性化。

如果再回到原变量 \(x\)，对应的 Schröder 函数就是
$$
\phi(x)=\psi(x-c).
$$

于是
$$
\phi(f(x))
=\psi(f(x)-c)
=\psi(F(x-c))
=\lambda\psi(x-c)
=\lambda\phi(x).
$$

所以原变量里的方程
$$
\phi(f(x))=\lambda\phi(x)
$$
和原点形式
$$
\psi(F(y))=\lambda\psi(y)
$$
是同一个东西。

只是原点形式更干净。

## 3. 第一条桥梁：幂级数逐阶消项

假设 \(\psi\) 也可以写成幂级数：
$$
\psi(y)=y+b_2y^2+b_3y^3+b_4y^4+\cdots.
$$

这里把一次项系数固定为 \(1\)，是为了固定尺度。

因为如果 \(\psi\) 是一个解，那么
$$
C\psi
$$
也是解。

还有两个隐含要求：

第一，\(\psi(0)=0\)。

因为 \(0\) 是不动点，线性化后也应该对应缩放运动的固定点 \(0\)。

事实上，把 \(y=0\) 代入
$$
\psi(F(y))=\lambda\psi(y)
$$
得到
$$
\psi(0)=\lambda\psi(0).
$$

若 \(\lambda\ne 1\)，这会逼出
$$
\psi(0)=0.
$$

第二，\(\psi'(0)\ne 0\)。

因为 \(\psi\) 要作为局部坐标，不能在 \(0\) 附近塌掉。

为了固定尺度，通常取
$$
\psi'(0)=1.
$$

所以最自然的形式就是
$$
\psi(y)=y+b_2y^2+b_3y^3+\cdots.
$$

现在把
$$
F(y)=\lambda y+a_2y^2+a_3y^3+\cdots
$$
代入 Schröder 方程：
$$
\psi(F(y))=\lambda\psi(y).
$$

左边是：
$$
\psi(\lambda y+a_2y^2+a_3y^3+\cdots).
$$

右边是：
$$
\lambda(y+b_2y^2+b_3y^3+\cdots).
$$

然后比较两边的 \(y^2,y^3,y^4,\ldots\) 的系数。

这样就可以一个一个解出
$$
b_2,b_3,b_4,\ldots.
$$

所以幂级数法的直觉是：

> 新坐标 \(\psi\) 逐阶修正原坐标，把 \(F\) 的非线性项一项一项消掉。

这一步可以理解为一种“坐标清洗”：

$$
y
\quad\longrightarrow\quad
y+b_2y^2
\quad\longrightarrow\quad
y+b_2y^2+b_3y^3
\quad\longrightarrow\quad
\cdots
$$

每加一个系数 \(b_n\)，就试图把第 \(n\) 阶的非线性误差清掉。

## 4. 二阶项怎么出来

为了看见机制，先只算到二阶。

设
$$
F(y)=\lambda y+a_2y^2+O(y^3),
$$
并设
$$
\psi(y)=y+b_2y^2+O(y^3).
$$

那么
$$
\psi(F(y))
=F(y)+b_2F(y)^2+O(y^3).
$$

代入 \(F(y)\)：
$$
\psi(F(y))
=\lambda y+a_2y^2+b_2\lambda^2y^2+O(y^3).
$$

右边是：
$$
\lambda\psi(y)
=\lambda y+\lambda b_2y^2+O(y^3).
$$

比较 \(y^2\) 系数：
$$
a_2+b_2\lambda^2=\lambda b_2.
$$

所以
$$
b_2=\frac{a_2}{\lambda-\lambda^2}
=\frac{a_2}{\lambda(1-\lambda)}.
$$

这就是第一步修正。

它告诉我们：只要分母不出问题，就可以把二阶非线性项吸收到坐标变化里。

更高阶也是类似，只是公式越来越复杂。

例如三阶项也能看见同样的机制。

设
$$
F(y)=\lambda y+a_2y^2+a_3y^3+O(y^4),

\psi(y)=y+b_2y^2+b_3y^3+O(y^4).
$$

那么
$$
\psi(F(y))=F(y)+b_2F(y)^2+b_3F(y)^3+O(y^4).
$$

保留到三阶：
$$
F(y)^2=\lambda^2y^2+2\lambda a_2y^3+O(y^4),

F(y)^3=\lambda^3y^3+O(y^4).
$$

所以左边的三阶系数是
$$
a_3+2\lambda a_2b_2+\lambda^3b_3.
$$

右边
$$
\lambda\psi(y)
$$
的三阶系数是
$$
\lambda b_3.
$$

比较三阶系数：
$$
a_3+2\lambda a_2b_2+\lambda^3b_3=\lambda b_3.
$$

于是
$$
b_3=\frac{a_3+2\lambda a_2b_2}{\lambda-\lambda^3}.
$$

这里可以看清楚递推结构：

- \(b_2\) 先由二阶项决定；
- \(b_3\) 再由 \(a_3\) 和已经知道的 \(b_2\) 决定；
- 后面的 \(b_4,b_5,\ldots\) 继续这样递推。

这就是“逐阶消项”的具体含义。

## 5. 共振：什么时候幂级数法会卡住

在更高阶比较系数时，常常会出现类似
$$
\lambda-\lambda^n
$$
这样的分母。

如果
$$
\lambda^{n-1}=1,
$$
分母就可能为零。

这叫共振。

共振意味着：某些高阶项无法简单通过坐标变化消掉。

因此，Schröder 方程不是永远无条件可解。它的解析解会受到不动点类型和乘子 \(\lambda\) 的影响。

在最常见、最干净的情形中，如果
$$
0<|\lambda|<1,
$$
也就是不动点是吸引的，那么 Koenigs 定理给出非常好的局部解析线性化。

## 6. 第二条桥梁：Koenigs 极限

现在看更漂亮的一条路。

假设
$$
0<|\lambda|<1.
$$

这表示 \(0\) 是吸引不动点。

于是对靠近 \(0\) 的点 \(y\)，反复迭代会靠近 \(0\)：
$$
F^n(y)\longrightarrow 0.
$$

而一阶近似告诉我们：
$$
F(y)\approx \lambda y.
$$

所以反复迭代后大致有：
$$
F^n(y)\approx \lambda^n y.
$$

问题是：\(F^n(y)\) 本身趋向 \(0\)，直接看会什么都看不见。

于是把主要的线性收缩因子除掉：
$$
\frac{F^n(y)}{\lambda^n}.
$$

这一步非常关键。

如果 \(F\) 完全等于线性函数
$$
F(y)=\lambda y,
$$
那么
$$
F^n(y)=\lambda^n y.
$$

于是
$$
\frac{F^n(y)}{\lambda^n}=y.
$$

也就是说，在线性模型里，这个比值正好恢复原坐标。

但真实的 \(F\) 是
$$
F(y)=\lambda y+\text{高阶项}.
$$

所以
$$
\frac{F^n(y)}{\lambda^n}
$$
是在问：

> 当轨道不断靠近不动点时，扣掉标准线性收缩后，还剩下什么稳定坐标？

如果这个极限存在，就定义：
$$
\psi(y)=\lim_{n\to\infty}\frac{F^n(y)}{\lambda^n}.
$$

这就是 Koenigs 极限。

可以把
$$
\psi_n(y)=\frac{F^n(y)}{\lambda^n}
$$
看成一列越来越精细的坐标尺。

第 \(n\) 把尺子观察的是：点 \(y\) 经过 \(n\) 次迭代后，按照线性模型倒推回来的位置。

当 \(n\to\infty\) 时，轨道已经非常靠近不动点，非线性项越来越弱，于是这些尺子趋向一个稳定极限。

那个稳定极限就是 \(\psi\)。

## 7. 为什么 Koenigs 极限满足 Schröder 方程

假设
$$
\psi(y)=\lim_{n\to\infty}\frac{F^n(y)}{\lambda^n}.
$$

那么：
$$
\psi(F(y))
=\lim_{n\to\infty}\frac{F^n(F(y))}{\lambda^n}.
$$

因为
$$
F^n(F(y))=F^{n+1}(y),
$$
所以：
$$
\psi(F(y))
=\lim_{n\to\infty}\frac{F^{n+1}(y)}{\lambda^n}.
$$

把一个 \(\lambda\) 提出来：
$$
\frac{F^{n+1}(y)}{\lambda^n}
=\lambda\frac{F^{n+1}(y)}{\lambda^{n+1}}.
$$

因此：
$$
\psi(F(y))
=\lambda\lim_{n\to\infty}\frac{F^{n+1}(y)}{\lambda^{n+1}}
=\lambda\psi(y).
$$

这正是 Schröder 方程。

所以 Koenigs 极限的意义是：

> 点在迭代中靠近不动点；把标准线性收缩速度除掉，剩下的极限就是线性化坐标。

这里还有一个更直观的有限步版本。

定义
$$
\psi_n(y)=\frac{F^n(y)}{\lambda^n}.
$$

那么
$$
\psi_n(F(y))
=\frac{F^n(F(y))}{\lambda^n}
=\frac{F^{n+1}(y)}{\lambda^n}
=\lambda\frac{F^{n+1}(y)}{\lambda^{n+1}}
=\lambda\psi_{n+1}(y).
$$

也就是说，有限 \(n\) 时还不是精确的 Schröder 方程，而是：
$$
\psi_n(F(y))=\lambda\psi_{n+1}(y).
$$

当 \(n\to\infty\)，如果 \(\psi_n\to\psi\)，就得到：
$$
\psi(F(y))=\lambda\psi(y).
$$

这解释了为什么极限一旦存在，就必然满足 Schröder 方程。

## 8. 一个简单例子

设
$$
F(y)=\frac12 y+y^2.
$$

这里
$$
\lambda=\frac12.
$$

Schröder 方程是：
$$
\psi\!\left(\frac12y+y^2\right)=\frac12\psi(y).
$$

我们假设
$$
\psi(y)=y+b_2y^2+O(y^3).
$$

前面二阶公式给出：
$$
b_2=\frac{a_2}{\lambda(1-\lambda)}.
$$

这里 \(a_2=1\)，\(\lambda=\frac12\)，所以：
$$
b_2=\frac{1}{\frac12(1-\frac12)}=4.
$$

因此开头几项是：
$$
\psi(y)=y+4y^2+\cdots.
$$

这说明，新坐标不是简单的 \(y\)，而是要加上修正项，才能把
$$
y\longmapsto \frac12y+y^2
$$
变成纯粹缩放
$$
w\longmapsto \frac12w.
$$

## 9. 和 Abel 方程的连接

如果已经找到 Schröder 解：
$$
\psi(F(y))=\lambda\psi(y),
$$
那么取对数可以得到 Abel 坐标：
$$
A(y)=\frac{\log\psi(y)}{\log\lambda}.
$$

因为：
$$
A(F(y))
=\frac{\log\psi(F(y))}{\log\lambda}
=\frac{\log(\lambda\psi(y))}{\log\lambda}
=A(y)+1.
$$

所以：

- Schröder 方程把迭代变成乘法；
- Abel 方程把迭代变成加法；
- 对数把乘法变成加法。

这就是二者之间最直接的桥梁。

## 10. 为什么 Kneser 要用反函数 \(\log\)

现在回到指数函数：
$$
f(z)=e^z.
$$

它的复不动点 \(c\) 满足：
$$
e^c=c.
$$

在这个点，
$$
f'(c)=e^c=c.
$$

而 Kneser 选用的那个复不动点满足：
$$
|c|>1.
$$

这表示 \(c\) 对 \(e^z\) 是排斥不动点。

排斥不动点附近，正向迭代会离开 \(c\)，不适合直接使用吸引型 Koenigs 极限。

但指数的局部反函数是对数。

对
$$
L(z)=\log z
$$
来说，同一个 \(c\) 满足：
$$
L(c)=c.
$$

并且
$$
L'(c)=\frac1c,
$$
所以：
$$
\left|\frac1c\right|<1.
$$

这表示 \(c\) 对 \(\log z\) 是吸引不动点。

于是可以对 \(\log\) 使用 Koenigs/Schröder 线性化。

这就是 Kneser 路线的关键技巧之一：

> 指数在复不动点附近是排斥的，于是改看反函数对数；对数在同一点附近是吸引的。

用前面的语言说，Kneser 做的是：

$$
\text{指数的排斥不动点}
\quad\longrightarrow\quad
\text{对数的吸引不动点}
\quad\longrightarrow\quad
\text{Koenigs 线性化}
\quad\longrightarrow\quad
\text{Schröder 坐标}
\quad\longrightarrow\quad
\text{Abel 坐标}.
$$

这就是为什么文献里会先出现复不动点、\(\log\)、Schröder 函数，再回到半指数。

它不是绕远路，而是为了把问题放进一个可以收敛的局部模型里。

## 11. 总结：Schröder 解是怎么“长出来”的

Schröder 方程不是硬猜出来的。

它的解有非常自然的来源。

第一条来源是幂级数：
$$
F(y)=\lambda y+a_2y^2+a_3y^3+\cdots,

\psi(y)=y+b_2y^2+b_3y^3+\cdots.
$$

把它们代入
$$
\psi(F(y))=\lambda\psi(y),
$$
逐阶比较系数，就能逐步求出 \(b_2,b_3,\ldots\)。

第二条来源是 Koenigs 极限：
$$
\psi(y)=\lim_{n\to\infty}\frac{F^n(y)}{\lambda^n}.
$$

它的直觉是：

> 迭代会把点拉向吸引不动点；除掉标准线性收缩速度后，剩下的稳定量就是线性化坐标。

所以最朴素的桥梁是：

$$
\text{不动点附近的一阶缩放}
\longrightarrow
\text{高阶扰动}
\longrightarrow
\text{坐标修正}
\longrightarrow
\text{精确缩放}
\longrightarrow
\text{Schröder 方程}.
$$

一句话：

> Schröder 解是一把显微镜；它重新标定不动点附近的尺度，让复杂迭代看起来像单纯的乘法。
