# Kneser 1950 实解析半指数函数的证明

下面给出一条按 Kneser 资料整理出来的严谨证明。证明的核心是：先构造实解析 Abel 函数 \(\Psi\)，再用
\[
\vartheta(x)=\Psi^{-1}\!\left(\Psi(x)+\frac12\right)
\]
得到半迭代。

## 定理

存在实解析、严格递增函数 \(\vartheta:\mathbb R\to\mathbb R\)，使得
\[
\vartheta(\vartheta(x))=e^x\qquad(x\in\mathbb R).
\]

## 证明

第一步，Abel 化。若存在实解析双射
\[
\Psi:\mathbb R\to(0,\infty),\qquad \Psi'(x)>0,
\]
满足 Abel 方程
\[
\Psi(e^x)=\Psi(x)+1, \tag{A}
\]
则令
\[
\vartheta(x)=\Psi^{-1}\!\left(\Psi(x)+\frac12\right).
\]
因为 \(\Psi\) 是实解析微分同胚，\(\vartheta\) 也是实解析且严格递增。并且
\[
\Psi(\vartheta(\vartheta(x)))
=\Psi(x)+1
=\Psi(e^x).
\]
由 \(\Psi\) 单射，得
\[
\vartheta(\vartheta(x))=e^x.
\]
所以只需构造这样的 \(\Psi\)。

第二步，取指数函数的复不动点。设
\[
e^c=c,\qquad c=a+ib,\quad b>0
\]
为离实轴最近的上半平面不动点。Kneser 通过实虚部分离证明其存在唯一性：
\[
e^a\cos b=a,\qquad e^a\sin b=b,
\]
等价于
\[
a=b\cot b,\qquad b^2=e^{2a}-a^2.
\]
在半带 \(0<b<\pi\) 中两条曲线恰有一个交点，因此存在唯一这样的 \(c\)。数值上
\[
a\approx0.3181315,\qquad b\approx1.3372357,\qquad |c|=e^a>1.
\]
因为 \(0<b<\pi\)，上半平面主支对数满足
\[
\log c=c.
\]
于是对 \(L(z)=\log z\)，有
\[
L(c)=c,\qquad L'(c)=\frac1c,\qquad \left|\frac1c\right|<1.
\]
所以 \(c\) 是 \(L\) 的吸引不动点。

第三步，用 Koenigs 定理构造 Schroder 函数。由 Koenigs 定理，在 \(c\) 的邻域内存在唯一解析函数 \(\chi\)，满足
\[
\chi(c)=0,\qquad \chi'(c)=1,
\]
以及
\[
\chi(\log z)=\frac1c\,\chi(z). \tag{S}
\]
等价地，在相应邻域中
\[
\chi(e^z)=c\,\chi(z). \tag{S'}
\]
Kneser 随后沿反复取对数的轨道解析延拓 \(\chi\)。设
\[
e_0=0,\quad e_{n+1}=e^{e_n}.
\]
在上半平面及其实边界去掉这些特殊点后，反复取主支对数会趋向 \(c\)。因此可定义
\[
\chi(z)=c^n\chi_0(\log^{\circ n} z)
\]
只要 \(\log^{\circ n}z\) 已落入 \(c\) 的局部邻域。Schroder 方程保证这个定义与 \(n\) 的选择相容，所以 \(\chi\) 被解析延拓到 Kneser 的区域 \(\mathfrak G\)，并仍满足 \((S)\)、\((S')\)。

第四步，证明 \(\chi\) 在该区域单叶。局部反函数 \(g=\chi^{-1}\) 在 \(0\) 的邻域存在。由 \((S')\) 得
\[
g(c\zeta)=\exp(g(\zeta)). \tag{I}
\]
因为 \(|c|>1\)，公式 \((I)\) 可把 \(g\) 从小圆盘逐步延拓到半径扩大 \(|c|\) 倍的圆盘，反复进行得到整个复平面上的整函数 \(g\)。于是
\[
g(\chi(z))=z
\]
先在 \(c\) 附近成立，再由解析延拓在整个区域成立。因此 \(\chi\) 单叶，且 \(\chi'\neq0\)。

第五步，把 Schroder 函数变成 Abel 函数。取
\[
w(z)=\log\chi(z)
\]
的适当单值分支，并规定
\[
\lim_{z\to c}\bigl(w(z)-\log(z-c)\bigr)=0.
\]
由 \(\chi(e^z)=c\chi(z)\)，得
\[
w(e^z)=w(z)+\log c.
\]
由于主支下 \(\log c=c\)，所以
\[
w(e^z)=w(z)+c. \tag{B}
\]

第六步，做 Kneser 的共形归一化。Kneser 考察 \(w\)-平面中由基本区域反复平移 \(w\mapsto w+c\) 得到的区域 \(\mathfrak B\)。区域 \(\mathfrak B\) 单连通，且平移
\[
T(w)=w+c
\]
把 \(\mathfrak B\) 保持为自身。由 Riemann 映射定理，把 \(\mathfrak B\) 共形映到上半平面。平移 \(T\) 在上半平面中对应一个无内点不动点的自同构。Kneser 排除双曲情形，得到它必为抛物型自同构。于是可选择共形映射 \(R\)，使得
\[
R(w+c)=R(w)+1.
\]
定义
\[
\Psi(z)=R(w(z)).
\]
由 \((B)\) 立刻得到
\[
\Psi(e^z)=\Psi(z)+1. \tag{A}
\]

第七步，证明 \(\Psi\) 在整条实轴上实解析且单调。最初 \(\Psi\) 在实轴某个区间的一侧解析，并把贴近该区间的上半小带映到上半平面中贴近实轴的小带。因此由 Schwarz 反射原理，\(\Psi\) 可跨过该实区间解析延拓，并在该区间取实值。

再用 Abel 方程传播解析性：若 \(\Psi\) 已在一段实区间上解析，则
\[
\Psi(x)=\Psi(e^x)-1
\]
把它向左延拓，而
\[
\Psi(x)=\Psi(\log x)+1
\]
把它向右延拓。反复进行，\(\Psi\) 在整个 \(\mathbb R\) 上实解析，并满足
\[
\Psi(e^x)=\Psi(x)+1\qquad(x\in\mathbb R).
\]
初始区间上 \(\Psi'(x)>0\)，而延拓公式给出
\[
(\Psi(e^x)-1)'=\Psi'(e^x)e^x>0,\qquad
(\Psi(\log x)+1)'=\frac{\Psi'(\log x)}x>0,
\]
所以
\[
\Psi'(x)>0\qquad(x\in\mathbb R).
\]
因此 \(\Psi\) 严格递增。

最后看值域。由
\[
\Psi(e^x)=\Psi(x)+1
\]
可知 \(x\to+\infty\) 时 \(\Psi(x)\to+\infty\)。令 \(x\to-\infty\)，则 \(e^x\to0\)，所以
\[
\Psi(x)=\Psi(e^x)-1\to \Psi(0)-1.
\]
\(\Psi\) 还可加任意常数而不破坏 Abel 方程，因此归一化为
\[
\lim_{x\to-\infty}\Psi(x)=0.
\]
于是
\[
\Psi(\mathbb R)=(0,\infty).
\]

综上，存在实解析严格递增双射 \(\Psi:\mathbb R\to(0,\infty)\) 满足 Abel 方程。代回第一步，定义
\[
\boxed{\vartheta(x)=\Psi^{-1}\!\left(\Psi(x)+\frac12\right)}
\]
便得到实解析、严格递增函数，并且
\[
\boxed{\vartheta(\vartheta(x))=e^x}.
\]

这就是 Kneser 1950 年构造实解析半指数函数的完整逻辑链。注意：这证明的是存在性和 Kneser 规范化下的典范构造，不是说所有连续或非解析的复合平方根都唯一。

## 存在性与唯一性到底能证明什么

结论要分层说：

1. **存在性可以证明。** Kneser 1950 年原文证明了存在实解析、严格递增的 Abel 函数
\[
\Psi(e^x)=\Psi(x)+1,
\]
从而存在实解析、严格递增函数
\[
\vartheta(x)=\Psi^{-1}\!\left(\Psi(x)+\frac12\right)
\]
满足
\[
\vartheta(\vartheta(x))=e^x.
\]

2. **只在“实解析、严格递增”这一类中，唯一性是假的。** 设 \(\Psi\) 是一个实解析 Abel 函数。取
\[
h(t)=t+\varepsilon\sin(2\pi t),
\qquad 0<|\varepsilon|<\frac1{2\pi}.
\]
则
\[
h(t+1)=h(t)+1,
\qquad
h'(t)=1+2\pi\varepsilon\cos(2\pi t)>0.
\]
定义
\[
\widetilde\Psi(x)=h(\Psi(x)).
\]
于是
\[
\widetilde\Psi(e^x)
=h(\Psi(e^x))
=h(\Psi(x)+1)
=h(\Psi(x))+1
=\widetilde\Psi(x)+1.
\]
因此 \(\widetilde\Psi\) 仍是实解析、严格递增的 Abel 函数，并给出另一个半迭代
\[
\widetilde\vartheta(x)
=\widetilde\Psi^{-1}\!\left(\widetilde\Psi(x)+\frac12\right).
\]
一般来说 \(\widetilde\vartheta\ne\vartheta\)。例如
\[
h\!\left(t+\frac12\right)
=t+\frac12-\varepsilon\sin(2\pi t),
\]
而
\[
h(t)+\frac12
=t+\frac12+\varepsilon\sin(2\pi t),
\]
二者通常不同。所以仅靠实解析性和单调性不能推出唯一性。

3. **Kneser 型解在附加复解析规范后有唯一性。** Trappmann-Kouznetsov 给出了全纯 Abel 函数的唯一性判据：在合适的初始区域 \(H\) 上，若 Abel 函数 \(\alpha\) 满足
\[
\alpha(F(z))=\alpha(z)+1,
\]
并且在 \(H\) 上全纯、单叶，归一化 \(\alpha(d)=0\)，同时整数平移覆盖整个复平面
\[
\bigcup_{k\in\mathbb Z}\bigl(\alpha(H)+k\bigr)=\mathbb C,
\]
则这样的 Abel 函数至多一个。Kneser 构造出的实解析 Abel 函数满足这个判据。因此，Kneser 解不是在所有实解析半迭代中唯一，而是在这套复解析、单叶、平移覆盖的规范条件下唯一。

简而言之：
\[
\boxed{\text{存在性可以证明；无条件唯一性不能证明，因为它是假的。}}
\]
\[
\boxed{\text{加入 Trappmann-Kouznetsov 的复解析唯一性判据后，Kneser 型 Abel 函数唯一。}}
\]

参考资料：

- H. Kneser, *Reelle analytische Lösungen der Gleichung \(\vartheta(\vartheta(x))=e^x\) und verwandter Funktionalgleichungen*, J. Reine Angew. Math. 187 (1950), 56-67. <https://eudml.org/doc/150158>
- G. Szekeres, *Fractional iteration of exponentially growing functions*, J. Austral. Math. Soc. 2 (1961), 301-320. <https://www.cambridge.org/core/services/aop-cambridge-core/content/view/60E1D3CCC6B3BE35F6AFE622EA22C58C/S1446788700026902a.pdf/fractional-iteration-of-exponentially-growing-functions.pdf>
- H. Trappmann and D. Kouznetsov, *Uniqueness of Holomorphic Abel Functions*, Aequationes Mathematicae 81 (2011), 65-76. <https://link.springer.com/article/10.1007/s00010-010-0021-6>
