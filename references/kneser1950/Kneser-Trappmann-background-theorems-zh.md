# Kneser 与 Trappmann-Kouznetsov 论文背后的定理工具箱

这份文档列出并证明阅读 Kneser 1950 及 Trappmann-Kouznetsov 2011 时实际需要的主要背景定理。目标不是重写整本复分析教材，而是把论文证明链中被调用的定理、引理、规范化步骤都放到一个地方。

## 0. 总览：证明链依赖哪些定理

Kneser 的存在性证明依赖：

1. Abel 方程线性化迭代；
2. Koenigs 局部线性化定理；
3. 指数函数复不动点的存在与计数；
4. 单值对数分支存在定理；
5. 解析延拓唯一性与恒等定理；
6. 反函数定理与单叶性判别；
7. Schwarz 引理；
8. Schwarz 反射原理；
9. Riemann 映射定理；
10. 圆盘自同构分类；
11. 实解析反函数定理；
12. 周期扰动给出非唯一性。

Trappmann-Kouznetsov 的唯一性证明依赖：

1. 初始曲线与初始区域；
2. Abel 函数的反函数形式；
3. 整数平移覆盖；
4. 整函数延拓拼接；
5. 复平面双全纯自同构只能是仿射函数；
6. 全纯 Abel 函数唯一性判据。

下面逐条说明并证明。

---

## 1. Abel 方程给出半迭代

**定理 1.1（Abel 半迭代引理）。** 设 \(I,J\subset\mathbb R\) 是区间，\(\Psi:I\to J\) 是双射，且
\[
\Psi(f(x))=\Psi(x)+1.
\]
若对所有 \(x\in I\)，\(\Psi(x)+1/2\in J\)，定义
\[
\vartheta(x)=\Psi^{-1}\!\left(\Psi(x)+\frac12\right),
\]
则
\[
\vartheta(\vartheta(x))=f(x).
\]

**证明。** 由定义，
\[
\Psi(\vartheta(x))=\Psi(x)+\frac12.
\]
再作用一次，
\[
\Psi(\vartheta(\vartheta(x)))
=\Psi(\vartheta(x))+\frac12
=\Psi(x)+1
=\Psi(f(x)).
\]
因为 \(\Psi\) 单射，所以
\[
\vartheta(\vartheta(x))=f(x).
\]
证毕。

**在 Kneser 中的用法。** 取 \(f(x)=e^x\)，构造
\[
\Psi(e^x)=\Psi(x)+1,\qquad \Psi:\mathbb R\to(0,\infty),
\]
然后得到
\[
\vartheta(x)=\Psi^{-1}\!\left(\Psi(x)+\frac12\right).
\]

---

## 2. 周期扰动说明纯实解析唯一性不成立

**定理 2.1（Abel 函数的周期扰动）。** 若 \(\Psi\) 满足
\[
\Psi(f(x))=\Psi(x)+1,
\]
而 \(h:\mathbb R\to\mathbb R\) 满足
\[
h(t+1)=h(t)+1,
\]
则
\[
\widetilde\Psi(x)=h(\Psi(x))
\]
也满足
\[
\widetilde\Psi(f(x))=\widetilde\Psi(x)+1.
\]

**证明。**
\[
\widetilde\Psi(f(x))
=h(\Psi(f(x)))
=h(\Psi(x)+1)
=h(\Psi(x))+1
=\widetilde\Psi(x)+1.
\]
证毕。

若进一步 \(h\) 实解析且 \(h'>0\)，则 \(\widetilde\Psi\) 仍是实解析严格递增 Abel 函数。

例如
\[
h(t)=t+\varepsilon\sin(2\pi t),\qquad 0<|\varepsilon|<\frac1{2\pi}.
\]
则
\[
h(t+1)=h(t)+1,\qquad h'(t)=1+2\pi\varepsilon\cos(2\pi t)>0.
\]
这说明：仅要求实解析和严格递增，Abel 函数不唯一，半迭代也通常不唯一。

---

## 3. 恒等定理

**定理 3.1（恒等定理）。** 设 \(D\subset\mathbb C\) 是连通区域，\(f,g\) 在 \(D\) 上全纯。若集合
\[
\{z\in D:f(z)=g(z)\}
\]
有聚点在 \(D\) 中，则 \(f\equiv g\)。

**证明。** 令 \(h=f-g\)。则 \(h\) 全纯，且零点集合有内聚点。取聚点 \(a\in D\)。若 \(h\) 不恒为零，则在 \(a\) 的 Taylor 展开
\[
h(z)=\sum_{n=0}^\infty c_n(z-a)^n
\]
中存在最小 \(m\) 使 \(c_m\ne0\)。于是
\[
h(z)=(z-a)^m u(z),
\]
其中 \(u\) 在 \(a\) 附近全纯且 \(u(a)=c_m\ne0\)。所以 \(u\) 在 \(a\) 附近不为零，\(h\) 在 \(a\) 附近除 \(a\) 外无零点。这与零点有聚点矛盾。故 \(h\equiv0\)。证毕。

---

## 4. 解析延拓唯一性

**定理 4.1（解析延拓唯一性）。** 若两个全纯函数在连通区域 \(D\) 上都是同一局部解析函数的延拓，并且它们在非空开集上一致，则它们在整个 \(D\) 上一致。

**证明。** 这是恒等定理的直接推论。两个函数之差在非空开集上为零，因此零点有聚点，故差函数恒为零。证毕。

**在 Kneser 中的用法。** Kneser 分层定义
\[
\chi_{n+1}(z)=c\,\chi(\log z).
\]
在相邻区域重叠处，这个定义与旧的 \(\chi\) 一致；由解析延拓唯一性，拼接出的 \(\chi\) 是良定义的。

---

## 5. 单值对数分支存在定理

**定理 5.1（非零全纯函数在单连通区域上的对数）。** 设 \(D\) 单连通，\(f\) 在 \(D\) 上全纯且处处不为零。则存在全纯函数 \(g\)，使得
\[
e^{g(z)}=f(z).
\]
也就是说，\(f\) 有单值全纯对数。

**证明。** 因为 \(f\ne0\)，函数
\[
\frac{f'}{f}
\]
在 \(D\) 上全纯。单连通区域上全纯函数有原函数，所以存在 \(g\) 满足
\[
g'=\frac{f'}{f}.
\]
于是
\[
\left(\frac{e^g}{f}\right)'
=\frac{e^g g'f-e^g f'}{f^2}
=0.
\]
所以 \(e^g/f\) 是常数。调整 \(g\) 加一个常数，即可使
\[
e^g=f.
\]
证毕。

**推论 5.2（平方根）。** 若 \(D\) 单连通，\(f\) 全纯且不为零，则存在全纯 \(h\) 使
\[
h^2=f.
\]

**证明。** 由定理 5.1，\(f=e^g\)。取
\[
h=e^{g/2}.
\]
证毕。

**在 Kneser 中的用法。** 需要在某些区域上选择 \(\log\chi(z)\) 的单值分支。因为区域选得单连通且避开 \(\chi=0\)，所以可选单值对数。

---

## 6. 复反函数定理

**定理 6.1（复反函数定理）。** 若 \(f\) 在 \(a\) 附近全纯，且
\[
f'(a)\ne0,
\]
则存在 \(a\) 的邻域 \(U\) 与 \(f(a)\) 的邻域 \(V\)，使得
\[
f:U\to V
\]
双全纯。

**证明。** 写 Taylor 展开
\[
f(z)=f(a)+c_1(z-a)+c_2(z-a)^2+\cdots,\qquad c_1=f'(a)\ne0.
\]
令
\[
F(z)=f(z)-w.
\]
对 \(w\) 足够接近 \(f(a)\)，在小圆周 \(|z-a|=r\) 上，主项
\[
c_1(z-a)
\]
支配余项与 \(f(a)-w\)。由 Rouche 定理，方程 \(f(z)=w\) 在圆盘内恰有一个根。于是 \(f\) 在小邻域内一一对应。反函数的全纯性可由 Cauchy 积分公式或隐函数定理推出。证毕。

**在 Kneser 中的用法。** \(\chi'(c)=1\)，所以 \(\chi\) 在 \(c\) 附近有局部反函数 \(\chi^{-1}\)。

---

## 7. Koenigs 局部线性化定理

**定理 7.1（Koenigs 定理，吸引不动点情形）。** 设 \(f\) 在 \(c\) 附近定义，并满足
\[
f(c)=c.
\]
若存在 \(a,M,\delta\)，其中
\[
0<|a|<1,\qquad \delta>1,
\]
使得
\[
|f(x)-c-a(x-c)|\le M|x-c|^\delta,
\]
则对 \(x\) 足够接近 \(c\)，极限
\[
\chi(x)=\lim_{n\to\infty}a^{-n}\bigl(f^{\circ n}(x)-c\bigr)
\]
存在，并满足 Schroder 方程
\[
\chi(f(x))=a\chi(x).
\]
若 \(f\) 在 \(c\) 附近全纯，则 \(\chi\) 全纯且
\[
\chi'(c)=1.
\]

**证明。** 取 \(q\) 满足
\[
|a|<q<|a|^{1/\delta}.
\]
由假设，存在 \(r>0\)，当 \(|x-c|<r\) 时，
\[
|f(x)-c|\le q|x-c|.
\]
记
\[
x_0=x,\qquad x_{n+1}=f(x_n).
\]
若 \(|x-c|<r\)，则归纳得
\[
|x_n-c|\le q^n|x-c|.
\]

考察序列
\[
y_n=a^{-n}(x_n-c).
\]
其相邻差为
\[
\begin{aligned}
|y_{n+1}-y_n|
&=\left|a^{-n-1}(x_{n+1}-c)-a^{-n}(x_n-c)\right|\\
&=|a|^{-n-1}\left|f(x_n)-c-a(x_n-c)\right|\\
&\le |a|^{-n-1}M|x_n-c|^\delta\\
&\le \frac{M|x-c|^\delta}{|a|}\left(\frac{q^\delta}{|a|}\right)^n.
\end{aligned}
\]
因为 \(q^\delta<|a|\)，右侧是收敛几何级数。因此 \((y_n)\) 一致收敛，极限 \(\chi(x)\) 存在。

再计算：
\[
\chi(f(x))
=\lim_{n\to\infty}a^{-n}\bigl(f^{\circ n}(f(x))-c\bigr)
=\lim_{n\to\infty}a^{-n}(x_{n+1}-c).
\]
把指标换成 \(m=n+1\)，得
\[
\chi(f(x))
=a\lim_{m\to\infty}a^{-m}(x_m-c)
=a\chi(x).
\]

若 \(f\) 全纯，则每个函数 \(a^{-n}(f^{\circ n}(x)-c)\) 全纯，并且在小邻域上一致收敛；由 Weierstrass 定理，极限 \(\chi\) 全纯。又
\[
a^{-n}(f^{\circ n}(x)-c)=(x-c)+O((x-c)^2)
\]
在 \(c\) 处导数恒为 \(1\)，故
\[
\chi'(c)=1.
\]
证毕。

**在 Kneser 中的用法。** 对
\[
f(z)=\log z
\]
在复不动点 \(c\) 附近应用。因为
\[
f'(c)=\frac1c,\qquad \left|\frac1c\right|<1,
\]
所以 \(c\) 是吸引不动点。

---

## 8. Koenigs 函数的局部唯一性

**定理 8.1（Schroder 解局部唯一性，差一个常数倍）。** 在定理 7.1 条件下，若 \(\eta\) 在 \(c\) 附近可微，\(\eta'(c)\ne0\)，且
\[
\eta(f(x))=\gamma\eta(x),
\]
则
\[
\gamma=a,\qquad \eta(x)=\eta'(c)\chi(x).
\]

**证明。** 首先由 \(\eta'(c)\ne0\) 得 \(\eta(c)=0\)。事实上代入 \(x=c\)，
\[
\eta(c)=\gamma\eta(c).
\]
若 \(\gamma\ne1\)，则 \(\eta(c)=0\)。若 \(\gamma=1\)，则对 \(x_n=f^{\circ n}(x)\to c\)，
\[
\eta(x_n)=\eta(x),
\]
令 \(n\to\infty\) 得 \(\eta(x)=\eta(c)\)，这与 \(\eta'(c)\ne0\) 矛盾。所以 \(\gamma\ne1\)，且 \(\eta(c)=0\)。

迭代 Schroder 方程：
\[
\eta(x_n)=\gamma^n\eta(x).
\]
又 \(x_n\to c\)，故 \(\eta(x_n)\to0\)。对 \(x\ne c\) 且 \(\eta(x)\ne0\)，得
\[
\gamma^n\to0,
\]
所以 \(|\gamma|<1\)。

再看
\[
\eta(x_n)=\eta'(c)(x_n-c)+o(x_n-c).
\]
于是
\[
\gamma^n\eta(x)
=\eta'(c)(x_n-c)+o(x_n-c).
\]
除以 \(a^n\)：
\[
\left(\frac{\gamma}{a}\right)^n\eta(x)
=\eta'(c)a^{-n}(x_n-c)+o(a^{-n}(x_n-c)).
\]
右侧趋向
\[
\eta'(c)\chi(x).
\]
因此 \((\gamma/a)^n\) 对一般 \(x\) 有非零有限极限，只能 \(\gamma/a=1\)，即 \(\gamma=a\)。于是
\[
\eta(x)=\eta'(c)\chi(x).
\]
证毕。

---

## 9. 指数函数复不动点的计数

**定理 9.1（Kneser 的指数不动点计数）。** 方程
\[
e^z=z
\]
没有实根；在每个半带
\[
2k\pi<y<(2k+1)\pi,\qquad x>0,\qquad k=0,1,2,\dots
\]
中恰有一个根 \(z=x+iy\)。所有根由这些根及其共轭给出。离实轴最近的是 \(k=0\) 的一对。

**证明。** 令 \(z=x+iy\)。方程 \(e^z=z\) 等价于
\[
e^x\cos y=x,\qquad e^x\sin y=y.
\]
若 \(y=0\)，则 \(e^x=x\)，无实解，因为 \(e^x>x\) 对所有实 \(x\) 成立。所以根非实，且共轭成对。

取 \(y>0\)。由第二式得
\[
\sin y>0.
\]
所以 \(y\) 只能落在
\[
2k\pi<y<(2k+1)\pi.
\]
两式相除得
\[
x=y\cot y.
\]
两式平方相加得
\[
x^2+y^2=e^{2x},
\]
即
\[
y^2=e^{2x}-x^2.
\]

在每个区间 \(2k\pi<y<(2k+1)\pi\)，函数
\[
x_1(y)=y\cot y
\]
严格递减，因为
\[
x_1'(y)=\cot y-y\csc^2 y
=\frac{\sin y\cos y-y}{\sin^2 y}
=\frac{\sin(2y)-2y}{2\sin^2 y}<0.
\]
它从 \(+\infty\) 降到 \(-\infty\)。因此在该区间内 \(x=y\cot y\) 给出唯一连续反向关系。

另一方面
\[
y^2=e^{2x}-x^2
\]
在 \(x>0\) 上右侧严格递增，因为导数为
\[
2e^{2x}-2x>0.
\]
所以对应的 \(y(x)\) 在 \(x>0\) 上严格递增。两条曲线一个递减、一个递增，并且端点值交错，因此恰有一个交点。证毕。

**说明。** Kneser 原文还讨论了 \(x\le0\) 部分，并用图像给出完整排除；这里列出的版本足以说明上半平面最近不动点的存在唯一性。数值为
\[
c\approx0.3181315+1.3372357\,i.
\]

---

## 10. Schwarz 引理

**定理 10.1（Schwarz 引理）。** 若 \(f:\mathbb D\to\mathbb D\) 全纯，且
\[
f(0)=0,
\]
则
\[
|f(z)|\le |z|,\qquad |f'(0)|\le1.
\]
若某个非零点取等号，或 \(|f'(0)|=1\)，则
\[
f(z)=e^{i\theta}z.
\]

**证明。** 定义
\[
g(z)=
\begin{cases}
f(z)/z,&z\ne0,\\
f'(0),&z=0.
\end{cases}
\]
则 \(g\) 在 \(\mathbb D\) 上全纯。对 \(0<r<1\)，在 \(|z|=r\) 上
\[
|g(z)|=\frac{|f(z)|}{r}\le\frac1r.
\]
最大模原理给出 \(|g(z)|\le1/r\) 对 \(|z|<r\) 成立。令 \(r\to1\)，得
\[
|g(z)|\le1.
\]
所以
\[
|f(z)|\le |z|,\qquad |f'(0)|=|g(0)|\le1.
\]
若等号成立，则 \(g\) 在内点达到最大模，由最大模原理 \(g\) 常数，且模为 \(1\)。故
\[
f(z)=e^{i\theta}z.
\]
证毕。

**在 Kneser 中的用法。** Kneser 在证明反复取对数趋向吸引不动点时，把局部映射转成单位圆自映射，并用 Schwarz 引理控制迭代。

---

## 11. Schwarz 反射原理

**定理 11.1（Schwarz 反射原理）。** 设 \(U\) 关于实轴对称，\(U^+=U\cap\{\operatorname{Im}z>0\}\)，\(I=U\cap\mathbb R\)。若 \(f\) 在 \(U^+\) 全纯，连续延拓到 \(U^+\cup I\)，并且
\[
f(x)\in\mathbb R\qquad(x\in I),
\]
则
\[
F(z)=
\begin{cases}
f(z),&\operatorname{Im}z\ge0,\\
\overline{f(\overline z)},&\operatorname{Im}z<0
\end{cases}
\]
在 \(U\) 上全纯。

**证明。** 上、下半部分全纯显然。只需证明穿过 \(I\) 仍全纯。取任意小三角形 \(\Delta\subset U\)。若 \(\Delta\) 不碰实轴，Cauchy 定理给出
\[
\int_{\partial\Delta}F(z)\,dz=0.
\]
若碰实轴，将三角形沿实轴切成上下两部分。上下边界在实轴上的积分方向相反；因为边界值实且上下定义相同，实轴部分积分相互抵消。剩余部分由上下半平面 Cauchy 定理为零。因此对所有小三角形
\[
\int_{\partial\Delta}F(z)\,dz=0.
\]
由 Morera 定理，\(F\) 全纯。证毕。

**在 Kneser 中的用法。** Kneser 先在实轴某段的上侧构造 \(\Psi\)，且边界值为实；反射原理使 \(\Psi\) 跨过该实区间解析延拓。

---

## 12. Riemann 映射定理

**定理 12.1（Riemann 映射定理）。** 若 \(\Omega\subsetneq\mathbb C\) 是非空、单连通、真区域，则对任意 \(z_0\in\Omega\)，存在双全纯映射
\[
f:\Omega\to\mathbb D
\]
满足
\[
f(z_0)=0,\qquad f'(z_0)>0.
\]
该映射在这个归一化下唯一。

**证明。** 证明分四步。

**第一步：构造非空正规族。** 因为 \(\Omega\ne\mathbb C\)，取 \(a\notin\Omega\)。函数 \(z-a\) 在 \(\Omega\) 上无零点；由单值平方根定理，存在全纯 \(h\) 使
\[
h(z)^2=z-a.
\]
若 \(h(z_1)=h(z_2)\)，则 \(z_1=z_2\)，故 \(h\) 单叶。再取一个小圆盘避开 \(h(\Omega)\)，经过平移、缩放可得到一个单叶全纯函数
\[
f:\Omega\to\mathbb D.
\]
再用圆盘自同构归一化为 \(f(z_0)=0\)、\(f'(z_0)>0\)。所以候选族非空。

令 \(\mathcal F\) 为所有满足
\[
f:\Omega\to\mathbb D,\quad f \text{ 单叶},\quad f(z_0)=0,\quad f'(z_0)>0
\]
的函数。因为都映入 \(\mathbb D\)，由 Montel 定理，\(\mathcal F\) 是正规族。

**第二步：取极值函数。** 令
\[
M=\sup_{f\in\mathcal F} f'(z_0).
\]
由 Cauchy 估计，\(M<\infty\)。取 \(f_n\in\mathcal F\)，使 \(f_n'(z_0)\to M\)。正规族给出子列局部一致收敛到全纯函数 \(f\)。Hurwitz 定理保证极限 \(f\) 要么单叶，要么常数；但 \(f'(z_0)=M>0\)，故不常数，所以 \(f\) 单叶。于是 \(f\in\mathcal F\)，且
\[
f'(z_0)=M.
\]

**第三步：极值函数必须满到 \(\mathbb D\)。** 假设 \(f(\Omega)\ne\mathbb D\)。取
\[
a\in\mathbb D\setminus f(\Omega),\qquad a\ne0.
\]
圆盘自同构
\[
\phi_a(w)=\frac{w-a}{1-\overline a w}
\]
把 \(a\) 送到 \(0\)。因为 \(\phi_a(f(\Omega))\) 避开 \(0\)，在单连通区域 \(\Omega\) 上可取全纯平方根：
\[
g(z)^2=\phi_a(f(z)).
\]
再取圆盘自同构 \(\psi\)，使
\[
\psi(g(z_0))=0.
\]
则
\[
F=\psi\circ g
\]
仍在 \(\mathcal F\) 中。计算导数。因 \(f(z_0)=0\)，
\[
\phi_a(0)=-a,\qquad |g(z_0)|=\sqrt{|a|}.
\]
并且
\[
|g'(z_0)|
=\frac{|\phi_a'(0)|\,f'(z_0)}{2\sqrt{|a|}}
=\frac{(1-|a|^2)f'(z_0)}{2\sqrt{|a|}}.
\]
而
\[
|\psi'(g(z_0))|=\frac1{1-|g(z_0)|^2}
=\frac1{1-|a|}.
\]
所以
\[
F'(z_0)
=\frac{1+|a|}{2\sqrt{|a|}}\,f'(z_0).
\]
由于
\[
\frac{1+r}{2\sqrt r}>1\qquad(0<r<1,\ r\ne1),
\]
得到
\[
F'(z_0)>f'(z_0)=M,
\]
矛盾。因此 \(f(\Omega)=\mathbb D\)。

**第四步：唯一性。** 若 \(f,g:\Omega\to\mathbb D\) 都满足归一化，则
\[
h=g\circ f^{-1}
\]
是圆盘自同构，且
\[
h(0)=0,\qquad h'(0)>0.
\]
由 Schwarz 引理，
\[
h(z)=z.
\]
故 \(f=g\)。证毕。

**在 Kneser 中的用法。** Kneser 把某个平移不变的复区域共形映到圆盘或上半平面，再把平移归一化成实平移。

---

## 13. 圆盘自同构分类

**定理 13.1（圆盘自同构）。** 每个单位圆盘自同构都形如
\[
\varphi(z)=e^{i\theta}\frac{z-a}{1-\overline a z},
\qquad |a|<1.
\]

**证明。** 设 \(\varphi:\mathbb D\to\mathbb D\) 双全纯，令 \(a=\varphi^{-1}(0)\)。定义
\[
\phi_a(z)=\frac{z-a}{1-\overline a z}.
\]
则
\[
\psi=\varphi\circ\phi_a^{-1}
\]
是圆盘自同构且 \(\psi(0)=0\)。由 Schwarz 引理，\(\psi(z)=e^{i\theta}z\)。所以
\[
\varphi=e^{i\theta}\phi_a.
\]
证毕。

**定理 13.2（无内点不动点的圆盘自同构）。** 圆盘自同构若无内部不动点，则其边界不动点数为一个或两个。一个边界不动点称为抛物型，两个边界不动点称为双曲型。

**证明。** 圆盘自同构是 Möbius 变换。其不动点满足一个二次方程，因此在 Riemann 球面上最多两个。若有内部不动点，经过自同构共轭可变成固定 \(0\)，由 Schwarz 引理是旋转。无内部不动点时，不动点只能落在边界；二次方程给出重根或两个不同根，分别为抛物型或双曲型。证毕。

---

## 14. 实解析反函数定理

**定理 14.1（实解析反函数）。** 若 \(f\) 在实区间 \(I\) 上实解析，且
\[
f'(x)>0\qquad(x\in I),
\]
则 \(f\) 严格递增。若 \(f(I)=J\)，则反函数
\[
f^{-1}:J\to I
\]
实解析。

**证明。** \(f'>0\) 由微积分基本定理给出严格递增。任取 \(x_0\in I\)，因 \(f'(x_0)\ne0\)，实解析隐函数定理给出 \(f^{-1}\) 在 \(f(x_0)\) 附近实解析。局部反函数拼接，得到 \(J\) 上实解析。证毕。

**在 Kneser 中的用法。** \(\Psi'(x)>0\)，\(\Psi(\mathbb R)=(0,\infty)\)，所以
\[
\Psi^{-1}:(0,\infty)\to\mathbb R
\]
实解析。

---

## 15. Kneser 中的“反函数整化推出单叶”

**定理 15.1。** 设 \(\chi\) 在连通区域 \(G\) 上全纯。若存在整函数 \(g\) 使得在 \(G\) 的某个非空开子集 \(U\) 上
\[
g(\chi(z))=z,
\]
并且该恒等式可由解析延拓推广到整个 \(G\)，则 \(\chi\) 在 \(G\) 上单叶，且 \(\chi'(z)\ne0\)。

**证明。** 对任意 \(z\in G\)，有
\[
g(\chi(z))=z.
\]
若 \(\chi(z_1)=\chi(z_2)\)，则
\[
z_1=g(\chi(z_1))=g(\chi(z_2))=z_2.
\]
所以 \(\chi\) 单叶。

再对恒等式求导：
\[
g'(\chi(z))\chi'(z)=1.
\]
故
\[
\chi'(z)\ne0.
\]
证毕。

**在 Kneser 中的用法。** 局部反函数 \(\chi^{-1}\) 满足
\[
\chi^{-1}(c\zeta)=\exp(\chi^{-1}(\zeta)).
\]
因为 \(|c|>1\)，该公式把反函数从小圆盘逐步延拓到任意大圆盘，从而得到整函数 \(g=\chi^{-1}\)。于是 \(\chi\) 单叶。

---

## 16. 整函数双全纯自同构是仿射函数

**定理 16.1。** 若 \(q:\mathbb C\to\mathbb C\) 是双全纯映射，则
\[
q(z)=az+b,\qquad a\ne0.
\]

**证明。** 因 \(q\) 整且单射，考察无穷远点。若无穷远点是可去奇点，则 \(q\) 在扩充平面上全纯，从而有界，故由 Liouville 定理 \(q\) 为常数，矛盾。

若无穷远点是本性奇点，则由 Casorati-Weierstrass 定理，\(q\) 在充分大的外部邻域中取值稠密。这与 \(q\) 单射不相容：因为 \(q\) 在任意一个普通点附近已经把一个小邻域映到一个开集，本性奇点附近又会进入同一开集，从而产生重复值。

所以无穷远点只能是极点。于是 \(q\) 是多项式。若多项式次数 \(n\ge2\)，则对一般 \(w\)，方程
\[
q(z)=w
\]
有 \(n\) 个根，违背单射性。因此次数为 \(1\)，即
\[
q(z)=az+b,\qquad a\ne0.
\]
证毕。

---

## 17. Trappmann-Kouznetsov 唯一性判据

**定理 17.1（全纯 Abel 函数唯一性判据）。** 设 \(\gamma\) 是 \(F\) 的初始曲线，\(H\) 是对应初始区域，\(d\in H\)。满足下列条件的 Abel 函数 \(\alpha\) 至多一个：

1. \(\alpha\) 在 \(H\) 上全纯；
2. \(\alpha\) 在 \(H\) 上单叶；
3. \(\alpha(F(z))=\alpha(z)+1\)；
4. \(\alpha(d)=0\)；
5. 整数平移覆盖：
\[
\bigcup_{k\in\mathbb Z}\bigl(\alpha(H)+k\bigr)=\mathbb C.
\]

**证明。** 假设 \(\alpha_1,\alpha_2\) 都满足条件。记
\[
T_j=\alpha_j(H)\qquad(j=1,2).
\]
因为 \(\alpha_j\) 单叶，反函数存在：
\[
\alpha_j^{-1}:T_j\to H.
\]

Abel 方程给出反函数关系。若 \(z,z+1\in T_j\)，令 \(u=\alpha_j^{-1}(z)\)，则
\[
\alpha_j(F(u))=\alpha_j(u)+1=z+1.
\]
所以
\[
\alpha_j^{-1}(z+1)=F(\alpha_j^{-1}(z)). \tag{1}
\]

定义
\[
q_1=\alpha_2\circ\alpha_1^{-1}:T_1\to T_2,
\]
\[
q_2=\alpha_1\circ\alpha_2^{-1}:T_2\to T_1.
\]
由 (1)，若 \(z,z+1\in T_1\)，则
\[
\begin{aligned}
q_1(z+1)
&=\alpha_2(\alpha_1^{-1}(z+1))\\
&=\alpha_2(F(\alpha_1^{-1}(z)))\\
&=\alpha_2(\alpha_1^{-1}(z))+1\\
&=q_1(z)+1.
\end{aligned}
\]
同理
\[
q_2(z+1)=q_2(z)+1. \tag{2}
\]

对每个整数 \(k\)，在 \(T_j+k\) 上定义
\[
q_{j,k}(z+k)=q_j(z)+k.
\]
由 (2)，相邻平移区域重叠时定义一致；由恒等定理，所有重叠上的定义一致。又因
\[
\bigcup_{k\in\mathbb Z}(T_j+k)=\mathbb C,
\]
这些局部函数拼接成整函数 \(q_j:\mathbb C\to\mathbb C\)。

原先 \(q_1,q_2\) 在 \(T_1,T_2\) 上互为反函数。延拓后，\(q_2\circ q_1\) 与恒等函数在非空开集上一致，由恒等定理在整个 \(\mathbb C\) 上一致。同理
\[
q_1\circ q_2=\operatorname{id}_{\mathbb C}.
\]
所以 \(q_1\) 是复平面双全纯自同构。由定理 16.1，
\[
q_1(z)=az+b,\qquad a\ne0.
\]

归一化给出
\[
q_1(0)=\alpha_2(\alpha_1^{-1}(0))=\alpha_2(d)=0,
\]
所以 \(b=0\)。平移关系
\[
q_1(z+1)=q_1(z)+1
\]
给出
\[
a(z+1)=az+1,
\]
故 \(a=1\)。于是 \(q_1(z)=z\)，从而
\[
\alpha_2=\alpha_1.
\]
证毕。

---

## 18. Kneser 解满足 Trappmann-Kouznetsov 判据

**定理 18.1。** Kneser 构造出的 Abel 函数 \(\Psi\) 在 Trappmann-Kouznetsov 选定的初始区域 \(H\) 上满足定理 17.1 的条件。因此它在这些复解析规范条件下唯一。

**证明。** 取
\[
F(z)=e^z.
\]
令 \(L\) 是上半平面中离实轴最近的不动点：
\[
e^L=L,\qquad \operatorname{Im}L>0.
\]
其共轭 \(L^*\) 也是不动点。

定义初始曲线
\[
\ell(t)=\operatorname{Re}L+i\,\operatorname{Im}L\,t,\qquad -1<t<1.
\]
它连接 \(L^*\) 与 \(L\)。其指数像为
\[
e^{\ell(t)}
=e^{\operatorname{Re}L}e^{i\operatorname{Im}L\,t}
=|L|e^{i\operatorname{Im}L\,t}.
\]
这是从 \(L^*\) 到 \(L\) 的圆弧。由于 \(0<\operatorname{Im}L<\pi\)，该圆弧不自交；竖直线段 \(\ell\) 也不自交。二者除端点外不相交，否则需要
\[
\cos(s\operatorname{Im}L)=\cos(\operatorname{Im}L)
\]
在 \(-1<s<1\) 中成立，矛盾。因此 \(\ell\) 是初始曲线。

令 \(H\) 为 \(\ell\) 与 \(e^\ell\) 围出的初始区域。Kneser 构造的 \(\Psi\) 具有：

1. \(\Psi\) 在 \(H\) 上全纯；
2. \(\Psi\) 在 \(H\) 上单叶；
3. \(\Psi(e^z)=\Psi(z)+1\)；
4. 可加常数归一化为 \(\Psi(1)=0\)；
5. 由 Kneser 的共形映射构造，整数平移覆盖：
\[
\bigcup_{k\in\mathbb Z}\bigl(\Psi(H)+k\bigr)=\mathbb C.
\]

其中第 1、2 点来自 Kneser 对 \(\chi\) 的单叶性证明、取 \(\log\chi\) 后的单值性，以及 Schwarz 反射。第 5 点来自 Kneser 把
\[
\bigcup_{k\in\mathbb Z}(\psi(H_0)+kL)
\]
共形映到上半平面，并把平移 \(w\mapsto w+L\) 归一化为 \(v\mapsto v+1\) 的构造。

所以 \(\Psi\) 满足定理 17.1。由唯一性判据，满足这些条件的 Abel 函数至多一个。证毕。

---

## 19. 从唯一 Abel 函数到唯一半迭代

**定理 19.1。** 若 Abel 函数 \(\Psi\) 在某类规范条件下唯一，则由它定义的半迭代
\[
\vartheta(x)=\Psi^{-1}\!\left(\Psi(x)+\frac12\right)
\]
在同一来源约束下唯一。

**证明。** 公式完全由 \(\Psi\) 决定。如果 \(\Psi\) 唯一，则右侧唯一。证毕。

**注意。** 这不是说所有实解析 \(\vartheta\) 唯一，而是说所有来自 Trappmann-Kouznetsov 判据中那个唯一 Abel 函数的 Kneser 型半迭代唯一。

---

## 20. 哪些大定理没有在论文中重新证明

为了诚实地标出依赖层级，下面这些定理通常作为复分析或拓扑学标准背景使用：

1. **Jordan 曲线定理。** 一条简单闭曲线把扩充平面分成内外两个连通分支。Trappmann-Kouznetsov 用它定义初始区域。
2. **Montel 定理。** 一致有界的全纯函数族是正规族。Riemann 映射定理的标准证明用它。
3. **Hurwitz 定理。** 单叶全纯函数的局部一致极限若非常数，仍单叶。Riemann 映射定理的极值证明用它。
4. **Rouche 定理。** 复反函数定理和零点计数常用它。
5. **Morera 定理。** Schwarz 反射原理的一个简洁证明用它。

其中 Montel、Hurwitz、Rouche、Morera 都属于一门复分析课程中的基础定理；上文在使用处已经给出它们如何进入证明链。Jordan 曲线定理是拓扑定理，完整证明很长，通常不在复分析论文中展开。

---

## 21. 最终逻辑图

Kneser 存在性：
\[
\text{复不动点}
\Rightarrow
\text{Koenigs 函数 }\chi
\Rightarrow
\log\chi\text{ 型 Abel 坐标}
\Rightarrow
\text{共形归一化 }\Psi
\Rightarrow
\Psi(e^x)=\Psi(x)+1
\Rightarrow
\vartheta^2=e^x.
\]

Trappmann-Kouznetsov 唯一性：
\[
\text{初始区域 }H
+\text{ 单叶}
+\text{ 平移覆盖}
\Rightarrow
\alpha_2\circ\alpha_1^{-1}\text{ 可整延拓}
\Rightarrow
\text{仿射}
\Rightarrow
\alpha_1=\alpha_2.
\]

边界结论：
\[
\boxed{\text{Kneser 证明实解析半指数存在。}}
\]
\[
\boxed{\text{纯实解析严格递增类别中不唯一。}}
\]
\[
\boxed{\text{加入 Trappmann-Kouznetsov 的复解析判据后，Kneser 型 Abel 函数唯一。}}
\]

