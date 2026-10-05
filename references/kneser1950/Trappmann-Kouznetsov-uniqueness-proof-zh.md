# Trappmann-Kouznetsov 唯一性判据及 Kneser 解唯一性的证明

本文整理 Trappmann-Kouznetsov 2011 年论文 *Uniqueness of Holomorphic Abel Functions at a Complex Fixed Point Pair* 的核心唯一性证明，并说明 Kneser 的 Abel 函数为何满足该判据。

本地 PDF：

- `references/trappmann-kouznetsov-uniqueness-holomorphic-abel-functions-2011.pdf`

## 1. Abel 函数与初始区域

设 \(F\) 是复平面某区域上的全纯函数。若 \(\alpha\) 在区域 \(D\) 上全纯，并满足
\[
\alpha(F(z))=\alpha(z)+1
\]
对所有 \(z,F(z)\in D\) 成立，则称 \(\alpha\) 是 \(F\) 的 Abel 函数。

设 \(\gamma:(-1,1)\to\mathbb C\) 是一条曲线，满足：

1. \(\gamma\) 与 \(F\circ\gamma\) 都是单射；
2. \(\gamma\cap F(\gamma)=\varnothing\)；
3. 两个端点极限
\[
\gamma(-1):=\lim_{t\to-1}\gamma(t),\qquad
\gamma(1):=\lim_{t\to1}\gamma(t)
\]
存在，且是 \(F\) 的两个不同不动点。

则
\[
\gamma\cup F(\gamma)\cup\{\gamma(-1),\gamma(1)\}
\]
是一条 Jordan 闭曲线。它围出的内侧区域连同两条边界曲线，去掉两个不动端点，称为初始区域 \(H\)。

## 2. 唯一性判据

固定 \(d\in H\)。考虑满足以下条件的 Abel 函数 \(\alpha\)：

1. \(\alpha\) 在 \(H\) 上全纯；
2. \(\alpha\) 在 \(H\) 上单叶；
3. \(\alpha(F(z))=\alpha(z)+1\)；
4. 归一化
\[
\alpha(d)=0;
\]
5. 整数平移覆盖整个复平面：
\[
\bigcup_{k\in\mathbb Z}\bigl(\alpha(H)+k\bigr)=\mathbb C.
\]

Trappmann-Kouznetsov 的 Theorem 1 说：满足以上条件的 \(\alpha\) 至多一个。

下面给出证明。

## 3. Theorem 1 的证明

假设有两个 Abel 函数 \(\alpha_1,\alpha_2\) 都满足上述条件。记
\[
T_j=\alpha_j(H)\qquad(j=1,2).
\]
由于 \(\alpha_j\) 在 \(H\) 上全纯且单叶，故
\[
\alpha_j:H\to T_j
\]
是双全纯映射，存在反函数
\[
\alpha_j^{-1}:T_j\to H.
\]

由 Abel 方程可得反函数形式。若 \(z,z+1\in T_j\)，令
\[
u=\alpha_j^{-1}(z).
\]
则
\[
\alpha_j(F(u))=\alpha_j(u)+1=z+1.
\]
因此
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
它们都是双全纯映射，并且互为反函数。

接下来证明 \(q_j\) 与整数平移相容。以 \(q_1\) 为例。若 \(z,z+1\in T_1\)，则
\[
\begin{aligned}
q_1(z+1)
&=\alpha_2\bigl(\alpha_1^{-1}(z+1)\bigr)\\
&=\alpha_2\bigl(F(\alpha_1^{-1}(z))\bigr)\\
&=\alpha_2\bigl(\alpha_1^{-1}(z)\bigr)+1\\
&=q_1(z)+1.
\end{aligned}
\]
同理
\[
q_2(z+1)=q_2(z)+1. \tag{2}
\]

现在把 \(q_j\) 解析延拓到整个复平面。对每个整数 \(k\)，在平移区域 \(T_j+k\) 上定义
\[
q_{j,k}(z+k)=q_j(z)+k,\qquad z\in T_j.
\]
也就是
\[
q_{j,k}(w)=q_j(w-k)+k,\qquad w\in T_j+k.
\]

由于 \((2)\)，相邻平移区域重叠时，这些局部定义在重叠部分相容。更具体地说，在 \(T_j+k\) 与 \(T_j+k+1\) 的交集上，两个定义都由 Abel 方程和平移关系给出同一个值；由解析函数的恒等定理，它们在每个连通重叠部分一致。

又因为假设
\[
\bigcup_{k\in\mathbb Z}(T_j+k)=\mathbb C,
\]
所以这些局部函数拼接成整个复平面上的整函数，仍记为
\[
q_j:\mathbb C\to\mathbb C.
\]

原来在 \(T_1,T_2\) 上，\(q_1,q_2\) 互为反函数。由于二者已经整函数延拓，复合函数
\[
q_2\circ q_1,\qquad q_1\circ q_2
\]
都是整函数，并且分别在非空开集上等于恒等映射。由恒等定理，
\[
q_2\circ q_1=\operatorname{id}_{\mathbb C},
\qquad
q_1\circ q_2=\operatorname{id}_{\mathbb C}.
\]
因此 \(q_1\) 是复平面的双全纯自同构。

下面证明一个标准引理：复平面的双全纯自同构只能是仿射函数。设 \(q\) 是复平面的双全纯自同构。因为 \(q\) 整且单射，考察 \(q\) 在无穷远点的孤立奇性。若无穷远点是本性奇点，则由 Casorati-Weierstrass 定理，\(q\) 在充分大的外部邻域中取值稠密，这与单射性不相容。若无穷远点是可去奇点，则 \(q\) 在整个扩充平面有界，从而 \(q\) 为常数，也与双射矛盾。因此无穷远点只能是极点，故 \(q\) 是多项式。单射多项式只能一次；若次数 \(n\ge2\)，则 \(q(z)-w\) 对一般 \(w\) 有 \(n\) 个根，矛盾。所以
\[
q(z)=az+b,\qquad a\ne0.
\]

应用到 \(q_1\)，存在 \(a\ne0,b\in\mathbb C\)，使得
\[
q_1(z)=az+b.
\]

由归一化 \(\alpha_1(d)=\alpha_2(d)=0\)，得
\[
q_1(0)=\alpha_2(\alpha_1^{-1}(0))=\alpha_2(d)=0,
\]
所以 \(b=0\)。

再由平移相容式 \(q_1(z+1)=q_1(z)+1\)，代入 \(q_1(z)=az\)，得到
\[
a(z+1)=az+1,
\]
所以
\[
a=1.
\]
因此
\[
q_1(z)=z.
\]

于是对 \(z\in H\)，
\[
\alpha_2(z)=q_1(\alpha_1(z))=\alpha_1(z).
\]
所以
\[
\alpha_1=\alpha_2.
\]
Theorem 1 得证。

## 4. 不依赖初始区域的版本

Trappmann-Kouznetsov 还给出 Theorem 2：若 \(D\) 是连通区域，\(F\) 在 \(D\) 上全纯，则在 \(D\) 上至多存在一个 Abel 函数 \(\alpha\)，满足：

1. \(\alpha\) 在 \(D\) 上全纯；
2. \(\alpha'(d)\ne0\)；
3. \(\alpha\) 在某个初始区域 \(H\subset D\) 上满足 Criterion 1。

证明思想如下。若有两个这样的函数 \(\alpha_1,\alpha_2\)，它们可能对应不同初始区域 \(H_1,H_2\)。分别按 Theorem 1 的构造得到整函数
\[
q_1=\alpha_2\circ\alpha_1^{-1},
\qquad
q_2=\alpha_1\circ\alpha_2^{-1}.
\]
由于 \(\alpha_1'(d),\alpha_2'(d)\ne0\)，二者在 \(d\) 的邻域内局部单叶，所以 \(q_1,q_2\) 在 \(0\) 的邻域内互为反函数。由整函数恒等延拓，\(q_1,q_2\) 在整个复平面互为反函数；再由归一化和平移相容，推出 \(q_1=\operatorname{id}\)。因此 \(\alpha_1=\alpha_2\) 在 \(d\) 的邻域成立，再由 \(D\) 连通和恒等定理，得 \(\alpha_1=\alpha_2\) 在整个 \(D\) 成立。

## 5. Kneser 构造满足唯一性判据

现在取
\[
F(z)=e^z.
\]
设 \(L\) 是上半平面中离实轴最近的复不动点：
\[
e^L=L,\qquad \operatorname{Im}L>0.
\]
其共轭 \(L^*\) 是另一个不动点。

定义曲线
\[
\ell(t)=\operatorname{Re}L+i\,\operatorname{Im}L\,t,
\qquad -1<t<1.
\]
这是一条从 \(L^*\) 到 \(L\) 的竖直线段。其指数像为
\[
e^{\ell(t)}
=e^{\operatorname{Re}L}e^{i\operatorname{Im}L\,t}
=|L|e^{i\operatorname{Im}L\,t}.
\]
这是一段以 \(0\) 为圆心、半径 \(|L|\) 的圆弧，从 \(L^*\) 到 \(L\)。

Kneser 所用的初始区域可写为
\[
H=\{z\in\mathbb C:\operatorname{Re}z\ge\operatorname{Re}L,\ |z|\le |L|\}\setminus\{L,L^*\}.
\]
其左边界是 \(\ell\)，右边界是 \(e^\ell\)。下面检查 \(\ell\) 确实是初始曲线。

首先，\(\ell\) 显然单射。其次，因为
\[
-\operatorname{Im}L<t\,\operatorname{Im}L<\operatorname{Im}L
\]
且 \(0<\operatorname{Im}L<\pi\)，圆弧参数没有绕满一圈，所以 \(e^\ell\) 也是单射。

再看二者是否相交。若
\[
\ell(t)=e^{\ell(s)}
\]
成立，则取实部得到
\[
\operatorname{Re}L=|L|\cos(s\,\operatorname{Im}L).
\]
而 \(L=|L|e^{i\operatorname{Im}L}\)，所以
\[
\operatorname{Re}L=|L|\cos(\operatorname{Im}L).
\]
于是
\[
\cos(s\,\operatorname{Im}L)=\cos(\operatorname{Im}L).
\]
由于 \(s\,\operatorname{Im}L\in(-\operatorname{Im}L,\operatorname{Im}L)\)，且 \(0<\operatorname{Im}L<\pi\)，这只能在端点 \(s=\pm1\) 发生；但端点被去掉。因此 \(\ell\cap e^\ell=\varnothing\)。

端点 \(L,L^*\) 都满足 \(e^z=z\)。所以 \(\ell\) 是 \(F(z)=e^z\) 的初始曲线，\(H\) 是对应初始区域。

Kneser 的构造可概括如下。

首先，在 \(L\) 附近用 Koenigs 方法构造 Schroder 函数 \(\chi\)，满足
\[
\chi(e^z)=L\chi(z)
\]
并将 \(\chi\) 解析延拓到合适的上半平面区域。Kneser 证明 \(\chi\) 在该区域上单叶；关键理由是其局部反函数可由
\[
\chi^{-1}(L\zeta)=\exp(\chi^{-1}(\zeta))
\]
逐步延拓为整函数。

然后取合适分支
\[
\psi(z)=\log\chi(z).
\]
由 Schroder 方程得到 Abel 型关系
\[
\psi(e^z)=\psi(z)+\log L.
\]
由于 \(L\) 是主支对数的不动点，即
\[
\log L=L,
\]
可写成
\[
\psi(e^z)=\psi(z)+L.
\]

最后，Kneser 对由 \(\psi(H_0)+kL\) 组成的平移并区域作共形映射，把平移 \(w\mapsto w+L\) 归一化为 \(v\mapsto v+1\)。于是得到 Abel 函数
\[
\Psi(z)=\rho(\psi(z)),
\]
满足
\[
\Psi(e^z)=\Psi(z)+1.
\]

Trappmann-Kouznetsov 从 Kneser 构造中抽取出以下三个性质：

1. \(\Psi\) 在上半初始区域 \(H_0\cup\{1\}\) 上全纯且单叶；
2. 通过 Schwarz 反射，\(\Psi\) 延拓到完整初始区域 \(H\)，仍全纯且单叶；
3. 整数平移覆盖整个复平面：
\[
\bigcup_{k\in\mathbb Z}\bigl(\Psi(H)+k\bigr)=\mathbb C.
\]

此外，因为 Abel 函数可加任意常数而不改变 Abel 方程，可以归一化为
\[
\Psi(1)=0.
\]

所以 \(\Psi\) 满足 Criterion 1：

- 在 \(H\) 上全纯；
- 在 \(H\) 上单叶；
- 满足 \(\Psi(e^z)=\Psi(z)+1\)；
- 满足 \(\Psi(1)=0\)；
- 满足整数平移覆盖 \(\mathbb C\)。

由 Theorem 1，满足这些条件的 Abel 函数至多一个。因此：
\[
\boxed{\text{Kneser 的 Abel 函数在该复解析初始区域、单叶性和平移覆盖规范下唯一。}}
\]

进一步，由 Abel 函数定义的半迭代
\[
\vartheta(z)=\Psi^{-1}\!\left(\Psi(z)+\frac12\right)
\]
也随之唯一，只要要求它来自上述唯一的 \(\Psi\)。

## 6. 这不是无条件唯一性

这个唯一性不是说所有实解析半指数函数都唯一。若只在实轴上要求实解析和严格递增，仍可用周期扰动制造不同 Abel 函数：
\[
\widetilde\Psi(x)=\Psi(x)+g(\Psi(x)),
\]
其中 \(g\) 是周期为 \(1\) 的小实解析函数并满足
\[
1+g'(t)>0.
\]
则
\[
\widetilde\Psi(e^x)=\widetilde\Psi(x)+1,
\]
通常给出不同的半迭代。

因此准确结论是：
\[
\boxed{\text{实解析存在性：Kneser 已证明。}}
\]
\[
\boxed{\text{纯实解析唯一性：不成立。}}
\]
\[
\boxed{\text{附加 Trappmann-Kouznetsov 复解析判据后的 Kneser 型唯一性：成立。}}
\]

## 参考文献

- H. Trappmann and D. Kouznetsov, *Uniqueness of Holomorphic Abel Functions at a Complex Fixed Point Pair*, Aequationes Mathematicae 81 (2011), 65-76.
- H. Kneser, *Reelle analytische Lösungen der Gleichung \(\vartheta(\vartheta(x))=e^x\) und verwandter Funktionalgleichungen*, J. Reine Angew. Math. 187 (1950), 56-67.
- G. Szekeres, *Fractional iteration of exponentially growing functions*, J. Austral. Math. Soc. 2 (1961), 301-320.
