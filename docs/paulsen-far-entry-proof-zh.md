# 一个远离 η 的边界弧入口确为同一分支

本笔记在 `paper-submission/main-full.tex` 已证明的尖点比较定理、外侧宽走廊定理和
`paper-submission/main.tex` 的上半 Shell--Thron 全域定理基础上，完成一个**明确**
非尖点入口的分支识别。它不声称任意远端弧都已被覆盖。

记 (p_0=0.1000435842)、(c=0.01/p_0)、
\[
  \theta=p(1+ic),\quad 0<p\le p_0,
  \qquad b(\theta)=\exp\!\left(
       \frac{\theta e^{-\theta\cot\theta}}{\sin\theta}\right).
\]
`main-full.tex` 的 `cor:exterior-wide-full-height` 已从实外侧把 Kneser 芽沿
\(\Re\theta=p_0,0\le\Im\theta\le0.01\) 延拓到
\(\theta_0=p_0+0.01i\)。该线穿过 `cor:exterior-full-height` 的一段
非尖点 ST 边界。下面证明：它在 \(\theta_0\) 的参数芽等于
`main.tex` 的尖点入口全域芽 \(F^{\rm tr}\)。由底数变量的恒等定理，
同一结论随后覆盖该远端边界小弧的内侧公共邻域。

## 定理

在上述已认证的边界小弧附近，从实外侧 Kneser 族进入上半 ST 区域
\(U^+\) 所得的高度芽，与从尖点入口延拓所得的 \(F^{\rm tr}\) **相同**。
特别地，它在 \(\theta_0\) 处等于 \(F^{\rm tr}_{b(\theta_0)}\)，
并且这是一条参数芽的等式，而不仅是一个底数上的数值吻合。

### 1. 整条连接路径都在 \(U^+\)

令 \(\lambda_+(\theta)=\theta\cot\theta+i\theta\)。这两个乘子之一是
吸引不动点的乘子。取 \(\delta=\theta\cot\theta-1\)。脚本
`certify_cone_mark_crossing.py` 对收敛幂级数作外向舍入，严格给出
\[
 \Re(\delta/p^2)<-0.31,\qquad
 |\Im(\delta/p^2)|<0.08,\qquad |\delta/p^2|<0.36.
\]
因而 \(\Im\lambda_+>p-0.08p^2>0\)，且按逐项展开平方并用
\(c<0.1\)、\(p\le p_0\)，有
\[
 |\lambda_+|^2\le 1-2cp+0.414p^2<1.
\]
所以这条路径严格位于 \(U^+\)。`certify_exterior_cone_cylinder.py`
还证明 \(b(\theta)\) 在整个候选锥上单叶，故它是无自交的底数路径。

### 2. 月牙及商面的统一存在

置
\[
 r=e^{\theta\cot\theta},\quad L_\pm=r e^{\pm i\theta},\quad
 \zeta(w)=\frac{w/r-\cos\theta}{i\sin\theta},\quad
 s_\theta(t)=\frac{e^{i\theta t}-\cos\theta}{i\sin\theta}.
\]
于是弦 \(\gamma\) 对应 \([-1,1]\)，\(E_b(\gamma)\) 对应
\(s_\theta([-1,1])\)，并且 **精确地**
\(\zeta(E_b(w))=s_\theta(\zeta(w))\)。
`certify_exterior_cone_cylinder.py` 在
\(0<p\le0.100044,0\le\Im\theta/\Re\theta\le0.1\) 证明
\(\Re s_\theta'(t)>0.98\) 及
\(\Im(s_\theta(t)-t)<-0.4p(1-t^2)\)。故弦与像弧围成非退化
Jordan 月牙 \(H_\theta\)。同一证书的显式平直模型具有
\(|\mu|<1/10\)；两边按 \(E_b\) 缝合后的带端商面 \(X_\theta\)
同胚并拟共形等价于 \(\mathbb C^*\)，两端都是穿孔。

### 3. 底点轨道始终有**同一个第一次穿越标记**

令 \(w_n=E_b^{\circ n}(1)\)，从 \(n=0\) 开始，定义连续提升
\[
 q_n=\frac{w_n-L_+}{w_n-L_-}=e^{\chi_n},
 \qquad \chi_n=x_n+i y_n.
\]
其初值取趋于零的对数。上述第二个脚本对 \(\chi_0/p\) 的解析级数
在整个 \(0<p\le p_0\) 给出
\[
 -0.4p<x_0<0,\qquad 3p<y_0<3.3p.
 \tag{1}
\]
特别地，\(-0.04<x_0<0\)。以下步进不等式适用于
\(-1\le x\le0.16\)、\(3p\le y\le\pi+1.14p\)：
\[
 -0.24p<x_{n+1}-x_n<0.04p,
 \qquad 0.86p<y_{n+1}-y_n<1.14p.
 \tag{2}
\]
这不是迭代采样。其解析证明如下。写 \(q=e^\chi\)、
\(v=i\theta/(1-q)\)、\(T(v)=\sinh(v)/v\)。直接代入
\(s_\theta\) 得到精确恒等式
\[
 \frac{q_{n+1}}{q_n}
  =e^{i\theta}\frac{T(v-i\theta)}{T(v)},
 \qquad
 \chi_{n+1}-\chi_n
  =i\theta+\log T(v-i\theta)-\log T(v).
 \tag{3}
\]
在指定的 \(y\)-带上，\(y\le\pi/2\) 时
\(|1-e^{x+iy}|\ge\sin y\ge\sin(3p)\)；
\(\pi/2\le y\le\pi+1.14p<3\pi/2\) 时该模至少为 \(1\)。
于是 \(|v|<0.341\)。线段 \(v-ti\theta\) 可写成
\(v(1-t+tq)\)，所以其模小于
\(e^{0.16}|v|<0.4\)。在 \(|v|\le0.4\) 上，
\[
 |(\log T)'(v)|\le
 \frac{(0.4\cosh0.4-\sinh0.4)/0.4^2}
      {2-\sinh(0.4)/0.4}<0.1393.
\]
脚本用精确有理阈值和 Arb 严格核对
\(0.1393\sqrt{1.01}<0.14\)。因此式 (3) 的对数校正模
小于 \(0.14p\)，给出式 (2)。由于 \(T\) 在此盘内非零，
式 (3) 同时指定了连续对数分支。

令 \(n_*\) 为首个 \(y_{n_*}\ge\pi\) 的指标。式 (1)、(2) 与
简单归纳给出 \(n_*<\pi/(0.86p)+1\)；脚本核对
\(-1<x_n<0.16\) 在 \(0\le n\le n_*\) 全程自洽。
由 \(q_n=e^{\chi_n}\) 与
\(\zeta(w_n)=(1+q_n)/(1-q_n)\)，\(0<y_n<\pi\) 等价于
\(\Im\zeta(w_n)>0\)，即轨道仍在弦的上方。在首次穿越时
\(y_{n_*-1}<\pi\le y_{n_*}<\pi+1.14p\)。外向舍入证书把这两点
放在中央矩形
\((-0.2,0.6)+i(-0.1,0.1)\)，并证明 \(s_\theta\)
在其稍大矩形上 \(\Re s_\theta'>0.9\)；另有
\(\Re s_\theta(-0.7)<-0.2\) 与
\(\Re s_\theta(0.7)>0.6\)。因此
\(s_\theta(\zeta(w_{n_*-1}))=\zeta(w_{n_*})\)
位于像弧的上侧、弦的下侧，即在 \(H_\theta\) 内；
若 \(y_{n_*}=\pi\)，它就在弦上，与下一迭代的像弧点是商面的
同一个标记。这个判定使用了弦附近的单叶及正方向，未把穿越点
仅凭“虚部变号”擅自判为月牙内点。

于是 \(w=1\) 在每个 \(X_\theta\) 都有连续的**第一次穿越**商面标记
\(m_\theta\)。当指标 \(n_*\) 改变时，两个局部代表恰好是
\(w_n\in\gamma\) 与 \(w_{n+1}=E_b(w_n)\in E_b(\gamma)\)，
它们是缝合的同一点。所有更早的轨道点都在弦上方，故标记不可能
悄悄跳到另一条回归圈。

### 4. 参数芽沿路径解析接通两端

在路径的每一个 \(p>0\) 附近，取该点的实数 \(p\) 为固定平直
模型尺度 \(y=(2/p)\operatorname{artanh}t\)。保持源圆柱坐标固定时，
月牙插值 \(t+x(s_\theta(t)-t)\) 对复参数 \(\theta\) 全纯，
其 Beltrami 系数也是 \(L^\infty\)-值全纯函数；由前述严格
\(|\mu|<1/10\)，它在一个复参数邻域内仍满足 \(|\mu|<1\)。
Ahlfors--Bers 参数定理及物理坐标的逆映射恒等式（与
`main-full.tex` 的 `prop:exterior-analytic-germ-corridor` 相同）
使两穿孔商面的端点及标记三点归一化坐标 \(Q_\theta\)
在标记附近联合全纯。局部的高度芽由
\[
 A_\theta(w)=\frac1{2\pi i}\log Q_\theta(E_{b(\theta)}^{\circ n_*}(w)),
 \qquad A_\theta(1)=0,
 \qquad F_\theta=A_\theta^{-1}
\]
给出。当 \(n_*\) 改变时，商面缝线恒等式
\(Q_\theta(E_b u)=Q_\theta(u)\) 在缝线解析邻域内成立，
所以相邻的 \(A_\theta\) 是同一个参数芽。由紧路径上的有限覆盖，
这构成从尖点附近到 \(\theta_0\) 的解析延拓。

当 \(p\downarrow0\) 时，\(\varepsilon=1-\lambda_+\) 满足
\(\varepsilon=(c-i)p+O(p^2)\)。故 \(\arg\varepsilon\) 属于
`main-full.tex` 的尖点允许扇区，水平线
\(\Im\chi=\pi\) 满足其 `eq:admissible`。这条线的物理像**正是**
上面的弦 \(\gamma\)。本证明的第一次穿越标记与
`lem:cusp-base` 的标记一致；`lem:change-line` 将它与尖点族选用的
其它允许线比较。因此此处的 \(F_\theta\) 与 \(F^{\rm tr}\)
在一段小参数开集上完全相同。`main.tex` 的 `thm:global` 及
底数变量恒等定理把等式传到 \(\theta_0\)。

在 \(\theta_0\)，`main-full.tex` 的
`prop:exterior-analytic-germ-corridor`、`cor:exterior-wide-full-height`
使用同一个弦商面、同一个两端归一化和 \(w_{28}=E_b^{28}(1)\)
的标记。其严格证书还给出此前各迭代位于弦上方，所以
\(28=n_*\)。故它的外侧 Kneser 参数芽也正是上述 \(F_\theta\)。
这给出内、外两族在 \(\theta_0\) 的**参数芽等式**；在宽走廊与
\(U^+\) 的连通公共部分应用恒等定理，覆盖所述非尖点边界弧。

## 适用范围

证明覆盖 `main-full.tex` 已认证的 \(p\approx p_0\) 那一小段
非尖点边界弧及其内侧公共邻域。若“某段弧”指任意远端弧，尚需
为该弧另行建立从尖点到入口的标记路径或等价的边界粘合条件。
单凭 \(U^+\) 单连通不能推出这种任意弧的识别。
