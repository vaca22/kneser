# 从局部理想固定点到全局延拓：已验证的条件与尚缺的恒等式

**后续更新：** 本文此前缺少的精确拼接恒等式，已由
[周期拟共形构造及逆支桥接](theta-qc-global-existence.md)证明。
下文保留原条件延拓和归一化分支审查；Kneser 规范身份仍待证明。

2026-09-12。所有数值计算和检查均在 galic 执行。
本报告接续 [连续无限维收缩证书](theta-continuous-ball.md)。
f 表示该证书确定的唯一局部理想固定点，p 是 e50 中心多项式。

**本轮完成局部单叶/无零点证书、带明确假设的全局延拓定理，
以及一个非主支归一化的 Rouché 证书。没有证明精确拼接，
没有把 f 标为 Kneser 函数。**

## 1. 已验证的局部几何和两类误差

取 r=11/20、s=27/50，已知 ||f-p||_r<=E，其中 E<8.399e-21。
证书：[identity-bridge-e50/certificate.json](certificates/identity-bridge-e50/certificate.json)。

在整个 |z|<=s 内，有

    Re f(z) > 0.28937,
    Re f'(z) > 0.54408,
    |f(z)| < 1.71063.

这里没有把 f 截断为有限多项式。若 p=sum c_k z^k，则使用

    Re f >= 1 - sum_{k>=1} |c_k| s^k - E,
    Re f' >= c_1 - sum_{k>=2} k |c_k| s^(k-1) - E/(r-s).

最后一项来自 h=f-p 在半径 r 的圆盘上的 Cauchy 导数估计。
因为圆盘凸，对其中任意 z1!=z2，

    (f(z2)-f(z1))/(z2-z1)
      = integral_0^1 f'(z1+t(z2-z1)) dt

的实部严格为正，所以 f 单叶。Re f>0 同时给出无零点和解析主对数。

令 A、S 为已验证的正则 Koenigs 逆支和正向函数，并定义

    g_f(t) = A(f(t+i delta))-t-i delta,
    a_m(f) = integral_{-1/2}^{1/2} g_f(t) exp(-2 pi i m t) dt,
    theta_f(z) = sum_{m>=0} a_m(f) exp(2 pi i m(z-i delta)),
    G_+(z) = S(z+theta_f(z)),                 Im z>delta,
    G_-(z) = conjugate(G_+(conjugate(z))),    Im z<-delta.

delta 始终是代码中 float(.1) 的精确 binary64 值。
对真正的无限维固定点 f，已验证：

| 表达式 | 整个复圆盘上的上界 |
|---|---:|
| f(z)-G_+(z)，圆心 i/4、半径 1/100 | 7.050e-20 |
| f(z+1)-exp(f(z))，圆心 -1/2+i delta、半径 1/200 | 2.239e-20 |

求界采用 96 项形式幂级数、两倍半径上的解析模界及 Cauchy 余项，
再加有限深度、连续 Fourier 系数、无限 Fourier 尾与 E 的传播。
在上方重叠圆盘，|q|<1，所以未知高 Fourier 模使用绝对几何尾，
不是假定一般输入的端点已经周期匹配。

**上界很小不代表函数恒等于零。** 两个证书值都严格保留为正的
误差预算，检查器拒绝将它们改成零或将精确拼接标记改为 true。

## 2. 上下半平面重建已经具备的精确性质

以下结论针对 G_+、G_-，不需要先假设它们与 f 拼接。

采样线上 g_f 有界，所以 |a_m(f)|<=H。对 Im z>delta，Fourier
级数在紧集上一致绝对收敛，theta_f 解析且 1 周期。因此

    G_+(z+1)=exp(G_+(z)).

正则 S 可写为 H_0(exp(L z))，其中 H_0 是 Koenigs 局部逆的整函数
延拓，满足 H_0(Lv)=exp(H_0(v))、H_0(0)=L。
由此 S 整且没有零点；所以 G_+ 没有零点。
这些是 [正则极限证明](theta-regular-depth.md)的解析推论。

当 y 趋向正无穷时，theta_f(x+iy) 趋向 a_0(f)，对 x 一致。
因为 Re L>0、Im L>0，exp(L(x+iy+theta_f(x+iy))) 在 x 的每个
有界区间上一致趋于零。因此

    G_+(x+iy) -> L.

共轭给出 G_- 的函数方程、无零点以及下方极限 conjugate(L)。

## 3. 只假设一个局部恒等式的延拓定理

**定理（条件式）。** 设 f 在 |z|<s 上解析、实对称，f(0)=1，
并满足第 1 节的单叶、正实部条件。设 G_± 满足第 2 节的性质。
如果在一个非空开集

    U subset {|z|<s, Im z>delta}

上有精确恒等式 f=G_+，则它们唯一拼接为 Re z>-2 上的解析函数 F，
满足 F(0)=1、F(-1)=0、F(z+1)=exp(F(z))，并具有上下方固定点极限。
F 实对称，且在 Re z>-1 没有零点。

### 3.1 从一个开集传播到局部函数方程

圆盘与上半平面的交集连通，所以恒等定理把 f=G_+ 传播到整个
上方交集。实对称性给出整个下方交集上的 f=G_-。

集合 {|z|<s, |z+1|<s} 是非空凸透镜。因为

    1/4 + delta^2 < s^2,

它与 Im z>delta 有非空开交集。在这个交集，G_+ 的函数方程给出
f(z+1)=exp(f(z))。恒等定理将此等式传播到整个透镜。

### 3.2 构造第一片右半平面

在整数 n>=0 平移的圆盘上定义

    F_n(z)=exp^{circ n}(f(z-n)),   |z-n|<s.

相邻圆盘上的定义由透镜内的函数方程相容；s<1 保证没有非相邻
圆盘重叠。它们与 G_± 在所有上、下交集中也相容。

这些区域覆盖 Re z>-1/2：当 |Im z|<=delta，取最近的非负整数 n，
有 |Re z-n|<=1/2，故 |z-n|<s。其余点由 G_± 覆盖。
记拼接后的解析函数为 F_0。它无零点：n=0 用 Re f>0，n>=1
用指数无零点，半平面部分用 G_± 无零点。恒等定理还给出
F_0(z+1)=exp(F_0(z)) 在 Re z>-1/2 全部成立。

### 3.3 第一次取解析对数并排除额外零点

右半平面单连通，因此 F_0 有唯一解析对数 ell_0，规定 ell_0(0)=0。
在与原圆盘的交集中，它就是 f 的主对数。令

    F_1(z)=ell_0(z+1),   Re z>-3/2.

它与 F_0 在原半平面一致：二者指数相等，差是固定的 2 pi i 整数；
在实点 z=-49/100 用局部函数方程和 f 的正实部可确定该整数为零。
于是 F_1 是延拓，F_1(-1)=0。恒等定理也保证它在上下部分分别等于
G_±，并满足同一个指数函数方程。

再证明 Re z>-1 上没有零点。若 |Im z|>delta，使用 G_±。
若 Re z>-1/2，使用 F_0。剩下的点满足

    -1<Re z<=-1/2,   |Im z|<=delta.

令 w=z+1，则 0<Re w<=1/2、|w|<s，且 F_1(z)=Log f(w)。
若 F_1(z)=0，则 f(w)=1=f(0)，与 f 的单叶性和 w!=0 矛盾。

### 3.4 第二次取对数

在 Re z>-1 上取 F_1 的解析对数 ell_1，仍规定 ell_1(0)=0。
令 F(z)=ell_1(z+1)，其定义域为 Re z>-2。通过与上一步相同的
分支及恒等定理检查，它延拓 F_1，并满足所列全部性质。
解析对数的归一化和实对称性保证每次延拓仍实对称。
上下方极限来自已拼接的 G_±。定理得证。

**定理的假设 f=G_+ 尚未证明。** 第 1 节的 7.050e-20 上界
不能代替它。归一化 Cauchy 投影固定点方程也还没有推出它。

## 4. 为什么必须保留复对数的分支条件

本轮读取了作者上传的
[Paulsen《Tetration for Complex Bases》全文](https://www.researchgate.net/profile/William-Paulsen-2/publication/325532999_Tetration_for_complex_bases/links/5d88c9d992851ceb79346b5f/Tetration-for-complex-bases.pdf)。
其中 Proposition 2 在 Re z>-2 上陈述函数方程、F(0)=1 和两端极限的
唯一性，并在证明末尾由相同函数值消去复平移常数。这里不能省略
对逆支、实对称性或选定归一化支的检查。这是本次审查发现的使用风险；
没有据此声称 Kneser 的经典唯一性结论错误。

下面给出针对当前上方重建的独立检查，说明该风险是具体的。
取正则逆支 A(2 pi i)，设

    P=2 pi i/L,
    w_n=A(2 pi i)+1+nP.

S 的精确周期和函数方程给出 S(w_n)=1、S(w_n-1)=2 pi i。
又因 Re P、Im P 均为正，而 theta_f(z)->a_0(f)，当 n 足够大时，
z+theta_f(z)=w_n 在 w_n-a_0(f) 附近有根。

本轮不依赖“足够大”的定性说法：n=8 时已用区间算术和 Rouché
定理验证一个圆盘内存在根 c，圆心约为 38.58+9.17i，准确有理
中心在证书中，圆盘半径为 10^-17。严格 Rouché 余量大于 9.970e-18。
因此对实际理想固定点所生成的上方重建，有

    G_+(c)=1,   G_+(c-1)=2 pi i.

证书：[upper-branch-shift-e50/certificate.json](certificates/upper-branch-shift-e50/certificate.json)。
它证明的是上方重建的性质，**不是一个已经全局拼接的 Kneser 反例**。

若第 3 节的精确拼接日后成立，令 F_c(z)=F(z+c)。因为 Re c>0，
F_c 在 Re z>-2 仍解析，满足函数方程、F_c(0)=1 和相同上下极限；
但 F_c(-1)=2 pi i，而 F(-1)=0，故二者不同，且 F_c 不实对称。
这说明仅按上述较弱条件的字面表述，复平移不能被 F(0)=1 排除。
最终识别应使用明确保留实对称/分支条件的定理，或逐项验证
Trappmann–Kouznetsov 的初始区域单叶与整数平移覆盖判据。

## 5. 验收范围与复现

后续的[负 Fourier 模判据](theta-negative-modes.md)给出了本报告
精确拼接假设的一个直接充分条件，并证明球内满足该条件的函数
至多一个。尚缺的是无限负模方程的存在性，有限数值检查不替代它。

已完成：无限维固定点的局部几何；上下重建的解析性、函数方程和
渐近性质；精确局部拼接条件下的右半平面延拓证明；两个重叠缺陷
上界；非主支归一化点的 Rouché 证书。

未完成：局部拼接缺陷恒等于零，以及在充分且分支明确的唯一性
条件下识别 Kneser。既没有把小残差当作精确零，也没有把某个投影
的唯一固定点当作所有函数方程解的唯一解。

检查器重算有理预算、几何包含、Rouché 不等式并校验依赖和源码
哈希。原始区间包络与形式幂级数的正确性仍依赖冻结执行源码、
mpmath 和 FLINT；不是证明助手级算术追踪。局部几何有 10 项检查，
归一化支有 7 项检查，包括拒绝错误的精确拼接和全局结论标记。

```sh
# 在 galic 执行，脚本位于同一目录
PYTHONPATH=/data/kneser-verify/src python3 certify_theta_identity_bridge.py \
  --contraction /data/kneser-exp/goal3-rigorous/continuous-jacobian-v2/full/certificate.json \
  --out fresh-bridge
python3 check_theta_identity_bridge.py fresh-bridge/certificate.json --sources fresh-bridge/sources
python3 check_theta_identity_bridge_tests.py fresh-bridge/certificate.json
PYTHONPATH=/data/kneser-verify/src python3 certify_theta_branch_shift.py \
  --bridge fresh-bridge/certificate.json --out fresh-shift
python3 check_theta_branch_shift.py fresh-shift/certificate.json \
  --bridge fresh-bridge/certificate.json --sources fresh-shift/sources
python3 check_theta_branch_shift_tests.py fresh-shift/certificate.json fresh-bridge/certificate.json
```
