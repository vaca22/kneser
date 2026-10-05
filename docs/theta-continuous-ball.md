# 连续 theta 算子的整球定义域与导数验证

计算平台：`ssh galic`。本文针对 e 底、精确 binary64 高度
`float(.1)`、中心 e50 多项式 p、加权 Wiener 空间 A_r，r=11/20。
不是固定 DFT 算子的收缩证明，也不自动给出 Kneser 身份。

**已通过 galic 计算和独立预算检查：完整连续理想算子在
R=10^-18 的无限系数球上收缩，q<0.141711，
中心到其唯一局部固定点的 A_(11/20) 距离 <8.399e-21。**
证书：[continuous-ideal-contraction-e50/certificate.json](certificates/continuous-ideal-contraction-e50/certificate.json)。
全局 Kneser 识别仍未证明。

后续：[局部拼接与身份桥接](theta-identity-bridge.md)已补上半径 0.54
圆盘上的单叶/无零点证书、条件式全局延拓证明，以及非主支归一化的
Rouché 证书。精确拼接仍未证明。

| 验证量 | 严格上界 |
|---|---:|
| 中心低阶连续 Jacobian 列范数 | 0.054748 |
| 边界导数的无限 Fourier/正则一致性误差 | 0.069049 |
| 输出 Taylor 尾的导数贡献 | 2.011e-5 |
| 无限输入尾块 | 0.141711 |
| R=10^-18 球内的导数变化 | 2.230e-7 |
| 完整整球收缩常数 | 0.141711 |
| 完整理想算子点缺陷 | 7.209e-21 |
| 中心到唯一局部理想固定点的距离 | 8.399e-21 |

预算使用证书中的精确有理数，不能把表中向上舍入后的各行直接
相加替代它。该固定点实对称、f(0)=1，并在 |z|<1 解析：
固定点等于有界圆周数据的 Cauchy 投影，其 Taylor 系数一致有界。
这项单位圆内解析性仍不等于割平面上的全局延拓。

## 1. 完整复函数球的定义域

已生成并通过独立预算检查的证书：
[continuous-ball-domain-e50/certificate.json](certificates/continuous-ball-domain-e50/certificate.json)。
取 R0=10^-6，球为 p+h，h(0)=0，sum |h_j|r^j<=R0。
不是把未知函数截断为有限个系数。

将 [-1/2,1/2] 划为 128 段，以每段中点为圆心、
半径 a+1/256 的复圆盘覆盖，a=1/40。平移 i delta 后，每个圆盘
均严格位于 |z|<r。对每个圆盘，利用

    |h(z)| <= ||h||_r |z|/r

扩张 p(z) 的包络，再用正则 Koenigs 逆函数的区间算法逐步验证
全部 logarithm 分支。记所得统一逆函数导数上界为 L_A。
这一构造覆盖整球，并保证沿实采样线的每点都有半径 a 的解析邻域。

## 2. 非周期输入的无限 Fourier 级数

对一个范数不超过 1 的扰动方向 h，令

    v(t) = A'(f(t+i delta)) h(t+i delta).

上述解析圆盘内 |v|<=L_A。对 f-p 的差函数，沿复线段积分同样
得到 |A(f)-A(p)|<=L_A ||f-p||_r。无需假设一般输入满足周期性。

令 M=192、K=10。与连续点缺陷证书相同，上弧的
q=exp(2 pi i(z-i delta)) 满足 |q|<=1、|1+q|>=1/2。
分部积分 K 次，并对端点项使用 Abel 求和，有

    ||sum_{m>=M} v_hat(m) q^m|| <= H E,
    E = 4 sum_{j=0}^{K-1} 2 j! / [a^j (6M)^(j+1)]
        + K!/(6a)^K * (M-1)^(1-K)/(K-1),

其中 H 是解析圆盘内的模上界。端点跳跃的 j 阶导数界为
2 j! H/a^j；绝不能省略这些非周期端点项。这个统一尾界同时证明
函数球上 Fourier 重建的一致收敛，以及逐方向求导的合法性。
前 M 项用每个 Fourier 系数模不超过 H，得到

    ||D theta(f)|| <= (M+E) L_A = L_theta.

中心的连续/DFT 差已有独立证书；于是整个函数球上，上弧参数
与中心有限 DFT 参数之差不超过

    epsilon_theta(p) + R0 L_theta < 1/100.

## 3. 连续圆周和复化

将右 band、上弧、左 band 分别划成 16、256、16 段。每段以
复圆盘覆盖完整实角区间。上弧在所有可能的精确参数外再扩张
1/100，验证正则 S 的模界 B；Cauchy 给 |S'|<=100B。
两段 band 分别验证 exp(p+h) 和 Log(p+h) 的完整分支及导数。
因此全部连续圆周数据在函数球上有统一导数界。

实对称算子的复化必须说明：不能对复系数输入直接取实部。
上弧表达式记作 B_+(f)，下弧定义为
overline(B_+(overline(f)))，参数按共轭反射。它关于 f 是解析的，
在实系数子空间上等于原算子。上下弧的估计相同。归一化 Cauchy
投影去掉第 0 项后，范数至多边界模界乘 r/(1-r)。这证明复化后的
连续理想 T 在球内是 Banach 空间值全纯映射，且

    ||DT(f)|| <= L < 222991.

这不是收缩常数。不能把 L>1 的定义域证书称作 Banach 固定点证明。

## 4. 中心导数如何延伸到整球

设另外验证中心导数的范数 q0。因为 DT 是算子空间值全纯映射，
在 R0 球内有界于 L，沿任意单位方向应用 Cauchy 估计得到

    ||D²T(x)|| <= L/(R0-||x-p||).

沿 p 到 f 的线段积分，保守地得到：对 ||f-p||<=R<R0，

    ||DT(f)-DT(p)|| <= L R/(R0-R).

在 R=10^-18 时，已验证这一变化量小于 2.230e-7。
因此中心导数 q0 若留有这一裕量，就能推出整球收缩。
这不复用旧离散算子的 Jacobian。

## 5. 连续中心 Jacobian 的验证方案

驱动：[certify_theta_continuous_jacobian.py](certify_theta_continuous_jacobian.py)。
它直接对连续 Fourier 积分与分段连续 Cauchy 积分求导。
输入采用范数为 1 的基向量 (z/r)^j，j=1,...,127；
输出保留 k=1,...,31。积分采用 64 阶 Taylor 展开及半径比 1/2
的显式 Cauchy 余项；前一级 Fourier 积分的区间误差传入后一级。
正则有限深度导数误差单独加入。

执行版本把截断卷积重排为区间矩阵乘法，避免对每一输入列重复
计算相同的 q 幂。截断次数与余项不变。
[check_theta_moments.py](check_theta_moments.py) 用独立的精确有理
复多项式卷积核对四个批量积分。首版逐列版本因耗时中止，远端
`continuous-jacobian-v1` 留有源码与退出记录；实际证书使用 v2。

无限 Fourier 尾的导数不能直接沿用中心函数的微小尾界，
而是用第 2 节的 E L_A。这使低块比较多出

    r/(1-r) [L_S E L_A + epsilon_S' M L_A]。

这里 epsilon_S' 同时覆盖有限深度导数误差和中心 theta 参数误差。
若完整边界导数上界为 B_D，输出尾为

    B_D r^32/(1-r)。

对输入 j>=128，令 rho_s 为实采样线最大模长，rho_a 为第 1 节
解析圆盘的最大模长，rho_b 为 band 内输入最大模长。高输入块由

    r/(1-r) max{
        L_S L_A [M (rho_s/r)^128 + E (rho_a/r)^128],
        L_band (rho_b/r)^128
    }

控制。低列的加权绝对和与这些误差合并后给 q0，再加入第 4 节
的变化界，最后检查点缺陷 d<=(1-q)R。本节计算约 358 秒，
已通过 [独立检查器](check_theta_continuous_jacobian.py)。

## 6. 可信边界和剩余身份问题

预算检查器重新计算有理不等式、积分余项、块范数和依赖哈希；
log/exp 分支包络、形式幂级数积分与标量区间的正确性依赖冻结的
执行源码、mpmath 区间实现和 FLINT。不是证明助手逐指令重放。
整球定义域另有 10 项篡改拒绝测试及一项正常证书测试。
连续收缩另配七项篡改拒绝测试及一项正常证书测试，覆盖列缺失、
求积余项、两种无限尾项、中心到整球变化量和冒称 Kneser 身份。

已通过的连续收缩识别的是“归一化连续投影算子的局部固定点”。
还必须证明拼接数据的负圆周 Fourier 模为零、常数修正为零，
或通过独立构造把 Kneser 真解包进同一个球。
投影会消去负 Fourier 模，故不能从投影固定点方程直接推出
全局 exp 函数方程，更不能跳过全局唯一性定理的假设。

本轮进一步定位到 Cowgill 的
[2017 年学位论文官方记录](https://arch.astate.edu/all-etd/562/)，
摘要涉及唯一性与连续 Fourier/Cauchy 算法。其公开下载入口在本次
访问中返回 HTTP 403，未取得证明正文，故没有用摘要代替定理假设。

整球定义域的复现（在 galic 执行）：

```sh
PYTHONPATH=/data/kneser-verify/src python3 certify_theta_ball_domain.py \
  --point /data/kneser-exp/goal3-rigorous/continuous-point-v1/full/certificate.json \
  --out fresh-domain
python3 check_theta_ball_domain.py fresh-domain/certificate.json --sources fresh-domain/sources
python3 check_theta_ball_domain_tests.py fresh-domain/certificate.json
```

完整连续收缩的复现：

```sh
PYTHONPATH=/data/kneser-verify/src python3 certify_theta_continuous_jacobian.py \
  --domain fresh-domain/certificate.json --out fresh-contraction
python3 check_theta_continuous_jacobian.py fresh-contraction/certificate.json \
  --sources fresh-contraction/sources
python3 check_theta_continuous_jacobian_tests.py fresh-contraction/certificate.json
PYTHONPATH=/data/kneser-verify/src python3 check_theta_moments.py
```
