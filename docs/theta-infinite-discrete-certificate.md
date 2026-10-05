# 固定离散 θ 算子的无限 Taylor 证书

本次把有限非线性证书扩展到完整的实系数 Wiener 空间
`A_r={f(z)=sum c_k z^k : sum |c_k|r^k<infinity}`，固定 `c0=1`。
目标是固定深度、固定 Fourier 模数、固定采样节点的离散算子。
它不是连续理想算子，也没有给出到真正 Kneser 函数的误差界。

## 包络为何能覆盖无限函数球

令中心 p 为 n 项多项式，`||f-p||_r<=R`。每个输入求值点满足
`|z|<=rho<r` 时，由常数项固定，有 `|f(z)-p(z)|<=R|z|/r`。
现有 `make_coeffs` 使用完整复系数圆盘；其一次系数半径至少为
`R/r`。对 z 非零，以一次项扰动 `(f(z)-p(z))/z` 作点态代理，
便能产生同样的求值。z=0 时扰动为零。因此有限圆盘传播实际已覆盖
无限函数球，不需要重建无穷多个系数。不同求值点可使用不同代理，
因为后续区间运算本来就放弃了它们之间的相关性。

这一论证只用于包含性，不声称复系数代理属于原来的实函数球。
传播所得分支、链导数和有限低块上界因此同样适用于无限球。

## 有限低块与其余三个块

令 P 保留 0 到 n-1 项，Q=I-P，切向量 h 满足 h0=0。设 rho 为
所有 theta 采样点及 band 输入点模长的共同上界，`t=rho/r<1`。
区间求值得到有限逆函数导数上界 L_A、各上弧节点的正向导数
L_S,j，以及 band 导数上界 L_band,j。因上弧高度不小于采样高度，
每个 Fourier 重建因子的模至多 1，M 项之和至多 M。取

```
K=max(max_arc L_S,j M L_A, max_band L_band,j)
C_low=sum[k=1,...,n-1] r^k
C_tail=r^n/(1-r)
```

圆周节点的导数作用于 Ph、Qh 时分别不超过
`K t ||Ph||_r`、`K t^n ||Qh||_r`。每个 Cauchy 系数是节点值的
平均，取实部及下半圆共轭均不增大模。若有限矩阵给出低块上界 a，
整个导数的块支配矩阵与范数上界为

```
[[a, b], [c, d]]
b=C_low K t^n
c=C_tail K t
d=C_tail K t^n
q=max(a+c,b+d)
```

所有输入求值是有界线性映射；经过已验证的解析分支、有限复合与
Fourier 求和，再由有界离散 Cauchy 投影进入 A_r。因此算子在球的
邻域连续可微，可以使用均值积分及 Banach 固定点定理。

令有限点缺陷为 Y，中心 p 处圆周节点模长共同上界为 B。无限输出
尾部至多 `B C_tail`，故完整缺陷 `D=Y+B C_tail`。独立检查器用
精确有理数重算全部四块、q、D，并要求

```
q<1, D+qR<R
||f_discrete-p||_r <= D/(1-q)
```

最后一个界也控制 `|z|<=r` 上的函数值误差。这里采用粗的节点模长
尾界；没有把高项误差当作零，也没有依赖未经证明的系数衰减。

## 实现与复现

`theta_certify.py --infinite-tail` 在同一次点/球区间运行中保存
导数、求值半径、节点模长的有理上界。这些尾部辅助量先用整数运算
向上取整到 2^-40 网格，避免高次幂的分子分母超过默认 JSON 整数
字符串长度限制；低块矩阵及点缺陷仍使用原来的完整精确界。
`theta_infinite.py` 负责
尾块和自映射检验。`check_theta_certificate.py` 先完整核对原有限
证书，再核对新增无限块证书；旧证书没有新增字段时仍按原范围检查。
与原检查器一样，它核对保存的包络及不等式，不重演每个初等函数。
底层圆盘、区间算术及链式法则的信任范围保持不变。

数值工作在 galic 执行：

```sh
cd /data/kneser-exp/goal3-rigorous/infinite-taylor-v2
PYTHONPATH=/data/kneser-verify/src python3 -u theta_certify.py \
  --base e --digits 50 --dps 130 --matrix-bits 100 \
  --weight 11/20 --radius 1e-30 --infinite-tail --out e50
python3 check_theta_certificate.py e50/certificate.json --sources e50/sources
python3 check_theta_certificate_failures.py e50/certificate.json
python3 check_theta_infinite.py
```

## 2026-09-12 完整运行结果

galic 上的计算及独立检查均成功退出。参数为 e 底、n=150、深度
370、Fourier 模数 192、采样数 404、圆周节点数 600，区间精度
130 位十进制、矩阵精度 100 bits，r=11/20、R=10^-30。
下面均为从精确证书向外放宽的可读上界：

| 项目 | 严格上界 |
|---|---:|
| 低到低块 a | 0.054816 |
| 尾到低块 b | 0.009473 |
| 低到尾块 c | 1.546e-36 |
| 尾到尾块 d | 1.953e-41 |
| 完整收缩常数 q | 0.054816 |
| 完整点缺陷 D | 6.847e-39 |
| 到无限离散固定点的距离 | **7.244e-39** |

这证明该闭球内存在唯一的固定离散算子不动点，并在 `|z|<=0.55`
上给出相同的函数值误差上界。此处的完整缺陷主要来自保守的输出
尾界；有限点缺陷仍小于 4.336e-52。不能把较小的有限缺陷代替
完整函数误差。

点传播约 342 秒、球传播约 334 秒、区间矩阵约 94 秒。数据在
[`certificates/e50-infinite-discrete/`](certificates/e50-infinite-discrete/)，
包括精确 JSON 证书、执行源码快照及检查日志。
独立检查器核对了源码散列，10 类证书篡改全部被拒绝，6 项尾部
代数及序列化检查全部通过。此外，galic 上已有核心与误差证书测试
`tests/test_core.py`、`tests/test_certificate.py` 共 20 项通过。
早期 v1 运行在发现大整数序列化问题后主动终止（退出码 143），
没有生成证书；上述结果全部来自修正后的 v2 新运行。

## 剩余的数学问题

无限离散输出的 Taylor 系数以圆周节点数为周期（第零项另外归一化），
所以得到的是单位圆内的有理函数。由此不能推断它在整个上半平面
具有真正 tetration 所需的解析性质。

还需控制有限深度误差、Fourier/DFT 与连续投影之差、圆周求积误差，
并证明理想固定点的 Kneser 身份或独立的真解落球条件。
详见 [理想算子分析](theta-ideal-operator.md)。本证书解决无限 Taylor
维数这一项，不解决以上各项。
