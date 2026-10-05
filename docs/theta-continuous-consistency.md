# 连续 θ 投影：从求积证书到理想算子的点缺陷

2026-09-12。本轮保留 e 底、150 项中心多项式 p，并补上深度、连续
Fourier 积分、无限 Fourier 尾项与连续 Cauchy 积分的误差归约。
**点缺陷本身不是固定点距离。** 后续已独立完成
[连续整球收缩](theta-continuous-ball.md)，得到局部理想固定点距离
<8.399e-21；全局 Kneser 身份仍未证明。

## 1. 有解析余项的 Fourier 积分

令 `g(t)=A(p(t+i delta))-t-i delta`，其中 A 是
[已验证的正则 Koenigs 逆支](theta-regular-depth.md)。目标系数为

```
a_m=integral[-1/2,1/2] g(t) exp(-2 pi i m t) dt
```

将区间分为 64 个小段，半长 h，每段以半径 R=2h 的复圆盘验证
所有主支 log 和正则深度误差。对有限深度的解析函数 g_D 展开
224 项 Taylor 级数，乘以指数因子的 Taylor 级数，并精确积分
偶数项。正式幂级数运算全部使用 FLINT 复区间系数。

若该圆盘上 `|g_D|<=B`，则乘积的模不超过 `B exp(2 pi m R)`，
截断后的积分误差至多

```
2h B exp(2 pi m R) (h/R)^224/(1-h/R)
```

再加入已验证的 A-A_D 深度误差的积分。没有假设端点匹配，也没有
用周期解析函数的 DFT aliasing 公式。

192 个连续系数与原 404 点、有限深度 DFT 的逐项差异均被包络，
最大值严格小于 **6.213e-51**。完整计算约 132 秒，独立检查核对
Taylor 余项、深度预算、复矩形范数与执行源码散列。

## 2. 非周期端点的无限 Fourier 尾项

这里只针对中心 p，不能自动推广到整个函数球。令 M=192、k=50、
a=1/20。用 128 个复圆盘覆盖采样线上的每一个半径 a 邻域，验证
g 解析且模长不超过 B；因此 `|g^(k)|<=k! B/a^k`。
两端的前 k 个 Taylor 系数另外计算，加入正则深度误差的 Cauchy
导数余项。记 j 阶端点导数之差的模上界为 J_j。

分部积分 k 次，把 Fourier 系数分成端点项与导数积分余项。重建
点在单位上圆弧且 `Im z>=delta` 时，令
`q=exp(2 pi i(z-i delta))`，则 `|q|<=1`，并有 `|1+q|>=1/2`：

- 若 `Im z>=1/4`，由 `delta<1/8` 得 `|q|<1/2`。
- 否则 `|Re z|>3/4`，故 `Re q>=0`，从而 `|1+q|>=1`。

这里用 `pi>3`、`log 2<3/4` 即足够；后一条可由 1/x 在 [1,2]
上的梯形积分上界证明。

端点项中的相位为 `(-q)^m`。Abel 求和给出
`|sum[m>=M] (-q)^m/m^s|<=4/M^s`，s>=1；导数积分余项则可绝对
求和。最终统一尾界为

```
E_tail <= 4 sum[j=0,...,k-1] J_j/(6M)^(j+1)
          + k! B/(6a)^k * (M-1)^(1-k)/(k-1)
```

结果严格小于 **2.111e-23**。其中端点部分小于 3.322e-53，其余为
保守的 Cauchy 导数余项。这个界在弧端 `Im z=delta` 仍成立，没有
丢掉不绝对收敛的 1/m 端点项。

## 3. 连续圆周 Cauchy 积分

以 `alpha=asin(delta)` 将上半圆分成右 band、上弧、左 band，分别
在角度区间 `[0,alpha]`、`[alpha,pi-alpha]`、`[pi-alpha,pi]` 上积分。
alpha 与 pi 均由区间算术包围。下半圆取共轭，因而第 k 个实系数为

```
(1/pi) Re integral[0,pi] B(exp(i t)) exp(-i k t) dt
```

每段重新参数化到 [0,1]，分别使用 16、256、16 个小段和 96 项
Taylor 积分，每段同样在两倍半长的复圆盘上验证解析界及 Cauchy
余项。对不同分段分别使用其解析表达式，绝不跨拼接点套用全局
解析的梯形求积误差公式。

先积分使用原有限 DFT 和有限深度 S_D 的边界函数。其有限低项
缺陷记为 Y，边界模长上界为 B0。令

```
e_theta=sum[m=0,...,191] |a_m-a_m_DFT| + E_tail
```

在上弧每个实际输入包络外再扩张 0.02，并验证精确正则 S 的模界。
Cauchy 导数估计给出在中间 0.01 邻域中的导数上界 L_S。检查
`e_theta<0.01` 后，有边界一致性误差

```
e_boundary <= e_depth_forward + L_S e_theta
```

因此，r=11/20、n=150 时，完整连续理想算子的点缺陷满足

```
||T_ideal(p)-p||_r
  <= Y + B0 r^n/(1-r) + r/(1-r) e_boundary
```

这同时包含无限 Taylor 输出、全部 Fourier 模、连续 Fourier
积分、连续圆周积分和正则函数的无限深度。归一化只修改第零项，
所以低项缺陷从 k=1 起求和。

## 4. 已完成的点缺陷结果与复现

完整连续 Cauchy 运行约 188 秒，并通过独立检查器、两个前置证书
检查及所有源码/依赖散列检查。向外放宽的界为：

| 量 | 严格上界 |
|---|---:|
| 有限 DFT/深度边界的连续 Cauchy 低项缺陷 Y | 4.404e-29 |
| 深度与无限 Fourier 重建产生的边界一致性误差 | 5.898e-21 |
| **连续理想算子的完整点缺陷** | **7.209e-21** |

检查器拒绝七类预算/范围篡改，包括把点证书冒称连续收缩或 Kneser
身份。非周期函数 g(t)=t 的三个连续 Fourier 系数及其非零 DFT
均值另有四项回归检查，全部通过。

四份可复核数据与执行源码分别位于：

- `certificates/regular-depth-e50/`
- `certificates/fourier-continuous-e50/`
- `certificates/fourier-tail-e50/`
- `certificates/continuous-ideal-point-e50/`

在 galic 的最终积分目录中复现：

```sh
cd /data/kneser-exp/goal3-rigorous/continuous-point-v1
PYTHONPATH=/data/kneser-verify/src python3 certify_theta_continuous.py \
  --out fresh \
  --fourier ../fourier-continuous-v1/full/certificate.json \
  --tail ../fourier-tail-v1/full/certificate.json
python3 check_theta_continuous.py fresh/certificate.json --sources fresh/sources
python3 check_theta_continuous_tests.py fresh/certificate.json
```

独立检查器核对误差归约、复矩形不等式、求积余项及依赖证书。
底层 exp/log、形式幂级数和解析圆盘界的可信来源仍是执行源码及
mpmath/FLINT 区间后端，没有声称把全部初等运算形式化验证。

## 5. 最终目标尚缺什么

更新：下面的整球收缩义务现已在 [后续报告](theta-continuous-ball.md)
闭合；本节关于全局拼接与 Kneser 身份的义务仍未闭合。

即使上述点缺陷很小，也不能除以旧离散收缩常数的 `1-q` 就称为
真函数误差。旧 q 是 T_disc 的导数界；这里需要 T_ideal 在完整
闭球上的导数界及自映射检验。中心的解析圆盘、端点跳跃、导数与
尾部界也不能冒充对整个球一致的界。

此外，需要独立证明全局拼接和 Kneser 身份。核对原文后，
[Trappmann–Kouznetsov 的 Criterion 1](https://arxiv.org/abs/1006.3981)
要求在初始区域上的全纯单叶 Abel 函数、归一化及整数平移覆盖
整个复平面。Criterion 3 可用初始曲线像的虚部单调和两端趋于
正负无穷来推出这些条件，但仍预设精确 Abel 方程与全纯性。
局部投影固定点证书没有验证这些全局前提。

本轮另外试探了实轴在正则 Abel 坐标中的周期曲线方案。数值斜率
已超过 1.82，故不能调用斜率小于 1 的简单 Theodorsen 全局收缩
路线；这是路线筛查，没有证明所有共形映射方案都不可行。

作者原站 `myweb.astate.edu` 本轮无法解析，2017 年 Paulsen–Cowgill
全文仍未取得；本报告没有把摘要中的唯一性结论当作已核对的可用
定理。[大学书目记录](https://arch.astate.edu/scm-mathfac/9/)仅用于
确认论文信息。这里也不以查不到文献替代上述缺失证明。
