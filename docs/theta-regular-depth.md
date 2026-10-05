# 正则超函数的有限深度误差

2026-09-12。对象为 e 底正则 Koenigs 函数及其逆支；这里的“正则”
不等于实轴归一化的 Kneser 函数。所有数值在 galic 上运行。

## 1. 一个带显式常数的局部极限

L 是既有 Krawczyk 包络中唯一的 `exp(L)=L` 根。证书验证
`1.37<|L|<1.38`、`Re L>0.1`、`0<Im L<pi`，所以主支 `Log L=L`。
写 `m=1.37, M=1.38, rho=0.1`，并在 `|u|<=rho` 定义

```
g(u)=Log(L+u)-L
q=1/(m-rho)
h=1/(2m(m-rho))
```

Log 的积分形式与幂级数给出

```
|g(u)| <= q |u|
|g(u)-u/L| <= h |u|^2
M q^2 < 1
M h/(1-M q^2) < 3
```

第二条来自 `sum[k>=2] |u/L|^k/k <= |u/L|^2/(2(1-|u/L|))`。
令 `chi_n(u)=L^n g^[n](u)`，相邻两项之差至多
`M h (M q^2)^n |u|^2`。几何级数证明在闭圆盘上一致收敛到解析
函数 chi，满足

```
chi(g(u))=chi(u)/L
chi(0)=0, chi'(0)=1
|chi(u)-u| <= 3 |u|^2
```

当 `2|u|<rho`，对 `chi-id` 在以 u 为心、半径 |u| 的圆盘使用
Cauchy 导数估计，得到 `|chi'(u)-1|<=12|u|`；u=0 取极限。
这补上了此前仅有 `O(|L|^-D)` 尺度、没有绝对常数的缺口。

## 2. 逆正则函数

对已验证全部主支 log 的输入 w，令 `u=Log^[D](w)-L`，有限算法为

```
A_D(w)=Log(L^D u)/Log L
```

精确局部 Koenigs 极限给出所选逆支

```
A(w)=Log(L^D chi(u))/Log L
```

设 `|u|<=U<rho/2`，`ell<=|Log L|`。程序另外验证 u 非零，并验证
以 `L^D u` 为心、半径 `|L^D| 3 U^2` 的包络不触及 log 割线。
因此有限值和极限使用同一主支，且

```
|A-A_D| <= 3U/((1-3U) ell)
|A'-A_D'| <= |A_D'| 15U/(1-3U)
```

第一条使用 `-log(1-x)<=x/(1-x)`；第二条将
`chi'(u)/(chi(u)/u)-1` 分子中的误差分别估为 `12U`、`3U`。
这些界没有通过两个有限深度计算的差来猜测剩余误差。

## 3. 正向正则函数

令 `v=exp((z-D)Log L)`，`|v|<=V`，取 `E0=6V^2`。验证

```
2(V+E0)<rho
3(V+E0)^2<E0
12(V+E0)<1
```

后两式与 Rouche 定理、导数估计说明 `chi(u)=v` 在
`|u-v|<E0` 内有唯一解，且为零点附近的逆支。因此精确正则超函数为

```
S(z)=exp^[D](L+chi^-1(v))
```

与有限 `S_D(z)=exp^[D](L+v)` 的初始误差至多 E0。若第 j 步有限值
包络的实部上界为 b_j，当前误差为 E_j，则

```
E_(j+1) <= E_j exp(b_j+E_j)
```

由沿线段积分指数导数立即得到。程序逐步向上取整传播增益，并保存
最终增益与误差；独立检查器核对 `E_final>=E0*gain`。

正向定义不依赖充分大的 D：由 chi 的函数方程，
`exp(L+chi^-1(v/L))=L+chi^-1(v)`。相邻深度的定义在重叠域完全相同，
而这些局部域随 D 增大覆盖整个 z 平面，故 S 是整函数。这个一致性
论证也给出 `S(z+1)=exp(S(z))`。

## 4. 已完成的连续域证书

参数 D=370、区间精度 130 位。逆函数验证覆盖
`z=t+i delta, -1/2<=t<=1/2` 的全部 64 段及原 `A_(11/20)` 中
半径 `10^-30` 的无限输入函数球；这里沿用复一次系数圆盘的点态
覆盖论证。正向验证覆盖独立矩形
`[-1.5,0.6]+i[-0.9,0.1]` 的全部 16×8 小格。

向外放宽的结果：

| 量 | 严格上界 |
|---|---:|
| 逆正则函数的深度误差 | 4.780e-51 |
| 逆函数导数的相对深度误差 | 3.285e-50 |
| 正向正则函数的深度误差 | 1.675e-49 |

正向矩形证书本身不声称连续 theta 的像已经落入此矩形。
后续连续积分程序直接对其实际输入包络调用同一正则函数验证器，
因此不靠这项未证明的落域假设。

中心 polynomial 的 theta 导数界，与整个无限函数球的导数界也须
区分。`g_center_derivative_upper` 只对应中心，代码没有将有限
系数导数盒冒充无限函数的导数包络。

## 5. 复现与检查范围

```sh
cd /data/kneser-exp/goal3-rigorous/regular-depth-v2
PYTHONPATH=/data/kneser-verify/src python3 certify_regular_depth.py --out fresh
python3 check_regular_depth.py fresh/certificate.json --sources fresh/sources
PYTHONPATH=/data/kneser-verify/src python3 check_regular_depth_tests.py fresh/certificate.json
```

完整运行约 47 秒。检查器及源码散列检查通过；五种篡改拒绝、60/100
深度正向和逆向包络交集、实数 1 的奇异 log 轨道拒绝测试均通过。
数据保存于 `certificates/regular-depth-e50/`。

信任范围仍包括圆盘后端、mpmath 定向区间算术及所述解析公式。
独立检查器重算有理常数、根包络条件与误差归约，不重演每个 exp/log。
这里没有得到 Kneser 身份或真 Kneser 距离。
