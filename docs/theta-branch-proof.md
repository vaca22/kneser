# 有限 θ 算子的分支证书

本文件只证明有限算子中的解析分支与离散决策；不把有限固定点认作真正 Kneser 函数。
实现见 `theta_branch.py`。该实现以有向圆盘后端给出的包含关系为前提。

## 证明对象与 builder 的关系

固定参数 `nt, nf, n_modes, n_circ, depth`，定义实系数有限映射
`T: {c in R^nt: c[0]=1} -> {c in R^nt: c[0]=1}`。
采样点为精确有理 `j/nf-1/2` 加 `i delta`；圆周点和DFT旋转因子由精确 π 的指数定义。
`delta` 若来自 Python float，则其**精确二进制有理值**是常数；不能在证书中偷偷改成打印出的十进制数。
固定点 L 由独立包含/唯一性证明指定，而不是将一次浮点 L 当作真固定点。

`build.py` 的几何不是 binary64 圆周：它在 `mp.workdps(p.dps)` 内计算 mpmath 圆周。
其 arc/band+/band-、lower 标签只依赖固定参数，在证明映射中可以明确冻结为 builder 在该精度产生的标签，
同时仍然对精确采样几何作区间计算。这是一个定义明确的**固定标签、精确几何有限映射**。
若声称标签等于精确几何判别，还需逐点证明阈值不等式；在圆周实轴交点等边界，
必须用精确对称性规定标签或说明所选两公式相等，不能用浮点 sin(π) 的符号证明。
若要冻结几何数值本身，应保存 builder 的 mpmath dyadic 值并以零半径精确读入；那是另一个有限映射。
现有 Pass 是精确几何包含加浮点冻结标签路线，不应称作冻结 binary64 几何。

T 使用精确算术解释 builder 的公式，浮点 builder 是其数值实现，不是数学上的同一映射。
残差证书须直接包住精确 T(c)-c，浮点 build-check 只能验证实现一致性。
`Lpow=exp(depth*logL)` 与 `multiplier**depth` 在精确算术下相等（depth为整数），舍入结果可有差别。

## Principal log 的充分条件

对于圆盘 D(c,r)，到零的距离下界为 `|c|-r`；到闭负实轴的距离下界为

- `|Im c|-r`，若 `Re c <= 0`；
- `|c|-r`，若 `Re c >= 0`。

两个下界严格正时，整个闭圆盘包含在 principal log 的解析域中。
`LogAudit.observe` 通过 mpmath.iv 有向运算计算这两个量，记录精确二进制端点并在失败时停止。
应覆盖初始化中的 `log(logb*L)`（非 e 时还包括 log(base)）、每个 theta 样本的 depth 次逆迭代、
最终 `log(Lpow*(w-L))`，以及所有 band- 圆周样本。分母非零另由圆盘除法验证。

若某个圆盘碰割线，不能继续套用解析 log 导数半径并声称包住 principal log。
可缩小系数球、提高算术精度以减少舍入圆盘，或对输入球细分。
只有在证明原 principal 分支加 unwrap 与指定解析延拓在整个域上逐点相等后，才可以更换计算分支。
单凭“superf 有周期”不足以替换中间逆迭代的每一层 log。

## 逐样本 unwrap 的归纳证明

第一样本保持不动。设前一个修正圆盘 U[j-1] 已包含全部球内输入的修正样本，令

`Q[j] = (Theta_raw[j]-U[j-1])/period`，`period = 2πi/logL`。

若 `Re Q[j]` 严格包含于 `(k-1/2,k+1/2)`，所有输入均选择同一 nearest integer k。
因此 `U[j]=Theta_raw[j]-k*period` 严格包含原 builder unwrap 的值。
逐步归纳即可证明全部样本的分支稳定。函数 `audited_unwrap` 实现此证明，
记录全部 k（包括非零 k）及半整数边界裕量。中心值的 nint 只提议候选整数，严格区间判断才授予证书。
外部可传入中心 pass 的完整 shifts 列表以明确验证同一选择。

`build.py` 最后计算 closing wrap 只产生 warning，不改变 theta。
实现记录其区间及稳定性；closing wrap 不稳定不影响已定义 T 的连续性，但不能据此声称样本1周期闭合。

## 归一化与导数

最后覆盖 `new[0]=1` 是算子定义的一部分。因此 DT 第0行严格为零。
输入也限制 c[0]=1，残差、球与矩阵范数应在指标1..nt-1的实仿射子空间上解释。
允许额外 c[0] 不确定性只会扩大包含盒，不能替代在该子空间上的定理表述。
非零 unwrap 整数只对 theta 常数值作修正，分支稳定后其对系数导数为零；
但修正后的 theta 会影响后续 superf 的导数，故区间 pass 不可省略非零 shift。

## 最小集成

1. 对每个 principal log 参数调用 `LogAudit.observe(d,site)`。
2. `Pass.run` 的 A 阶段在 disc 后端调用
   `theta,audit = audited_unwrap(theta,2*I*ctx.pi/logL,shifts)`，把 audit 存入返回字典。
3. 浮点中心 pass 保存其完整 shifts；禁止区间分支直接跳过 unwrap。
4. 结果文件同时保存日志分支记录、unwrap记录、精度、球半径和几何标签定义。
5. 球上 DT 证明与残差证明必须使用同一参数、同一标签、同一精确常数定义。

## 本轮验证

在 galic 的 `/data/kneser-exp/goal3-rigorous/branch` 上使用新 `theta_ball.py` 后端验证：
非零整数序列 `[0,1,-2]` 被严格证明并正确应用；半整数 tie 被拒绝；负实轴 log 被拒绝；
成功/失败计数与紧凑最差见证记录正确。所有数值运算均在 galic 执行。

base e、digits=20 的浮点诊断（depth=153,nf=184）得到所有中心 unwrap shifts 为零，
最小 half-integer 裕量约 0.4993253764，逆 log 链最小中心割线距离约 0.1088643360
（样本93、第2次逆log）。该诊断说明中心处没有明显分支障碍，**不构成整个系数球的证书**；
最终结论必须来自严格圆盘全程检查。原始诊断保存在远端 `centre_e20.json`。
