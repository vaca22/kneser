# 最终 Kneser 规范身份：证书与复算

2026-09-12。结论是认证无限固定点 F=f*=F_K 于 C\(−∞,−2]，
且 150 项中心多项式 p 满足 ||F_K−p||_(0.55)<2.878e-30。
目录名 e50 表示计算参数，不表示已认证 50 位误差。

[完整解析证明](proofs/theta-canonical-identity.md)构造标准直边的逆支，
以辐角原理证明整个标准初始区域的单叶逆函数，再验证整数平移覆盖，
应用 Trappmann–Kouznetsov 的 Theorem 1 和 Theorem 5。

- `certificate.json`：64 个低段、149 个中高段区间，桥接及完整无限端点预算。
- `replay-result.json`：160 位精度重算所有 213 个有限单元及端点预算的结果。
- `canonical-identity-result.json`：数值证书、误差预算与解析证明的散列关联记录。
- `canonical-curve-check.log`：完整复算及 7 项篡改拒绝检查通过。
- `sources/`：galic 实际执行的脚本及 kneser 包快照。
- `proofs/`：最终结果记录引用的五份解析证明快照。
- `SHA256SUMS`：本目录交付文件散列。

所有数值计算均通过 SSH 在 galic 执行。生成使用 130 位精度，检查使用
160 位精度（FLINT 532 bits）。原始执行目录为
`/data/kneser-exp/goal3-rigorous/negative-fourier-v1`。实际执行命令：

```sh
PYTHONPATH=/data/kneser-verify/src python3 certify_theta_canonical_curve.py --parent /data/kneser-exp/goal3-rigorous/continuous-jacobian-v2/full --qc qc-overlap-v2/sewing-budgets.json --geometry upper-geometry-v2/certificate.json --out canonical-curve-v2
PYTHONPATH=/data/kneser-verify/src python3 check_theta_canonical_curve.py canonical-curve-v2/certificate.json --parent /data/kneser-exp/goal3-rigorous/continuous-jacobian-v2/full --qc qc-overlap-v2/sewing-budgets.json --geometry upper-geometry-v2/certificate.json --out canonical-curve-v2/replay-result.json
PYTHONPATH=/data/kneser-verify/src python3 finalize_theta_canonical_identity.py --curve canonical-curve-v2/certificate.json --replay canonical-curve-v2/replay-result.json --budgets qc-overlap-v2/sewing-budgets.json --proofs canonical-proofs --out canonical-curve-v2/canonical-identity-result.json
```

复算快照时，在本目录运行下面命令。依赖 Python、mpmath、numpy 和
python-flint（原执行版本 0.9.0）；工作目录不影响已记录的证书散列。

```sh
PYTHONPATH=sources python3 sources/check_theta_canonical_curve.py certificate.json --parent ../continuous-ideal-contraction-e50 --qc ../qc-overlap-e50/sewing-budgets.json --geometry ../upper-geometry-e50/certificate.json --out replay-local.json
PYTHONPATH=sources python3 sources/finalize_theta_canonical_identity.py --curve certificate.json --replay replay-local.json --budgets ../qc-overlap-e50/sewing-budgets.json --proofs proofs --out identity-local.json
```

父证书为[连续无限收缩](../../theta-continuous-ball.md)、
[拟共形拼接预算](../qc-overlap-e50/README.md)和
[上半平面几何](../upper-geometry-e50/README.md)。父证书保留各阶段的历史范围标志。

检查器验证数值前提；最终记录器验证关联和预算并记录解析结论。
它们不形式化验证辐角原理或文献唯一性定理。本交付是计算机辅助解析证明，
不是 Lean/Coq 证明。快照中的依赖文稿保留旧阶段措辞，最终结论以
`theta-canonical-identity.md` 为准；工作文档的导航链接可从
[文档索引](../../README-zh.md)访问。
