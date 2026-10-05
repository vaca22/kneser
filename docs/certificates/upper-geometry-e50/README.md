# 完整上条带几何证书

运行位置：galic，`/data/kneser-exp/goal3-rigorous/negative-fourier-v1`。

- `certificate.json`：26×143 个圆盘覆盖 [-0.5,0.5]+i[0.3,6]；
  连续 Fourier 尾部、正则极限和 y≥6 的局部 Koenigs 逆界全部计入。
- `upper-geometry-v2.log`：有限区域虚部下界约 0.264404、上界约 1.406318；
  无限端到 L 的距离上界约 0.00225809；|θ_p'| 上界小于 0.1。
- `upper-geometry-check.log`：完整覆盖与解析预算复核、6 项篡改拒绝通过。
- `sources/`：实际执行的数值源码及检查器快照，哈希见 `source-sha256.txt`。

父 Fourier 与尾部证书由 `../continuous-ideal-contraction-e50/` 提供，
其 SHA-256 在本证书中固定。执行时还需原项目的 src 作为 PYTHONPATH。

```sh
PYTHONPATH=/data/kneser-verify/src python3 certify_theta_upper_geometry.py \
  --parent /data/kneser-exp/goal3-rigorous/continuous-jacobian-v2/full \
  --out upper-geometry-new
PYTHONPATH=/data/kneser-verify/src python3 check_theta_upper_geometry.py \
  upper-geometry-new/certificate.json \
  --parent /data/kneser-exp/goal3-rigorous/continuous-jacobian-v2/full --tests
```

检查器独立重算覆盖、Fourier 导数和无限端预算；每个圆盘的基本
exp/log 区间运算由冻结的生产脚本完成，不在轻量检查器中重复。
割线延拓与局部同胚的解析论证见 `../../theta-slit-extension.md`。
本证书不证明当前函数的 Kneser 规范身份。
