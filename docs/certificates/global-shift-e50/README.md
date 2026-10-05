# 弱半平面唯一性反例的组合复核

运行位置：galic，`/data/kneser-exp/goal3-rigorous/identity-bridge-v1`。
`global-shift-check.log` 和 `global-shift-exit-status` 记录成功复核。

依赖既有 `../upper-branch-shift-e50/certificate.json` 与
`../identity-bridge-e50/certificate.json` 的完整依赖链。
`sources/theta-qc-global-existence.md` 是将上端根解释为全局解之根的
解析证明快照，其哈希写在结果中。程序不形式化验证这份解析证明。

复现（在 galic 的相同目录结构中）：

```sh
python3 check_theta_global_shift.py \
  --shift shift-v2/certificate.json --bridge full/certificate.json \
  --proof theta-qc-global-existence.md --out global-shift-result.json
```

所得反例不实对称，不能用于声称 Kneser 规范唯一性为假。
