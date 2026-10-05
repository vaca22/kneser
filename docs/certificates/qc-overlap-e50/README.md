# Uniform overlaps for periodic quasiconformal sewing

Executed on galic. The final run is `qc-overlap-v2`; v1 stopped during
serialization and produced no completed certificate.

The certificate bounds the full upper rectangle and the full functional-
equation seam rectangle, using circle covers and the maximum principle.
`sewing-budgets.json` contains the checked rational budgets for the analytic
construction in `../../theta-qc-global-existence.md`.

Run on galic with the sibling continuous contraction certificate available:

```sh
python3 checks/check_theta_qc_overlap.py certificate.json \
  --contraction ../continuous-ideal-contraction-e50/certificate.json \
  --out fresh-sewing-budgets.json
```

`sources/` freezes the producer; `checks/` freezes the arithmetic checker.
The analytic Beltrami and sewing theorems are not formalized proof-assistant
outputs. No canonical Kneser identity is asserted by this certificate.
