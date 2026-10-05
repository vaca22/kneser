# Exact inverse-branch bridge

Executed on galic. A 51 by 13 circle cover certifies the inverse branch on
the complete sampling band. A separate local univalence check identifies
that branch with the upper parameter of the independently sewn function.

Together with the analytic proof in `../../theta-qc-global-existence.md`,
these inequalities establish all negative moments equal to zero and identify
the sewn function with the unique local ideal theta fixed point. They do not
establish the final canonical Kneser uniqueness condition.

Run on galic with the two sibling certificate directories present:

```sh
python3 checks/check_theta_qc_branch.py certificate.json \
  --qc ../qc-overlap-e50/certificate.json \
  --contraction ../continuous-ideal-contraction-e50/certificate.json \
  --out fresh-bridge-result.json
python3 checks/check_theta_qc_tests.py \
  ../qc-overlap-e50/certificate.json certificate.json \
  ../continuous-ideal-contraction-e50/certificate.json \
  ../continuous-ideal-contraction-e50/domain.json \
  ../continuous-ideal-contraction-e50/fourier.json \
  ../continuous-ideal-contraction-e50/tail.json \
  ../qc-overlap-e50/sewing-budgets.json
```

Original logs, exit statuses and executed sources are retained. The checker
replays rational and interval reductions and source hashes; it does not replay
every elementary operation of the primitive regular-inverse computation.
