# Finite negative-moment root certificates

Executed on galic, 2026-09-12. The three certificates prove roots of the first
2, 4 and 8 complex negative-moment equations in respectively 4, 8 and 16 real
coefficient variables. Their common normalized coefficient ball has radius
1e-30. They do not prove a root of all negative-moment equations.

`sources/` freezes the executed producer and dependencies. `checks/` freezes
the rational inverse/Newton-budget checker and regression tests. The Jacobian
enclosures depend on the producer's verified-disc and FLINT arithmetic; the
checker does not replay the full interval Taylor calculation.

With sibling certificate directories available, run on galic:

```sh
python3 checks/check_theta_finite_negative.py certificate.json \
  --contraction ../continuous-ideal-contraction-e50/certificate.json \
  --negative ../negative-fourier-e50/certificate.json
python3 checks/check_theta_finite_negative_tests.py certificate.json \
  ../continuous-ideal-contraction-e50/certificate.json \
  ../continuous-ideal-contraction-e50/domain.json \
  ../negative-fourier-e50/certificate.json
```

The dependency JSON files are hash-bound by the root certificate. All three
recorded exit statuses are zero. No Kneser identification is asserted.
