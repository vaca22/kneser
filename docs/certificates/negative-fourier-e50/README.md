# Negative Fourier diagnostics, base e

Executed on galic, 2026-09-12. `certificate.json` contains continuous regular
Fourier integrals for modes -16 through -1. `sources/` freezes the producer
and its dependencies. `checks/` freezes the verification and regression tools.
The four exit-status files all record successful final runs.

`diagnostic.json` propagates these finite moments to the certified ideal
projection fixed point and checks positivity/univalence on the entire ball.
It hash-binds the negative certificate and the existing continuous contraction
certificate in `../continuous-ideal-contraction-e50/`. It does not certify zero
negative modes, exact gluing, or identification with Kneser's function.

Run arithmetic on galic. From this directory, with the sibling contraction
certificate directory copied alongside it:

```sh
python3 checks/check_theta_fourier.py certificate.json --sources sources
python3 checks/check_theta_negative_modes.py certificate.json \
  --contraction ../continuous-ideal-contraction-e50/certificate.json \
  --out fresh-diagnostic.json
PYTHONPATH=sources:/data/kneser-verify/src python3 checks/check_theta_fourier_kernel.py
python3 checks/check_theta_fourier_tests.py certificate.json \
  ../fourier-continuous-e50/certificate.json
```

The checker refuses to overwrite the diagnostic output. Original logs and
the successful output are retained here; exact rational bounds are in JSON.
These checks replay error-budget reductions, not a proof-assistant trace of
every FLINT and mpmath operation.
