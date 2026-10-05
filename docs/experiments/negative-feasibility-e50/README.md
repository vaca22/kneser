# Finite feasibility exploration

These are ordinary high-precision exploratory runs on galic, not interval
root certificates. The separate strict results are in
`../../certificates/finite-negative-roots-e50/`.

- `feasibility-v1/`: whole-interval Gauss quadrature failed cross-grid checks.
  Its apparent departures from the target ball must not be used as evidence
  against feasibility.
- `feasibility-v2/`: composite Gauss quadrature, with a finer partition and
  deeper regular inverse for cross-checking. This remains exploratory.
- `space-bounds.json`: exact rational consequences of the existing certified
  sampling geometry. Left-inverse lower bounds are conditional on such a
  finite inverse existing; they do not establish existence.

The executed exploratory programs, original logs and successful process exit
codes are preserved. A successful process exit is not a mathematical proof.
