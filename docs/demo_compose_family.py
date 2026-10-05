"""Two calibrated families for the equation f(f(x)) = g(x).

This deliberately does not propose a general existence theory.

* For g(x)=lambda*x with positive rational-square lambda, the principal
  real branch is exactly f(x)=sqrt(lambda)*x.
* For g(x)=exp(x)-1, reuse the exact ``Fraction`` composition routine from
  demo_infinite_system.py and solve the tangent-to-identity formal series
  degree by degree.  The result is checked exactly modulo x^(N+1).

Run:
  PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=src \
    python3 docs/demo_compose_family.py [--order 24]
"""

import argparse
from fractions import Fraction
from math import factorial, isqrt

try:  # direct script execution
    from demo_infinite_system import compose
except ImportError:  # import as docs.demo_compose_family
    from docs.demo_infinite_system import compose


def principal_rational_sqrt(value):
    """Exact positive square root of a nonnegative rational square."""
    value = Fraction(value)
    if value < 0:
        raise ValueError("the real principal branch requires lambda >= 0")
    numerator = isqrt(value.numerator)
    denominator = isqrt(value.denominator)
    if numerator * numerator != value.numerator or denominator * denominator != value.denominator:
        raise ValueError("lambda is not a square in the rational calibration domain")
    return Fraction(numerator, denominator)


def linear_half_iterate(lam, order=4):
    """Coefficients of the exact principal f(x)=sqrt(lam)*x calibration."""
    root = principal_rational_sqrt(lam)
    coefficients = [Fraction(0)] * (order + 1)
    coefficients[1] = root
    return coefficients


def exp_minus_one_coefficients(order):
    return [Fraction(0)] + [
        Fraction(1, factorial(k)) for k in range(1, order + 1)
    ]


def parabolic_half_iterate(order):
    """Exact tangent-to-identity formal root of exp(x)-1 through x^order."""
    if order < 1:
        raise ValueError("order must be at least 1")
    target = exp_minus_one_coefficients(order)
    coefficients = [Fraction(0), Fraction(1)] + [Fraction(0)] * (order - 1)
    for degree in range(2, order + 1):
        current = compose(coefficients, coefficients, degree)
        coefficients[degree] = (target[degree] - current[degree]) / 2
    return coefficients


def exact_composition_check(coefficients, target, order):
    return compose(coefficients, coefficients, order) == target[:order + 1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--order", type=int, default=24)
    args = parser.parse_args()
    if args.order < 2:
        parser.error("--order must be at least 2")

    lam = Fraction(9, 4)
    linear = linear_half_iterate(lam, args.order)
    linear_target = [Fraction(0), lam] + [Fraction(0)] * (args.order - 1)
    assert exact_composition_check(linear, linear_target, args.order)
    print("Calibration g(x)=lambda*x (not a general theorem):")
    print(f"  lambda={lam}, principal f(x)=sqrt(lambda)*x={linear[1]}*x")
    print(f"  exact composition modulo x^{args.order + 1}: PASS")

    target = exp_minus_one_coefficients(args.order)
    formal = parabolic_half_iterate(args.order)
    assert exact_composition_check(formal, target, args.order)
    print("\nParabolic family g(x)=exp(x)-1:")
    print("  branch fixed by f(0)=0 and f'(0)=1")
    print(f"  exact Fraction check f(f(x))=exp(x)-1 mod x^{args.order + 1}: PASS")
    print("  locked finite-order coefficients:")
    for degree in range(1, min(args.order, 10) + 1):
        print(f"    a[{degree}]={formal[degree]}")
    print("  formal finite-order solvability is not a convergence claim.")


if __name__ == "__main__":
    main()
