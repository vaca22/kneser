import Kneser.HeadTail
import Kneser.ParabolicOrbitSum

/-!
# Differentiating an actual orbit series by a moving finite cutoff

The analytic input consists of separate model, finite-head, and infinite-tail
estimates. Exact identities for convergent sums assemble these estimates into
a bound for the actual coordinate. A superlinear error then establishes its
right derivative. No theorem here assumes differentiability of the infinite
sum or an interchange of derivative and `tsum`.
-/

namespace Kneser

open Filter Set
open scoped BigOperators Topology

/-- The actual coordinate represented by a model plus its convergent series. -/
noncomputable def coordinateSeries (ψ : ℝ → ℂ) (term : ℝ → ℕ → ℂ) (s : ℝ) : ℂ :=
  ψ s + ∑' k : ℕ, term s k

/-- The proposed first-order coefficient, defined by its explicit orbit sum. -/
noncomputable def firstOrderCoefficient (dψ : ℂ) (δ : ℕ → ℂ) : ℂ :=
  dψ + ∑' k : ℕ, δ k

/-- The finite sum of individual remainders is the finite-head remainder. -/
theorem finite_head_remainder (term : ℝ → ℕ → ℂ) (δ : ℕ → ℂ)
    (s : ℝ) (J : ℕ) :
    (∑ k ∈ Finset.range J, (term s k - term 0 k - s • δ k)) =
      (∑ k ∈ Finset.range J, term s k) -
      (∑ k ∈ Finset.range J, term 0 k) - s • (∑ k ∈ Finset.range J, δ k) := by
  simp only [Finset.sum_sub_distrib, Finset.smul_sum]

/-- The separate analytic estimates give a superlinear bound for the actual
infinite sum. Absolute convergence of the coefficient is supplied explicitly;
the summable tails are handled by exact sum identities. -/
theorem coordinateSeries_power_error
    (ψ : ℝ → ℂ) (term : ℝ → ℕ → ℂ) (dψ : ℂ) (δ : ℕ → ℂ)
    (J : ℝ → ℕ) (Cψ CH CT CD q : ℝ)
    (hzero : Summable (term 0)) (hδ : Summable (fun k => ‖δ k‖))
    (hterms : ∀ᶠ s in 𝓝[>] (0 : ℝ), Summable (term s))
    (hmodel : ∀ᶠ s in 𝓝[>] (0 : ℝ), ‖ψ s - ψ 0 - s • dψ‖ ≤ Cψ * s ^ q)
    (hhead : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ‖∑ k ∈ Finset.range (J s), (term s k - term 0 k - s • δ k)‖ ≤ CH * s ^ q)
    (htail : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ‖∑' k : ℕ, term s (k + J s)‖ ≤ CT * s ^ q)
    (htailzero : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ‖∑' k : ℕ, term 0 (k + J s)‖ ≤ CT * s ^ q)
    (htailδ : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ‖s • (∑' k : ℕ, δ (k + J s))‖ ≤ CD * s ^ q) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ‖coordinateSeries ψ term s - coordinateSeries ψ term 0 -
        s • firstOrderCoefficient dψ δ‖ ≤ (Cψ + CH + 2 * CT + CD) * s ^ q := by
  have hd : Summable δ := hδ.of_norm
  filter_upwards [hterms, hmodel, hhead, htail, htailzero, htailδ]
    with s hss hψ hH hTs hT0 hD
  rw [finite_head_remainder] at hH
  have hs := hss.sum_add_tsum_nat_add (J s)
  have h0 := hzero.sum_add_tsum_nat_add (J s)
  have hder := hd.sum_add_tsum_nat_add (J s)
  have hb := head_tail_error_bound s (ψ s) (ψ 0) dψ
    (∑ k ∈ Finset.range (J s), term s k)
    (∑ k ∈ Finset.range (J s), term 0 k)
    (∑ k ∈ Finset.range (J s), δ k)
    (∑' k : ℕ, term s (k + J s))
    (∑' k : ℕ, term 0 (k + J s))
    (∑' k : ℕ, δ (k + J s))
    (Cψ * s ^ q) (CH * s ^ q) (CT * s ^ q) (CD * s ^ q) hψ hH hTs hT0 hD
  have heq : Cψ * s ^ q + CH * s ^ q + 2 * (CT * s ^ q) + CD * s ^ q =
      (Cψ + CH + 2 * CT + CD) * s ^ q := by ring
  rw [heq] at hb
  simpa only [coordinateSeries, firstOrderCoefficient, add_assoc, hs, h0, hder]
    using hb

/-- The orbit-sum coefficient is the actual right derivative of the coordinate.
The proof uses only the separate finite-head/tail estimates; derivative
existence and a complete remainder bound are conclusions. -/
theorem hasDerivWithinAt_coordinateSeries
    (ψ : ℝ → ℂ) (term : ℝ → ℕ → ℂ) (dψ : ℂ) (δ : ℕ → ℂ)
    (J : ℝ → ℕ) (Cψ CH CT CD q : ℝ) (hq : 1 < q)
    (hzero : Summable (term 0)) (hδ : Summable (fun k => ‖δ k‖))
    (hterms : ∀ᶠ s in 𝓝[>] (0 : ℝ), Summable (term s))
    (hmodel : ∀ᶠ s in 𝓝[>] (0 : ℝ), ‖ψ s - ψ 0 - s • dψ‖ ≤ Cψ * s ^ q)
    (hhead : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ‖∑ k ∈ Finset.range (J s), (term s k - term 0 k - s • δ k)‖ ≤ CH * s ^ q)
    (htail : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ‖∑' k : ℕ, term s (k + J s)‖ ≤ CT * s ^ q)
    (htailzero : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ‖∑' k : ℕ, term 0 (k + J s)‖ ≤ CT * s ^ q)
    (htailδ : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ‖s • (∑' k : ℕ, δ (k + J s))‖ ≤ CD * s ^ q) :
    HasDerivWithinAt (coordinateSeries ψ term) (firstOrderCoefficient dψ δ) (Ici 0) 0 := by
  apply hasDerivWithinAt_of_power_error _ _ (Cψ + CH + 2 * CT + CD) q hq
  exact coordinateSeries_power_error ψ term dψ δ J Cψ CH CT CD q
    hzero hδ hterms hmodel hhead htail htailzero htailδ

/-- The same construction with the coefficient's absolute convergence derived
from the paper's three component estimates. The first-order coefficient is the
sum of the direct parameter term and the spatial derivative times orbit velocity. -/
theorem hasDerivWithinAt_coordinateSeries_of_first_order_bounds
    (ψ : ℝ → ℂ) (term : ℝ → ℕ → ℂ) (dψ : ℂ) (a b v : ℕ → ℂ)
    (J : ℝ → ℕ) (Cψ CH CT CD q : ℝ) (hq : 1 < q)
    (C₁ C₂ C₃ : ℝ) (hC₂ : 0 ≤ C₂) {p : ℕ} (hp : 2 ≤ p)
    (ha : ∀ k, ‖a k‖ ≤ C₁ / ((k : ℝ) + 1) ^ p)
    (hb : ∀ k, ‖b k‖ ≤ C₂ / ((k : ℝ) + 1) ^ (p + 1))
    (hv : ∀ k, ‖v k‖ ≤ C₃ * ((k : ℝ) + 1))
    (hzero : Summable (term 0))
    (hterms : ∀ᶠ s in 𝓝[>] (0 : ℝ), Summable (term s))
    (hmodel : ∀ᶠ s in 𝓝[>] (0 : ℝ), ‖ψ s - ψ 0 - s • dψ‖ ≤ Cψ * s ^ q)
    (hhead : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ‖∑ k ∈ Finset.range (J s),
        (term s k - term 0 k - s • (a k + b k * v k))‖ ≤ CH * s ^ q)
    (htail : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ‖∑' k : ℕ, term s (k + J s)‖ ≤ CT * s ^ q)
    (htailzero : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ‖∑' k : ℕ, term 0 (k + J s)‖ ≤ CT * s ^ q)
    (htailδ : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ‖s • (∑' k : ℕ, (a (k + J s) + b (k + J s) * v (k + J s)))‖ ≤ CD * s ^ q) :
    HasDerivWithinAt (coordinateSeries ψ term)
      (firstOrderCoefficient dψ (fun k => a k + b k * v k)) (Ici 0) 0 := by
  exact hasDerivWithinAt_coordinateSeries ψ term dψ (fun k => a k + b k * v k)
    J Cψ CH CT CD q hq hzero
    (summable_norm_first_order_terms a b v C₁ C₂ C₃ hC₂ hp ha hb hv)
    hterms hmodel hhead htail htailzero htailδ

end Kneser
