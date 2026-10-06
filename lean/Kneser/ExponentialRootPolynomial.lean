import Kneser.ExponentialCuspParameter
import Kneser.AnalyticEvenDescent
import Mathlib.Tactic.Ring

/-!
# Actual analytic quadratic root polynomial

The two fixed-point branches are constructed through the analytic Morse
coordinate. Their symmetric functions descend analytically from `x` to
`s=x²`, yielding the actual monic quadratic whose roots are the two branches.
This file does not assume a Weierstrass polynomial supplied by preparation.
-/

noncomputable section

namespace Kneser.ExponentialRootPolynomial

open Kneser.ExponentialUnfolding Kneser.ExponentialCuspParameter
open Kneser.AnalyticEvenDescent Filter
open scoped Topology

/-- The monic quadratic determined by the symmetric functions of two roots. -/
def rootPolynomial (a b : ℂ → ℂ) (s u : ℂ) : ℂ := u ^ 2 - a s * u + b s

/-- The analytic root polynomial is constructed from the actual unfolding. -/
theorem exists_analytic_rootPolynomial :
    ∃ U a b : ℂ → ℂ,
      AnalyticAt ℂ U 0 ∧ U 0 = 0 ∧ deriv U 0 ≠ 0 ∧
      AnalyticAt ℂ a 0 ∧ AnalyticAt ℂ b 0 ∧ a 0 = 0 ∧ b 0 = 0 ∧
      (∀ x, a (x ^ 2) = U x + U (-x)) ∧
      (∀ x, b (x ^ 2) = U x * U (-x)) ∧
      (∀ x u, rootPolynomial a b (x ^ 2) u = (u - U x) * (u - U (-x))) ∧
      (∀ᶠ x in 𝓝 0, unfolding (x ^ 2) (U x) = U x ∧
        unfolding (x ^ 2) (U (-x)) = U (-x)) ∧
      (∀ᶠ x in 𝓝 0, U x = U (-x) ↔ x = 0) := by
  obtain ⟨U, hUa, hU0, hUne, hroot, hdistinct⟩ :=
    exists_analytic_distinct_fixedPoint_branches
  have hUaNeg : AnalyticAt ℂ (fun x => U (-x)) 0 := by
    have ha : AnalyticAt ℂ U (-(0 : ℂ)) := by simpa only [neg_zero] using hUa
    exact ha.comp analyticAt_id.neg
  have hsumEven : ∀ x, U (-x) + U (- -x) = U x + U (-x) := by
    intro x
    simp only [neg_neg, add_comm]
  have hprodEven : ∀ x, U (-x) * U (- -x) = U x * U (-x) := by
    intro x
    simp only [neg_neg, mul_comm]
  obtain ⟨a, haa, ha⟩ := exists_analytic_descent hsumEven (hUa.add hUaNeg)
  obtain ⟨b, hba, hb⟩ := exists_analytic_descent hprodEven (hUa.mul hUaNeg)
  change ∀ x, a (x ^ 2) = U x + U (-x) at ha
  change ∀ x, b (x ^ 2) = U x * U (-x) at hb
  have ha0 : a 0 = 0 := by simpa [hU0] using (ha (0 : ℂ))
  have hb0 : b 0 = 0 := by simpa [hU0] using (hb (0 : ℂ))
  refine ⟨U, a, b, hUa, hU0, hUne, haa, hba, ha0, hb0, ha, hb, ?_, ?_, hdistinct⟩
  · intro x u
    unfold rootPolynomial
    rw [ha, hb]
    ring
  · have hneg : Tendsto (fun x : ℂ => -x) (𝓝 0) (𝓝 0) := by
      simpa only [neg_zero] using continuous_neg.continuousAt.tendsto (x := (0 : ℂ))
    filter_upwards [hroot, hneg.eventually hroot] with x hx hx'
    exact ⟨hx, by simpa only [neg_sq] using hx'⟩

end Kneser.ExponentialRootPolynomial

end
