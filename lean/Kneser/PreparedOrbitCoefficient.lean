import Kneser.ExponentialUnfolding
import Kneser.ParabolicOrbitSum
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Prepared-residual coefficients along the actual exponential orbit

The chain-rule term in the first-order orbit series is proved here for the
actual finite iterates of `exp (-s + (1-s)u) - 1`. The prepared residual must
have the specified *joint* Fréchet derivative at each orbit point; merely
assuming separate partial derivatives would not suffice for this chain rule.

The three decay bounds remain explicit analytic hypotheses. They imply
absolute convergence of the actual finite-orbit derivatives and identify their
sum with the explicit variation-of-constants series. This module does not
exchange differentiation and an infinite orbit sum.
-/

set_option autoImplicit false

noncomputable section

namespace Kneser.PreparedOrbitCoefficient

open Kneser.ExponentialUnfolding
open scoped BigOperators

/-- The joint differential with direct parameter coefficient `a` and spatial
coefficient `b`. This is an actual continuous complex-linear map. -/
def residualDifferential (a b : ℂ) : (ℂ × ℂ) →L[ℂ] ℂ :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight a +
    (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight b

/-- The prepared residual evaluated at a genuine finite orbit. -/
def orbitResidual (F : ℂ × ℂ → ℂ) (u : ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  F (s, orbit u s k)

/-- A joint derivative and the genuine orbit tangent imply the chain-rule
coefficient for every finite orbit residual. -/
theorem hasDerivAt_orbitResidual (F : ℂ × ℂ → ℂ) (u : ℂ) (a b : ℕ → ℂ)
    (k : ℕ)
    (hF : HasFDerivAt F (residualDifferential (a k) (b k)) (0, orbit u 0 k)) :
    HasDerivAt (orbitResidual F u k) (a k + b k * orbitTangent u k) 0 := by
  have hgraph := (hasDerivAt_id (0 : ℂ)).prodMk
    (hasDerivAt_orbit_parameter_zero u k)
  have h := hF.comp_hasDerivAt 0 hgraph
  apply h.congr_deriv
  simp [residualDifferential, mul_comm]

/-- The derivative operator agrees with the explicit chain-rule coefficient. -/
theorem deriv_orbitResidual (F : ℂ × ℂ → ℂ) (u : ℂ) (a b : ℕ → ℂ) (k : ℕ)
    (hF : HasFDerivAt F (residualDifferential (a k) (b k)) (0, orbit u 0 k)) :
    deriv (orbitResidual F u k) 0 = a k + b k * orbitTangent u k :=
  (hasDerivAt_orbitResidual F u a b k hF).deriv

/-- Variation of constants removes the tangent recurrence from the actual
residual derivative and gives a finite, explicit orbit expression. -/
theorem deriv_orbitResidual_eq_finite_sum (F : ℂ × ℂ → ℂ) (u : ℂ)
    (a b : ℕ → ℂ) (k : ℕ)
    (hF : HasFDerivAt F (residualDifferential (a k) (b k)) (0, orbit u 0 k)) :
    deriv (orbitResidual F u k) 0 = a k - b k * orbitJacobian u k *
      (Finset.range k).sum (fun i => (1 + orbit u 0 i) / orbitJacobian u i) := by
  rw [deriv_orbitResidual F u a b k hF, orbitTangent_eq_finite_sum]
  ring

/-- The prepared-residual bounds prove absolute summability of the genuine
finite-orbit derivatives. -/
theorem summable_norm_deriv_orbitResidual (F : ℂ × ℂ → ℂ) (u : ℂ)
    (a b : ℕ → ℂ) (C₁ C₂ C₃ : ℝ) (hC₂ : 0 ≤ C₂) {q : ℕ} (hq : 2 ≤ q)
    (hF : ∀ k, HasFDerivAt F (residualDifferential (a k) (b k)) (0, orbit u 0 k))
    (ha : ∀ k, ‖a k‖ ≤ C₁ / ((k : ℝ) + 1) ^ q)
    (hb : ∀ k, ‖b k‖ ≤ C₂ / ((k : ℝ) + 1) ^ (q + 1))
    (hd : ∀ k, ‖orbitTangent u k‖ ≤ C₃ * ((k : ℝ) + 1)) :
    Summable (fun k => ‖deriv (orbitResidual F u k) 0‖) := by
  have h := Kneser.summable_norm_first_order_terms a b (orbitTangent u)
    C₁ C₂ C₃ hC₂ hq ha hb hd
  exact h.congr (fun k => by rw [deriv_orbitResidual F u a b k (hF k)])

/-- Absolute convergence gives convergence of the actual derivative series. -/
theorem summable_deriv_orbitResidual (F : ℂ × ℂ → ℂ) (u : ℂ)
    (a b : ℕ → ℂ) (C₁ C₂ C₃ : ℝ) (hC₂ : 0 ≤ C₂) {q : ℕ} (hq : 2 ≤ q)
    (hF : ∀ k, HasFDerivAt F (residualDifferential (a k) (b k)) (0, orbit u 0 k))
    (ha : ∀ k, ‖a k‖ ≤ C₁ / ((k : ℝ) + 1) ^ q)
    (hb : ∀ k, ‖b k‖ ≤ C₂ / ((k : ℝ) + 1) ^ (q + 1))
    (hd : ∀ k, ‖orbitTangent u k‖ ≤ C₃ * ((k : ℝ) + 1)) :
    Summable (fun k => deriv (orbitResidual F u k) 0) :=
  (summable_norm_deriv_orbitResidual F u a b C₁ C₂ C₃ hC₂ hq hF ha hb hd).of_norm

/-- Pointwise derivative identification gives the corresponding exact `tsum`
identity. Convergence is established separately by the preceding bounds. -/
theorem tsum_deriv_orbitResidual_eq (F : ℂ × ℂ → ℂ) (u : ℂ) (a b : ℕ → ℂ)
    (hF : ∀ k, HasFDerivAt F (residualDifferential (a k) (b k)) (0, orbit u 0 k)) :
    (∑' k : ℕ, deriv (orbitResidual F u k) 0) =
      ∑' k : ℕ, (a k + b k * orbitTangent u k) := by
  apply tsum_congr
  intro k
  exact deriv_orbitResidual F u a b k (hF k)

/-- The series of actual residual derivatives equals an explicit series using
only parabolic orbit points, Jacobian products, and finite sums. -/
theorem tsum_deriv_orbitResidual_eq_finite_orbit_series (F : ℂ × ℂ → ℂ)
    (u : ℂ) (a b : ℕ → ℂ)
    (hF : ∀ k, HasFDerivAt F (residualDifferential (a k) (b k)) (0, orbit u 0 k)) :
    (∑' k : ℕ, deriv (orbitResidual F u k) 0) =
      ∑' k : ℕ, (a k - b k * orbitJacobian u k *
        (Finset.range k).sum (fun i => (1 + orbit u 0 i) / orbitJacobian u i)) := by
  apply tsum_congr
  intro k
  exact deriv_orbitResidual_eq_finite_sum F u a b k (hF k)

/-- The norm bounds certify that the explicit orbit expression is the sum of
the absolutely convergent series of genuine residual derivatives. -/
theorem hasSum_deriv_orbitResidual_explicit (F : ℂ × ℂ → ℂ) (u : ℂ)
    (a b : ℕ → ℂ) (C₁ C₂ C₃ : ℝ) (hC₂ : 0 ≤ C₂) {q : ℕ} (hq : 2 ≤ q)
    (hF : ∀ k, HasFDerivAt F (residualDifferential (a k) (b k)) (0, orbit u 0 k))
    (ha : ∀ k, ‖a k‖ ≤ C₁ / ((k : ℝ) + 1) ^ q)
    (hb : ∀ k, ‖b k‖ ≤ C₂ / ((k : ℝ) + 1) ^ (q + 1))
    (hd : ∀ k, ‖orbitTangent u k‖ ≤ C₃ * ((k : ℝ) + 1)) :
    HasSum (fun k => deriv (orbitResidual F u k) 0)
      (∑' k : ℕ, (a k - b k * orbitJacobian u k *
        (Finset.range k).sum (fun i => (1 + orbit u 0 i) / orbitJacobian u i))) := by
  rw [← tsum_deriv_orbitResidual_eq_finite_orbit_series F u a b hF]
  exact (summable_deriv_orbitResidual F u a b C₁ C₂ C₃ hC₂ hq hF ha hb hd).hasSum

end Kneser.PreparedOrbitCoefficient

end
