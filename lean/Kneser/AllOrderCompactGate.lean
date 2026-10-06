import Kneser.AllOrderGateComposition

/-! The genuine fixed moving inverse and normalized transition have
globally coherent finite holomorphic coefficients and compact uniform
integer remainders on the common image disc.  Local inverses, local
composition remainders and coefficient gluing are all proved internally.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.AllOrderCompactGate

open Filter Set Metric
open scoped Topology
open Kneser.FiniteExpansionHolomorphy Kneser.FiniteLocalExpansionGluing
open Kneser.AllOrderMovingInverse Kneser.AllOrderGateComposition

def FinitePacket (T : ℝ → ℂ → ℂ) (b : ℕ → ℂ → ℂ) (m : ℕ) (U : Set ℂ) : Prop :=
  (∀ j ≤ m, AnalyticOnNhd ℂ (b j) U) ∧
  (∀ z ∈ U, b 0 z = T 0 z) ∧
  (∀ K : Set ℂ, IsCompact K → K ⊆ U →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ K,
      ‖T s z - complexPolynomial b m (s : ℂ) z‖ ≤ C * s ^ (m + 1))

theorem global_finite_inverse_expansion (F V : ℝ → ℂ → ℂ)
    (c : ℕ → ℂ → ℂ) (m : ℕ) (r C : ℝ) (hr : 0 < r) (hC : 0 ≤ C)
    (hV0 : ∀ z ∈ ball (0 : ℂ) (r / 4), V 0 z ∈ closedBall (0 : ℂ) r ∧ F 0 (V 0 z) = z)
    (hV : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ ball (0 : ℂ) (r / 4),
      V s z ∈ closedBall (0 : ℂ) r ∧ F s (V s z) = z)
    (hF0 : ApproximatesLinearOn (F 0) (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * r)) (1 / 2))
    (hF : ∀ᶠ s : ℝ in 𝓝[>] 0, ApproximatesLinearOn (F s) (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * r)) (1 / 2))
    (ha0 : AnalyticOnNhd ℂ (F 0) (ball (0 : ℂ) (2 * r)))
    (hc : ∀ j ≤ m, AnalyticOnNhd ℂ (c j) (ball (0 : ℂ) (4 * r)))
    (hzero : ∀ u ∈ ball (0 : ℂ) (4 * r), c 0 u = F 0 u)
    (hExpansion : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ closedBall (0 : ℂ) (4 * r),
      ‖F s u - complexPolynomial c m (s : ℂ) u‖ ≤ C * s ^ (m + 1)) :
    ∃ d : ℕ → ℂ → ℂ, FinitePacket V d m (ball (0 : ℂ) (r / 4)) := by
  apply exists_global_finite_expansion V m (ball (0 : ℂ) (r / 4))
  intro z₀ hz₀
  exact local_finite_inverse_expansion F V c m r C hr hC hV0 hV hF0 hF ha0 hc hzero hExpansion z₀ hz₀

/-- The transition's finite expansion is a conclusion.  The coordinate
coefficients and integer bounds are the actual prepared orbit data;
the fixed V is the already constructed genuine common inverse branch. -/
theorem global_finite_transition_expansion (F V A : ℝ → ℂ → ℂ)
    (c a : ℕ → ℂ → ℂ) (m : ℕ) (r CF CA : ℝ)
    (hr : 0 < r) (hCF : 0 ≤ CF) (hCA : 0 ≤ CA)
    (hV0 : ∀ z ∈ ball (0 : ℂ) (r / 4), V 0 z ∈ closedBall (0 : ℂ) r ∧ F 0 (V 0 z) = z)
    (hV : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ ball (0 : ℂ) (r / 4),
      V s z ∈ closedBall (0 : ℂ) r ∧ F s (V s z) = z)
    (hF0 : ApproximatesLinearOn (F 0) (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * r)) (1 / 2))
    (hF : ∀ᶠ s : ℝ in 𝓝[>] 0, ApproximatesLinearOn (F s) (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * r)) (1 / 2))
    (ha0 : AnalyticOnNhd ℂ (F 0) (ball (0 : ℂ) (2 * r)))
    (hc : ∀ j ≤ m, AnalyticOnNhd ℂ (c j) (ball (0 : ℂ) (4 * r)))
    (ha : ∀ j ≤ m, AnalyticOnNhd ℂ (a j) (closedBall (0 : ℂ) (4 * r)))
    (hc0 : ∀ u ∈ ball (0 : ℂ) (4 * r), c 0 u = F 0 u)
    (ha0value : ∀ u ∈ ball (0 : ℂ) (4 * r), a 0 u = A 0 u)
    (hExpansionF : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ closedBall (0 : ℂ) (4 * r),
      ‖F s u - complexPolynomial c m (s : ℂ) u‖ ≤ CF * s ^ (m + 1))
    (hExpansionA : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ closedBall (0 : ℂ) (4 * r),
      ‖A s u - complexPolynomial a m (s : ℂ) u‖ ≤ CA * s ^ (m + 1)) :
    ∃ b : ℕ → ℂ → ℂ, FinitePacket (fun s z => A s (V s z)) b m (ball (0 : ℂ) (r / 4)) := by
  apply exists_global_finite_expansion (fun s z => A s (V s z)) m (ball (0 : ℂ) (r / 4))
  intro z₀ hz₀
  obtain ⟨η, hη, hηimage, d, CV, hCV, hd, hd0, hInverse⟩ :=
    local_finite_inverse_expansion F V c m r CF hr hCF hV0 hV hF0 hF ha0 hc hc0 hExpansionF z₀ hz₀
  obtain ⟨ρ, hρ, hρη, b, C, hC, hb, hb0, hExpansion⟩ :=
    local_finite_composition_expansion A V a d m r η CA CV z₀ hr hη hCA hCV ha hd ha0value hd0
      (fun z hz => (hV0 z (hηimage hz)).1)
      (hV.mono fun s hs z hz => (hs z (hηimage hz)).1) hExpansionA hInverse
  exact ⟨ρ, hρ, (closedBall_subset_closedBall hρη).trans hηimage, b, C, hC, hb, hb0, hExpansion⟩

end Kneser.AllOrderCompactGate

end
