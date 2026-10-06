import Kneser.HigherMovingPreparationCompatibility

/-! A common preparation constant cancels between two different genuine
moving initial families, including a gate family and a real anchor orbit. -/

set_option autoImplicit false
noncomputable section
namespace Kneser.CrossMovingPreparationCompatibility

open Filter Set Metric Kneser.ParabolicExponentialOrbit
open Kneser.HigherMovingPreparationCompatibility
open scoped Topology

theorem moving_cross_compatibility (Q₁ Q₂ : ℂ → ℝ → ℂ) (R : ℝ) (hR : 0 < R)
    (hcompat : ∀ Z : ℝ, 0 ≤ Z → ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u v : ℂ,
      R + 1 ≤ (inverseCoordinate u).re → ‖inverseCoordinate u‖ ≤ Z →
      R + 1 ≤ (inverseCoordinate v).re → ‖inverseCoordinate v‖ ≤ Z →
      Q₁ u s - Q₁ v s = Q₂ u s - Q₂ v s)
    (W₁ W₂ : ℂ × ℂ → ℂ) (S : Set ℂ) (hS : IsCompact S)
    (hW₁ : ∀ u ∈ S, AnalyticAt ℂ W₁ (0, u))
    (hW₂ : ∀ u ∈ S, AnalyticAt ℂ W₂ (0, u))
    (hdeep₁ : ∀ u ∈ S, R + 2 ≤ (inverseCoordinate (W₁ (0, u))).re)
    (hdeep₂ : ∀ u ∈ S, R + 2 ≤ (inverseCoordinate (W₂ (0, u))).re) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
      Q₁ (W₁ (s, u)) s - Q₁ (W₂ (s, u)) s =
        Q₂ (W₁ (s, u)) s - Q₂ (W₂ (s, u)) s := by
  obtain ⟨Z₁, hZ₁, hb₁⟩ := exists_moving_bounded_petal W₁ S R hR hS hW₁ hdeep₁
  obtain ⟨Z₂, hZ₂, hb₂⟩ := exists_moving_bounded_petal W₂ S R hR hS hW₂ hdeep₂
  filter_upwards [hcompat (max Z₁ Z₂) (hZ₁.trans (le_max_left _ _)), hb₁, hb₂] with s hc h₁ h₂ u hu
  exact hc _ _ (h₁ u hu).1 ((h₁ u hu).2.trans (le_max_left _ _))
    (h₂ u hu).1 ((h₂ u hu).2.trans (le_max_right _ _))

end Kneser.CrossMovingPreparationCompatibility
