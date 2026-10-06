import Kneser.HigherGateSeeds
import Kneser.ReflectedPreparedDegreeCompatibility

/-! Actual preparation-degree compatibility at a parameter-dependent
compact initial family. The common parameter interval and bounded-petal
conditions are derived from joint continuity, rather than postulated. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Kneser.HigherMovingPreparationCompatibility

open Filter Set Metric Kneser.ParabolicExponentialOrbit Kneser.ParabolicFatouHolomorphic
open Kneser.HigherMovingSeed
open scoped Topology

theorem exists_moving_bounded_petal (W : ℂ × ℂ → ℂ) (S : Set ℂ) (R : ℝ) (hR : 0 < R)
    (hS : IsCompact S) (hW : ∀ u ∈ S, AnalyticAt ℂ W (0, u))
    (hdeep : ∀ u ∈ S, R + 2 ≤ (inverseCoordinate (W (0, u))).re) :
    ∃ Z : ℝ, 0 ≤ Z ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
      R + 1 ≤ (inverseCoordinate (W (s, u))).re ∧ ‖inverseCoordinate (W (s, u))‖ ≤ Z := by
  obtain ⟨r, T, hr, hT, hTV, hWT⟩ := exists_compact_complex_image_neighborhood
    W S (petal (R + 1)) hS (petal_isOpen (by linarith)) hW
      (fun u hu => by change R + 1 < _; linarith [hdeep u hu])
  have hne : ∀ v ∈ T, v ≠ 0 := by
    intro v hv he
    have hh : R + 1 < (inverseCoordinate v).re := hTV hv
    simp only [he, inverseCoordinate, div_zero, Complex.zero_re] at hh
    linarith
  have hi : ContinuousOn inverseCoordinate T := by
    intro v hv
    exact (continuousAt_const.div continuousAt_id (hne v hv)).continuousWithinAt
  obtain ⟨Z₁, hZ₁⟩ := hT.exists_bound_of_continuousOn hi
  refine ⟨max Z₁ 0, le_max_right _ _, ?_⟩
  have hs : ∀ᶠ s : ℝ in 𝓝[>] 0, s < r :=
    (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hs] with s hsp hsr u hu
  have hsp' : 0 < s := hsp
  have hwu := (hWT (s : ℂ) (by
    simp only [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsp']
    exact hsr.le) u hu).2
  exact ⟨(hTV hwu).le, (hZ₁ _ hwu).trans (le_max_left _ _)⟩

theorem moving_normalized_compatibility (Q₁ Q₂ : ℂ → ℝ → ℂ)
    (R : ℝ) (hR : 0 < R)
    (hcompat : ∀ Z : ℝ, 0 ≤ Z → ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u v : ℂ,
      R + 1 ≤ (inverseCoordinate u).re → ‖inverseCoordinate u‖ ≤ Z →
      R + 1 ≤ (inverseCoordinate v).re → ‖inverseCoordinate v‖ ≤ Z →
      Q₁ u s - Q₁ v s = Q₂ u s - Q₂ v s)
    (W : ℂ × ℂ → ℂ) (S : Set ℂ) (hS : IsCompact S)
    (hW : ∀ u ∈ S, AnalyticAt ℂ W (0, u))
    (hdeep : ∀ u ∈ S, R + 2 ≤ (inverseCoordinate (W (0, u))).re) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S, ∀ v ∈ S,
      Q₁ (W (s, u)) s - Q₁ (W (s, v)) s =
        Q₂ (W (s, u)) s - Q₂ (W (s, v)) s := by
  obtain ⟨Z, hZ, hbound⟩ := exists_moving_bounded_petal W S R hR hS hW hdeep
  filter_upwards [hcompat Z hZ, hbound] with s hc hb u hu v hv
  exact hc _ _ (hb u hu).1 (hb u hu).2 (hb v hv).1 (hb v hv).2

end Kneser.HigherMovingPreparationCompatibility
end
