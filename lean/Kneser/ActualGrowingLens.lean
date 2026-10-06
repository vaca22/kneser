import Kneser.ActualLensBootstrap
import Kneser.RealLensMidline

/-! Genuine growing forward lenses for every sufficiently small positive
parameter. The local hypotheses of the finite bootstrap are discharged by
the same actual preparation and the actual ordered real fixed points. -/

noncomputable section
set_option maxHeartbeats 1000000
namespace Kneser.ActualGrowingLens

open Filter Metric Kneser.ActualLensGeometry Kneser.ActualLensBounds Kneser.ActualLensModel
open Kneser.ActualLensFiniteError Kneser.ActualLensBootstrap
open Kneser.GrowingBandGeometry Kneser.GrowingBandKernel
open Kneser.ExponentialUnfolding Kneser.EvenPreparedOrbitDiscs
open Kneser.RealExponentialPetal Kneser.ReflectedOrbitChainCoefficient
open Kneser.PositiveKoenigsOrbit
open scoped Topology

theorem exists_bootstrap_constants (η M P : ℝ) (hη : 0 < η) (hM : 0 ≤ M) :
    ∃ Y τ : ℝ, 2 ≤ Y ∧ 0 < τ ∧
      5 * Real.pi / (Y / 2) ≤ η / 8 ∧
      2 * (Real.pi + 2 * P) + 1 < Y / 2 ∧
      ∀ θ : ℝ, 0 < θ → θ < τ → θ ≤ 1 ∧ θ * Y ≤ Real.pi / 2 ∧
        errorBound M (Y / 2) θ ≤ 1 := by
  let D := 2 * M * smallConstant ^ 2 * (2 + Real.pi / (3 / 4))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨Y, hY⟩ := exists_gt (max (max 2 (80 * Real.pi / η))
    (max (4 * (Real.pi + 2 * P) + 2) (2 * (D + 1))))
  have hY2 : 2 < Y := (le_trans (le_max_left _ _) (le_max_left _ _)).trans_lt hY
  have hYn : 80 * Real.pi / η < Y := (le_trans (le_max_right _ _) (le_max_left _ _)).trans_lt hY
  have hYm : 4 * (Real.pi + 2 * P) + 2 < Y := (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hY
  have hYD : 2 * (D + 1) < Y := (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hY
  have hcube : Y / 2 ≤ (Y / 2) ^ 3 := by
    have hy : 0 ≤ Y / 2 - 1 := by linarith
    have hh : 0 ≤ (Y / 2 - 1) * (Y / 2) * (Y / 2 + 1) := by positivity
    nlinarith
  have hE0 : errorBound M (Y / 2) 0 < 1 := by
    simp only [errorBound, zero_pow (by norm_num : 3 ≠ 0), mul_zero, add_zero]
    change D / (Y / 2) ^ 3 < 1
    apply (div_lt_one (by positivity : 0 < (Y / 2) ^ 3)).mpr
    linarith
  have hEc : ContinuousAt (fun θ : ℝ => errorBound M (Y / 2) θ) 0 := by
    unfold errorBound
    fun_prop
  obtain ⟨δ, hδ, hEb⟩ := Metric.eventually_nhds_iff.mp
    (hEc.eventually (gt_mem_nhds hE0))
  let τ := min δ (min 1 (Real.pi / (2 * Y)))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  refine ⟨Y, τ, hY2.le, hτ, ?_, by linarith, ?_⟩
  · apply (div_le_iff₀ (by linarith : 0 < Y / 2)).mpr
    have hh := (div_lt_iff₀ hη).mp hYn
    nlinarith
  · intro θ hθ hθτ
    have hθδ : θ < δ := hθτ.trans_le (min_le_left _ _)
    have hθone : θ < 1 := hθτ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hθπ : θ < Real.pi / (2 * Y) := hθτ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    refine ⟨hθone.le, ?_, ?_⟩
    · have hh := (lt_div_iff₀ (by linarith : 0 < 2 * Y)).mp hθπ
      linarith
    · apply (hEb (y := θ) ?_).le
      simpa [Real.dist_eq, abs_of_pos hθ] using hθδ

/-- Every actual preparation has a fixed lower margin Y and actual growing
lenses of height 2π/θ, invariant under all true forward iterates away from
the real midline. No roots, phase drift, or infinite orbit bounds are inputs. -/
theorem exists_actual_growing_nonreal_lens
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ Y s₀ : ℝ, 2 ≤ Y ∧ 0 < s₀ ∧
      ∀ s : ℝ, 0 < s → s < s₀ →
        ∃ a b θ : ℝ, a < 0 ∧ 0 < b ∧ 0 < θ ∧
          unfolding s a = (a : ℂ) ∧ unfolding s b = (b : ℂ) ∧
          θ = -Real.log (multiplier s a) ∧ θ * Y ≤ Real.pi ∧
          ∀ Z : ℂ, Z ∈ strip θ Y → (bandChart a b θ Z).im ≠ 0 →
            ∀ k : ℕ,
              orbit (bandChart a b θ Z) s k ≠ (a : ℂ) ∧
              orbit (bandChart a b θ Z) s k ≠ (b : ℂ) ∧
              (orbit (bandChart a b θ Z) s k).im ≠ 0 ∧
              bandTime a b θ (orbit (bandChart a b θ Z) s k) ∈ strip θ (Y / 2) := by
  obtain ⟨Q⟩ := exists_quotientControl
  obtain ⟨η₁, s₁, M, P, hη₁, hη₁q, hs₁, hs₁h, hM, hP, hlocal⟩ :=
    exists_actual_lens_bounds U H e₁ e₂ A B K F Γ hdata
  let η := min η₁ (Q.radius / 4)
  have hη : 0 < η := lt_min hη₁ (div_pos Q.radius_pos (by norm_num))
  have hηη₁ : η ≤ η₁ := min_le_left _ _
  have hηq : η ≤ 1 / 4 := hηη₁.trans hη₁q
  have hηr : η ≤ Q.radius / 4 := min_le_right _ _
  obtain ⟨Y, τ, hY, hτ, hYlarge, hmargin, hθbounds⟩ := exists_bootstrap_constants η M P hη hM.le
  let δ := min (η / 8) (τ / 4)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨s₂, hs₂, hs₂h, hroots⟩ := Kneser.RealExponentialRoots.exists_ordered_small_real_roots δ hδ
  let s₀ := min s₁ (min s₂ (η / 8))
  refine ⟨Y, s₀, hY, by dsimp [s₀]; positivity, ?_⟩
  intro s hs hss
  have hs₁' : s < s₁ := hss.trans_le (min_le_left _ _)
  have hs₂' : s < s₂ := hss.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsη : s ≤ η / 8 := (hss.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hs1 : s < 1 / 2 := hs₁'.trans_le hs₁h
  obtain ⟨a, b, hal, ha0, hb0, hbu, hfa, hfb⟩ := hroots s hs hs₂'
  have ha : |a| < δ := by rw [abs_of_neg ha0]; linarith
  have hb : |b| < δ := by rw [abs_of_pos hb0]; exact hbu
  have hδη : δ ≤ η / 8 := min_le_left _ _
  have hδτ : δ ≤ τ / 4 := min_le_right _ _
  have hκr : (1 - s) * (b - a) < Q.radius := by
    have hm : (1 - s) * (b - a) ≤ b - a := by nlinarith
    linarith [Q.radius_pos]
  let θ := timeScale Q ((1 - s) * (b - a))
  have hκ : 0 < (1 - s) * (b - a) := mul_pos (by linarith) (by linarith)
  have hθ := (timeScale_pos_and_gap_bound Q s a b hs hs1 (by linarith) hκr).1
  have hθτ : θ < τ := by
    have hh := (timeScale_bounds Q _ hκ hκr).2
    have hm : (1 - s) * (b - a) ≤ b - a := by nlinarith
    dsimp [θ]
    nlinarith
  obtain ⟨hθ1, hθYhalf, hE⟩ := hθbounds θ hθ hθτ
  have hθY : θ * Y ≤ Real.pi := hθYhalf.trans (by linarith [Real.pi_pos])
  have hθeq : θ = -Real.log (multiplier s a) :=
    timeScale_eq_neg_log_multiplier Q s a b (by linarith)
      (by have hh := (abs_lt.mp ha).1; linarith) (by linarith) hfa hfb
  have haη₁ : |a| < η₁ := ha.trans_le (hδη.trans (by linarith))
  have hbη₁ : |b| < η₁ := hb.trans_le (hδη.trans (by linarith))
  have hl := hlocal s a b hs hs₁' haη₁ hbη₁ ha0 hb0 hfa hfb
  refine ⟨a, b, θ, ha0, hb0, hθ, hfa, hfb, hθeq, hθY, ?_⟩
  intro Z hZ hi k
  have hnroots := bandChart_ne_roots a b θ Y Z (by linarith) hθ (by linarith) hθY hZ
  have ht := bandTime_bandChart a b θ Y Z (by linarith) hθ (by linarith) hθY hZ
  have hh := nonreal_true_lens_invariant Q A B Γ (e₁ s) (e₂ s)
    s a b η Y M P (bandChart a b θ Z) hη hηq hηr hs hs1 hsη
    (ha.le.trans hδη) (hb.le.trans hδη) ha0 hb0 hfa hfb hM.le hP.le hY hYlarge hmargin
    hθ1 hθY hE
    (fun v hv => hl.2.2.2.1 v (hv.trans_le hηη₁))
    (fun v hv => hl.2.2.2.2.1 v (hv.trans_le hηη₁))
    (fun v hv => hl.2.2.2.2.2 v (hv.trans_le hηη₁))
    hnroots.1 hnroots.2 hi (by rwa [ht]) k
  exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.2⟩

/-- The complete genuine growing strip, including its real midline. -/
theorem exists_actual_growing_lens
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ Y s₀ : ℝ, 2 ≤ Y ∧ 0 < s₀ ∧
      ∀ s : ℝ, 0 < s → s < s₀ →
        ∃ a b θ : ℝ, a < 0 ∧ 0 < b ∧ 0 < θ ∧
          unfolding s a = (a : ℂ) ∧ unfolding s b = (b : ℂ) ∧
          θ = -Real.log (multiplier s a) ∧ θ * Y ≤ Real.pi ∧
          ∀ Z : ℂ, Z ∈ strip θ Y → ∀ k : ℕ,
            orbit (bandChart a b θ Z) s k ≠ (a : ℂ) ∧
            orbit (bandChart a b θ Z) s k ≠ (b : ℂ) ∧
            bandTime a b θ (orbit (bandChart a b θ Z) s k) ∈ strip θ (Y / 2) := by
  obtain ⟨Y, s₁, hY, hs₁, hlens⟩ :=
    exists_actual_growing_nonreal_lens U H e₁ e₂ A B K F Γ hdata
  refine ⟨Y, min s₁ (1 / 2), hY, lt_min hs₁ (by norm_num), ?_⟩
  intro s hs hss
  have hs₁' := hss.trans_le (min_le_left _ _)
  have hs1 : s < 1 := lt_of_lt_of_le hss ((min_le_right _ _).trans (by norm_num))
  obtain ⟨a, b, θ, ha, hb, hθ, hfa, hfb, hθeq, hθY, horbit⟩ := hlens s hs hs₁'
  refine ⟨a, b, θ, ha, hb, hθ, hfa, hfb, hθeq, hθY, ?_⟩
  intro Z hZ k
  by_cases hi : (bandChart a b θ Z).im = 0
  · have hnr := bandChart_ne_roots a b θ Y Z (by linarith) hθ (by linarith) hθY hZ
    have ht := bandTime_bandChart a b θ Y Z (by linarith) hθ (by linarith) hθY hZ
    exact Kneser.RealLensMidline.real_midline_invariant s a b θ Y (bandChart a b θ Z)
      hs1 (by linarith) hθ (by linarith) hfa hfb hnr.1 hnr.2 hi (by rwa [ht]) k
  · have hh := horbit Z hZ hi k
    exact ⟨hh.1, hh.2.1, hh.2.2.2⟩

end Kneser.ActualGrowingLens
end
