import Kneser.ActualGrowingLens
import Kneser.ActualLensDynamics

/-! The actual prepared orbit series is absolutely convergent on its entire
growing forward lens, with a uniform total norm bound. -/

noncomputable section
set_option maxHeartbeats 1000000
namespace Kneser.ActualGrowingLensSeries

open Filter Metric Kneser.ActualLensGeometry Kneser.ActualLensBounds Kneser.ActualLensModel
open Kneser.ActualLensFiniteError Kneser.ActualLensBootstrap Kneser.ActualGrowingLens
open Kneser.GrowingBandGeometry Kneser.GrowingBandKernel
open Kneser.ExponentialUnfolding Kneser.EvenPreparedOrbitDiscs
open Kneser.RealExponentialPetal Kneser.ReflectedOrbitChainCoefficient
open Kneser.PositiveKoenigsOrbit
open scoped Topology

/-- A genuine absolutely convergent preparation series on a growing lens.
The sum bound and the entire forward orbit control are conclusions. -/
theorem exists_actual_growing_lens_absolute_series
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ Y s₀ : ℝ, 2 ≤ Y ∧ 0 < s₀ ∧
      ∀ s : ℝ, 0 < s → s < s₀ →
        ∃ a b θ : ℝ, a < 0 ∧ 0 < b ∧ 0 < θ ∧
          unfolding s a = (a : ℂ) ∧ unfolding s b = (b : ℂ) ∧
          θ = -Real.log (multiplier s a) ∧ θ * Y ≤ Real.pi ∧
          ∀ Z : ℂ, Z ∈ strip θ Y →
            Summable (fun k => ‖descendedTerm A B Γ 2 (bandChart a b θ Z) s k‖) ∧
            (∑' k, ‖descendedTerm A B Γ 2 (bandChart a b θ Z) s k‖) ≤ 1 ∧
            ∀ k : ℕ,
              orbit (bandChart a b θ Z) s k ≠ (a : ℂ) ∧
              orbit (bandChart a b θ Z) s k ≠ (b : ℂ) ∧
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
  intro Z hZ
  have hnroots := bandChart_ne_roots a b θ Y Z (by linarith) hθ (by linarith) hθY hZ
  have ht := bandTime_bandChart a b θ Y Z (by linarith) hθ (by linarith) hθY hZ
  have hstate := Kneser.ActualLensDynamics.true_lens_invariant Q A B Γ (e₁ s) (e₂ s)
    s a b η Y M P (bandChart a b θ Z) hη hηq hηr hs hs1 hsη
    (ha.le.trans hδη) (hb.le.trans hδη) ha0 hb0 hfa hfb hM.le hP.le hY hYlarge hmargin
    hθ1 hθY hE
    (fun v hv => hl.2.2.2.1 v (hv.trans_le hηη₁))
    (fun v hv => hl.2.2.2.2.1 v (hv.trans_le hηη₁))
    (fun v hv => hl.2.2.2.2.2 v (hv.trans_le hηη₁))
    hnroots.1 hnroots.2 (by rwa [ht])
  have hstep : ∀ k, (bandTime a b θ (orbit (bandChart a b θ Z) s k)).re + 3 / 4 ≤
      (bandTime a b θ (orbit (bandChart a b θ Z) s (k + 1))).re := by
    intro k
    have hki := Kneser.ActualLensDynamics.quotient_arguments_of_local_norm Q s a b η
      (orbit (bandChart a b θ Z) s k) hs.le (by linarith) hη hηr
      (ha.le.trans hδη) (hb.le.trans hδη) (hstate k).2.2.1
    have hd := actual_bandTime_re_drift Q s a b (orbit (bandChart a b θ Z) s k)
      hs hs1 (by have hh := (abs_lt.mp ha).1; linarith) (by linarith) hb0 hfa hfb
      (hstate k).1 (hstate k).2.1 hκr hki.1 hki.2
    simpa only [orbit_succ] using hd.2.2
  have hratio := (timeScale_pos_and_gap_bound Q s a b hs hs1 (by linarith) hκr).2
  have hhalf : θ * (Y / 2) ≤ Real.pi := by linarith [mul_pos hθ (show 0 < Y by linarith)]
  have habsolute := Kneser.ActualLensDynamics.true_lens_absolute_residual A B Γ
    (bandChart a b θ Z) s a b θ (Y / 2) M (by linarith) hθ hθ1 (by linarith)
    hhalf hratio hM.le
    (fun k => ⟨(hstate k).1, (hstate k).2.1⟩)
    (fun k => (hstate k).2.2.2)
    (fun k => hl.2.2.2.1 _ ((hstate k).2.2.1.trans_lt (by linarith [hηη₁]))) hstep
  refine ⟨habsolute.1, habsolute.2.trans hE, ?_⟩
  intro k
  exact ⟨(hstate k).1, (hstate k).2.1, (hstate k).2.2.2⟩

end Kneser.ActualGrowingLensSeries
end
