import Kneser.ActualGrowingLensSeries
import Kneser.ActualInverseLensDynamics

/-! Same-witness genuine bilateral growing lenses and absolutely convergent
true orbit series. Both dynamics are constructed from one actual preparation. -/

noncomputable section
set_option maxHeartbeats 1000000
namespace Kneser.ActualBilateralGrowingLens

open Kneser.ActualLensGeometry Kneser.ActualLensBounds Kneser.ActualLensModel
open Kneser.ActualLensFiniteError Kneser.ActualLensBootstrap Kneser.ActualGrowingLens
open Kneser.ActualLensDynamics Kneser.ActualInverseLensBootstrap
open Kneser.ActualInverseLensDynamics Kneser.ActualReflectedLensModel
open Kneser.GrowingBandGeometry Kneser.GrowingBandKernel
open Kneser.ExponentialUnfolding Kneser.EvenPreparedOrbitDiscs
open Kneser.RealExponentialPetal Kneser.ReflectedOrbitChainCoefficient
open Kneser.PositiveKoenigsOrbit

/-- The actual multiplier-height strip is controlled under BOTH genuine
forward and principal inverse dynamics. The true preparation series in both
directions converges absolutely with a uniform norm bound. -/
theorem exists_actual_bilateral_growing_lens
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ Y s₀ : ℝ, 2 ≤ Y ∧ 0 < s₀ ∧ s₀ ≤ 1 / 2 ∧
      ∀ s : ℝ, 0 < s → s < s₀ →
        ∃ a b θ : ℝ, a < 0 ∧ 0 < b ∧ 0 < θ ∧
          unfolding s a = (a : ℂ) ∧ unfolding s b = (b : ℂ) ∧
          θ = -Real.log (multiplier s a) ∧ θ * Y ≤ Real.pi / 2 ∧
          ∀ Z : ℂ, Z ∈ strip θ Y →
            Summable (fun k => ‖descendedTerm A B Γ 2 (bandChart a b θ Z) s k‖) ∧
            Summable (fun k => ‖descendedTerm A B Γ 2
              (inverseOrbit s (bandChart a b θ Z) (k + 1)) s 0‖) ∧
            (∑' k, ‖descendedTerm A B Γ 2 (bandChart a b θ Z) s k‖) ≤ 1 ∧
            (∑' k, ‖descendedTerm A B Γ 2
              (inverseOrbit s (bandChart a b θ Z) (k + 1)) s 0‖) ≤ 1 ∧
            ∀ k : ℕ,
              orbit (bandChart a b θ Z) s k ≠ (a : ℂ) ∧
              orbit (bandChart a b θ Z) s k ≠ (b : ℂ) ∧
              inverseOrbit s (bandChart a b θ Z) k ≠ (a : ℂ) ∧
              inverseOrbit s (bandChart a b θ Z) k ≠ (b : ℂ) ∧
              bandTime a b θ (orbit (bandChart a b θ Z) s k) ∈ strip θ (Y / 2) ∧
              bandTime a b θ (inverseOrbit s (bandChart a b θ Z) k) ∈ strip θ (Y / 2) ∧
              (bandTime a b θ (orbit (bandChart a b θ Z) s k)).re + 3 / 4 ≤
                (bandTime a b θ (orbit (bandChart a b θ Z) s (k + 1))).re ∧
              (bandTime a b θ (inverseOrbit s (bandChart a b θ Z) (k + 1))).re + 3 / 4 ≤
                (bandTime a b θ (inverseOrbit s (bandChart a b θ Z) k)).re := by
  obtain ⟨Q⟩ := exists_quotientControl
  obtain ⟨η₁, s₁, M, P, hη₁, hη₁q, hs₁, hs₁h, hM, hP, hlocal⟩ :=
    exists_actual_lens_bounds U H e₁ e₂ A B K F Γ hdata
  obtain ⟨η₂, s₂, hη₂, _hη₂q, hs₂, _hs₂η, _hs₂h, hinverse⟩ :=
    exists_actual_inverse_lensModel_one_step U H e₁ e₂ A B K F Γ hdata
  let η := min η₁ (min η₂ (min (Q.radius / 4) (1 / (M + 1))))
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min hη₁ (lt_min hη₂ (lt_min (div_pos Q.radius_pos (by norm_num)) (by positivity)))
  have hηη₁ : η ≤ η₁ := min_le_left _ _
  have hηη₂ : η ≤ η₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hηr : η ≤ Q.radius / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηM : η ≤ 1 / (M + 1) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hηq : η ≤ 1 / 4 := hηη₁.trans hη₁q
  have hMη : M * η ^ 4 ≤ 1 := by
    have hh : η ^ 4 ≤ η := by
      have hp : η ^ 3 ≤ 1 := pow_le_one₀ hη.le (by linarith)
      nlinarith [mul_le_mul_of_nonneg_right hp hη.le]
    calc
      M * η ^ 4 ≤ M * η := mul_le_mul_of_nonneg_left hh hM.le
      _ ≤ M * (1 / (M + 1)) := mul_le_mul_of_nonneg_left hηM hM.le
      _ = M / (M + 1) := by ring
      _ ≤ 1 := (div_le_one (by linarith : 0 < M + 1)).mpr (by linarith)
  obtain ⟨Y, τ, hY, hτ, hYlarge, hmargin', hθbounds⟩ :=
    exists_bootstrap_constants η M (P + 1) hη hM.le
  have hmarginF : 2 * (Real.pi + 2 * P) + 1 < Y / 2 := by linarith
  have hmarginG : 2 * (Real.pi + 2 * P) + 2 < Y / 2 := by linarith
  let δ := min (η / 8) (τ / 4)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨s₃, hs₃, _hs₃h, hroots⟩ := Kneser.RealExponentialRoots.exists_ordered_small_real_roots δ hδ
  let s₀ := min s₁ (min s₂ (min s₃ (η / 8)))
  refine ⟨Y, s₀, hY, by dsimp [s₀]; positivity, (min_le_left _ _).trans hs₁h, ?_⟩
  intro s hs hss
  have hs₁' : s < s₁ := hss.trans_le (min_le_left _ _)
  have hs₂' : s < s₂ := hss.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hs₃' : s < s₃ := hss.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsη : s ≤ η / 8 := (hss.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))).le
  have hs1 : s < 1 / 2 := hs₁'.trans_le hs₁h
  obtain ⟨a, b, hal, ha0, hb0, hbu, hfa, hfb⟩ := hroots s hs hs₃'
  have ha : |a| < δ := by rw [abs_of_neg ha0]; linarith
  have hb : |b| < δ := by rw [abs_of_pos hb0]; exact hbu
  have hδη : δ ≤ η / 8 := min_le_left _ _
  have hδτ : δ ≤ τ / 4 := min_le_right _ _
  have haa : -1 < a := by have hh := (abs_lt.mp ha).1; linarith
  have hab : a < b := by linarith
  have hκr : (1 - s) * (b - a) < Q.radius := by
    have hm : (1 - s) * (b - a) ≤ b - a := by nlinarith
    linarith [Q.radius_pos]
  let θ := timeScale Q ((1 - s) * (b - a))
  have hκ : 0 < (1 - s) * (b - a) := mul_pos (by linarith) (by linarith)
  obtain ⟨hθ, hratio⟩ := timeScale_pos_and_gap_bound Q s a b hs hs1 hab hκr
  have hθτ : θ < τ := by
    have hh := (timeScale_bounds Q _ hκ hκr).2
    have hm : (1 - s) * (b - a) ≤ b - a := by nlinarith
    dsimp [θ]
    nlinarith
  obtain ⟨hθ1, hθYhalf, hE⟩ := hθbounds θ hθ hθτ
  have hθY : θ * Y ≤ Real.pi := hθYhalf.trans (by linarith [Real.pi_pos])
  have hθeq : θ = -Real.log (multiplier s a) :=
    timeScale_eq_neg_log_multiplier Q s a b (by linarith) haa hab hfa hfb
  have haη₁ : |a| < η₁ := ha.trans_le (hδη.trans (by linarith))
  have hbη₁ : |b| < η₁ := hb.trans_le (hδη.trans (by linarith))
  have haη₂ : |a| < η₂ := ha.trans_le (hδη.trans (by linarith))
  have hbη₂ : |b| < η₂ := hb.trans_le (hδη.trans (by linarith))
  have hl := hlocal s a b hs hs₁' haη₁ hbη₁ ha0 hb0 hfa hfb
  have hInv := hinverse s a b hs hs₂' haη₂ hbη₂ ha0 hb0 hfa hfb
  refine ⟨a, b, θ, ha0, hb0, hθ, hfa, hfb, hθeq, hθYhalf, ?_⟩
  intro Z hZ
  let u := bandChart a b θ Z
  have hnroots := bandChart_ne_roots a b θ Y Z hab hθ (by linarith) hθY hZ
  have ht := bandTime_bandChart a b θ Y Z hab hθ (by linarith) hθY hZ
  have hstateF := true_lens_invariant Q A B Γ (e₁ s) (e₂ s)
    s a b η Y M P u hη hηq hηr hs hs1 hsη
    (ha.le.trans hδη) (hb.le.trans hδη) ha0 hb0 hfa hfb hM.le hP.le hY hYlarge hmarginF
    hθ1 hθY hE
    (fun v hv => hl.2.2.2.1 v (hv.trans_le hηη₁))
    (fun v hv => hl.2.2.2.2.1 v (hv.trans_le hηη₁))
    (fun v hv => hl.2.2.2.2.2 v (hv.trans_le hηη₁))
    hnroots.1 hnroots.2 (by dsimp [u]; rwa [ht])
  have hstateG := true_inverse_lens_invariant Q A B Γ (e₁ s) (e₂ s)
    s a b η Y M P u hη hηq (by linarith) hs hsη
    (ha.le.trans hδη) (hb.le.trans hδη) ha0 hb0 hfa hfb hM.le hMη hY hYlarge hmarginG
    (by simpa only [hθeq] using hθ1) (by simpa only [hθeq] using hθY)
    (by simpa only [hθeq] using hE)
    (fun v hv => hl.2.2.2.1 v (hv.trans_le hηη₁))
    (fun v hv => hl.2.2.2.2.1 v (hv.trans_le hηη₁))
    (fun v hv hi => (hInv v (hv.trans (by linarith)) hi).2.2.2)
    hnroots.1 hnroots.2 (by dsimp [u]; rw [← hθeq, ht]; exact hZ)
  rw [← hθeq] at hstateG
  have hstepF : ∀ k, (bandTime a b θ (orbit u s k)).re + 3 / 4 ≤
      (bandTime a b θ (orbit u s (k + 1))).re := by
    intro k
    have hki := quotient_arguments_of_local_norm Q s a b η (orbit u s k)
      hs.le (by linarith) hη hηr (ha.le.trans hδη) (hb.le.trans hδη) (hstateF k).2.2.1
    have hd := actual_bandTime_re_drift Q s a b (orbit u s k) hs hs1 haa hab hb0 hfa hfb
      (hstateF k).1 (hstateF k).2.1 hκr hki.1 hki.2
    simpa only [orbit_succ] using hd.2.2
  have hstepG : ∀ k, (bandTime a b θ (inverseOrbit s u (k + 1))).re + 3 / 4 ≤
      (bandTime a b θ (inverseOrbit s u k)).re := by
    intro k
    have hki := quotient_arguments_of_local_norm Q s a b η (inverseOrbit s u (k + 1))
      hs.le (by linarith) hη hηr (ha.le.trans hδη) (hb.le.trans hδη) (hstateG (k + 1)).2.2.1
    have hd := actual_bandTime_re_drift Q s a b (inverseOrbit s u (k + 1)) hs hs1 haa hab hb0 hfa hfb
      (hstateG (k + 1)).1 (hstateG (k + 1)).2.1 hκr hki.1 hki.2
    have he : unfolding s (inverseOrbit s u (k + 1)) = inverseOrbit s u k := by
      rw [inverseOrbit_succ]
      exact unfolding_inverseStep s _ (by linarith) ((hstateG k).2.2.1.trans_lt (by linarith))
    simpa only [he] using hd.2.2
  have hhalf : θ * (Y / 2) ≤ Real.pi := by linarith [mul_pos hθ (show 0 < Y by linarith)]
  have hsumF := true_lens_absolute_residual A B Γ u s a b θ (Y / 2) M hab hθ hθ1 (by linarith)
    hhalf hratio hM.le
    (fun k => ⟨(hstateF k).1, (hstateF k).2.1⟩) (fun k => (hstateF k).2.2.2)
    (fun k => hl.2.2.2.1 _ ((hstateF k).2.2.1.trans_lt (by linarith [hηη₁]))) hstepF
  have hsumG := true_inverse_lens_absolute_residual A B Γ u s a b θ (Y / 2) M hab hθ hθ1 (by linarith)
    hhalf hratio hM.le
    (fun k => ⟨(hstateG k).1, (hstateG k).2.1⟩) (fun k => (hstateG k).2.2.2)
    (fun k => hl.2.2.2.1 _ ((hstateG k).2.2.1.trans_lt (by linarith [hηη₁]))) hstepG
  refine ⟨hsumF.1, hsumG.1, hsumF.2.trans hE, hsumG.2.trans hE, ?_⟩
  intro k
  exact ⟨(hstateF k).1, (hstateF k).2.1, (hstateG k).1, (hstateG k).2.1,
    (hstateF k).2.2.2, (hstateG k).2.2.2, hstepF k, hstepG k⟩

end Kneser.ActualBilateralGrowingLens
end
