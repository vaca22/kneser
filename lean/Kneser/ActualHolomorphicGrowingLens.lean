import Kneser.ActualBilateralGrowingLens
import Kneser.GrowingLensCoordinateRegularity

/-! Actual same-preparation holomorphic coordinates on a growing multiplier
strip. All orbit and local analytic estimates are constructed from the
exponential family and its actual quadratic preparation. -/

noncomputable section
set_option maxHeartbeats 1000000
namespace Kneser.ActualHolomorphicGrowingLens

open Filter Set Metric
open Kneser.ActualLensGeometry Kneser.ActualLensBounds Kneser.ActualLensModel
open Kneser.ActualLensFiniteError Kneser.ActualLensBootstrap Kneser.ActualGrowingLens
open Kneser.ActualLensDynamics Kneser.ActualInverseLensBootstrap
open Kneser.ActualInverseLensDynamics Kneser.ActualReflectedLensModel
open Kneser.GrowingBandGeometry Kneser.GrowingBandKernel
open Kneser.ExponentialUnfolding Kneser.EvenPreparedOrbitDiscs
open Kneser.RealExponentialPetal Kneser.ReflectedOrbitChainCoefficient
open Kneser.PositiveKoenigsOrbit

open Kneser.GrowingLensSpatialHolomorphy Kneser.GrowingLensCoordinateRegularity
open scoped Topology

structure LensControl (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (s a b θ Y η M P : ℝ) : Prop where
  left_neg : a < 0
  right_pos : 0 < b
  theta_pos : 0 < θ
  left_fixed : unfolding s a = (a : ℂ)
  right_fixed : unfolding s b = (b : ℂ)
  theta_actual : θ = -Real.log (multiplier s a)
  width : θ * Y ≤ Real.pi / 2
  strong_width : θ * Y ≤ Real.pi / 4
  very_strong_width : θ * Y ≤ Real.pi / 8
  gap : (b - a) / θ ≤ 5
  radius_pos : 0 < η
  radius_small : η ≤ 1 / 4
  residual_constant : 0 ≤ M
  height_large : 2 ≤ Y
  first_model_bound : ‖e₁ s‖ ≤ P
  second_model_bound : ‖e₂ s‖ ≤ P
  residue_bound : ‖residueSum s a b‖ ≤ 1
  left_small : |a| ≤ η / 8
  right_small : |b| ≤ η / 8
  height_margin : 4 * (Real.pi + P * η + 2) < Y
  phase_margin : Real.pi + 2 * P + 1 < Y
  phase_margin_buffer : Real.pi + 2 * P + 3 < Y
  analytic_residual : ∀ v : ℂ, ‖v‖ ≤ η / 4 → AnalyticAt ℂ Γ (Complex.sqrt (s : ℂ), v)
  residual_bound : ∀ v : ℂ, ‖v‖ < η → ‖descendedTerm A B Γ 2 v s 0‖ ≤
    M * (‖v - (a : ℂ)‖ * ‖v - (b : ℂ)‖) ^ 2
  true_orbits : ∀ Z : ℂ, Z ∈ strip θ Y →
    Summable (fun k => ‖descendedTerm A B Γ 2 (bandChart a b θ Z) s k‖) ∧
    Summable (fun k => ‖descendedTerm A B Γ 2 (inverseOrbit s (bandChart a b θ Z) (k + 1)) s 0‖) ∧
    (∑' k, ‖descendedTerm A B Γ 2 (bandChart a b θ Z) s k‖) ≤ 1 ∧
    (∑' k, ‖descendedTerm A B Γ 2 (inverseOrbit s (bandChart a b θ Z) (k + 1)) s 0‖) ≤ 1 ∧
    (∀ k, orbit (bandChart a b θ Z) s k ≠ (a : ℂ) ∧
      orbit (bandChart a b θ Z) s k ≠ (b : ℂ) ∧
      ‖orbit (bandChart a b θ Z) s k‖ ≤ η / 4 ∧
      bandTime a b θ (orbit (bandChart a b θ Z) s k) ∈ strip θ (Y / 2) ∧
      (bandTime a b θ (orbit (bandChart a b θ Z) s k)).re + 3 / 4 ≤
        (bandTime a b θ (orbit (bandChart a b θ Z) s (k + 1))).re) ∧
    (∀ k, inverseOrbit s (bandChart a b θ Z) k ≠ (a : ℂ) ∧
      inverseOrbit s (bandChart a b θ Z) k ≠ (b : ℂ) ∧
      ‖inverseOrbit s (bandChart a b θ Z) k‖ ≤ η / 4 ∧
      bandTime a b θ (inverseOrbit s (bandChart a b θ Z) k) ∈ strip θ (Y / 2) ∧
      (bandTime a b θ (inverseOrbit s (bandChart a b θ Z) (k + 1))).re + 3 / 4 ≤
        (bandTime a b θ (inverseOrbit s (bandChart a b θ Z) k)).re)

  forward_nonreal_step : ∀ v : ℂ, ‖v‖ < η → v.im ≠ 0 →
    lensModel s a b θ (e₁ s) (e₂ s) (unfolding s v) - lensModel s a b θ (e₁ s) (e₂ s) v - 1 =
      descendedTerm A B Γ 2 v s 0
  inverse_nonreal_step : ∀ v : ℂ, ‖v‖ ≤ η / 4 → v.im ≠ 0 →
    lensModel s a b θ (e₁ s) (e₂ s) (inverseStep s v) - lensModel s a b θ (e₁ s) (e₂ s) v + 1 =
      -descendedTerm A B Γ 2 (inverseStep s v) s 0


theorem exists_actual_lens_control
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ Y s₀ η M P : ℝ, 2 ≤ Y ∧ 0 < s₀ ∧ s₀ ≤ 1 / 2 ∧
      ∀ s : ℝ, 0 < s → s < s₀ → ∃ a b θ : ℝ, LensControl e₁ e₂ A B Γ s a b θ Y η M P := by
  have hΓ0 : AnalyticAt ℂ Γ 0 := hdata.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨δΓ, hδΓ, hΓball⟩ := Metric.eventually_nhds_iff.mp hΓ0.eventually_analyticAt
  obtain ⟨Q⟩ := exists_quotientControl
  obtain ⟨η₁, s₁, M, P, hη₁, hη₁q, hs₁, hs₁h, hM, hP, hlocal⟩ :=
    exists_actual_lens_bounds U H e₁ e₂ A B K F Γ hdata
  obtain ⟨η₂, s₂, hη₂, _hη₂q, hs₂, _hs₂η, _hs₂h, hinverse⟩ :=
    exists_actual_inverse_lensModel_one_step U H e₁ e₂ A B K F Γ hdata
  let η := min η₁ (min η₂ (min (Q.radius / 4) (min (1 / (M + 1)) (δΓ / 2))))
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min hη₁ (lt_min hη₂ (lt_min (div_pos Q.radius_pos (by norm_num)) (lt_min (by positivity) (by positivity))))
  have hηη₁ : η ≤ η₁ := min_le_left _ _
  have hηη₂ : η ≤ η₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hηr : η ≤ Q.radius / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηM : η ≤ 1 / (M + 1) := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hηΓ : η ≤ δΓ / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
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
    exists_bootstrap_constants η M (P + 10000) hη hM.le
  have hmarginF : 2 * (Real.pi + 2 * P) + 1 < Y / 2 := by linarith
  have hmarginG : 2 * (Real.pi + 2 * P) + 2 < Y / 2 := by linarith
  let δ := min (η / 8) (τ / 8)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨s₃, hs₃, _hs₃h, hroots⟩ := Kneser.RealExponentialRoots.exists_ordered_small_real_roots δ hδ
  let s₀ := min s₁ (min s₂ (min s₃ (min (η / 8) (η ^ 2))))
  refine ⟨Y, s₀, η, M, P, hY, by dsimp [s₀]; positivity, (min_le_left _ _).trans hs₁h, ?_⟩
  intro s hs hss
  have hs₁' : s < s₁ := hss.trans_le (min_le_left _ _)
  have hs₂' : s < s₂ := hss.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hs₃' : s < s₃ := hss.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsη : s ≤ η / 8 := (hss.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))).le
  have hsηsq : s < η ^ 2 := hss.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hs1 : s < 1 / 2 := hs₁'.trans_le hs₁h
  obtain ⟨a, b, hal, ha0, hb0, hbu, hfa, hfb⟩ := hroots s hs hs₃'
  have ha : |a| < δ := by rw [abs_of_neg ha0]; linarith
  have hb : |b| < δ := by rw [abs_of_pos hb0]; exact hbu
  have hδη : δ ≤ η / 8 := min_le_left _ _
  have hδτ : δ ≤ τ / 8 := min_le_right _ _
  have haa : -1 < a := by have hh := (abs_lt.mp ha).1; linarith
  have hab : a < b := by linarith
  have hκr : (1 - s) * (b - a) < Q.radius := by
    have hm : (1 - s) * (b - a) ≤ b - a := by nlinarith only [hs, hab]
    have hg : b - a < η / 4 := by have h1 := (abs_lt.mp ha).1; have h2 := (abs_lt.mp hb).2; linarith only [h1,h2,hδη]
    linarith only [hm,hg,hηr,Q.radius_pos]
  let θ := timeScale Q ((1 - s) * (b - a))
  have hκ : 0 < (1 - s) * (b - a) := mul_pos (by linarith) (by linarith)
  obtain ⟨hθ, hratio⟩ := timeScale_pos_and_gap_bound Q s a b hs hs1 hab hκr
  have hθτ : θ < τ := by
    have hh := (timeScale_bounds Q _ hκ hκr).2
    have hm : (1 - s) * (b - a) ≤ b - a := by nlinarith only [hs, hab]
    have hg : b - a < τ / 4 := by have h1 := (abs_lt.mp ha).1; have h2 := (abs_lt.mp hb).2; linarith only [h1,h2,hδτ]
    change timeScale Q ((1 - s) * (b - a)) < τ
    linarith only [hh,hm,hg,hτ]
  have h2θτ : 4 * θ < τ := by
    have hh := (timeScale_bounds Q _ hκ hκr).2
    have hm : (1 - s) * (b - a) ≤ b - a := by nlinarith only [hs, hab]
    have hg : b - a < τ / 4 := by have h1 := (abs_lt.mp ha).1; have h2 := (abs_lt.mp hb).2; linarith only [h1,h2,hδτ]
    change 4 * timeScale Q ((1 - s) * (b - a)) < τ
    linarith only [hh,hm,hg,hτ]
  have hstrong : θ * Y ≤ Real.pi / 8 := by
    have hh := (hθbounds (4 * θ) (by linarith only [hθ]) h2θτ).2.1
    linarith only [hh]
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
  have hΓlocal : ∀ v : ℂ, ‖v‖ ≤ η / 4 → AnalyticAt ℂ Γ (Complex.sqrt (s : ℂ), v) := by
    intro v hv
    have hxsq : ‖Complex.sqrt (s : ℂ)‖ ^ 2 = s := by
      rw [← norm_pow, Kneser.AnalyticEvenDescent.square_sqrt, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    have hx : ‖Complex.sqrt (s : ℂ)‖ < η := by nlinarith only [hxsq, hsηsq, hη, norm_nonneg (Complex.sqrt (s : ℂ))]
    apply hΓball (y := (Complex.sqrt (s : ℂ), v))
    rw [dist_zero_right, Prod.norm_def]
    exact max_lt (by linarith only [hx,hηΓ,hδΓ]) (by linarith only [hv,hηΓ,hδΓ])
  have hheight : 4 * (Real.pi + P * η + 2) < Y := by
    have hPη : P * η ≤ P := (mul_le_mul_of_nonneg_left (show η ≤ 1 by linarith only [hηq]) hP.le).trans_eq (mul_one P)
    linarith only [hmargin',hPη,hP]
  have hAll : ∀ Z : ℂ, Z ∈ strip θ Y →
    Summable (fun k => ‖descendedTerm A B Γ 2 (bandChart a b θ Z) s k‖) ∧
    Summable (fun k => ‖descendedTerm A B Γ 2 (inverseOrbit s (bandChart a b θ Z) (k + 1)) s 0‖) ∧
    (∑' k, ‖descendedTerm A B Γ 2 (bandChart a b θ Z) s k‖) ≤ 1 ∧
    (∑' k, ‖descendedTerm A B Γ 2 (inverseOrbit s (bandChart a b θ Z) (k + 1)) s 0‖) ≤ 1 ∧
    (∀ k, orbit (bandChart a b θ Z) s k ≠ (a : ℂ) ∧ orbit (bandChart a b θ Z) s k ≠ (b : ℂ) ∧
      ‖orbit (bandChart a b θ Z) s k‖ ≤ η / 4 ∧ bandTime a b θ (orbit (bandChart a b θ Z) s k) ∈ strip θ (Y / 2) ∧
      (bandTime a b θ (orbit (bandChart a b θ Z) s k)).re + 3 / 4 ≤ (bandTime a b θ (orbit (bandChart a b θ Z) s (k + 1))).re) ∧
    (∀ k, inverseOrbit s (bandChart a b θ Z) k ≠ (a : ℂ) ∧ inverseOrbit s (bandChart a b θ Z) k ≠ (b : ℂ) ∧
      ‖inverseOrbit s (bandChart a b θ Z) k‖ ≤ η / 4 ∧ bandTime a b θ (inverseOrbit s (bandChart a b θ Z) k) ∈ strip θ (Y / 2) ∧
      (bandTime a b θ (inverseOrbit s (bandChart a b θ Z) (k + 1))).re + 3 / 4 ≤ (bandTime a b θ (inverseOrbit s (bandChart a b θ Z) k)).re) := by
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
   exact ⟨hsumF.1, hsumG.1, hsumF.2.trans hE, hsumG.2.trans hE,
     (fun k => ⟨(hstateF k).1, (hstateF k).2.1, (hstateF k).2.2.1, (hstateF k).2.2.2, hstepF k⟩),
     (fun k => ⟨(hstateG k).1, (hstateG k).2.1, (hstateG k).2.2.1, (hstateG k).2.2.2, hstepG k⟩)⟩
  refine ⟨a, b, θ, ?_⟩
  refine ⟨ha0, hb0, hθ, hfa, hfb, hθeq, hθYhalf, (hstrong.trans (by linarith [Real.pi_pos])), hstrong, hratio, hη, hηq, hM.le, hY,
    hl.1, hl.2.1, hl.2.2.1, ha.le.trans hδη, hb.le.trans hδη, hheight, (by linarith only [hmargin',hP,Real.pi_pos]),
    (by linarith only [hmargin',hP,Real.pi_pos]), hΓlocal,
    (fun v hv => hl.2.2.2.1 v (hv.trans_le hηη₁)), hAll, ?_, ?_⟩
  · intro v hv hi
    rw [hθeq]
    exact hl.2.2.2.2.2 v (hv.trans_le hηη₁) hi
  · intro v hv hi
    rw [hθeq]
    exact (hInv v (hv.trans (by linarith only [hηη₂])) hi).2.2.2


theorem actual_forwardSeries_analytic
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) :
    AnalyticOnNhd ℂ (forwardSeries A B Γ s a b θ) (strip θ Y) := by
  have hab : a < b := lt_trans hc.left_neg hc.right_pos
  have hYθ : θ * Y ≤ Real.pi := hc.width.trans (by linarith [Real.pi_pos])
  apply analyticOnNhd_forwardSeries_of_true_control A B Γ s a b θ Y M hab hc.theta_pos
    hc.height_large hYθ hc.gap hc.residual_constant
  · intro k Z hZ
    exact analyticAt_forwardTerm A B Γ s a b θ Y Z k hab hc.theta_pos (by linarith [hc.height_large]) hYθ hZ
      (hc.analytic_residual _ ((hc.true_orbits Z hZ).2.2.2.2.1 k).2.2.1)
  · intro Z hZ k
    exact ⟨((hc.true_orbits Z hZ).2.2.2.2.1 k).1, ((hc.true_orbits Z hZ).2.2.2.2.1 k).2.1⟩
  · intro Z hZ k
    exact ((hc.true_orbits Z hZ).2.2.2.2.1 k).2.2.2.1
  · intro Z hZ k
    apply hc.residual_bound
    exact ((hc.true_orbits Z hZ).2.2.2.2.1 k).2.2.1.trans_lt (by linarith [hc.radius_pos])
  · intro Z hZ k
    exact ((hc.true_orbits Z hZ).2.2.2.2.1 k).2.2.2.2

theorem actual_inverseSeries_analytic
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) :
    AnalyticOnNhd ℂ (inverseSeries A B Γ s a b θ) (strip θ Y) := by
  have hab : a < b := lt_trans hc.left_neg hc.right_pos
  have hYθ : θ * Y ≤ Real.pi := hc.width.trans (by linarith [Real.pi_pos])
  apply analyticOnNhd_inverseSeries_of_true_control A B Γ s a b θ Y M hab hc.theta_pos
    hc.height_large hYθ hc.gap hc.residual_constant
  · intro k Z hZ
    apply analyticAt_inverseTerm A B Γ s a b θ Y Z k hab hc.theta_pos (by linarith [hc.height_large]) hYθ hZ
    · intro j
      exact ((hc.true_orbits Z hZ).2.2.2.2.2 j).2.2.1.trans_lt (by linarith [hc.radius_small])
    · exact hc.analytic_residual _ ((hc.true_orbits Z hZ).2.2.2.2.2 (k+1)).2.2.1
  · intro Z hZ k
    exact ⟨((hc.true_orbits Z hZ).2.2.2.2.2 k).1, ((hc.true_orbits Z hZ).2.2.2.2.2 k).2.1⟩
  · intro Z hZ k
    exact ((hc.true_orbits Z hZ).2.2.2.2.2 k).2.2.2.1
  · intro Z hZ k
    apply hc.residual_bound
    exact ((hc.true_orbits Z hZ).2.2.2.2.2 k).2.2.1.trans_lt (by linarith [hc.radius_pos])
  · intro Z hZ k
    exact ((hc.true_orbits Z hZ).2.2.2.2.2 k).2.2.2.2

theorem actual_coordinates_analytic
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) :
    AnalyticOnNhd ℂ (attractingCoordinate A B Γ s a b θ (e₁ s) (e₂ s)) (strip θ Y) ∧
    AnalyticOnNhd ℂ (repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s)) (strip θ Y) := by
  have hab : a < b := lt_trans hc.left_neg hc.right_pos
  have hY : 0 < Y := by linarith [hc.height_large]
  have hYθ : θ * Y ≤ Real.pi := hc.width.trans (by linarith [Real.pi_pos])
  have hmodel := analyticOnNhd_chartModel s a b θ Y (e₁ s) (e₂ s) hab hc.theta_pos hY hYθ
  have hforward := actual_forwardSeries_analytic e₁ e₂ A B Γ s a b θ Y η M P hc
  have hinverse := actual_inverseSeries_analytic e₁ e₂ A B Γ s a b θ Y η M P hc
  constructor
  · intro Z hZ
    have hh := (hmodel Z hZ).add (hforward Z hZ)
    apply hh.congr
    filter_upwards [(strip_isOpen θ Y).mem_nhds hZ] with W hW
    simp only [Pi.add_apply, attractingCoordinate, chartModel_eq_lensModel s a b θ Y (e₁ s) (e₂ s) W hab hc.theta_pos hY hYθ hW]
  · intro Z hZ
    have hh := (hmodel Z hZ).sub (hinverse Z hZ)
    apply hh.congr
    filter_upwards [(strip_isOpen θ Y).mem_nhds hZ] with W hW
    simp only [Pi.sub_apply, repellingCoordinate, chartModel_eq_lensModel s a b θ Y (e₁ s) (e₂ s) W hab hc.theta_pos hY hYθ hW]

theorem actual_series_norm_le_one
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) (Z : ℂ) (hZ : Z ∈ strip θ Y) :
    ‖forwardSeries A B Γ s a b θ Z‖ ≤ 1 ∧ ‖inverseSeries A B Γ s a b θ Z‖ ≤ 1 := by
  have hh := hc.true_orbits Z hZ
  exact ⟨(norm_tsum_le_tsum_norm hh.1).trans hh.2.2.1,
    (norm_tsum_le_tsum_norm hh.2.1).trans hh.2.2.2.1⟩

theorem exists_actual_holomorphic_growing_coordinates
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ Y s₀ η M P : ℝ, 2 ≤ Y ∧ 0 < s₀ ∧ s₀ ≤ 1 / 2 ∧
      ∀ s : ℝ, 0 < s → s < s₀ → ∃ a b θ : ℝ,
        LensControl e₁ e₂ A B Γ s a b θ Y η M P ∧
        AnalyticOnNhd ℂ (attractingCoordinate A B Γ s a b θ (e₁ s) (e₂ s)) (strip θ Y) ∧
        AnalyticOnNhd ℂ (repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s)) (strip θ Y) := by
  obtain ⟨Y,s₀,η,M,P,hY,hs₀,hs₀h,hh⟩ := exists_actual_lens_control U H e₁ e₂ A B K F Γ hdata
  refine ⟨Y,s₀,η,M,P,hY,hs₀,hs₀h,?_⟩
  intro s hs hss
  obtain ⟨a,b,θ,hc⟩ := hh s hs hss
  exact ⟨a,b,θ,hc,actual_coordinates_analytic e₁ e₂ A B Γ s a b θ Y η M P hc⟩

end Kneser.ActualHolomorphicGrowingLens
end
