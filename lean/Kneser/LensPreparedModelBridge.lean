import Kneser.ActualLensModel
import Kneser.ReflectedPreparedModel

/-! Exact branch constants connect the genuine growing-lens model to
both prepared Fatou models.  These constants cancel when the repelling
coordinate is centered at one fixed physical point. -/

set_option autoImplicit false
noncomputable section
namespace Kneser.LensPreparedModelBridge

open Filter Set Metric Kneser.ActualLensModel Kneser.ActualKoenigsIdentification
open Kneser.ExponentialModelTime Kneser.ExponentialPreparedModel
open Kneser.ReflectedPreparedModel Kneser.ReflectedOrbitChainCoefficient
open Kneser.PositiveKoenigsOrbit Kneser.ExponentialUnfolding
open Kneser.ActualPreparedRootMatching
open scoped Topology

theorem negative_reflected_model_upper (U H e₁ e₂ : ℂ → ℂ)
    (hHlog : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (x u : ℂ) (hx : x ≠ 0) (hHx : H x ≠ 0) (hHnx : H (-x) ≠ 0)
    (hreal₁ : (U x).im = 0) (hreal₂ : (U (-x)).im = 0) (hu : 0 < u.im) :
    -preparedModelTime (-U) (-H) e₁ (-e₂) (x ^ 2) (-u) =
      preparedModelTime U H e₁ e₂ (x ^ 2) u +
        ((Complex.log (rootMultiplier U x))⁻¹ + (Complex.log (rootMultiplier U (-x)))⁻¹) *
          (Real.pi : ℂ) * Complex.I := by
  have hpa := preparedModelTime_residue_pair U H e₁ e₂ hHlog x u hx hHx hHnx
  have hpr := reflected_preparedModelTime_residue_pair U H e₁ e₂ hHlog x (-u) hx hHx hHnx
  simp only [neg_neg] at hpr
  have hl₁ : Complex.log (-U x - -u) = Complex.log (U x - u) + (Real.pi : ℂ) * Complex.I := by
    rw [show -U x - -u = -(U x - u) by ring]
    apply log_neg_of_im_neg
    simp only [Complex.sub_im, hreal₁]
    linarith
  have hl₂ : Complex.log (-U (-x) - -u) = Complex.log (U (-x) - u) + (Real.pi : ℂ) * Complex.I := by
    rw [show -U (-x) - -u = -(U (-x) - u) by ring]
    apply log_neg_of_im_neg
    simp only [Complex.sub_im, hreal₂]
    linarith
  rw [hpa,hpr,hl₁,hl₂]
  ring

theorem negative_reflected_model_pair_upper (U H e₁ e₂ : ℂ → ℂ)
    (hHlog : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (s a b θ : ℝ) (x u : ℂ) (hs1 : s < 1) (ha : -1 < a) (hb : 0 < b)
    (hab : a < b) (hθ : 0 < θ) (hθeq : θ = -Real.log (multiplier s a))
    (hx : x ^ 2 = (s : ℂ)) (hxne : x ≠ 0) (hHx : H x ≠ 0) (hHnx : H (-x) ≠ 0)
    (hm : (U x = (a : ℂ) ∧ U (-x) = (b : ℂ)) ∨
      (U x = (b : ℂ) ∧ U (-x) = (a : ℂ))) (hu : 0 < u.im) :
    -preparedModelTime (-U) (-H) e₁ (-e₂) s (-u) =
      lensModel s a b θ (e₁ s) (e₂ s) u + residueSum s a b * (Real.pi : ℂ) * Complex.I := by
  have hr₁ : (U x).im = 0 := by rcases hm with hm | hm <;> simp only [hm.1,Complex.ofReal_im]
  have hr₂ : (U (-x)).im = 0 := by rcases hm with hm | hm <;> simp only [hm.2,Complex.ofReal_im]
  have hp := negative_reflected_model_upper U H e₁ e₂ hHlog x u hxne hHx hHnx hr₁ hr₂ hu
  have hpa := preparedModelTime_pair_of_matching U H e₁ e₂ hHlog s a b x hs1 ha hb hx hxne hHx hHnx hm u
  have hμa : 0 < multiplier s a := by unfold multiplier; exact mul_pos (by linarith) (by linarith)
  have hμb : 0 < multiplier s b := by unfold multiplier; exact mul_pos (by linarith) (by linarith)
  have hsum : ((Complex.log (rootMultiplier U x))⁻¹ + (Complex.log (rootMultiplier U (-x)))⁻¹) =
      residueSum s a b := by
    rcases hm with hm | hm
    · rw [rootMultiplier_of_real_value U s a x hx hm.1,
        rootMultiplier_of_real_value U s b (-x) (by simpa only [neg_sq] using hx) hm.2,
        ← Complex.ofReal_log hμa.le, ← Complex.ofReal_log hμb.le]
      rfl
    · rw [rootMultiplier_of_real_value U s b x hx hm.1,
        rootMultiplier_of_real_value U s a (-x) (by simpa only [neg_sq] using hx) hm.2,
        ← Complex.ofReal_log hμb.le, ← Complex.ofReal_log hμa.le]
      exact add_comm _ _
  rw [hx,hpa,hsum] at hp
  rw [lensModel_eq_paired_upper s a b θ (e₁ s) (e₂ s) u hab hθ hθeq hu]
  exact hp

/-- Both actual branch identities hold on one genuine parameter/root
neighborhood, constructed from the same exponential preparation. -/
theorem exists_actual_upper_model_bridge (U H e₁ e₂ A B : ℂ → ℂ)
    (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ η s₀ : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ 0 < s₀ ∧ s₀ ≤ 1 / 2 ∧
      ∀ s a b θ : ℝ, 0 < s → s < s₀ → |a| < η → |b| < η → a < 0 → 0 < b →
        unfolding s a = (a : ℂ) → unfolding s b = (b : ℂ) →
        0 < θ → θ = -Real.log (multiplier s a) →
        ∀ u : ℂ, 0 < u.im →
          preparedModelTime U H e₁ e₂ s u = lensModel s a b θ (e₁ s) (e₂ s) u ∧
          -preparedModelTime (-U) (-H) e₁ (-e₂) s (-u) =
            lensModel s a b θ (e₁ s) (e₂ s) u + residueSum s a b * (Real.pi : ℂ) * Complex.I := by
  obtain ⟨ηm,sm,hηm,hsm,hηmq,hmodel⟩ := exists_actual_model_neighborhood U H e₁ e₂ A B K F Γ hdata
  obtain ⟨ηr,sr,hηr,hsr,hmatch⟩ := exists_root_matching_neighborhood U H e₁ e₂ A B K F Γ hdata
  have hd := hdata
  rcases hd with ⟨_hU,_hU0,_hUd,hH,hHne,hHlog,_hA,_hB,_hA0,_hB0,_he₁,_he₂,
    _hF,_hΓ,_hEven,_hK0,_hK,_hq,_hroots,_hfactor,_hprep,_hresidue⟩
  obtain ⟨δ,hδ,hHball⟩ := Metric.eventually_nhds_iff.mp (hH.continuousAt.eventually_ne hHne)
  let η := min ηm (min ηr (δ / 4))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηm' : η ≤ ηm := min_le_left _ _
  have hηr' : η ≤ ηr := (min_le_right _ _).trans (min_le_left _ _)
  have hηδ : η ≤ δ / 4 := (min_le_right _ _).trans (min_le_right _ _)
  let s₀ := min sm (min sr (min (η ^ 2) (1 / 2)))
  refine ⟨η,s₀,hη,hηm'.trans hηmq,by dsimp [s₀]; positivity,
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)),?_⟩
  intro s a b θ hs hss ha hb ha0 hb0 hfa hfb hθ hθeq u hu
  have hsm' : s < sm := hss.trans_le (min_le_left _ _)
  have hsr' : s < sr := hss.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsη : s < η ^ 2 := hss.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hs1 : s < 1 := (hss.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))).trans (by norm_num)
  let x := Complex.sqrt (s : ℂ)
  have hx : x ^ 2 = (s : ℂ) := Kneser.AnalyticEvenDescent.square_sqrt _
  have hxne : x ≠ 0 := by
    intro he
    have hh := hx
    rw [he,zero_pow (by norm_num : 2 ≠ 0)] at hh
    exact (by exact_mod_cast ne_of_gt hs : (s : ℂ) ≠ 0) hh.symm
  have hxsq : ‖x‖ ^ 2 = s := by
    rw [← norm_pow,hx,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs]
  have hxn : ‖x‖ < δ := by
    have hh : ‖x‖ < η := by nlinarith only [hxsq,hsη,hη,norm_nonneg x]
    linarith only [hh,hηδ,hδ]
  have hHx : H x ≠ 0 := hHball (by simpa only [dist_zero_right] using hxn)
  have hHnx : H (-x) ≠ 0 := hHball (by simpa only [dist_zero_right,norm_neg] using hxn)
  have hm := hmatch s a b hs hsr' (ha.trans_le hηr') (hb.trans_le hηr') (by linarith) hfa hfb x hx
  have haa : -1 < a := by have hh := (abs_lt.mp ha).1; linarith [hηm'.trans hηmq]
  refine ⟨?_,negative_reflected_model_pair_upper U H e₁ e₂ hHlog s a b θ x u hs1 haa hb0
    (by linarith) hθ hθeq hx hxne hHx hHnx hm hu⟩
  rw [(hmodel s a b hs hsm' (ha.trans_le hηm') (hb.trans_le hηm') ha0 hb0 hfa hfb).1 u,
    lensModel_eq_paired_upper s a b θ (e₁ s) (e₂ s) u (by linarith) hθ hθeq hu]

end Kneser.LensPreparedModelBridge
