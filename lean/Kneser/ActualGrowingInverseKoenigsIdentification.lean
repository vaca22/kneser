import Kneser.InverseLensKoenigsIdentification
import Kneser.ActualGrowingKoenigsIdentification
import Kneser.ActualNormalizedGrowingTransition

/-! The actual normalized repelling coordinate exponentiates to the
actual inverse Koenigs sum on the whole growing strip. The normalization
is the genuine physical residual sum at the specified real point. -/
set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
namespace Kneser.ActualGrowingInverseKoenigsIdentification
open Set Metric Filter Complex
open Kneser.ActualInverseLocalKoenigs Kneser.InverseKoenigsEntry
open Kneser.InverseKoenigsRealGeometry Kneser.InverseLensKoenigsIdentification
open Kneser.ExponentialUnfolding Kneser.PositiveKoenigsOrbit
open Kneser.GrowingBandGeometry Kneser.GrowingLensSpatialHolomorphy
open Kneser.ActualGrowingRealPhases Kneser.ActualHolomorphicGrowingLens
open Kneser.RealRepellingCoordinatePhase Kneser.ActualGrowingKoenigsIdentification
open Kneser.ActualNormalizedGrowingTransition
open scoped Topology

theorem normalized_repelling_exponential_real_of_control
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r r₀ : ℝ)
    (hs : 0<s) (hs1 : s<1/2) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (har : a<r) (hrb : r<b) (har₀ : a<r₀) (hr₀b : r₀<b) :
    Complex.exp ((Real.log (multiplier s b):ℂ)*
      (physicalRepelling A B Γ s a b θ (e₁ s) (e₂ s) r-
        physicalRepelling A B Γ s a b θ (e₁ s) (e₂ s) r₀))=
      inverseKoenigs s b r/inverseKoenigs s b r₀ := by
  have hr := physicalRepelling_eq_inverse_koenigs_real_of_control e₁ e₂ A B Γ s a b θ Y η M P r hs hs1 hc har hrb
  have hr₀ := physicalRepelling_eq_inverse_koenigs_real_of_control e₁ e₂ A B Γ s a b θ Y η M P r₀ hs hs1 hc har₀ hr₀b
  have hK := inverseKoenigs_negative_between_of_control e₁ e₂ A B Γ s a b θ Y η M P r hs hs1 hc har hrb
  have hK₀ := inverseKoenigs_negative_between_of_control e₁ e₂ A B Γ s a b θ Y η M P r₀ hs hs1 hc har₀ hr₀b
  have hkn : -inverseKoenigs s b r≠0 := by intro h; rw [neg_eq_zero] at h; rw [h,Complex.zero_re] at hK; linarith [hK.2]
  have hkn₀ : -inverseKoenigs s b r₀≠0 := by intro h; rw [neg_eq_zero] at h; rw [h,Complex.zero_re] at hK₀; linarith [hK₀.2]
  have hl : (Real.log (multiplier s b):ℂ)≠0 := by
    exact_mod_cast (ne_of_gt (Real.log_pos (actual_right_multiplier s b hc.right_pos hc.right_fixed)))
  rw [hr,hr₀]
  have he : (Real.log (multiplier s b):ℂ)*
      (intervalInverseKoenigsTime s b r+inverseModelConstant s a b (e₁ s) (e₂ s)+(Real.pi:ℂ)*I/(θ:ℂ)-
        (intervalInverseKoenigsTime s b r₀+inverseModelConstant s a b (e₁ s) (e₂ s)+(Real.pi:ℂ)*I/(θ:ℂ)))=
      Complex.log (-inverseKoenigs s b r)-Complex.log (-inverseKoenigs s b r₀) := by
    unfold intervalInverseKoenigsTime
    field_simp
    ring
  rw [he,Complex.exp_sub,Complex.exp_log hkn,Complex.exp_log hkn₀]
  simp only [neg_div_neg_eq]

theorem normalized_repelling_exponential_of_control
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r : ℝ)
    (hs : 0<s) (hs1 : s<1/2) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (har : a<r) (hrb : r<b) :
    ∀Z∈strip θ Y,
      Complex.exp ((Real.log (multiplier s b):ℂ)*
        (repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) Z-
          repellingConstant A B Γ s a b θ r (e₁ s) (e₂ s)))=
        inverseKoenigs s b (bandChart a b θ Z)/inverseKoenigs s b r := by
  have hS := (actual_coordinates_analytic e₁ e₂ A B Γ s a b θ Y η M P hc).2
  have hf : AnalyticOnNhd ℂ (fun Z => Complex.exp ((Real.log (multiplier s b):ℂ)*
        (repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) Z-
          repellingConstant A B Γ s a b θ r (e₁ s) (e₂ s)))) (strip θ Y) :=
    fun Z hZ => (analyticAt_const.mul ((hS Z hZ).sub analyticAt_const)).cexp
  have hchart := analyticOnNhd_bandChart a b θ Y (by linarith [hc.left_neg,hc.right_pos]) hc.theta_pos
    (by linarith [hc.height_large]) (hc.width.trans (by linarith [Real.pi_pos]))
  have hg : AnalyticOnNhd ℂ (fun Z => inverseKoenigs s b (bandChart a b θ Z)/inverseKoenigs s b r) (strip θ Y) :=
    fun Z hZ => ((inverseKoenigs_analytic_lens e₁ e₂ A B Γ s a b θ Y η M P hs hs1 hc Z hZ).comp (hchart Z hZ)).div_const
  apply eqOn_strip_of_midline _ _ θ Y hc.theta_pos hc.width hf hg
  intro x
  have hb := bandChart_midline_between a b θ x (by linarith [hc.left_neg,hc.right_pos]) hc.theta_pos
  let v : ℝ := (a+b*Real.exp (-θ*x))/(1+Real.exp (-θ*x))
  have he : bandChart a b θ ((x:ℂ)+((Real.pi/θ:ℝ):ℂ)*I)=(v:ℂ) := bandChart_midline a b θ x hc.theta_pos
  have hav : a<v := by simpa only [he,Complex.ofReal_re] using hb.1
  have hvb : v<b := by simpa only [he,Complex.ofReal_re] using hb.2
  change Complex.exp ((Real.log (multiplier s b):ℂ)*
      (physicalRepelling A B Γ s a b θ (e₁ s) (e₂ s) (bandChart a b θ _)-
        physicalRepelling A B Γ s a b θ (e₁ s) (e₂ s) r))= _
  rw [he]
  exact normalized_repelling_exponential_real_of_control e₁ e₂ A B Γ s a b θ Y η M P v r hs hs1 hc hav hvb har hrb

end Kneser.ActualGrowingInverseKoenigsIdentification
end
