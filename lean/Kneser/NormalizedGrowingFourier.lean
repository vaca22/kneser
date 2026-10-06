import Kneser.ActualNormalizedGrowingTransition
import Kneser.ActualGrowingFourier
import Kneser.FourierCenterShift
import Kneser.RealNormalizationAnchor

/-! Fourier coefficients of the genuine, real-normalized growing transition.
The attracting normalization is the logarithm of the actual Koenigs orbit
limit at a real left anchor. The repelling normalization is its actual
orbit-sum value at an interior real point. The mean has exact half-period
imaginary part, and subtracting this actual mean gives a uniform bound 4.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Kneser.NormalizedGrowingFourier

open Set Metric Complex MeasureTheory
open Kneser.GrowingBandGeometry Kneser.GrowingStripFourier
open Kneser.ActualHolomorphicGrowingLens Kneser.ActualGrowingCoordinateInverse
open Kneser.GrowingLensSpatialHolomorphy Kneser.GateFourierDerivative
open Kneser.ActualGrowingKoenigsIdentification Kneser.PositiveKoenigsAbel
open Kneser.ActualNormalizedGrowingTransition Kneser.ReflectedOrbitChainCoefficient
open scoped Topology Interval

def boundaryLoss (Y P : ℝ) : ℝ := 3*Y+boundaryMargin P+2*P

def outerWidth (θ Y P : ℝ) : ℝ := height θ/2-boundaryLoss Y P

def decayWidth (θ Y P : ℝ) : ℝ := outerWidth θ Y P-1

def meanRemoved (T : ℂ → ℂ) (z : ℂ) : ℂ := T z-gateFourierCoefficient 0 0 T

theorem coefficient_sub_constant (T : ℂ → ℂ) (c : ℂ) (n : ℤ)
    (hT : ContinuousOn (fun x : ℝ => T (x:ℂ)) (Icc 0 1)) :
    gateFourierCoefficient n 0 (fun z => T z-c)=gateFourierCoefficient n 0 T-
      c*(if n=0 then 1 else 0) := by
  have hcontinuous : ContinuousOn (fun x : ℝ =>
      (T (x:ℂ)-(x:ℂ))*exp (-Kneser.fourierFrequency n*(x:ℂ))) (uIcc 0 1) := by
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    exact (hT.sub Complex.continuous_ofReal.continuousOn).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn
  have hi : IntervalIntegrable (fun x : ℝ =>
      (T (x:ℂ)-(x:ℂ))*exp (-Kneser.fourierFrequency n*(x:ℂ))) volume 0 1 :=
    hcontinuous.intervalIntegrable
  have he : IntervalIntegrable (fun x : ℝ => exp (-Kneser.fourierFrequency n*(x:ℂ))) volume 0 1 :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).intervalIntegrable _ _
  have hp (x : ℝ) : (T (x:ℂ)-c-(x:ℂ))*exp (-Kneser.fourierFrequency n*(x:ℂ))=
      (T (x:ℂ)-(x:ℂ))*exp (-Kneser.fourierFrequency n*(x:ℂ))-
        c*exp (-Kneser.fourierFrequency n*(x:ℂ)) := by ring
  simp only [gateFourierCoefficient,gatePoint,gateWeight,Complex.ofReal_zero,mul_zero,add_zero]
  simp_rw [hp]
  rw [intervalIntegral.integral_sub hi (he.const_mul c),intervalIntegral.integral_const_mul,
    Kneser.FourierCenterShift.integral_weight]

theorem mean_removed_zero (T : ℂ → ℂ)
    (hT : ContinuousOn (fun x : ℝ => T (x:ℂ)) (Icc 0 1)) :
    gateFourierCoefficient 0 0 (meanRemoved T)=0 := by
  unfold meanRemoved
  rw [coefficient_sub_constant T _ 0 hT]
  simp

theorem mean_removed_nonzero (T : ℂ → ℂ) (n : ℤ) (hn : n≠0)
    (hT : ContinuousOn (fun x : ℝ => T (x:ℂ)) (Icc 0 1)) :
    gateFourierCoefficient n 0 (meanRemoved T)=gateFourierCoefficient n 0 T := by
  unfold meanRemoved
  rw [coefficient_sub_constant T _ n hT]
  simp [hn]

theorem mean_sub_constant_bound (T : ℂ → ℂ) (D : ℝ) (c : ℂ)
    (hD : 0<D) (ha : AnalyticOnNhd ℂ T (symmetricStrip D))
    (hb : ∀z∈symmetricStrip D, ‖T z-z-c‖≤2) :
    ‖gateFourierCoefficient 0 0 T-c‖≤2 := by
  have hcont : ContinuousOn (fun x : ℝ => T (x:ℂ)) (Icc 0 1) := by
    intro x _
    have hx : (x:ℂ)∈symmetricStrip D := by simpa [symmetricStrip] using hD
    exact ((ha _ hx).continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hh := Kneser.LocalStripFourierDecay.gate_coefficient_bound 0 (fun z => T z-c) 0 2 (by
    intro x _
    have hx : gatePoint 0 x∈symmetricStrip D := by simpa [gatePoint,symmetricStrip] using hD
    convert hb _ hx using 1
    congr 1
    ring)
  rw [coefficient_sub_constant T c 0 hcont] at hh
  simpa [Kneser.fourierFrequency] using hh

theorem mean_removed_norm_le_four (T : ℂ → ℂ) (D : ℝ) (c : ℂ)
    (hD : 0<D) (ha : AnalyticOnNhd ℂ T (symmetricStrip D))
    (hb : ∀z∈symmetricStrip D, ‖T z-z-c‖≤2) :
    ∀z∈symmetricStrip D, ‖meanRemoved T z-z‖≤4 := by
  have hm := mean_sub_constant_bound T D c hD ha hb
  intro z hz
  have he : meanRemoved T z-z=(T z-z-c)-(gateFourierCoefficient 0 0 T-c) := by
    unfold meanRemoved
    ring
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith [hb z hz])

theorem outer_width_positive
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) :
    2<outerWidth θ Y P ∧ 0<decayWidth θ Y P := by
  have hh : 16*Y≤height θ := by
    unfold height
    apply (le_div_iff₀ hc.theta_pos).mpr
    nlinarith only [hc.very_strong_width]
  have hP : 0≤P := (norm_nonneg (e₁ s)).trans hc.first_model_bound
  have hB : boundaryMargin P+2<Y := by dsimp [boundaryMargin]; linarith only [hc.phase_margin_buffer]
  have h2P : 2*P≤boundaryMargin P := by dsimp [boundaryMargin]; linarith [Real.pi_pos]
  have ho : 2<outerWidth θ Y P := by
    dsimp [outerWidth,boundaryLoss]
    linarith only [hh,hB,h2P,hc.height_large]
  exact ⟨ho,by dsimp [decayWidth]; linarith⟩

theorem normalized_shift_mem_target
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r : ℝ)
    (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (har : a<r) (hrb : r<b) (z : ℂ) (hz : z∈symmetricStrip (outerWidth θ Y P)) :
    z+repellingConstant A B Γ s a b θ r (e₁ s) (e₂ s)∈strip θ (3*Y+boundaryMargin P) := by
  obtain ⟨hphase,hbound⟩ := repellingConstant_phase_of_control e₁ e₂ A B Γ s a b θ Y η M P r hs1 hc har hrb
  have hzi := abs_lt.mp (show |z.im|<outerWidth θ Y P from hz)
  have hbi := abs_le.mp hbound
  change 3*Y+boundaryMargin P<(z+repellingConstant A B Γ s a b θ r (e₁ s) (e₂ s)).im ∧
    (z+repellingConstant A B Γ s a b θ r (e₁ s) (e₂ s)).im<height θ-(3*Y+boundaryMargin P)
  rw [Complex.add_im,hphase]
  dsimp [outerWidth,boundaryLoss] at hzi
  exact ⟨by linarith only [hzi.1,hbi.1],by linarith only [hzi.2,hbi.2]⟩

theorem actual_normalized_transition_bounds
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r₀ r : ℝ)
    (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (har : a<r) (hrb : r<b) (V : ℂ → ℂ)
    (hV : AnalyticOnNhd ℂ V (strip θ (3*Y+boundaryMargin P)))
    (hVs : ∀w∈strip θ (3*Y+boundaryMargin P), V w∈strip θ (3*Y) ∧
      repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w)=w) :
    AnalyticOnNhd ℂ (transition A B Γ s a b θ r₀ r (e₁ s) (e₂ s) V)
      (symmetricStrip (outerWidth θ Y P)) ∧
    (∀z∈symmetricStrip (outerWidth θ Y P),
      transition A B Γ s a b θ r₀ r (e₁ s) (e₂ s) V (z+1)=
        transition A B Γ s a b θ r₀ r (e₁ s) (e₂ s) V z+1) ∧
    ∀z∈symmetricStrip (outerWidth θ Y P),
      ‖transition A B Γ s a b θ r₀ r (e₁ s) (e₂ s) V z-z-
        (repellingConstant A B Γ s a b θ r (e₁ s) (e₂ s)-
          (koenigsTime s a r₀+modelConstant s a b (e₁ s) (e₂ s)))‖≤2 := by
  let c := repellingConstant A B Γ s a b θ r (e₁ s) (e₂ s)
  let cp := koenigsTime s a r₀+modelConstant s a b (e₁ s) (e₂ s)
  have hp := Kneser.ActualGrowingTransition.actual_transition_properties e₁ e₂ A B Γ s a b θ Y η M P hc V hV hVs
  refine ⟨?_,?_,?_⟩
  · intro z hz
    have hshift := normalized_shift_mem_target e₁ e₂ A B Γ s a b θ Y η M P r hs1 hc har hrb z hz
    have hcomp := (hp.1 _ hshift).comp (f:=fun w : ℂ => w+c) (analyticAt_id.add analyticAt_const)
    exact hcomp.sub analyticAt_const
  · intro z hz
    have hshift := normalized_shift_mem_target e₁ e₂ A B Γ s a b θ Y η M P r hs1 hc har hrb z hz
    have hperiod := Kneser.ActualGrowingPeriodicity.actual_transition_translation e₁ e₂ A B Γ s a b θ Y η M P hs1 hc V hVs (z+c) hshift
    change Kneser.ActualGrowingTransition.transition A B Γ s a b θ (e₁ s) (e₂ s) V (z+1+c)-cp=
      Kneser.ActualGrowingTransition.transition A B Γ s a b θ (e₁ s) (e₂ s) V (z+c)-cp+1
    rw [show z+1+c=z+c+1 by ring,hperiod]
    ring
  · intro z hz
    have hshift := normalized_shift_mem_target e₁ e₂ A B Γ s a b θ Y η M P r hs1 hc har hrb z hz
    exact Kneser.ActualGrowingTransition.normalized_transition_displacement A B Γ s a b θ (e₁ s) (e₂ s) V cp c z
      (hp.2.2.2 _ hshift).1


/-- The actual normalization uses the true Koenigs orbit limit at the
real anchor and the actual repelling value at an interior real point.
All Fourier coefficients here are the actual interval integrals. -/
theorem actual_normalized_fourier
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r₀ r : ℝ)
    (hs : 0<s) (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (hr₀ : r₀<a) (har : a<r) (hrb : r<b) (V : ℂ → ℂ)
    (hV : AnalyticOnNhd ℂ V (strip θ (3*Y+boundaryMargin P)))
    (hVs : ∀w∈strip θ (3*Y+boundaryMargin P), V w∈strip θ (3*Y) ∧
      repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w)=w) :
    let T := transition A B Γ s a b θ r₀ r (e₁ s) (e₂ s) V
    0<decayWidth θ Y P ∧
    (gateFourierCoefficient 0 0 T).im=height θ/2 ∧
    (∀x : ℝ, (T x).im=height θ/2) ∧
    gateFourierCoefficient 0 0 (meanRemoved T)=0 ∧
    (∀n : ℤ, n≠0 → gateFourierCoefficient n 0 (meanRemoved T)=gateFourierCoefficient n 0 T) ∧
    (∀z∈symmetricStrip (outerWidth θ Y P), ‖meanRemoved T z-z‖≤4) ∧
    (∀n : ℤ, ‖gateFourierCoefficient n 0 (meanRemoved T)‖≤
      4*Real.exp (-2*Real.pi*decayWidth θ Y P*|(n:ℝ)|)) ∧
    ∀z : ℂ, |z.im|<decayWidth θ Y P → HasSum (fun n : ℤ =>
      gateFourierCoefficient n 0 (meanRemoved T)*exp (Kneser.fourierFrequency n*z))
      (T z-z-gateFourierCoefficient 0 0 T) := by
  let T := transition A B Γ s a b θ r₀ r (e₁ s) (e₂ s) V
  let c := repellingConstant A B Γ s a b θ r (e₁ s) (e₂ s)-
    (koenigsTime s a r₀+modelConstant s a b (e₁ s) (e₂ s))
  have hw := outer_width_positive e₁ e₂ A B Γ s a b θ Y η M P hc
  have hD : 0<outerWidth θ Y P := by linarith only [hw.1]
  have hdD : decayWidth θ Y P<outerWidth θ Y P := by unfold decayWidth; linarith
  obtain ⟨ha,hp,hb⟩ := actual_normalized_transition_bounds e₁ e₂ A B Γ s a b θ Y η M P r₀ r hs1 hc har hrb V hV hVs
  have hcont : ContinuousOn (fun x : ℝ => T (x:ℂ)) (Icc 0 1) := by
    intro x _
    have hx : (x:ℂ)∈symmetricStrip (outerWidth θ Y P) := by simpa [symmetricStrip] using hD
    exact ((ha _ hx).continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hremoved : AnalyticOnNhd ℂ (meanRemoved T) (symmetricStrip (outerWidth θ Y P)) :=
    fun z hz => (ha z hz).sub analyticAt_const
  have hremovedperiod : ∀z∈symmetricStrip (outerWidth θ Y P), meanRemoved T (z+1)=meanRemoved T z+1 := by
    intro z hz
    change T (z+1)-gateFourierCoefficient 0 0 T=T z-gateFourierCoefficient 0 0 T+1
    have htp : T (z+1)=T z+1 := hp z hz
    rw [htp]
    ring
  have hnorm := mean_removed_norm_le_four T (outerWidth θ Y P) c hD ha hb
  have hfourier := actual_integral_decay_and_reconstruction (meanRemoved T)
    (outerWidth θ Y P) (decayWidth θ Y P) 4 hw.2 hdD (by norm_num) hremoved hremovedperiod hnorm
  refine ⟨hw.2,actual_transition_fourier_mean_phase e₁ e₂ A B Γ s a b θ Y η M P r₀ r hs hs1 hc hr₀ har hrb V hV hVs,
    actual_transition_real_phase e₁ e₂ A B Γ s a b θ Y η M P r₀ r hs hs1 hc hr₀ har hrb V hVs,
    mean_removed_zero T hcont,(fun n hn => mean_removed_nonzero T n hn hcont),hnorm,hfourier.1,?_⟩
  intro z hz
  convert hfourier.2 z hz using 1
  unfold meanRemoved
  ring

theorem actual_anchor_left_of_control
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) :
    Kneser.RealNormalizationAnchor.realAnchor<a := by
  have he : 2<Real.exp 1 := by
    have hh := Real.add_one_lt_exp (by norm_num : (1:ℝ)≠0)
    norm_num at hh ⊢
    exact hh
  have hneg : Real.exp (-1)<1/2 := by
    rw [Real.exp_neg]
    rw [inv_eq_one_div]
    exact (div_lt_iff₀ (Real.exp_pos _)).mpr (by linarith)
  have ha := (abs_le.mp hc.left_small).1
  dsimp [Kneser.RealNormalizationAnchor.realAnchor]
  linarith only [hneg,ha,hc.radius_small]

/-- One preparation, the actual anchor exp(-1)-1, an actual interior
repelling normalization, exact half-height mean, and full-width decay
for every integral Fourier mode. -/
theorem exists_actual_normalized_growing_fourier
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ Y s₀ η M P : ℝ, 2≤Y ∧ 0<s₀ ∧ s₀≤1/2 ∧
      ∀s : ℝ, 0<s → s<s₀ → ∃a b θ : ℝ, ∃V : ℂ → ℂ,
        LensControl e₁ e₂ A B Γ s a b θ Y η M P ∧
        AnalyticOnNhd ℂ V (strip θ (3*Y+boundaryMargin P)) ∧
        (∀w∈strip θ (3*Y+boundaryMargin P), V w∈strip θ (3*Y) ∧
          repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w)=w) ∧
        let T := transition A B Γ s a b θ Kneser.RealNormalizationAnchor.realAnchor ((a+b)/2) (e₁ s) (e₂ s) V
        0<decayWidth θ Y P ∧
        (gateFourierCoefficient 0 0 T).im=height θ/2 ∧
        (∀x : ℝ, (T x).im=height θ/2) ∧
        gateFourierCoefficient 0 0 (meanRemoved T)=0 ∧
        (∀n : ℤ, n≠0 → gateFourierCoefficient n 0 (meanRemoved T)=gateFourierCoefficient n 0 T) ∧
        (∀z∈symmetricStrip (outerWidth θ Y P), ‖meanRemoved T z-z‖≤4) ∧
        (∀n : ℤ, ‖gateFourierCoefficient n 0 (meanRemoved T)‖≤
          4*Real.exp (-2*Real.pi*decayWidth θ Y P*|(n:ℝ)|)) ∧
        ∀z : ℂ, |z.im|<decayWidth θ Y P → HasSum (fun n : ℤ =>
          gateFourierCoefficient n 0 (meanRemoved T)*exp (Kneser.fourierFrequency n*z))
          (T z-z-gateFourierCoefficient 0 0 T) := by
  obtain ⟨Y,s₀,η,M,P,hY,hs₀,hs₀h,hall⟩ := exists_actual_lens_control U H e₁ e₂ A B K F Γ hdata
  refine ⟨Y,s₀,η,M,P,hY,hs₀,hs₀h,?_⟩
  intro s hs hss
  obtain ⟨a,b,θ,hc⟩ := hall s hs hss
  obtain ⟨_Vp,V,_hVp,hV,_hspecp,hspec⟩ := actual_bilateral_holomorphic_strip_inverses e₁ e₂ A B Γ s a b θ Y η M P hc
  have hs1 : s<1 := by linarith [hss.trans_le hs₀h]
  have har : a<(a+b)/2 := by linarith [hc.left_neg,hc.right_pos]
  have hrb : (a+b)/2<b := by linarith [hc.left_neg,hc.right_pos]
  exact ⟨a,b,θ,V,hc,hV,hspec,actual_normalized_fourier e₁ e₂ A B Γ s a b θ Y η M P
    Kneser.RealNormalizationAnchor.realAnchor ((a+b)/2) hs hs1 hc
    (actual_anchor_left_of_control e₁ e₂ A B Γ s a b θ Y η M P hc) har hrb V hV hspec⟩

end Kneser.NormalizedGrowingFourier
end
