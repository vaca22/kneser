import Kneser.ActualRepellingRealGeometry
import Kneser.RealKoenigsFourierMean

/-! True real normalizations and the exact Fourier mean phase for the
actual growing transition. All real inverse points are derived from
actual holomorphic coverage, reflection and injectivity. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
namespace Kneser.ActualNormalizedGrowingTransition
open Set Metric Filter Complex
open Kneser.ExponentialUnfolding Kneser.PositiveKoenigsOrbit Kneser.PositiveKoenigsAbel
open Kneser.ActualLensModel Kneser.GrowingBandGeometry Kneser.GrowingLensSpatialHolomorphy
open Kneser.ActualGrowingRealPhases Kneser.ActualHolomorphicGrowingLens
open Kneser.ActualGrowingKoenigsIdentification Kneser.RealRepellingCoordinatePhase
open Kneser.ActualGrowingCoordinateInverse Kneser.ActualRepellingRealGeometry
open Kneser.ActualKoenigsEntryRealPhase Kneser.ActualKoenigsGlobalRealPhase
open Kneser.ActualKoenigsRealPhase Kneser.ActualKoenigsUpperBranch
open Kneser.GrowingLensCoordinateRegularity Kneser.RealKoenigsFourierMean
open Kneser.ReflectedOrbitChainCoefficient Kneser.QuantitativeHornExpansion Kneser.GateFourierDerivative
open scoped Topology BigOperators

def repellingConstant (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ r : ℝ) (e₁ e₂ : ℂ) : ℂ :=
  physicalRepelling A B Γ s a b θ e₁ e₂ r

def transition (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ r₀ r : ℝ)
    (e₁ e₂ : ℂ) (V : ℂ → ℂ) (w : ℂ) : ℂ :=
  normalizedAttracting A B Γ s a b θ r₀ e₁ e₂
    (V (w+repellingConstant A B Γ s a b θ r e₁ e₂))

theorem polynomialImag_bound (e₁ e₂ : ℂ) (b P : ℝ) (hP : 0≤P)
    (h₁ : ‖e₁‖≤P) (h₂ : ‖e₂‖≤P) (hb : |b|≤1) :
    |polynomialImag e₁ e₂ b|≤2*P := by
  have hi₁ := (Complex.abs_im_le_norm e₁).trans h₁
  have hi₂ := (Complex.abs_im_le_norm e₂).trans h₂
  have hb2 : |b^2|≤1 := by rw [abs_pow]; nlinarith [abs_nonneg b]
  unfold polynomialImag
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul]
  have h1 := mul_le_mul hi₁ hb (abs_nonneg b) hP
  have h2 := mul_le_mul hi₂ hb2 (abs_nonneg (b^2)) hP
  nlinarith

theorem repellingConstant_phase_of_control
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r : ℝ)
    (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (har : a<r) (hrb : r<b) :
    (repellingConstant A B Γ s a b θ r (e₁ s) (e₂ s)).im=
      height θ/2+polynomialImag (e₁ s) (e₂ s) b ∧
      |polynomialImag (e₁ s) (e₂ s) b|≤2*P := by
  have hP : 0≤P := (norm_nonneg (e₁ s)).trans hc.first_model_bound
  have hb1 : |b|≤1 := hc.right_small.trans (by linarith [hc.radius_small])
  refine ⟨?_,polynomialImag_bound (e₁ s) (e₂ s) b P hP hc.first_model_bound hc.second_model_bound hb1⟩
  have hh := (actual_real_phases_of_control e₁ e₂ A B Γ s a b θ Y η M P r hs1 hc har hrb).2
  change (physicalRepelling A B Γ s a b θ (e₁ s) (e₂ s) r).im= _
  rw [hh]
  unfold height
  congr 1
  ring

theorem real_shift_mem_inverse_target
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r x : ℝ)
    (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (har : a<r) (hrb : r<b) :
    (x:ℂ)+repellingConstant A B Γ s a b θ r (e₁ s) (e₂ s)∈strip θ (3*Y+boundaryMargin P) := by
  obtain ⟨hphase,hbound⟩ := repellingConstant_phase_of_control e₁ e₂ A B Γ s a b θ Y η M P r hs1 hc har hrb
  have hheight : 16*Y≤height θ := by
    unfold height
    apply (le_div_iff₀ hc.theta_pos).mpr
    nlinarith [hc.very_strong_width]
  have hP : 0≤P := (norm_nonneg (e₁ s)).trans hc.first_model_bound
  have hB : boundaryMargin P<Y := hc.phase_margin
  have h2P : 2*P<Y := by dsimp [boundaryMargin] at hB; linarith [Real.pi_pos]
  simp only [strip,mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,zero_add,hphase]
  constructor <;> linarith [(abs_le.mp hbound).1,(abs_le.mp hbound).2]

theorem koenigsTime_real_left_im (s a r₀ : ℝ)
    (hneg : (koenigsValue s a r₀).im=0 ∧ (koenigsValue s a r₀).re<0) :
    (koenigsTime s a r₀).im=0 := by
  have he : -koenigsValue s a r₀=(-(koenigsValue s a r₀).re:ℂ) := by apply Complex.ext <;> simp [hneg.1]
  have harg : Complex.arg (-koenigsValue s a r₀)=0 := by
    rw [he,←Complex.ofReal_neg]
    exact Complex.arg_ofReal_of_nonneg (by linarith [hneg.2])
  simp only [koenigsTime,Complex.div_ofReal_im,Complex.log_im,harg,zero_div]

theorem normalizedAttracting_midline_phase_of_control
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r₀ x : ℝ)
    (hs : 0<s) (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (hr₀ : r₀<a) :
    (normalizedAttracting A B Γ s a b θ r₀ (e₁ s) (e₂ s)
      ((x:ℂ)+((Real.pi/θ:ℝ):ℂ)*I)).im=height θ/2 := by
  have ha := real_root_gt_neg_one s a hc.left_fixed
  have hμ : 0<multiplier s a := by unfold multiplier; exact mul_pos (by linarith) (by linarith)
  have hμ1 : multiplier s a<1 := by unfold multiplier; nlinarith [hc.left_neg]
  have hlim₀ := real_left_orbit_limit s a r₀ hs1 ha hc.left_fixed hμ.le hμ1 hr₀
  have hsum₀ := actual_koenigs_sum_of_orbit_limit s a r₀ hs.le hs1 ha hc.left_neg.le hc.left_fixed hμ hμ1 hlim₀
  have hneg := koenigsValue_negative_left s a r₀ hs.le hs1 ha hc.left_neg.le hc.left_fixed hμ hμ1 hsum₀ hlim₀ hr₀
  have hb := bandChart_midline_between a b θ x (by linarith [hc.left_neg,hc.right_pos]) hc.theta_pos
  let v : ℝ := (a+b*Real.exp (-θ*x))/(1+Real.exp (-θ*x))
  have he : bandChart a b θ ((x:ℂ)+((Real.pi/θ:ℝ):ℂ)*I)=(v:ℂ) := bandChart_midline a b θ x hc.theta_pos
  have hav : a<v := by simpa only [he,Complex.ofReal_re] using hb.1
  have hvb : v<b := by simpa only [he,Complex.ofReal_re] using hb.2
  have hlim := Kneser.GrowingLensKoenigs.lensControl_forward_limit e₁ e₂ A B Γ s a b θ Y η M P hc v
    ⟨_,midline_mem_strip θ Y x hc.theta_pos hc.width,he⟩
  have hsum := actual_koenigs_sum_of_orbit_limit s a v hs.le hs1 ha hc.left_neg.le hc.left_fixed hμ hμ1 hlim
  have hpos := koenigsValue_positive_between s a b v hs.le hs1 ha hc.left_neg.le hc.left_fixed hc.right_fixed hμ hμ1 hsum hlim hav hvb
  rw [normalizedAttracting_midline_eq_upperTime e₁ e₂ A B Γ s a b θ Y η M P r₀ x hs hs1 hc,he]
  rw [upperTime_half_height s a v r₀ hpos hneg,←hc.theta_actual]
  unfold height
  ring

/-- Every real value of the actual normalized repelling inverse lies on
the physical real interval, and the actual transition there has exactly
half of the genuine attracting multiplier height. -/
theorem actual_transition_real_phase
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r₀ r : ℝ)
    (hs : 0<s) (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (hr₀ : r₀<a) (har : a<r) (hrb : r<b) (V : ℂ → ℂ)
    (hV : ∀ w∈strip θ (3*Y+boundaryMargin P), V w∈strip θ (3*Y) ∧
      repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w)=w) :
    ∀ x : ℝ, (transition A B Γ s a b θ r₀ r (e₁ s) (e₂ s) V x).im=height θ/2 := by
  intro x
  let c := repellingConstant A B Γ s a b θ r (e₁ s) (e₂ s)
  have hx := real_shift_mem_inverse_target e₁ e₂ A B Γ s a b θ Y η M P r x hs1 hc har hrb
  have hv := hV ((x:ℂ)+c) hx
  have hsource : V ((x:ℂ)+c)∈strip θ (2*Y) := ⟨by linarith [hv.1.1,hc.height_large],by linarith [hv.1.2,hc.height_large]⟩
  have hreal : (normalizedRepelling A B Γ s a b θ r (e₁ s) (e₂ s) (V ((x:ℂ)+c))).im=0 := by
    unfold normalizedRepelling
    rw [hv.2]
    change ((x:ℂ)+c-c).im=0
    simp
  have hgeo := actual_normalizedRepelling_real_preimage e₁ e₂ A B Γ s a b θ Y η M P r hs1 hc har hrb _ hsource hreal
  have he : V ((x:ℂ)+c)=((V ((x:ℂ)+c)).re:ℂ)+((Real.pi/θ:ℝ):ℂ)*I := by
    apply Complex.ext
    · simp
    · simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add]
      rw [hgeo.1]
      unfold height
      ring
  unfold transition
  change (normalizedAttracting A B Γ s a b θ r₀ (e₁ s) (e₂ s) (V ((x:ℂ)+c))).im= _
  rw [he]
  exact normalizedAttracting_midline_phase_of_control e₁ e₂ A B Γ s a b θ Y η M P r₀ _ hs hs1 hc hr₀

/-- Holomorphy of the actual inverse supplies the continuous real trace
needed by the Fourier integral. The exact half-height is derived above. -/
theorem actual_transition_fourier_mean_phase
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r₀ r : ℝ)
    (hs : 0<s) (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (hr₀ : r₀<a) (har : a<r) (hrb : r<b) (V : ℂ → ℂ)
    (hVan : AnalyticOnNhd ℂ V (strip θ (3*Y+boundaryMargin P)))
    (hV : ∀ w∈strip θ (3*Y+boundaryMargin P), V w∈strip θ (3*Y) ∧
      repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w)=w) :
    (gateFourierCoefficient 0 0 (transition A B Γ s a b θ r₀ r (e₁ s) (e₂ s) V)).im=height θ/2 := by
  have hN := (normalizedAttracting_exponential_of_control e₁ e₂ A B Γ s a b θ Y η M P r₀ hs hs1 hc hr₀).1
  have hT : ∀ x : ℝ, AnalyticAt ℂ (transition A B Γ s a b θ r₀ r (e₁ s) (e₂ s) V) (x:ℂ) := by
    intro x
    let c := repellingConstant A B Γ s a b θ r (e₁ s) (e₂ s)
    have hx := real_shift_mem_inverse_target e₁ e₂ A B Γ s a b θ Y η M P r x hs1 hc har hrb
    have hv := hV ((x:ℂ)+c) hx
    have hvY : V ((x:ℂ)+c)∈strip θ Y := ⟨by linarith [hv.1.1,hc.height_large],by linarith [hv.1.2,hc.height_large]⟩
    have hshift : AnalyticAt ℂ (fun W : ℂ => W+c) (x:ℂ) := analyticAt_id.add analyticAt_const
    have hvc : AnalyticAt ℂ (fun W : ℂ => V (W+c)) (x:ℂ) :=
      (hVan _ hx).comp (f:=fun W : ℂ => W+c) hshift
    exact (hN _ hvY).comp (f:=fun W : ℂ => V (W+c)) hvc
  apply mean_im_of_real_phase _ (height θ/2)
  · intro x hx
    exact ((hT x).continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  · intro x hx
    exact actual_transition_real_phase e₁ e₂ A B Γ s a b θ Y η M P r₀ r hs hs1 hc hr₀ har hrb V hV x

/-- Actual preparation constructs a genuine inverse transition with the
correct Koenigs logarithm, real repelling normalization and exact mean
phase. No real-inverse or half-height condition is an input. -/
theorem exists_actual_normalized_growing_transition
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ Y s₀ η M P : ℝ, 2≤Y ∧ 0<s₀ ∧ s₀≤1/2 ∧
      ∀ s : ℝ, 0<s → s<s₀ → ∃ a b θ : ℝ,
        LensControl e₁ e₂ A B Γ s a b θ Y η M P ∧
        ∀ r₀ r : ℝ, r₀<a → a<r → r<b → ∃ V : ℂ → ℂ,
          AnalyticOnNhd ℂ V (strip θ (3*Y+boundaryMargin P)) ∧
          (∀ w∈strip θ (3*Y+boundaryMargin P), V w∈strip θ (3*Y) ∧
            repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w)=w) ∧
          (∀ x : ℝ, (transition A B Γ s a b θ r₀ r (e₁ s) (e₂ s) V x).im=height θ/2) ∧
          (gateFourierCoefficient 0 0 (transition A B Γ s a b θ r₀ r (e₁ s) (e₂ s) V)).im=height θ/2 := by
  obtain ⟨Y,s₀,η,M,P,hY,hs₀,hs₀h,hall⟩ := exists_actual_lens_control U H e₁ e₂ A B K F Γ hdata
  refine ⟨Y,s₀,η,M,P,hY,hs₀,hs₀h,?_⟩
  intro s hs hss
  obtain ⟨a,b,θ,hc⟩ := hall s hs hss
  refine ⟨a,b,θ,hc,?_⟩
  intro r₀ r hr₀ har hrb
  obtain ⟨Vplus,V,hVp,hV,hsp,hsv⟩ := actual_bilateral_holomorphic_strip_inverses e₁ e₂ A B Γ s a b θ Y η M P hc
  have hs1 : s<1 := by linarith [hss.trans_le hs₀h]
  exact ⟨V,hV,hsv,
    actual_transition_real_phase e₁ e₂ A B Γ s a b θ Y η M P r₀ r hs hs1 hc hr₀ har hrb V hsv,
    actual_transition_fourier_mean_phase e₁ e₂ A B Γ s a b θ Y η M P r₀ r hs hs1 hc hr₀ har hrb V hV hsv⟩

end Kneser.ActualNormalizedGrowingTransition
end
