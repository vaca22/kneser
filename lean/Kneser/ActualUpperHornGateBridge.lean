import Kneser.CenteredUpperHornMean
import Kneser.ActualCanonicalFourierExpansion
import Kneser.CanonicalDepthIndependence

/-! The actual centered gate transition is the canonical upper horn,
with its true complex origin and real normalization anchor. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Kneser.ActualUpperHornGateBridge
open Filter Set Metric Complex
open Kneser.ReflectedOrbitChainCoefficient Kneser.ActualDeepCoordinateData Kneser.ActualGateAbel
open Kneser.ActualQuantitativeGateTransition Kneser.CanonicalBasinExtension
open Kneser.UpperCanonicalInjectivity Kneser.CanonicalHighImaginaryAsymptotics
open Kneser.CanonicalUpperHornCharts Kneser.HolomorphicInjectiveInverse
open Kneser.PeriodicChartGluing Kneser.PeriodicHornGlobal Kneser.LocalPeriodicStrip
open Kneser.CenteredUpperHornMean Kneser.GateFourierDerivative
open Kneser.ParabolicExponentialOrbit
open scoped Topology

theorem gate_center_actual
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R Rₛ : ℝ)
    (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ)
    (hs : CanonicalSeedData Rₛ) (hRR : Rₛ≤R)
    (ht : ActualTransitionData U H e₁ e₂ A B Γ R N M Y V) :
    FullCanonicalImageGate.canonicalGateInZeta N (ActualQuantitativeGateTransition.chartCenter Y)-
      (Real.pi:ℂ)*I/3=imageCenter Rₛ Y := by
  have h0 : (0:ℂ)∈closedBall (0:ℂ) 64 := by simp
  have hu := chartPoint_in_gate N Y ht.height 0 h0
  have hb := backward_zero_eq_global U H e₁ e₂ A B Γ R Rₛ N hs hRR ht.bilateral _ hu
  have hc : ActualBilateralGate.backwardCoordinate U H e₁ e₂ A B Γ N (chartPoint Y 0) 0=
      FullCanonicalImageGate.canonicalGateInZeta N (ActualQuantitativeGateTransition.chartCenter Y) := by
    rw [(ht.bilateral.canonical _ hu).2,FullCanonicalImageGate.canonicalGateInZeta_eq]
    simp only [chartPoint,add_zero,FiniteGateJacobian.transportedRepellingCoordinate]
  rw [hb] at hc
  dsimp [imageCenter,repellingZeta,upperRepelling,CanonicalUpperHornCharts.center]
  rw [←hc]
  simp only [chartPoint,ActualQuantitativeGateTransition.chartCenter,add_zero]

theorem actual_gate_eq_upper_horn
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R Rₛ Y₁ Y₀ : ℝ)
    (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ) (G : ℂ → ℂ)
    (hs : CanonicalSeedData Rₛ) (hRR : Rₛ≤R)
    (hd : DeepCoordinateData U H e₁ e₂ A B Γ R)
    (ht : ActualTransitionData U H e₁ e₂ A B Γ R N M Y V)
    (hi : InjOn (repellingZeta Rₛ) (region 32 Y₁))
    (hY₀ : Y₀<Y) (hY₁ : Y₁+16<Y)
    (hpatch : ∀ Y, Y₀<Y → ∀ z∈chartStrip (imageCenter Rₛ Y),
      G z=patch (hornOnImage Rₛ Y₁) (imageCenter Rₛ Y) z)
    (hp : ∀ w∈ball (0:ℂ) 2,
      hornOnImage Rₛ Y₁ (imageCenter Rₛ Y+(w+1))=hornOnImage Rₛ Y₁ (imageCenter Rₛ Y+w)+1)
    (w : ℂ) (hw : w∈ball (0:ℂ) 2) (hws : w∈strip) :
    transitionValue U H e₁ e₂ A B Γ N M Y V 0 w=
      G (imageCenter Rₛ Y+w)-globalAttracting Rₛ RealNormalizationAnchor.normalizationAnchor := by
  have hw4 : w∈ball (0:ℂ) 4 := ball_subset_ball (by norm_num) hw
  let z : ℂ := CanonicalUpperHornCharts.center Y+V 0 w
  have hn : ‖V 0 w‖≤16 := by simpa only [mem_closedBall,dist_zero_right] using (ht.inverse_zero w hw4).1
  have hz : z∈region 32 Y₁ := by
    constructor
    · have hh := (Complex.abs_re_le_norm (V 0 w)).trans hn
      simp only [z,CanonicalUpperHornCharts.center,Complex.add_re,Complex.mul_re,Complex.I_re,
        Complex.ofReal_re,zero_mul,Complex.I_im,Complex.ofReal_im,mul_zero,sub_self,zero_add]
      linarith
    · have hh := (abs_le.mp ((Complex.abs_im_le_norm (V 0 w)).trans hn)).1
      simp only [z,CanonicalUpperHornCharts.center,Complex.add_im,Complex.mul_im,Complex.I_re,
        Complex.ofReal_im,zero_mul,Complex.I_im,Complex.ofReal_re,one_mul,zero_add]
      linarith
  have he := transition_zero_eq_global U H e₁ e₂ A B Γ R Rₛ N M Y V hs hRR hd ht w hw4
  have hc := gate_center_actual U H e₁ e₂ A B Γ R Rₛ N M Y V hs hRR ht
  have hS : repellingZeta Rₛ z=imageCenter Rₛ Y+w := by
    change globalRepelling Rₛ (inverseCoordinate z)-(Real.pi:ℂ)*I/3=_
    have hzarg : inverseCoordinate z=chartPoint Y (V 0 w) := rfl
    rw [hzarg,he.2]
    linear_combination hc
  have hInv := imageInverse_left (repellingZeta Rₛ) (region 32 Y₁) hi z hz
  rw [hS] at hInv
  have hH : hornOnImage Rₛ Y₁ (imageCenter Rₛ Y+w)=globalAttracting Rₛ (chartPoint Y (V 0 w)) := by
    dsimp only [hornOnImage]
    rw [hInv]
    rfl
  have hstrip : imageCenter Rₛ Y+w∈chartStrip (imageCenter Rₛ Y) := by
    simpa only [chartStrip,strip,Set.mem_setOf_eq,add_sub_cancel_left] using hws
  have hG : G (imageCenter Rₛ Y+w)=hornOnImage Rₛ Y₁ (imageCenter Rₛ Y+w) := by
    rw [hpatch Y hY₀ _ hstrip]
    exact patch_eq_of_small _ _ _ hp (by simpa only [add_sub_cancel_left] using hw) hstrip
  rw [he.1,←hH,←hG]

/-- A genuine deeper chart of the same prepared coordinate is identified
with the canonical upper horn. Its raw zero mode has the actual gauge. -/
theorem exists_actual_upper_horn_gate_bridge :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      ActualPreparationData U H e₁ e₂ A B K F Γ ∧
      ∃ Rₛ R Y₁ Y₀ Mh Ch : ℝ, ∃ G : ℂ → ℂ,
      CanonicalSeedData Rₛ ∧ Rₛ≤R ∧
      DeepCoordinateData U H e₁ e₂ A B Γ R ∧ LocalAbelData U H e₁ e₂ A B Γ R ∧
      G=globalHorn (hornOnImage Rₛ Y₁) (imageCenter Rₛ) Y₀ ∧
      17≤Y₀ ∧ 0≤Mh ∧ 0≤Ch ∧
      (∀ z : ℂ, Y₀+Mh+18<z.im → ‖G z-z‖≤Ch/(z.im-Mh-17)) ∧
      AnalyticOnNhd ℂ G {z : ℂ | Y₀+Mh+2<z.im} ∧
      (∀ z : ℂ, G (z+1)=G z+1) ∧
      (∀ n : ℤ, n≤0 → ∀ Y : ℝ, Y₀+Mh+18<Y → gateFourierCoefficient n Y G=0) ∧
      ∃ (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ),
      ActualTransitionData U H e₁ e₂ A B Γ R N M Y V ∧
      ActualFourierExpansion.AbsoluteGateCoefficientData U H e₁ e₂ A B Γ N M Y V ∧
      ActualStripTransition.StripTransitionData (transitionValue U H e₁ e₂ A B Γ N M Y V)
        (transitionCorrection U H e₁ e₂ A B Γ N M Y V) ∧
      (∀ w∈strip, LocalPeriodicStrip.lift (transitionValue U H e₁ e₂ A B Γ N M Y V 0) w=
        G (imageCenter Rₛ Y+w)-globalAttracting Rₛ RealNormalizationAnchor.normalizationAnchor) ∧
      gateFourierCoefficient 0 0 (transitionValue U H e₁ e₂ A B Γ N M Y V 0)=
        FullCanonicalImageGate.canonicalGateInZeta N (ActualQuantitativeGateTransition.chartCenter Y)-
          (Real.pi:ℂ)*I/3-globalAttracting Rₛ RealNormalizationAnchor.normalizationAnchor ∧
      ∃ Vroot p Rp : ℂ → ℂ,
        ActualFourierExpansion.FourierExpansionData
          (fun s => LocalPeriodicStrip.lift (transitionValue U H e₁ e₂ A B Γ N M Y V s))
          (periodize (transitionCorrection U H e₁ e₂ A B Γ N M Y V)) Vroot p Rp := by
  obtain ⟨U,H,e₁,e₂,A,B,K,F,Γ,hdata,R₀,hd₀,hl₀⟩ := exists_actual_deep_abel_data
  let Rₛ : ℝ := R₀+2
  have hs : CanonicalSeedData Rₛ := canonical_seed_of_deep U H e₁ e₂ A B Γ R₀ hd₀ hl₀
  obtain ⟨Y₁,Y₀,Mh,Ch,G,hdef,h17,hMh,hCh,hi,hcp,ha,hp,hpatch,_hactual,hbound⟩ :=
    ActualGlobalUpperHorn.exists_actual_global_upper_horn Rₛ hs
  obtain ⟨Yg,Mc,hMc,_hcc,hcb,_hclose,_hsep⟩ := ActualUpperHornCenters.exists_actual_centers_geometry Rₛ hs
  let R : ℝ := max Rₛ (max (Y₀+Mh+Mc+100) (max (Y₁+32) (Yg+32)))
  have hRR : Rₛ≤R := le_max_left _ _
  have hR₀ : R₀≤R := by
    have hh : R₀≤Rₛ := by dsimp [Rₛ]; linarith
    exact hh.trans hRR
  have hd : DeepCoordinateData U H e₁ e₂ A B Γ R := hd₀.mono hR₀
  have hl : LocalAbelData U H e₁ e₂ A B Γ R := hl₀.mono hR₀
  obtain ⟨N,M,Y,V,ht⟩ := exists_transition_data_of_deep U H e₁ e₂ A B Γ R hd
  have hRY : R+100<Y := by linarith [ht.length_margin,ht.height,Nat.cast_nonneg (α:=ℝ) N]
  have hRg : Yg+32≤R := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hR₁ : Y₁+32≤R := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hR₀b : Y₀+Mh+Mc+100≤R := (le_max_left _ _).trans (le_max_right _ _)
  have hY : Y₀<Y := by linarith
  have hY₁ : Y₁+16<Y := by linarith
  have hcim : Y₀+Mh+18<(imageCenter Rₛ Y).im := by
    have hh := (abs_le.mp (hcb Y (by linarith : Yg<Y))).1
    linarith
  have hzero : ∀ n : ℤ, n≤0 → ∀ Y : ℝ, Y₀+Mh+18<Y → gateFourierCoefficient n Y G=0 := by
    intro n hn Z hZ
    apply UpperHornVanishingModes.nonpositive_coefficient_zero G (Y₀+Mh+18) (Mh+17) Ch
      (by linarith) (by linarith) hCh
      (ha.mono (by intro z hz; change Y₀+Mh+2<z.im; change Y₀+Mh+18<z.im at hz; linarith)) hp
    · intro z hz
      have he : z.im-(Mh+17)=z.im-Mh-17 := by ring
      rw [he]
      exact hbound z hz
    · exact hn
    · exact hZ
  have hlocal : ∀ w∈ball (0:ℂ) 2, w∈strip → transitionValue U H e₁ e₂ A B Γ N M Y V 0 w=
      G (imageCenter Rₛ Y+w)-globalAttracting Rₛ RealNormalizationAnchor.normalizationAnchor := by
    intro w hw hws
    exact actual_gate_eq_upper_horn U H e₁ e₂ A B Γ R Rₛ Y₁ Y₀ N M Y V G hs hRR hd ht hi hY hY₁
      hpatch (hcp Y hY) w hw hws
  have hlift : ∀ w∈strip, LocalPeriodicStrip.lift (transitionValue U H e₁ e₂ A B Γ N M Y V 0) w=
      G (imageCenter Rₛ Y+w)-globalAttracting Rₛ RealNormalizationAnchor.normalizationAnchor :=
    lift_of_centered_eq _ G _ _ hp hlocal
  have hmean := mean_of_lift_eq_centered_upper (transitionValue U H e₁ e₂ A B Γ N M Y V 0) G
    (Y₀+Mh+2) (imageCenter Rₛ Y) (globalAttracting Rₛ RealNormalizationAnchor.normalizationAnchor)
    ha hp (by linarith) (hzero 0 (by norm_num) _ hcim) hlift
  rw [←gate_center_actual U H e₁ e₂ A B Γ R Rₛ N M Y V hs hRR ht] at hmean
  obtain ⟨Vroot,p,Rp,hf⟩ := ActualFourierExpansion.exists_fourier_data_of_transition U H e₁ e₂ A B Γ R N M Y V ht
  exact ⟨U,H,e₁,e₂,A,B,K,F,Γ,hdata,Rₛ,R,Y₁,Y₀,Mh,Ch,G,hs,hRR,hd,hl,hdef,h17,hMh,hCh,hbound,ha,hp,hzero,N,M,Y,V,ht,
    ActualFourierExpansion.absolute_gate_coefficients_of_deep U H e₁ e₂ A B Γ R N M Y V hd ht,
    ActualStripTransition.strip_data_of_transition U H e₁ e₂ A B Γ R N M Y V hd hl ht,
    hlift,hmean,Vroot,p,Rp,ActualStripTransition.fourier_data_lift _ _ _ _ _ hf⟩

end Kneser.ActualUpperHornGateBridge
end
