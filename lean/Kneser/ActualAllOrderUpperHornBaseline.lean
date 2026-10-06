import Kneser.ActualCenteredBaselineBridge
import Kneser.ActualRealNormalizedTransitionAtDepth
import Kneser.ActualAllOrderPeriodicHorn
import Kneser.ActualRealNormalizedFirstCoefficient

/-! One actual all-order preparation, one actual moving inverse and one
real anchor have the same true global upper-horn baseline. The coherent
multiplier-parameter logarithm coefficients and their orbit-series first
coefficient belong to this same transition. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
namespace Kneser.ActualAllOrderUpperHornBaseline
open Set Metric Filter Complex
open Kneser.ReflectedOrbitChainCoefficient Kneser.CommonQuadraticBaseline
open Kneser.ActualBilateralGate Kneser.ActualGateAbel Kneser.ActualDeepCoordinateData
open Kneser.ActualQuantitativeGateTransition Kneser.ActualCenteredGatePacket
open Kneser.AllOrderSingleInverse Kneser.AllOrderCompactGate Kneser.AllOrderPeriodicPacket
open Kneser.ActualAllOrderHornParameter Kneser.ActualAllOrderPeriodicHorn
open Kneser.ActualCenteredBaselineBridge Kneser.ActualUpperHornGateBridge
open Kneser.CanonicalBasinExtension Kneser.CanonicalUpperHornCharts
open Kneser.CanonicalHighImaginaryAsymptotics Kneser.PeriodicHornGlobal
open Kneser.LocalPeriodicStrip Kneser.GateFourierDerivative Kneser.CenteredUpperHornMean
open Kneser.ActualRealNormalizedFirstCoefficient Kneser.AllOrderParameterExpansion
open Kneser.ParabolicExponentialOrbit Kneser.ExponentialUnfolding
open scoped Topology

abbrev actualTransition := Kneser.ActualRealNormalizedTransition.transition

structure BaselineData
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Rₛ Y₁ Y₀ Mh Ch : ℝ) (N M M₀ : ℕ) (Y : ℝ)
    (Vold V : ℝ → ℂ → ℂ) (p r G : ℂ → ℂ) : Prop where
  actual : ActualPreparationData U H (first (e 1)) (second (e 1)) A B K F (Γ 1)
  prepared : ∀ n, Kneser.CommonPreparedFamily.Prepared A B F n (e n) (Γ n)
  depth : 64≤R
  canonical : CanonicalSeedData Rₛ
  seed_depth : Rₛ≤R
  deep : DeepCoordinateData U H (first (e 1)) (second (e 1)) A B (Γ 1) R
  local_abel : LocalAbelData U H (first (e 1)) (second (e 1)) A B (Γ 1) R
  absolute : Kneser.HigherGateIntegerRemainder.AbsoluteIntegerGateExpansions U H A B e Γ N
  entry : R+2≤(inverseCoordinate (orbit Kneser.RealNormalizationAnchor.normalizationAnchor 0 M)).re
  original_transition : ActualTransitionData U H (first (e 1)) (second (e 1)) A B (Γ 1) R N M₀ Y Vold
  moving_inverse : InverseData (centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y) V 12
  parameter_analytic : AnalyticAt ℂ p 0
  parameter_zero : p 0=0
  parameter_derivative : HasDerivAt p 2 0
  actual_parameter : ∀ x : ℂ, p (x^2)= -Complex.log (Kneser.ExponentialPreparedModel.rootMultiplier U x)*
    Complex.log (Kneser.ExponentialPreparedModel.rootMultiplier U (-x))
  inverse_parameter_analytic : AnalyticAt ℂ r 0
  inverse_parameter_zero : r 0=0
  inverse_parameter_derivative : HasDerivAt r (1/2) 0
  parameter_left_inverse : ∀ᶠ z : ℂ in 𝓝 0, r (p z)=z
  parameter_right_inverse : ∀ᶠ z : ℂ in 𝓝 0, p (r z)=z
  actual_global_horn : G=globalHorn (hornOnImage Rₛ Y₁) (imageCenter Rₛ) Y₀
  height : 17≤Y₀
  margin_nonneg : 0≤Mh
  bound_nonneg : 0≤Ch
  global_bound : ∀ z : ℂ, Y₀+Mh+18<z.im → ‖G z-z‖≤Ch/(z.im-Mh-17)
  global_analytic : AnalyticOnNhd ℂ G {z : ℂ | Y₀+Mh+2<z.im}
  global_translation : ∀ z : ℂ, G (z+1)=G z+1
  nonpositive_modes : ∀ n : ℤ, n≤0 → ∀ y : ℝ, Y₀+Mh+18<y → gateFourierCoefficient n y G=0
  actual_baseline : ∀ w∈strip,
    lift (actualTransition U H A B e Γ N M Y V 0) w=
      G (imageCenter Rₛ Y+w)-globalAttracting Rₛ Kneser.RealNormalizationAnchor.normalizationAnchor
  baseline_mean : gateFourierCoefficient 0 0 (actualTransition U H A B e Γ N M Y V 0)=
    imageCenter Rₛ Y-globalAttracting Rₛ Kneser.RealNormalizationAnchor.normalizationAnchor
  baseline_analytic : AnalyticOnNhd ℂ (lift (actualTransition U H A B e Γ N M Y V 0)) strip
  positive_analytic : ∀ᶠ s : ℝ in 𝓝[>] 0,
    AnalyticOnNhd ℂ (lift (actualTransition U H A B e Γ N M Y V s)) strip
  packets : ∀ m : ℕ, 1≤m → ∃ b : ℕ → ℂ → ℂ,
    FinitePacket (actualTransition U H A B e Γ N M Y V) b m (ball (0:ℂ) 3) ∧
    FinitePacket (fun s => lift (actualTransition U H A B e Γ N M Y V s)) (stripCoefficient b) m strip
  coherent : CoherentHornData (actualTransition U H A B e Γ N M Y V) p r
  physical_first : ∀ n : ℤ, gateFourierCoefficient n 0 (actualTransition U H A B e Γ N M Y V 0)≠0 →
    ∃ a : ℕ → ℂ, a 0=0 ∧
      (∀ m : ℕ, ParameterExpansion (logarithm (actualTransition U H A B e Γ N M Y V) n) p a m) ∧
      a 1=Kneser.hornKappa n
        (gateFourierCoefficient n 0 (actualTransition U H A B e Γ N M Y V 0))
        (gateCorrectionCoefficient n 0 (physicalCorrection U H A B e Γ N M Y V))
        (gateCorrectionCoefficient 0 0 (physicalCorrection U H A B e Γ N M Y V))

/-- The same supplied actual preparation is retained while a sufficiently
deep gate and its true global baseline are constructed. -/
theorem baseline_of_actual_all_orders_at_depth
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H (first (e 1)) (second (e 1)) A B K F (Γ 1))
    (hprep : ∀ n, Kneser.CommonPreparedFamily.Prepared A B F n (e n) (Γ n)) (Dmin : ℝ) :
    ∃ R Rₛ Y₁ Y₀ Mh Ch : ℝ, ∃ N M M₀ : ℕ, ∃ Y : ℝ,
      ∃ Vold V : ℝ → ℂ → ℂ, ∃ p r G : ℂ → ℂ,
        Dmin≤R ∧ BaselineData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch N M M₀ Y Vold V p r G := by
  obtain ⟨Rd,hd⟩ := Kneser.ActualBaselineDeep.deep_data_of_actual U H (first (e 1)) (second (e 1)) A B K F (Γ 1) hdata
  obtain ⟨Rl,_hRl,hl⟩ := local_abel_data_of_actual U H (first (e 1)) (second (e 1)) A B K F (Γ 1) hdata
  let Rb := max Rd Rl
  let Rₛ := Rb+2
  have hs : CanonicalSeedData Rₛ := canonical_seed_of_deep U H (first (e 1)) (second (e 1)) A B (Γ 1) Rb
    (hd.mono (le_max_left _ _)) (hl.mono (le_max_right _ _))
  obtain ⟨Y₁,Y₀,Mh,Ch,G,hdef,h17,hMh,hCh,hi,hcp,ha,hp,hpatch,_hactual,hbound⟩ :=
    Kneser.ActualGlobalUpperHorn.exists_actual_global_upper_horn Rₛ hs
  obtain ⟨Yg,Mc,_hMc,_hcc,hcb,_hclose,_hsep⟩ := Kneser.ActualUpperHornCenters.exists_actual_centers_geometry Rₛ hs
  let D0 := max Rₛ (max (Y₀+Mh+Mc+100) (max (Y₁+32) (Yg+32)))
  let D := max Dmin D0
  obtain ⟨R,N,M,M₀,Y,Vold,V,_hactualPrep,_hprep,hDR,hR,hlocal,hdeep,hab,hentry,ht,hv,hT,hpack⟩ :=
    Kneser.ActualRealNormalizedTransitionAtDepth.exists_real_normalized_transition_at_depth U H A B K F e Γ hdata hprep D
  have hD0R : D0≤R := (le_max_right _ _).trans hDR
  have hDminR : Dmin≤R := (le_max_left _ _).trans hDR
  have hRR : Rₛ≤R := (le_max_left _ _).trans hD0R
  have hRY : R+100<Y := by linarith [ht.length_margin,ht.height,Nat.cast_nonneg (α:=ℝ) N]
  have hRg : Yg+32≤R := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hD0R
  have hR₁ : Y₁+32≤R := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hD0R
  have hR₀b : Y₀+Mh+Mc+100≤R := ((le_max_left _ _).trans (le_max_right _ _)).trans hD0R
  have hY : Y₀<Y := by linarith
  have hY₁ : Y₁+16<Y := by linarith
  have hcim : Y₀+Mh+18<(imageCenter Rₛ Y).im := by
    have hh := (abs_le.mp (hcb Y (by linarith : Yg<Y))).1
    linarith
  have hzero : ∀ n : ℤ, n≤0 → ∀ y : ℝ, Y₀+Mh+18<y → gateFourierCoefficient n y G=0 := by
    intro n hn y hy
    apply Kneser.UpperHornVanishingModes.nonpositive_coefficient_zero G (Y₀+Mh+18) (Mh+17) Ch
      (by linarith) (by linarith) hCh
      (ha.mono (by intro z hz; change Y₀+Mh+2<z.im; change Y₀+Mh+18<z.im at hz; linarith)) hp
    · intro z hz
      rw [show z.im-(Mh+17)=z.im-Mh-17 by ring]
      exact hbound z hz
    · exact hn
    · exact hy
  have hlocalZero : ∀ w∈ball (0:ℂ) 2, w∈strip → actualTransition U H A B e Γ N M Y V 0 w=
      G (imageCenter Rₛ Y+w)-globalAttracting Rₛ Kneser.RealNormalizationAnchor.normalizationAnchor := by
    intro w hw hws
    change Kneser.ActualRealNormalizedTransition.transition U H A B e Γ N M Y V 0 w = _
    rw [real_normalized_zero_eq_original U H A B e Γ R Rₛ Y N M M₀ Vold V hs hRR hdeep ht hv hentry
      w (ball_subset_ball (by norm_num) hw)]
    exact actual_gate_eq_upper_horn U H (first (e 1)) (second (e 1)) A B (Γ 1)
      R Rₛ Y₁ Y₀ N M₀ Y Vold G hs hRR hdeep ht hi hY hY₁ hpatch (hcp Y hY) w hw hws
  have hlift := lift_of_centered_eq _ G _ _ hp hlocalZero
  have hmean := mean_of_lift_eq_centered_upper (actualTransition U H A B e Γ N M Y V 0) G
    (Y₀+Mh+2) (imageCenter Rₛ Y) (globalAttracting Rₛ Kneser.RealNormalizationAnchor.normalizationAnchor)
    ha hp (by linarith) (hzero 0 (by norm_num) _ hcim) hlift
  have hperiod := Kneser.ActualRealNormalizedPeriodicity.eventually_transition_translation U H A B e Γ R N M M₀ Y Vold V ht hR hlocal hv
  have hperiod0 := Kneser.ActualRealNormalizedPeriodicity.transition_zero_translation U H A B e Γ R N M M₀ Y Vold V ht hR hlocal hv
  obtain ⟨b₁,hb₁⟩ := hpack 1 le_rfl
  have hT0 := finitePacket_zero_analytic _ b₁ 1 hb₁
  have hposLift : ∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (lift (actualTransition U H A B e Γ N M Y V s)) strip := by
    filter_upwards [hT,hperiod] with s hs hp
    exact lift_analytic_of_ball_three _ hs hp
  have hpackLift : ∀ m : ℕ, 1≤m → ∃ b : ℕ → ℂ → ℂ,
      FinitePacket (actualTransition U H A B e Γ N M Y V) b m (ball (0:ℂ) 3) ∧
      FinitePacket (fun s => lift (actualTransition U H A B e Γ N M Y V s)) (stripCoefficient b) m strip := by
    intro m hm
    obtain ⟨b,hb⟩ := hpack m hm
    exact ⟨b,hb,finitePacket_lift _ b m hb hperiod⟩
  obtain ⟨p,hpa,hp0,hpd,hproduct⟩ := Kneser.ActualCommonMultiplierParameter.exists_parameter_of_actual_data
    U H (first (e 1)) (second (e 1)) A B K F (Γ 1) hdata
  obtain ⟨r,hra,hr0,hrd,hleft,hright,hcoh⟩ := coherent_horn_data_of_actual_packets _ p hpack hT hpa hp0 hpd
  refine ⟨R,Rₛ,Y₁,Y₀,Mh,Ch,N,M,M₀,Y,Vold,V,p,r,G,hDminR,?_⟩
  exact ⟨hdata,hprep,hR,hs,hRR,hdeep,hlocal,hab,hentry,ht,hv,hpa,hp0,hpd,hproduct,hra,hr0,hrd,hleft,hright,
    hdef,h17,hMh,hCh,hbound,ha,hp,hzero,hlift,hmean,lift_analytic_of_ball_three _ hT0 hperiod0,hposLift,hpackLift,hcoh,
    coherent_horn_first_coefficient U H A B K F e Γ hdata hprep R hR hlocal hdeep N M M₀ Y Vold V ht hab hv hentry p r hr0 hrd hcoh⟩

/-- Same-preparation baseline without a prescribed minimum depth. -/
theorem baseline_of_actual_all_orders
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H (first (e 1)) (second (e 1)) A B K F (Γ 1))
    (hprep : ∀ n, Kneser.CommonPreparedFamily.Prepared A B F n (e n) (Γ n)) :
    ∃ R Rₛ Y₁ Y₀ Mh Ch : ℝ, ∃ N M M₀ : ℕ, ∃ Y : ℝ,
      ∃ Vold V : ℝ → ℂ → ℂ, ∃ p r G : ℂ → ℂ,
        BaselineData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch N M M₀ Y Vold V p r G := by
  obtain ⟨R,Rₛ,Y₁,Y₀,Mh,Ch,N,M,M₀,Y,Vold,V,p,r,G,_hDR,hb⟩ :=
    baseline_of_actual_all_orders_at_depth U H A B K F e Γ hdata hprep 0
  exact ⟨R,Rₛ,Y₁,Y₀,Mh,Ch,N,M,M₀,Y,Vold,V,p,r,G,hb⟩

/-- Unconditional endpoint: the all-order preparation and the true global
upper horn, with its coherent coefficient sequence, share one witness. -/
theorem exists_actual_all_order_upper_horn_baseline :
    ∃ U H A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F : ℂ × ℂ → ℂ,
    ∃ e : (n : ℕ) → Fin (2*n) → ℂ → ℂ, ∃ Γ : ℕ → ℂ × ℂ → ℂ,
    ∃ R Rₛ Y₁ Y₀ Mh Ch : ℝ, ∃ N M M₀ : ℕ, ∃ Y : ℝ,
      ∃ Vold V : ℝ → ℂ → ℂ, ∃ p r G : ℂ → ℂ,
        BaselineData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch N M M₀ Y Vold V p r G := by
  obtain ⟨U,H,A,B,K,F,e,Γ,hdata,hprep,_ha,_hr,_hca,_hcr⟩ :=
    Kneser.ActualBilateralHigherPreparation.exists_actual_bilateral_common_all_orders
  obtain ⟨R,Rₛ,Y₁,Y₀,Mh,Ch,N,M,M₀,Y,Vold,V,p,r,G,hb⟩ := baseline_of_actual_all_orders U H A B K F e Γ hdata hprep
  exact ⟨U,H,A,B,K,F,e,Γ,R,Rₛ,Y₁,Y₀,Mh,Ch,N,M,M₀,Y,Vold,V,p,r,G,hb⟩

end Kneser.ActualAllOrderUpperHornBaseline
end
