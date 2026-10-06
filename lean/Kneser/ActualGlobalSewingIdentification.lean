import Kneser.ActualGlobalHornFamily
import Kneser.ActualNormalizedSewing
import Kneser.ActualFourierGaugeBridge
import Kneser.ActualOrderedLambdaFlatness

/-! The actual all-order horn family and the actual Fourier sewing share
the same preparation, roots, growing inverse and normalized transition.
The local/global horn gauge is identified by genuine contour integrals,
and all sewing smallness conditions are derived from actual height. -/

set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
namespace Kneser.ActualGlobalSewingIdentification

open Set Metric Filter Complex
open Kneser.ReflectedOrbitChainCoefficient Kneser.CommonQuadraticBaseline
open Kneser.ActualGlobalHornFamily Kneser.ActualAllOrderUpperHornBaseline
open Kneser.ActualHolomorphicGrowingLens Kneser.GrowingBandGeometry
open Kneser.ActualGrowingCoordinateInverse Kneser.GrowingLensSpatialHolomorphy
open Kneser.ActualNormalizedGrowingTransition Kneser.NormalizedGrowingFourier
open Kneser.ActualNormalizedSewing Kneser.ActualBandTimeConfluence
open Kneser.ActualFourierGaugeBridge Kneser.GateFourierDerivative
open Kneser.ActualLocalGrowingTransitionBridge Kneser.FourierSewing
open Kneser.RealNormalizationAnchor
open scoped Topology

def SewnFamily (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ) : Prop :=
  ∃ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P : ℝ, ∃ N M M₀ : ℕ,
  ∃ Vold V : ℝ → ℂ → ℂ, ∃ p r G : ℂ → ℂ,
    BaselineData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch N M M₀ Yg Vold V p r G ∧
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∃ a b θ : ℝ, ∃ Vg : ℂ → ℂ,
      LensControl (first (e 1)) (second (e 1)) A B (Γ 1) s a b θ Y η Mg P ∧
      AnalyticOnNhd ℂ Vg (strip θ (3*Y+boundaryMargin P)) ∧
      (∀ w ∈ strip θ (3*Y+boundaryMargin P), Vg w ∈ strip θ (3*Y) ∧
        repellingCoordinate A B (Γ 1) s a b θ (first (e 1) s) (second (e 1) s) (Vg w)=w) ∧
      let T := transition A B (Γ 1) s a b θ realAnchor ((a+b)/2) (first (e 1) s) (second (e 1) s) Vg
      SewingWitness (height θ) (boundaryLoss Y P) T ∧
      (∀ n : ℤ, n≠0 →
        gateFourierCoefficient n 0 (actualTransition U H A B e Γ N M Yg V s) *
            exp (-Kneser.fourierFrequency n * gateFourierCoefficient 0 0
              (actualTransition U H A B e Γ N M Yg V s)) =
          gateFourierCoefficient n 0 T * exp (-Kneser.fourierFrequency n * gateFourierCoefficient 0 0 T)) ∧
      lambda (height θ)=Kneser.ActualLambdaFlatness.lambdaFactor s a

theorem sewing_of_global_family (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (hf : Family U H A B K F e Γ 0) : SewnFamily U H A B K F e Γ := by
  obtain ⟨R,Yg,Y,η,Mg,P,Rₛ,Y₁,Y₀,Mh,Ch,N,M,M₀,Vold,V,p,r,G,
    _hR,hbase,_ht,_hv,_hpack,hglobal⟩ := hf
  obtain ⟨H₀,hthreshold⟩ := exists_sewing_height_threshold (boundaryLoss Y P)
  let C := max H₀ 1 + 1
  have hC : 0 < C := by dsimp [C]; linarith [le_max_right H₀ 1]
  have htheta := actual_theta_uniform_small U H (first (e 1)) (second (e 1)) A B K F (Γ 1)
    hbase.actual (2*Real.pi/C) (by positivity)
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0<s := self_mem_nhdsWithin
  have hless : ∀ᶠ s : ℝ in 𝓝[>] 0, s<1 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  refine ⟨R,Rₛ,Y₁,Y₀,Mh,Ch,Yg,Y,η,Mg,P,N,M,M₀,Vold,V,p,r,G,hbase,?_⟩
  filter_upwards [hglobal,htheta,hpos,hless] with s hs hθ hspos hs1
  obtain ⟨a,b,θ,Vg,hc,hVan,hVs,hδ,hident⟩ := hs
  have hsmall := (hθ a b hc.left_neg hc.right_pos hc.left_fixed hc.right_fixed).2
  rw [←hc.theta_actual] at hsmall
  have hheight : H₀ ≤ height θ := by
    have hh : C < height θ := (lt_div_iff₀ hc.theta_pos).mpr
      (by have hi := (lt_div_iff₀ hC).mp hsmall; nlinarith)
    have hHC : H₀<C := by dsimp [C]; linarith [le_max_left H₀ 1]
    linarith
  obtain ⟨hH,hg,hpoint,hn,hl⟩ := hthreshold (height θ) hheight
  have har : a<(a+b)/2 := by linarith [hc.left_neg,hc.right_pos]
  have hrb : (a+b)/2<b := by linarith [hc.left_neg,hc.right_pos]
  have hr₀ := actual_anchor_left_of_control (first (e 1)) (second (e 1)) A B (Γ 1)
    s a b θ Y η Mg P hc
  let T := transition A B (Γ 1) s a b θ realAnchor ((a+b)/2) (first (e 1) s) (second (e 1) s) Vg
  have hw := actual_normalized_sewing_of_height (first (e 1)) (second (e 1)) A B (Γ 1)
    s a b θ Y η Mg P realAnchor ((a+b)/2) hspos hs1 hc hr₀ har hrb Vg hVan hVs
    hH hg hpoint hn hl
  obtain ⟨ha,hp,_hbound⟩ := actual_normalized_transition_bounds (first (e 1)) (second (e 1)) A B (Γ 1)
    s a b θ Y η Mg P realAnchor ((a+b)/2) hs1 hc har hrb Vg hVan hVs
  have hD : 0<outerWidth θ Y P := by
    have hh := (outer_width_positive (first (e 1)) (second (e 1)) A B (Γ 1)
      s a b θ Y η Mg P hc).1
    linarith
  let δ := gateConstant A B (Γ 1) s a b θ Yg (first (e 1) s) (second (e 1) s) -
    repellingConstant A B (Γ 1) s a b θ ((a+b)/2) (first (e 1) s) (second (e 1) s)
  have he : ∀ x ∈ Icc (0:ℝ) 1, actualTransition U H A B e Γ N M Yg V s (x:ℂ)=T ((x:ℂ)+δ) := by
    intro x hx
    have hx3 : (x:ℂ)∈ball (0:ℂ) 3 := by
      simp only [mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs]
      rw [abs_of_nonneg hx.1]
      linarith [hx.2]
    convert (hident (x:ℂ) hx3).2 using 1
    congr 1
    dsimp [δ]
    ring
  refine ⟨a,b,θ,Vg,hc,hVan,hVs,hw,?_,
    actual_height_lambda (first (e 1)) (second (e 1)) A B (Γ 1) s a b θ Y η Mg P hc⟩
  intro n hn0
  exact local_horn_gauge_invariant n hn0 _ T (outerWidth θ Y P) δ hD ha hp hδ he

theorem exists_actual_global_sewn_horn_family :
    ∃ U H A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F : ℂ × ℂ → ℂ,
    ∃ e : (n : ℕ) → Fin (2*n) → ℂ → ℂ, ∃ Γ : ℕ → ℂ × ℂ → ℂ,
      SewnFamily U H A B K F e Γ := by
  obtain ⟨U,H,A,B,K,F,e,Γ,_hdata,_hprep,hfamily⟩ := exists_actual_global_horn_family
  exact ⟨U,H,A,B,K,F,e,Γ,sewing_of_global_family U H A B K F e Γ hfamily⟩

end Kneser.ActualGlobalSewingIdentification
end
