import Kneser.ActualNormalizedSewing
import Kneser.HolomorphicInjectiveInverse
import Kneser.FourierSewingGluing

/-! Genuine physical inverse charts and sewing on their proved regular
patches. The attracting inverse is defined on its actual open image,
so no continuation across Koenigs cuts or entire inverse is asserted. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Kneser.ActualRegularWelding

open Filter Set Metric Complex
open Kneser.GrowingBandGeometry Kneser.ActualLensModel
open Kneser.GrowingLensSpatialHolomorphy Kneser.ActualHolomorphicGrowingLens
open Kneser.ActualGrowingCoordinateInverse Kneser.ActualGrowingTransition
open Kneser.ActualGrowingAbel Kneser.GrowingLensKoenigs
open Kneser.ActualGrowingRealPhases Kneser.RealRepellingCoordinatePhase
open Kneser.ActualLensGeometry Kneser.ActualInverseLensBootstrap
open Kneser.ActualReflectedLensModel Kneser.EvenPreparedOrbitDiscs
open Kneser.ActualGrowingPeriodicity Kneser.ReflectedOrbitChainCoefficient
open Kneser.GrowingStripFourier Kneser.NormalizedGrowingFourier
open Kneser.ActualGrowingKoenigsIdentification Kneser.HolomorphicInjectiveInverse
open Kneser.WeightedFourier Kneser.FourierSewing
open Kneser.GrowingLensCoordinateRegularity Kneser.GateFourierDerivative
open scoped Topology

/-- The true strip inverse intertwines unit translation and the actual
exponential unfolding on its whole proved target strip. -/
theorem actual_inverse_translation
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) (V : ℂ → ℂ)
    (hVs : ∀w∈strip θ (3*Y+boundaryMargin P),
      V w∈strip θ (3*Y) ∧ repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w)=w)
    (w : ℂ) (hw : w∈strip θ (3*Y+boundaryMargin P)) :
    bandChart a b θ (V (w+1))=Kneser.ExponentialUnfolding.unfolding s (bandChart a b θ (V w)) := by
  have hY : 0 < Y := by linarith [hc.height_large]
  have hP : 0 ≤ P := (norm_nonneg (e₁ s)).trans hc.first_model_bound
  have hab : a < b := lt_trans hc.left_neg hc.right_pos
  have hsub : strip θ (3 * Y) ⊆ strip θ Y := by
    intro Z hZ
    exact ⟨by linarith [hZ.1],by linarith [hZ.2]⟩
  have hsub2 : strip θ (3 * Y) ⊆ strip θ (2 * Y) := by
    intro Z hZ
    exact ⟨by linarith [hZ.1],by linarith [hZ.2]⟩
  have hw1 : w+1 ∈ strip θ (3 * Y + boundaryMargin P) := by
    change 3 * Y + boundaryMargin P < (w+1).im ∧ (w+1).im < height θ - (3 * Y + boundaryMargin P)
    simp only [Complex.add_im,Complex.one_im,add_zero]
    exact hw
  let Z := V (w+1)
  let u := bandChart a b θ Z
  have hZ : Z ∈ strip θ (3 * Y) := (hVs (w+1) hw1).1
  have hZu := hc.true_orbits Z (hsub hZ)
  have hu : u ∈ physicalLens a b θ Y := ⟨Z,hsub hZ,rfl⟩
  have hS : physicalRepelling A B Γ s a b θ (e₁ s) (e₂ s) u = w+1 := (hVs (w+1) hw1).2
  have hgstate := hZu.2.2.2.2.2 1
  have hgnorm : ‖inverseStep s u‖ ≤ η / 4 := hgstate.2.2.1
  have hroota : inverseStep s u ≠ (a : ℂ) := hgstate.1
  have hrootb : inverseStep s u ≠ (b : ℂ) := hgstate.2.1
  have hSg : physicalRepelling A B Γ s a b θ (e₁ s) (e₂ s) (inverseStep s u) = w := by
    rw [physicalRepelling_inverse_abel_of_control e₁ e₂ A B Γ s a b θ Y η M P hs1 hc u hu,hS]
    ring
  have hm := Kneser.ActualLensBounds.lensModel_phase_bound s a b θ P (e₁ s) (e₂ s)
    (inverseStep s u) hc.residue_bound hP hc.first_model_bound hc.second_model_bound
    (hgnorm.trans (by linarith [hc.radius_small]))
  have hn := inverse_tail_norm_le_one A B Γ s u hZu.2.1 hZu.2.2.2.1
  have hi := (Complex.abs_im_le_norm (∑' k, descendedTerm A B Γ 2
    (inverseOrbit s (inverseStep s u) (k+1)) s 0)).trans hn
  have hphase : |(physicalRepelling A B Γ s a b θ (e₁ s) (e₂ s) (inverseStep s u) -
      bandTime a b θ (inverseStep s u)).im| ≤ boundaryMargin P := by
    have hh := abs_add_le (lensModel s a b θ (e₁ s) (e₂ s) (inverseStep s u) -
      bandTime a b θ (inverseStep s u)).im (-(∑' k, descendedTerm A B Γ 2
        (inverseOrbit s (inverseStep s u) (k+1)) s 0).im)
    rw [abs_neg,←sub_eq_add_neg] at hh
    change |((lensModel s a b θ (e₁ s) (e₂ s) (inverseStep s u) -
      ∑' k, descendedTerm A B Γ 2 (inverseOrbit s (inverseStep s u) (k+1)) s 0) -
      bandTime a b θ (inverseStep s u)).im| ≤ boundaryMargin P
    simp only [Complex.sub_im] at hm hh ⊢
    change |(lensModel s a b θ (e₁ s) (e₂ s) (inverseStep s u)).im -
      (∑' k, descendedTerm A B Γ 2 (inverseOrbit s (inverseStep s u) (k+1)) s 0).im -
      (bandTime a b θ (inverseStep s u)).im| ≤ Real.pi + 2 * P + 1
    have he : (lensModel s a b θ (e₁ s) (e₂ s) (inverseStep s u)).im -
      (∑' k, descendedTerm A B Γ 2 (inverseOrbit s (inverseStep s u) (k+1)) s 0).im -
      (bandTime a b θ (inverseStep s u)).im =
      ((lensModel s a b θ (e₁ s) (e₂ s) (inverseStep s u)).im - (bandTime a b θ (inverseStep s u)).im) -
      (∑' k, descendedTerm A B Γ 2 (inverseOrbit s (inverseStep s u) (k+1)) s 0).im := by ring
    rw [he]
    exact hh.trans (add_le_add hm hi)
  rw [hSg,Complex.sub_im] at hphase
  have htime : bandTime a b θ (inverseStep s u) ∈ strip θ (3 * Y) :=
    ⟨by linarith only [(abs_le.mp hphase).2,hw.1],by linarith only [(abs_le.mp hphase).1,hw.2]⟩
  have hchart := bandChart_bandTime a b θ (inverseStep s u) (ne_of_lt hab) (ne_of_gt hc.theta_pos) hroota hrootb
  have hg : inverseStep s u ∈ physicalLens a b θ Y := ⟨_,hsub htime,hchart⟩
  have hSchart : repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s)
      (bandTime a b θ (inverseStep s u)) = w := by
    change physicalRepelling A B Γ s a b θ (e₁ s) (e₂ s)
      (bandChart a b θ (bandTime a b θ (inverseStep s u))) = w
    rw [hchart,hSg]
  have htimeEq := (actual_coordinates_injective_buffered e₁ e₂ A B Γ s a b θ Y η M P hc).2
    (hsub2 htime) (hsub2 (hVs w hw).1) (hSchart.trans (hVs w hw).2.symm)
  have hgEq : inverseStep s u = bandChart a b θ (V w) := by rw [←htimeEq,hchart]
  have hfu : Kneser.ExponentialUnfolding.unfolding s (inverseStep s u) = u :=
    unfolding_inverseStep s u hs1 (by
      have hh := (hZu.2.2.2.2.1 0).2.2.1
      simp only [Kneser.ExponentialUnfolding.orbit_zero] at hh
      linarith only [hh,hc.radius_small])
  rw [hgEq] at hfu
  exact hfu.symm

def attractingImage (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y r₀ : ℝ)
    (e₁ e₂ : ℂ) : Set ℂ :=
  normalizedAttracting A B Γ s a b θ r₀ e₁ e₂ '' strip θ (2*Y)

def regularAttractingInverse (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y r₀ : ℝ)
    (e₁ e₂ : ℂ) (w : ℂ) : ℂ :=
  bandChart a b θ (imageInverse (normalizedAttracting A B Γ s a b θ r₀ e₁ e₂) (strip θ (2*Y)) w)

def regularRepellingInverse (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ r : ℝ)
    (e₁ e₂ : ℂ) (V : ℂ → ℂ) (w : ℂ) : ℂ :=
  bandChart a b θ (V (w+Kneser.ActualNormalizedGrowingTransition.repellingConstant A B Γ s a b θ r e₁ e₂))

theorem normalized_attracting_regular_data
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r₀ : ℝ)
    (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) :
    InjOn (normalizedAttracting A B Γ s a b θ r₀ (e₁ s) (e₂ s)) (strip θ (2*Y)) ∧
    ∀Z∈strip θ (2*Y), AnalyticAt ℂ (normalizedAttracting A B Γ s a b θ r₀ (e₁ s) (e₂ s)) Z ∧
      deriv (normalizedAttracting A B Γ s a b θ r₀ (e₁ s) (e₂ s)) Z≠0 := by
  have hY : 0<Y := by linarith [hc.height_large]
  have hA := (actual_coordinates_analytic e₁ e₂ A B Γ s a b θ Y η M P hc).1
  refine ⟨?_,?_⟩
  · intro Z hZ W hW he
    apply (actual_coordinates_injective_buffered e₁ e₂ A B Γ s a b θ Y η M P hc).1 hZ hW
    change attractingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) Z-
      (Kneser.PositiveKoenigsAbel.koenigsTime s a r₀+Kneser.PositiveKoenigsAbel.modelConstant s a b (e₁ s) (e₂ s))=
      attractingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) W-
      (Kneser.PositiveKoenigsAbel.koenigsTime s a r₀+Kneser.PositiveKoenigsAbel.modelConstant s a b (e₁ s) (e₂ s)) at he
    exact sub_left_inj.mp he
  · intro Z hZ
    have hZa := hA Z (inner_strip_subset θ Y hY.le hZ)
    have hNa : AnalyticAt ℂ (normalizedAttracting A B Γ s a b θ r₀ (e₁ s) (e₂ s)) Z := hZa.sub analyticAt_const
    refine ⟨hNa,?_⟩
    have hd := (hZa.differentiableAt.hasDerivAt.sub_const
      (Kneser.PositiveKoenigsAbel.koenigsTime s a r₀+Kneser.PositiveKoenigsAbel.modelConstant s a b (e₁ s) (e₂ s))).deriv
    change deriv (normalizedAttracting A B Γ s a b θ r₀ (e₁ s) (e₂ s)) Z=
      deriv (attractingCoordinate A B Γ s a b θ (e₁ s) (e₂ s)) Z at hd
    rw [hd]
    exact derivative_ne_zero_of_close_to_one (actual_coordinate_derivative_bounds e₁ e₂ A B Γ s a b θ Y η M P hc Z hZ).1

theorem actual_regular_inverse_charts
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r₀ r : ℝ)
    (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (har : a<r) (hrb : r<b) (V : ℂ → ℂ)
    (hV : AnalyticOnNhd ℂ V (strip θ (3*Y+boundaryMargin P)))
    (hVs : ∀w∈strip θ (3*Y+boundaryMargin P), V w∈strip θ (3*Y) ∧
      repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w)=w) :
    IsOpen (attractingImage A B Γ s a b θ Y r₀ (e₁ s) (e₂ s)) ∧
    AnalyticOnNhd ℂ (regularAttractingInverse A B Γ s a b θ Y r₀ (e₁ s) (e₂ s))
      (attractingImage A B Γ s a b θ Y r₀ (e₁ s) (e₂ s)) ∧
    AnalyticOnNhd ℂ (regularRepellingInverse A B Γ s a b θ r (e₁ s) (e₂ s) V)
      (symmetricStrip (Kneser.NormalizedGrowingFourier.outerWidth θ Y P)) ∧
    ∀w∈symmetricStrip (Kneser.NormalizedGrowingFourier.outerWidth θ Y P),
      Kneser.ActualNormalizedGrowingTransition.transition A B Γ s a b θ r₀ r (e₁ s) (e₂ s) V w∈
        attractingImage A B Γ s a b θ Y r₀ (e₁ s) (e₂ s) ∧
      regularAttractingInverse A B Γ s a b θ Y r₀ (e₁ s) (e₂ s)
        (Kneser.ActualNormalizedGrowingTransition.transition A B Γ s a b θ r₀ r (e₁ s) (e₂ s) V w)=
          regularRepellingInverse A B Γ s a b θ r (e₁ s) (e₂ s) V w := by
  obtain ⟨hi,hF⟩ := normalized_attracting_regular_data e₁ e₂ A B Γ s a b θ Y η M P r₀ hc
  have hY : 0<Y := by linarith [hc.height_large]
  have hab : a<b := lt_trans hc.left_neg hc.right_pos
  have hchart := analyticOnNhd_bandChart a b θ Y hab hc.theta_pos hY (hc.width.trans (by linarith [Real.pi_pos]))
  have hiA := analyticOnNhd_imageInverse _ _ (strip_isOpen θ (2*Y)) hi hF
  refine ⟨image_isOpen _ _ (strip_isOpen θ (2*Y)) hF,?_,?_,?_⟩
  · intro w hw
    have hv := (imageInverse_spec _ _ w hw).1
    exact (hchart _ (inner_strip_subset θ Y hY.le hv)).comp (f:=imageInverse _ _) (hiA w hw)
  · intro w hw
    have hm := normalized_shift_mem_target e₁ e₂ A B Γ s a b θ Y η M P r hs1 hc har hrb w hw
    have hv := (hVs _ hm).1
    have hvY : V (w+Kneser.ActualNormalizedGrowingTransition.repellingConstant A B Γ s a b θ r (e₁ s) (e₂ s))∈strip θ Y :=
      ⟨by linarith [hv.1],by linarith [hv.2]⟩
    exact (hchart _ hvY).comp (f:=fun W : ℂ => V (W+Kneser.ActualNormalizedGrowingTransition.repellingConstant A B Γ s a b θ r (e₁ s) (e₂ s)))
      ((hV _ hm).comp (f:=fun W : ℂ => W+Kneser.ActualNormalizedGrowingTransition.repellingConstant A B Γ s a b θ r (e₁ s) (e₂ s))
        (analyticAt_id.add analyticAt_const))
  · intro w hw
    have hm := normalized_shift_mem_target e₁ e₂ A B Γ s a b θ Y η M P r hs1 hc har hrb w hw
    have hv := (hVs _ hm).1
    have hv2 : V (w+Kneser.ActualNormalizedGrowingTransition.repellingConstant A B Γ s a b θ r (e₁ s) (e₂ s))∈strip θ (2*Y) :=
      ⟨by linarith [hv.1],by linarith [hv.2]⟩
    refine ⟨⟨_,hv2,rfl⟩,?_⟩
    unfold regularAttractingInverse regularRepellingInverse Kneser.ActualNormalizedGrowingTransition.transition
    rw [imageInverse_left _ _ hi _ hv2]


theorem regular_repelling_inverse_abel
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r : ℝ)
    (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (har : a<r) (hrb : r<b) (V : ℂ → ℂ)
    (hVs : ∀w∈strip θ (3*Y+boundaryMargin P), V w∈strip θ (3*Y) ∧
      repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w)=w)
    (w : ℂ) (hw : w∈symmetricStrip (Kneser.NormalizedGrowingFourier.outerWidth θ Y P)) :
    regularRepellingInverse A B Γ s a b θ r (e₁ s) (e₂ s) V (w+1)=
      Kneser.ExponentialUnfolding.unfolding s (regularRepellingInverse A B Γ s a b θ r (e₁ s) (e₂ s) V w) := by
  have hm := normalized_shift_mem_target e₁ e₂ A B Γ s a b θ Y η M P r hs1 hc har hrb w hw
  unfold regularRepellingInverse
  rw [show w+1+Kneser.ActualNormalizedGrowingTransition.repellingConstant A B Γ s a b θ r (e₁ s) (e₂ s)=
    w+Kneser.ActualNormalizedGrowingTransition.repellingConstant A B Γ s a b θ r (e₁ s) (e₂ s)+1 by ring]
  exact actual_inverse_translation e₁ e₂ A B Γ s a b θ Y η M P hs1 hc V hVs _ hm

def lowerPhysicalPatch (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ r H : ℝ)
    (e₁ e₂ : ℂ) (V : ℂ → ℂ) (Q : Space) (z : ℂ) : ℂ :=
  regularRepellingInverse A B Γ s a b θ r e₁ e₂ V (lowerMap H Q z)

def upperPhysicalPatch (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y r₀ H : ℝ)
    (e₁ e₂ t₀ : ℂ) (P : Space) (z : ℂ) : ℂ :=
  regularAttractingInverse A B Γ s a b θ Y r₀ e₁ e₂ (upperMap H P t₀ z)

theorem lowerMap_mem_regular_strip (h Y D : ℝ) (Q : Space) (hQ : ‖Q‖≤1)
    (z : ℂ) (hz : z∈symmetricStrip (sewingWidth h Y 64 1))
    (he : D=h/2-Y) : lowerMap (sewingWidth h Y 64 1) Q z∈symmetricStrip D := by
  have hn := (norm_evaluate_le _ Q z (show |z.im|≤sewingWidth h Y 64 1 from le_of_lt hz)).trans hQ
  have hi := (Complex.abs_im_le_norm (evaluate (sewingWidth h Y 64 1) Q z)).trans hn
  have hh := abs_add_le z.im (evaluate (sewingWidth h Y 64 1) Q z).im
  change |(z+evaluate (sewingWidth h Y 64 1) Q z).im|<D
  rw [Complex.add_im]
  rw [he]
  change |z.im|<sewingWidth h Y 64 1 at hz
  unfold sewingWidth bandWidth at hz
  linarith

/-- The constructed Q/P/shift sew genuine physical inverse charts on a
regular common patch. The upper inverse is used only on its actual open
image. Holomorphy and Abel are derived from the true inverse dynamics. -/
theorem actual_regular_physical_welding
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P₀ r₀ r : ℝ)
    (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P₀)
    (har : a<r) (hrb : r<b) (V : ℂ → ℂ)
    (hV : AnalyticOnNhd ℂ V (strip θ (3*Y+boundaryMargin P₀)))
    (hVs : ∀w∈strip θ (3*Y+boundaryMargin P₀), V w∈strip θ (3*Y) ∧
      repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w)=w)
    (hw : Kneser.ActualNormalizedSewing.SewingWitness (height θ) (boundaryLoss Y P₀)
      (Kneser.ActualNormalizedGrowingTransition.transition A B Γ s a b θ r₀ r (e₁ s) (e₂ s) V)) :
    let H := sewingWidth (height θ) (boundaryLoss Y P₀) 64 1
    let T := Kneser.ActualNormalizedGrowingTransition.transition A B Γ s a b θ r₀ r (e₁ s) (e₂ s) V
    let t₀ := gateFourierCoefficient 0 0 T
    ∃Q P : Space, ∃ζ : ℂ,
      Q∈Negative ∧ ‖Q‖≤1 ∧ (∀n : ℤ, n<0 → P n=0) ∧ ‖P‖≤1 ∧
      ‖ζ‖≤normalizationConstant (boundaryLoss Y P₀) 64 1 4*lambda (height θ) ∧
      sewnCoordinate H (height θ) P t₀ ζ 0=0 ∧
      AnalyticOnNhd ℂ (lowerPhysicalPatch A B Γ s a b θ r H (e₁ s) (e₂ s) V Q) (symmetricStrip H) ∧
      AnalyticOnNhd ℂ (upperPhysicalPatch A B Γ s a b θ Y r₀ H (e₁ s) (e₂ s) t₀ P) (symmetricStrip H) ∧
      (∀z∈symmetricStrip H, upperMap H P t₀ z∈attractingImage A B Γ s a b θ Y r₀ (e₁ s) (e₂ s)) ∧
      EqOn (lowerPhysicalPatch A B Γ s a b θ r H (e₁ s) (e₂ s) V Q)
        (upperPhysicalPatch A B Γ s a b θ Y r₀ H (e₁ s) (e₂ s) t₀ P) (symmetricStrip H) ∧
      (∀n : ℕ, 1≤n →
        ‖gateFourierCoefficient n 0 (sewnCoordinate H (height θ) P t₀ ζ)/(lambda (height θ):ℂ)^n-
          gateFourierCoefficient n 0 T*hornPhase t₀ n‖≤
            comparisonConstant (boundaryLoss Y P₀) 64 1 4 n*lambda (height θ)) ∧
      ∀z∈symmetricStrip H,
        lowerPhysicalPatch A B Γ s a b θ r H (e₁ s) (e₂ s) V Q (z+1)=
          Kneser.ExponentialUnfolding.unfolding s (lowerPhysicalPatch A B Γ s a b θ r H (e₁ s) (e₂ s) V Q z) := by
  let H := sewingWidth (height θ) (boundaryLoss Y P₀) 64 1
  let T := Kneser.ActualNormalizedGrowingTransition.transition A B Γ s a b θ r₀ r (e₁ s) (e₂ s) V
  let t₀ := gateFourierCoefficient 0 0 T
  obtain ⟨Q,P,ζ,hneg,hQ,hpos,hP,hζ,_hζ1,_hroot,hzero,hseam,hint,hcomp⟩ := hw
  obtain ⟨_hopen,hR,hS,hcompat⟩ := actual_regular_inverse_charts e₁ e₂ A B Γ s a b θ Y η M P₀ r₀ r hs1 hc har hrb V hV hVs
  have hmem : ∀z∈symmetricStrip H, lowerMap H Q z∈symmetricStrip (Kneser.NormalizedGrowingFourier.outerWidth θ Y P₀) := by
    intro z hz
    exact lowerMap_mem_regular_strip (height θ) (boundaryLoss Y P₀) _ Q hQ z hz rfl
  have hupper : ∀z∈symmetricStrip H, upperMap H P t₀ z∈attractingImage A B Γ s a b θ Y r₀ (e₁ s) (e₂ s) := by
    intro z hz
    have hh := (hcompat _ (hmem z hz)).1
    change T (lowerMap H Q z)∈attractingImage A B Γ s a b θ Y r₀ (e₁ s) (e₂ s) at hh
    have he := hseam z (show |z.im|≤H from le_of_lt hz)
    change T (lowerMap H Q z)=upperMap H P t₀ z at he
    rwa [he] at hh
  have hlowanalytic : AnalyticOnNhd ℂ (lowerPhysicalPatch A B Γ s a b θ r H (e₁ s) (e₂ s) V Q) (symmetricStrip H) := by
    intro z hz
    have hzi := abs_lt.mp (show |z.im|<H from hz)
    have hqa : AnalyticAt ℂ (fun w => evaluate H Q w) z :=
      (differentiableOn_evaluate_negative H Q hneg).analyticAt
        ((isOpen_lt Complex.continuous_im continuous_const).mem_nhds hzi.2)
    exact (hS _ (hmem z hz)).comp (f:=lowerMap H Q) (analyticAt_id.add hqa)
  have hupanalytic : AnalyticOnNhd ℂ (upperPhysicalPatch A B Γ s a b θ Y r₀ H (e₁ s) (e₂ s) t₀ P) (symmetricStrip H) := by
    intro z hz
    have hzi := abs_lt.mp (show |z.im|<H from hz)
    have hpa : AnalyticAt ℂ (fun w => evaluate H P w) z :=
      (differentiableOn_evaluate_positive H P hpos).analyticAt
        ((isOpen_lt continuous_const (continuous_const.add Complex.continuous_im)).mem_nhds (by linarith : 0<H+z.im))
    exact (hR _ (hupper z hz)).comp (f:=upperMap H P t₀) ((analyticAt_id.add analyticAt_const).add hpa)
  refine ⟨Q,P,ζ,hneg,hQ,hpos,hP,hζ,hzero,hlowanalytic,hupanalytic,hupper,?_,?_,?_⟩
  · intro z hz
    have hh := (hcompat _ (hmem z hz)).2
    change regularAttractingInverse A B Γ s a b θ Y r₀ (e₁ s) (e₂ s) (T (lowerMap H Q z))=
      regularRepellingInverse A B Γ s a b θ r (e₁ s) (e₂ s) V (lowerMap H Q z) at hh
    have he := hseam z (show |z.im|≤H from le_of_lt hz)
    change T (lowerMap H Q z)=upperMap H P t₀ z at he
    rw [he] at hh
    exact hh.symm
  · intro n hn
    have he : translatedCoefficient H (height θ) P t₀ ζ n=
        gateFourierCoefficient n 0 (sewnCoordinate H (height θ) P t₀ ζ) := by
      rw [hint n hn]
      dsimp only [H,t₀,T]
      simp only [gateFourierCoefficient,gatePoint,gateWeight,Complex.ofReal_zero,mul_zero,add_zero,sewnDisplacement]
    rw [←he]
    exact hcomp n hn
  · intro z hz
    unfold lowerPhysicalPatch
    rw [lowerMap_translation]
    exact regular_repelling_inverse_abel e₁ e₂ A B Γ s a b θ Y η M P₀ r hs1 hc har hrb V hVs _ (hmem z hz)


/-- Semantic identification of the regular attracting inverse with the
actual Koenigs orbit limit on every point of its proved open image. -/
theorem regular_attracting_inverse_koenigs
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r₀ : ℝ)
    (hs : 0<s) (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (hr₀ : r₀<a) (w : ℂ) (hw : w∈attractingImage A B Γ s a b θ Y r₀ (e₁ s) (e₂ s)) :
    exp ((Real.log (Kneser.PositiveKoenigsOrbit.multiplier s a):ℂ)*w)=
      Kneser.PositiveKoenigsOrbit.koenigsValue s a (regularAttractingInverse A B Γ s a b θ Y r₀ (e₁ s) (e₂ s) w)/
        Kneser.PositiveKoenigsOrbit.koenigsValue s a r₀ := by
  have hY : 0<Y := by linarith [hc.height_large]
  have hv := imageInverse_spec (normalizedAttracting A B Γ s a b θ r₀ (e₁ s) (e₂ s)) (strip θ (2*Y)) w hw
  have hh := (normalizedAttracting_exponential_of_control e₁ e₂ A B Γ s a b θ Y η M P r₀ hs hs1 hc hr₀).2 _
    (inner_strip_subset θ Y hY.le hv.1)
  rwa [hv.2] at hh

def RegularPhysicalCertificate
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y P₀ r₀ r : ℝ)
    (V : ℂ → ℂ) : Prop :=
    let H := sewingWidth (height θ) (boundaryLoss Y P₀) 64 1
    let T := Kneser.ActualNormalizedGrowingTransition.transition A B Γ s a b θ r₀ r (e₁ s) (e₂ s) V
    let t₀ := gateFourierCoefficient 0 0 T
    ∃Q P : Space, ∃ζ : ℂ,
      Q∈Negative ∧ ‖Q‖≤1 ∧ (∀n : ℤ, n<0 → P n=0) ∧ ‖P‖≤1 ∧
      ‖ζ‖≤normalizationConstant (boundaryLoss Y P₀) 64 1 4*lambda (height θ) ∧
      sewnCoordinate H (height θ) P t₀ ζ 0=0 ∧
      AnalyticOnNhd ℂ (lowerPhysicalPatch A B Γ s a b θ r H (e₁ s) (e₂ s) V Q) (symmetricStrip H) ∧
      AnalyticOnNhd ℂ (upperPhysicalPatch A B Γ s a b θ Y r₀ H (e₁ s) (e₂ s) t₀ P) (symmetricStrip H) ∧
      (∀z∈symmetricStrip H, upperMap H P t₀ z∈attractingImage A B Γ s a b θ Y r₀ (e₁ s) (e₂ s)) ∧
      EqOn (lowerPhysicalPatch A B Γ s a b θ r H (e₁ s) (e₂ s) V Q)
        (upperPhysicalPatch A B Γ s a b θ Y r₀ H (e₁ s) (e₂ s) t₀ P) (symmetricStrip H) ∧
      (∀n : ℕ, 1≤n →
        ‖gateFourierCoefficient n 0 (sewnCoordinate H (height θ) P t₀ ζ)/(lambda (height θ):ℂ)^n-
          gateFourierCoefficient n 0 T*hornPhase t₀ n‖≤
            comparisonConstant (boundaryLoss Y P₀) 64 1 4 n*lambda (height θ)) ∧
      ∀z∈symmetricStrip H,
        lowerPhysicalPatch A B Γ s a b θ r H (e₁ s) (e₂ s) V Q (z+1)=
          Kneser.ExponentialUnfolding.unfolding s (lowerPhysicalPatch A B Γ s a b θ r H (e₁ s) (e₂ s) V Q z)

/-- The genuine same-witness sewing has nonempty regular physical patches,
exact seam and exponential Abel identity, actual Fourier integral
comparison, and normalized sewn time. No inverse-branch regularity or
physical seam is supplied as an assumption. -/
theorem exists_actual_regular_physical_welding
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃Y η M P₀ : ℝ, 2≤Y ∧
      ∀ᶠs : ℝ in 𝓝[>] 0, ∃a b θ : ℝ, ∃V : ℂ → ℂ,
        LensControl e₁ e₂ A B Γ s a b θ Y η M P₀ ∧
        AnalyticOnNhd ℂ V (strip θ (3*Y+boundaryMargin P₀)) ∧
        (∀w∈strip θ (3*Y+boundaryMargin P₀), V w∈strip θ (3*Y) ∧
          repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w)=w) ∧
        Kneser.FourierSewing.lambda (height θ)=Kneser.ActualLambdaFlatness.lambdaFactor s a ∧
        1≤sewingWidth (height θ) (boundaryLoss Y P₀) 64 1 ∧
        RegularPhysicalCertificate e₁ e₂ A B Γ s a b θ Y P₀
          Kneser.RealNormalizationAnchor.realAnchor ((a+b)/2) V := by
  obtain ⟨Y,η,M,P₀,hY,hall⟩ := Kneser.ActualNormalizedSewing.exists_actual_normalized_sewing U H e₁ e₂ A B K F Γ hdata
  have hsmall : ∀ᶠs : ℝ in 𝓝[>] 0,
      s<1 ∧ s<Real.exp (-2*Real.pi*(2*(boundaryLoss Y P₀+68))) :=
    ((eventually_lt_nhds (by norm_num : (0:ℝ)<1)).and
      (eventually_lt_nhds (Real.exp_pos _))).filter_mono nhdsWithin_le_nhds
  refine ⟨Y,η,M,P₀,hY,?_⟩
  filter_upwards [hall,hsmall,Kneser.ActualLambdaFlatness.actual_lambda_flat 1] with s hs hss hflat
  obtain ⟨a,b,θ,V,hc,hV,hVs,hscale,_hphase,hw⟩ := hs
  have ha : -1/2≤a := by
    have hh := (abs_le.mp hc.left_small).1
    linarith only [hh,hc.radius_small]
  have hΛ : lambda (height θ)≤s := by
    rw [hscale]
    simpa only [pow_one] using hflat a ha hc.left_neg hc.left_fixed
  have hheight : 2*(boundaryLoss Y P₀+68)<height θ := by
    have he : Real.exp (-2*Real.pi*height θ)<Real.exp (-2*Real.pi*(2*(boundaryLoss Y P₀+68))) := hΛ.trans_lt hss.2
    have hh := Real.exp_lt_exp.mp he
    nlinarith only [hh,Real.pi_pos]
  have hwidth : 1≤sewingWidth (height θ) (boundaryLoss Y P₀) 64 1 := by
    unfold sewingWidth bandWidth
    linarith
  have har : a<(a+b)/2 := by linarith [hc.left_neg,hc.right_pos]
  have hrb : (a+b)/2<b := by linarith [hc.left_neg,hc.right_pos]
  exact ⟨a,b,θ,V,hc,hV,hVs,hscale,hwidth,
    actual_regular_physical_welding e₁ e₂ A B Γ s a b θ Y η M P₀ Kneser.RealNormalizationAnchor.realAnchor ((a+b)/2)
      hss.1 hc har hrb V hV hVs hw⟩

end Kneser.ActualRegularWelding
end
