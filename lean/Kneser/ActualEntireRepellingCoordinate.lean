import Kneser.ActualInversePoincareFunction
import Kneser.ActualGrowingInverseKoenigsIdentification
import Kneser.ActualRegularWelding

/-! A genuine whole-plane repelling Poincare coordinate for the actual
exponential family. Its normalization agrees exactly with the actual
regular growing-lens inverse, including the specified real base point. -/
set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
namespace Kneser.ActualEntireRepellingCoordinate
open Set Metric Filter Complex
open Kneser.ActualInversePoincareFunction Kneser.ActualInverseLocalKoenigs
open Kneser.ActualGrowingInverseKoenigsIdentification Kneser.InverseKoenigsRealGeometry
open Kneser.ExponentialUnfolding Kneser.PositiveKoenigsOrbit
open Kneser.ActualHolomorphicGrowingLens Kneser.ActualGrowingRealPhases
open Kneser.GrowingBandGeometry Kneser.GrowingLensSpatialHolomorphy
open Kneser.ActualNormalizedGrowingTransition Kneser.ActualRegularWelding
open Kneser.ActualGrowingCoordinateInverse Kneser.NormalizedGrowingFourier
open Kneser.PoincareTimeChart
open Kneser.GrowingStripFourier
open scoped Topology

def repellingPeriod (s b : ℝ) : ℂ := 2*(Real.pi:ℂ)*I/(Real.log (multiplier s b):ℂ)

theorem exists_actual_entire_repelling_of_control
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r : ℝ)
    (hs : 0<s) (hs1 : s<1/2) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (har : a<r) (hrb : r<b) :
    ∃ S : ℂ → ℂ,
      (∀ w, AnalyticAt ℂ S w) ∧ S 0=(r:ℂ) ∧
      (∀ w, S (w+1)=unfolding s (S w)) ∧
      (∀ w, S (w+repellingPeriod s b)=S w) ∧
      ∀ V : ℂ → ℂ,
        (∀w∈strip θ (3*Y+boundaryMargin P), V w∈strip θ (3*Y) ∧
          repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w)=w) →
        ∀w∈symmetricStrip (outerWidth θ Y P),
          S w=regularRepellingInverse A B Γ s a b θ r (e₁ s) (e₂ s) V w := by
  obtain ⟨F,hFa,_hF0,_hFd,hFe,hFi⟩ := exists_actual_poincare_function_of_control e₁ e₂ A B Γ s a b θ Y η M P hs hs1 hc
  have hm : 0 < inverseMultiplier s b := inv_pos.mpr
    (lt_trans (by norm_num) (actual_right_multiplier s b hc.right_pos hc.right_fixed))
  have hmlog : Real.log (inverseMultiplier s b)= -Real.log (multiplier s b) := Real.log_inv _
  have hmlogne : Real.log (inverseMultiplier s b)≠0 := by
    rw [hmlog]
    exact neg_ne_zero.mpr (ne_of_gt (Real.log_pos (actual_right_multiplier s b hc.right_pos hc.right_fixed)))
  have hK := inverseKoenigs_negative_between_of_control e₁ e₂ A B Γ s a b θ Y η M P r hs hs1 hc har hrb
  have hKn : inverseKoenigs s b r≠0 := by intro he; rw [he,Complex.zero_re] at hK; linarith [hK.2]
  let S := chart F (inverseMultiplier s b) (inverseKoenigs s b r)
  have hS0 : S 0=(r:ℂ) := by
    obtain ⟨hZ,hchart⟩ := interval_source a b θ Y r hc.theta_pos hc.width har hrb
    have hh := hFi (bandTime a b θ r) hZ
    rw [hchart] at hh
    simpa only [S,chart,mul_zero,Complex.exp_zero,mul_one] using hh
  have hp : imaginaryPeriod (inverseMultiplier s b)=repellingPeriod s b := by
    unfold imaginaryPeriod repellingPeriod
    rw [hmlog,Complex.ofReal_neg,neg_neg]
  refine ⟨S,chart_analytic F _ _ hFa,hS0,chart_abel F (unfolding s) _ hm _ hFe,?_,?_⟩
  · intro w
    rw [←hp]
    exact chart_periodic F _ hmlogne _ w
  · intro V hVs w hw
    have hmz := normalized_shift_mem_target e₁ e₂ A B Γ s a b θ Y η M P r (by linarith) hc har hrb w hw
    have hv := hVs _ hmz
    have hvY : V (w+repellingConstant A B Γ s a b θ r (e₁ s) (e₂ s))∈strip θ Y :=
      ⟨by linarith [hv.1.1,hc.height_large],by linarith [hv.1.2,hc.height_large]⟩
    have he := normalized_repelling_exponential_of_control e₁ e₂ A B Γ s a b θ Y η M P r hs hs1 hc har hrb _ hvY
    rw [hv.2,add_sub_cancel_right] at he
    have harg : inverseKoenigs s b r*Complex.exp ((Real.log (multiplier s b):ℂ)*w)=
        inverseKoenigs s b (bandChart a b θ (V (w+repellingConstant A B Γ s a b θ r (e₁ s) (e₂ s)))) := by
      rw [he]
      field_simp
    change F (inverseKoenigs s b r*Complex.exp (-(Real.log (inverseMultiplier s b):ℂ)*w))= _
    rw [hmlog,Complex.ofReal_neg,neg_neg,harg]
    exact hFi _ hvY

end Kneser.ActualEntireRepellingCoordinate
end
