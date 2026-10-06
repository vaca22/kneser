import Kneser.ActualLocalGrowingTransitionBridge
import Kneser.NormalizedGrowingFourier

/-! The actual fixed gate's change of repelling origin lies inside the
proved normalized global Fourier strip. Thus the contour change needed
for equality of its genuine horn coefficients stays in the true domain. -/

set_option autoImplicit false
noncomputable section
namespace Kneser.ActualNormalizedGateShift

open Set Complex Kneser.GrowingBandGeometry Kneser.ActualLensModel
open Kneser.ActualHolomorphicGrowingLens Kneser.GrowingLensSpatialHolomorphy
open Kneser.ActualGrowingCoordinateInverse Kneser.ActualLocalGrowingTransitionBridge
open Kneser.ActualNormalizedGrowingTransition Kneser.NormalizedGrowingFourier
open Kneser.ActualQuantitativeGateTransition

theorem actual_gate_shift_mem_fourier_strip
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P Yg r : ℝ)
    (hs1 : s < 1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (har : a < r) (hrb : r < b) (Z : ℂ)
    (hZ : Z ∈ strip θ (3 * Y + 2 * boundaryMargin P + 4 * P))
    (he : bandChart a b θ Z = chartPoint Yg 0) :
    |(gateConstant A B Γ s a b θ Yg (e₁ s) (e₂ s) -
      repellingConstant A B Γ s a b θ r (e₁ s) (e₂ s)).im| < outerWidth θ Y P := by
  have hP : 0 ≤ P := (norm_nonneg (e₁ s)).trans hc.first_model_bound
  have hB : 0 ≤ boundaryMargin P := by unfold boundaryMargin; positivity
  have hY : 0 < Y := by linarith [hc.height_large]
  have hsource : Z ∈ strip θ Y := ⟨by linarith [hZ.1],by linarith [hZ.2]⟩
  have hg : gateConstant A B Γ s a b θ Yg (e₁ s) (e₂ s) =
      repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) Z := by
    unfold gateConstant
    rw [←he]
    rfl
  have hp := (actual_coordinate_phase_bounds e₁ e₂ A B Γ s a b θ Y η M P hc Z hsource).2
  have hr := repellingConstant_phase_of_control e₁ e₂ A B Γ s a b θ Y η M P r hs1 hc har hrb
  rw [hg,Complex.sub_im,hr.1]
  apply abs_lt.mpr
  have hbp := abs_le.mp hp
  have hbr := abs_le.mp hr.2
  simp only [Complex.sub_im] at hbp
  dsimp only [outerWidth,boundaryLoss]
  constructor <;> linarith [hZ.1,hZ.2,hbp.1,hbp.2,hbr.1,hbr.2]

end Kneser.ActualNormalizedGateShift
end
