import Kneser.ActualLambdaFlatness
import Kneser.GrowingBandGeometry

/-!
The height in the genuine two-root chart is exactly the logarithmic period
of the actual attracting multiplier. Its exponential sewing scale is the
paper's actual Lambda, so the scale is not an independent model parameter.
-/

set_option autoImplicit false
noncomputable section
namespace Kneser.ActualSewingScale

open Kneser.ExponentialUnfolding Kneser.RealExponentialPetal
open Kneser.ActualLambdaFlatness

def actualHeight (s a : ℝ) : ℝ := -2 * Real.pi / Real.log (attractingMultiplier s a)

theorem actualHeight_positive (s a : ℝ)
    (hμ : 0 < attractingMultiplier s a) (hμ1 : attractingMultiplier s a < 1) :
    0 < actualHeight s a := by
  unfold actualHeight
  exact div_pos_of_neg_of_neg (by linarith [Real.pi_pos]) (Real.log_neg hμ hμ1)

theorem exponential_actualHeight (s a : ℝ) :
    Real.exp (-2 * Real.pi * actualHeight s a) = lambdaFactor s a := by
  unfold actualHeight lambdaFactor
  congr 1
  ring

theorem actual_band_height (Q : QuotientControl) (s a b : ℝ)
    (hs : s < 1) (ha : -1 < a) (hab : a < b)
    (hroota : unfolding s a = (a : ℂ)) (hrootb : unfolding s b = (b : ℂ)) :
    GrowingBandGeometry.height (timeScale Q ((1 - s) * (b - a))) = actualHeight s a := by
  rw [timeScale_eq_neg_log_multiplier Q s a b hs ha hab hroota hrootb]
  unfold GrowingBandGeometry.height actualHeight attractingMultiplier
  ring

theorem actual_band_exponential_scale (Q : QuotientControl) (s a b : ℝ)
    (hs : s < 1) (ha : -1 < a) (hab : a < b)
    (hroota : unfolding s a = (a : ℂ)) (hrootb : unfolding s b = (b : ℂ)) :
    Real.exp (-2 * Real.pi * GrowingBandGeometry.height
      (timeScale Q ((1 - s) * (b - a)))) = lambdaFactor s a := by
  rw [actual_band_height Q s a b hs ha hab hroota hrootb, exponential_actualHeight]

theorem exists_actual_positive_height_and_flat_scale (m : ℕ) :
    ∀ᶠ s : ℝ in nhdsWithin 0 (Set.Ioi 0), ∃ a : ℝ,
      -1 / 2 < a ∧ a < 0 ∧ unfolding (s : ℂ) (a : ℂ) = (a : ℂ) ∧
      deriv (unfolding (s : ℂ)) (a : ℂ) = (attractingMultiplier s a : ℂ) ∧
      0 < actualHeight s a ∧ Real.exp (-2 * Real.pi * actualHeight s a) ≤ s ^ m := by
  filter_upwards [exists_actual_flat_lambda m] with s hs
  obtain ⟨a, ha, ha0, hroot, hd, hμ, hμ1, _hΛ, hflat⟩ := hs
  exact ⟨a, ha, ha0, hroot, hd, actualHeight_positive s a hμ hμ1,
    by rwa [exponential_actualHeight]⟩

end Kneser.ActualSewingScale
end
