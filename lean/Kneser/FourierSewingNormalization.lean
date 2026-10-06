import Kneser.WeightedFourierHalfPlane

/-!
The normalizing translation is constructed from the actual positive
Fourier function by Banach contraction.  A root of the normalization
equation is not an input.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.FourierSewing

open Set Filter Metric
open scoped Topology Classical
open Kneser.WeightedFourier

def normalizationRate (H : ℝ) (c : ℂ) : ℝ :=
  Real.exp (-2 * Real.pi * (H + c.im - 1))

def normalizationValueBound (H : ℝ) (c : ℂ) (ρ B : ℝ) : ℝ :=
  B + ρ * normalizationRate H c / (1 - normalizationRate H c)

def normalizationLipschitzBound (H : ℝ) (c : ℂ) (ρ : ℝ) : ℝ :=
  4 * Real.pi * ρ * normalizationRate H c / (1 - normalizationRate H c) ^ 2

/-- The genuine normalization root exists on a controlled disc, with
the quantitative smallness bound needed for coefficient comparison. -/
theorem exists_normalizing_shift (H : ℝ) (P : Space)
    (hP : ∀ n : ℤ, n < 0 → P n = 0) (c : ℂ) (ρ B : ℝ)
    (hgap : 0 < H + c.im - 1) (hρ : 0 ≤ ρ) (hB : 0 ≤ B)
    (hPnorm : ‖P‖ ≤ ρ) (hconstant : ‖coefficient H P 0‖ ≤ B)
    (hvalue : normalizationValueBound H c ρ B ≤ 1)
    (hlip : normalizationLipschitzBound H c ρ ≤ (1 / 2 : ℝ)) :
    ∃ ζ : ℂ, ‖ζ‖ ≤ normalizationValueBound H c ρ B ∧ ‖ζ‖ ≤ 1 ∧
      (c + ζ) + evaluate H P (c + ζ) = c := by
  let f : ℂ → ℂ := fun ζ => -evaluate H P (c + ζ)
  have hq : 0 < normalizationRate H c := Real.exp_pos _
  have hqlt : normalizationRate H c < 1 := by
    unfold normalizationRate
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have hpoint (ζ : ℂ) (hζ : ζ ∈ closedBall (0 : ℂ) 1) : c + ζ ∈ closedBall c 1 := by
    simpa [mem_closedBall, dist_eq_norm] using hζ
  have hb (ζ : ℂ) (hζ : ζ ∈ closedBall (0 : ℂ) 1) :
      ‖f ζ‖ ≤ normalizationValueBound H c ρ B := by
    have hζim := im_lower_on_closedBall c (c + ζ) 1 (hpoint ζ hζ)
    have he := norm_evaluate_positive_sub_constant_le H (c.im - 1)
      (by linarith) P hP (c + ζ) hζim
    have he' : ‖evaluate H P (c + ζ) - coefficient H P 0‖ ≤
        ρ * normalizationRate H c / (1 - normalizationRate H c) := by
      have hi : H + (c.im - 1) = H + c.im - 1 := by ring
      rw [hi] at he
      exact he.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hPnorm hq.le) (sub_nonneg.mpr hqlt.le))
    change ‖-evaluate H P (c + ζ)‖ ≤ _
    rw [norm_neg]
    calc
      _ ≤ ‖evaluate H P (c + ζ) - coefficient H P 0‖ + ‖coefficient H P 0‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ ρ * normalizationRate H c / (1 - normalizationRate H c) + B := add_le_add he' hconstant
      _ = _ := by unfold normalizationValueBound; ring
  have hm : MapsTo f (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := by
    intro ζ hζ
    rw [mem_closedBall, dist_zero_right]
    exact (hb ζ hζ).trans hvalue
  have hc : ContractingWith (1 / 2 : NNReal) (hm.restrict f _ _) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro ζ η
    change dist (f ζ.val) (f η.val) ≤ _ * dist ζ.val η.val
    rw [dist_eq_norm, dist_eq_norm]
    have he : f ζ.val - f η.val =
        -(evaluate H P (c + ζ.val) - evaluate H P (c + η.val)) := by
      dsimp [f]
      abel
    rw [he, norm_neg]
    have hx := norm_evaluate_positive_sub_le_on_disc H P hP c 1 hgap
      (c + ζ.val) (c + η.val) (hpoint _ ζ.property) (hpoint _ η.property)
    have hediff : (c + ζ.val) - (c + η.val) = ζ.val - η.val := by abel
    rw [hediff] at hx
    exact hx.trans (mul_le_mul_of_nonneg_right
      ((div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hPnorm (by positivity : (0 : ℝ) ≤ 4 * Real.pi)) hq.le)
        (sq_nonneg _)).trans hlip) (norm_nonneg _))
  obtain ⟨ζ, hζ, hfixed, _, _⟩ := ContractingWith.exists_fixedPoint'
    isClosed_closedBall.isComplete hm hc (by simp : (0 : ℂ) ∈ closedBall 0 1) (edist_ne_top 0 (f 0))
  have hζnorm : ‖ζ‖ ≤ 1 := by simpa using hζ
  have hn : ‖ζ‖ ≤ normalizationValueBound H c ρ B := by
    rw [← hfixed]
    exact hb ζ hζ
  refine ⟨ζ, hn, hζnorm, ?_⟩
  have he : -evaluate H P (c + ζ) = ζ := hfixed
  linear_combination -he

end Kneser.FourierSewing

end
