import Kneser.FourierSewingQuantitative
import Kneser.StripFourierReconstruction

/-!
The coefficient-space Fourier coefficients are genuine interval-integral
coefficients.  This also proves uniqueness of evaluated coefficients,
and hence associativity and the unit law for the actual convolution.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.WeightedFourier

open Set Filter Metric MeasureTheory
open scoped Topology Classical Interval

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

def circleCoefficientCLM (n : ℤ) : C(AddCircle (1 : ℝ), ℂ) →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp
    ((fourierBasis (T := (1 : ℝ))).repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ))

theorem circleCoefficientCLM_apply (n : ℤ) (f : C(AddCircle (1 : ℝ), ℂ)) :
    circleCoefficientCLM n f = fourierCoeff f n := by
  change (fourierBasis.repr ((ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ) f)) n = _
  rw [fourierBasis_repr, fourierCoeff_toLp]

theorem norm_coefficient_le_coordinate (H : ℝ) (hH : 0 ≤ H) (a : Space) (n : ℤ) :
    ‖coefficient H a n‖ ≤ ‖a n‖ := by
  have hw : 1 ≤ weight H n := by
    rw [weight, Real.one_le_exp_iff]
    positivity
  rw [coefficient, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (weight_pos H n)]
  apply (div_le_iff₀ (weight_pos H n)).mpr
  simpa using mul_le_mul_of_nonneg_left hw (norm_nonneg (a n))

def circleSeries (H : ℝ) (a : Space) : C(AddCircle (1 : ℝ), ℂ) :=
  ∑' m : ℤ, coefficient H a m • fourier m

theorem summable_circleSeries (H : ℝ) (hH : 0 ≤ H) (a : Space) :
    Summable (fun m : ℤ => coefficient H a m • (fourier m : C(AddCircle (1 : ℝ), ℂ))) := by
  apply Summable.of_norm_bounded (summable_norm a)
  intro m
  rw [norm_smul, fourier_norm, mul_one]
  exact norm_coefficient_le_coordinate H hH a m

theorem circleSeries_coe_real (H : ℝ) (hH : 0 ≤ H) (a : Space) (x : ℝ) :
    circleSeries H a (x : AddCircle (1 : ℝ)) = evaluate H a (x : ℂ) := by
  change ContinuousMap.evalCLM ℂ (x : AddCircle (1 : ℝ))
    (∑' m : ℤ, coefficient H a m • fourier m) = _
  rw [(ContinuousMap.evalCLM ℂ (x : AddCircle (1 : ℝ))).map_tsum (summable_circleSeries H hH a)]
  simp only [map_smul, ContinuousMap.evalCLM_apply, fourier_coe_apply, smul_eq_mul,
    Complex.ofReal_one, div_one]
  change (∑' m : ℤ, coefficient H a m *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (x : ℂ))) = _
  rfl

theorem circleSeries_coefficient (H : ℝ) (hH : 0 ≤ H) (a : Space) (n : ℤ) :
    circleCoefficientCLM n (circleSeries H a) = coefficient H a n := by
  rw [circleSeries, (circleCoefficientCLM n).map_tsum (summable_circleSeries H hH a)]
  simp only [map_smul, circleCoefficientCLM_apply, fourierCoeff_fourier]
  rw [tsum_eq_single n]
  · simp
  · intro m hm
    simp [Pi.single_apply, hm.symm]

/-- The nth coefficient is the actual Fourier interval integral. -/
theorem coefficient_eq_intervalIntegral (H : ℝ) (hH : 0 ≤ H) (a : Space) (n : ℤ) :
    coefficient H a n =
      ∫ x in (0 : ℝ)..1, evaluate H a (x : ℂ) *
        Complex.exp (-Kneser.fourierFrequency n * (x : ℂ)) := by
  rw [← circleSeries_coefficient H hH a n, circleCoefficientCLM_apply,
    fourierCoeff_eq_intervalIntegral _ n 0]
  simp only [zero_add, div_self (by norm_num : (1 : ℝ) ≠ 0), one_smul]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [circleSeries_coe_real H hH a x, fourier_coe_apply]
  simp only [smul_eq_mul, Complex.ofReal_one, div_one, Int.cast_neg]
  dsimp [Kneser.fourierFrequency]
  ring

theorem evaluate_injective (H : ℝ) (hH : 0 ≤ H) (a b : Space)
    (hab : ∀ x : ℝ, evaluate H a (x : ℂ) = evaluate H b (x : ℂ)) : a = b := by
  have hcircle : circleSeries H a = circleSeries H b := by
    ext z
    refine QuotientAddGroup.induction_on z ?_
    intro x
    rw [circleSeries_coe_real H hH a x, circleSeries_coe_real H hH b x]
    exact hab x
  apply lp.ext
  funext n
  have he := congrArg (circleCoefficientCLM n) hcircle
  rw [circleSeries_coefficient H hH a n, circleSeries_coefficient H hH b n] at he
  dsimp only [coefficient] at he
  exact (div_left_inj' (Complex.ofReal_ne_zero.mpr (weight_pos H n).ne')).mp he

theorem product_comm (H : ℝ) (hH : 0 ≤ H) (a b : Space) :
    product H hH a b = product H hH b a := by
  apply evaluate_injective H hH
  intro x
  have hx : |(x : ℂ).im| ≤ H := by simpa using hH
  rw [evaluate_product H hH a b _ hx, evaluate_product H hH b a _ hx, mul_comm]

theorem product_assoc (H : ℝ) (hH : 0 ≤ H) (a b c : Space) :
    product H hH (product H hH a b) c = product H hH a (product H hH b c) := by
  apply evaluate_injective H hH
  intro x
  have hx : |(x : ℂ).im| ≤ H := by simpa using hH
  rw [evaluate_product H hH _ _ _ hx, evaluate_product H hH _ _ _ hx,
    evaluate_product H hH _ _ _ hx, evaluate_product H hH _ _ _ hx, mul_assoc]

theorem product_atom_zero_right (H : ℝ) (hH : 0 ≤ H) (a : Space) :
    product H hH a (atom H 0) = a := by
  apply evaluate_injective H hH
  intro x
  have hx : |(x : ℂ).im| ≤ H := by simpa using hH
  rw [evaluate_product H hH _ _ _ hx, evaluate_atom]
  simp [mode, Kneser.fourierFrequency]

theorem product_atom_zero_left (H : ℝ) (hH : 0 ≤ H) (a : Space) :
    product H hH (atom H 0) a = a := by
  rw [product_comm, product_atom_zero_right]

end Kneser.WeightedFourier

end
