import Kneser.GateFourierDerivative
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
Fourier coefficients of a holomorphic translation-equivariant transition
are independent of the chosen horizontal gate height. Cauchy's theorem
and cancellation of the genuine vertical integrals prove the identity.
-/

noncomputable section

namespace Kneser.GateFourierHeight

open Set Complex MeasureTheory Kneser.GateFourierDerivative
open scoped Interval

def weightedDifference (n : ℤ) (T : ℂ → ℂ) (z : ℂ) : ℂ :=
  (T z - z) * Complex.exp (-fourierFrequency n * z)

theorem exp_neg_frequency (n : ℤ) : Complex.exp (-fourierFrequency n) = 1 := by
  have h : -fourierFrequency n = ((-n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    simp only [fourierFrequency, Int.cast_neg]
    ring
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I (-n)

theorem weightedDifference_periodic (n : ℤ) (T : ℂ → ℂ)
    (hT : ∀ z : ℂ, T (z + 1) = T z + 1) (z : ℂ) :
    weightedDifference n T (z + 1) = weightedDifference n T z := by
  have hf : -fourierFrequency n * (z + 1) =
      -fourierFrequency n * z + -fourierFrequency n := by ring
  simp only [weightedDifference, hT, hf, Complex.exp_add, exp_neg_frequency, mul_one]
  congr 1
  ring

theorem gateFourier_height_independent (n : ℤ) (T : ℂ → ℂ) (Y₀ Y₁ : ℝ)
    (hT : ∀ z : ℂ, T (z + 1) = T z + 1)
    (hhol : DifferentiableOn ℂ T
      (Set.uIcc (0 : ℝ) 1 ×ℂ Set.uIcc Y₀ Y₁)) :
    gateFourierCoefficient n Y₀ T = gateFourierCoefficient n Y₁ T := by
  let G : ℂ → ℂ := weightedDifference n T
  have hG : DifferentiableOn ℂ G (Set.uIcc (0 : ℝ) 1 ×ℂ Set.uIcc Y₀ Y₁) :=
    (hhol.sub differentiableOn_id).mul
      ((differentiable_const (-fourierFrequency n)).mul differentiable_id).cexp.differentiableOn
  have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G
    (Complex.I * (Y₀ : ℂ)) (1 + Complex.I * (Y₁ : ℂ)) (by simpa using hG)
  have hv : (∫ y : ℝ in Y₀..Y₁, G (1 + y * Complex.I)) =
      ∫ y : ℝ in Y₀..Y₁, G (0 + y * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro y _hy
    have h := weightedDifference_periodic n T hT ((y : ℂ) * Complex.I)
    simpa only [G, add_comm, zero_add, add_zero] using h
  simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, Complex.mul_im, one_mul,
    zero_add, Complex.add_re, Complex.one_re, add_zero, Complex.add_im,
    Complex.one_im, Complex.ofReal_one, Complex.ofReal_zero] at hc
  rw [hv] at hc
  simp only [zero_add] at hc
  have hgate : ∀ Y : ℝ, (∫ x : ℝ in (0 : ℝ)..1, G (x + Y * Complex.I)) =
      gateFourierCoefficient n Y T := by
    intro Y
    unfold gateFourierCoefficient gateWeight
    apply intervalIntegral.integral_congr
    intro x _hx
    simp only [G, weightedDifference, gatePoint, mul_comm Complex.I (Y : ℂ)]
  rw [hgate Y₀, hgate Y₁] at hc
  linear_combination hc

end Kneser.GateFourierHeight

end
