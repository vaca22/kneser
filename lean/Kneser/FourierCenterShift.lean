import Kneser.GateFourierHeight
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
The actual integral coefficients are transported under a complex change of
repelling-coordinate origin. The zero mode changes by the origin; every
nonzero mode picks up its exponential phase. Consequently the normalized
horn coefficient is exactly independent of that choice, at every parameter.
-/

set_option autoImplicit false
noncomputable section
namespace Kneser.FourierCenterShift

open Complex MeasureTheory Kneser.GateFourierDerivative Kneser.GateFourierHeight
open scoped Interval

def centered (T : ℂ → ℂ) (c z : ℂ) : ℂ := T (z - c)

theorem integral_weight (n : ℤ) :
    (∫ x : ℝ in (0 : ℝ)..1, exp (-Kneser.fourierFrequency n * (x : ℂ))) =
      if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · simp [hn, Kneser.fourierFrequency]
  · have hf : -Kneser.fourierFrequency n ≠ 0 := by
      simp only [neg_ne_zero, Kneser.fourierFrequency, ne_eq, mul_eq_zero]
      have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      simp [hp, hnc, Complex.I_ne_zero]
    rw [integral_exp_mul_complex hf]
    simp [exp_neg_frequency, hn]

theorem shifted_periodic_integral (n : ℤ) (T : ℂ → ℂ)
    (hp : ∀ z : ℂ, T (z + 1) = T z + 1) (d : ℝ) :
    (∫ x : ℝ in (0 : ℝ)..1,
      weightedDifference n T ((x - d : ℝ) : ℂ)) = gateFourierCoefficient n 0 T := by
  let G : ℝ → ℂ := fun x => weightedDifference n T (x : ℂ)
  have hG : Function.Periodic G 1 := by
    intro x
    simpa only [G, Complex.ofReal_add, Complex.ofReal_one] using
      weightedDifference_periodic n T hp (x : ℂ)
  change (∫ x : ℝ in (0 : ℝ)..1, G (x - d)) = _
  rw [intervalIntegral.integral_comp_sub_right]
  simp only [zero_sub]
  have he := hG.intervalIntegral_add_eq (-d) 0
  simp only [zero_sub, zero_add, neg_add_eq_sub] at he
  rw [he]
  unfold gateFourierCoefficient gateWeight
  simp only [gatePoint, Complex.ofReal_zero, mul_zero, add_zero]
  rfl

theorem coefficient_center_shift (n : ℤ) (T : ℂ → ℂ) (c : ℂ)
    (hp : ∀ z : ℂ, T (z + 1) = T z + 1)
    (hc : Continuous (fun x : ℝ => T (x : ℂ))) :
    gateFourierCoefficient n c.im (centered T c) =
      exp (-Kneser.fourierFrequency n * c) *
        (gateFourierCoefficient n 0 T - if n = 0 then c else 0) := by
  let ω := Kneser.fourierFrequency n
  let G : ℝ → ℂ := fun x => weightedDifference n T ((x - c.re : ℝ) : ℂ)
  let E : ℝ → ℂ := fun x => exp (-ω * ((x - c.re : ℝ) : ℂ))
  have hpoint (x : ℝ) : gatePoint c.im x - c = ((x - c.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [gatePoint]
  have hweight (x : ℝ) : gateWeight n c.im x = exp (-ω * c) * E x := by
    have he : -ω * gatePoint c.im x = -ω * c + -ω * ((x - c.re : ℝ) : ℂ) := by
      have := hpoint x
      linear_combination -ω * this
    change exp (-ω * gatePoint c.im x) = _
    rw [he, exp_add]
  have hG : IntervalIntegrable G volume (0 : ℝ) 1 := by
    apply Continuous.intervalIntegrable
    unfold G weightedDifference
    exact ((hc.comp (continuous_id.sub continuous_const)).sub
      (Complex.continuous_ofReal.comp (continuous_id.sub continuous_const))).mul
      ((Complex.continuous_exp).comp
        (continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_id.sub continuous_const))))
  have hE : IntervalIntegrable E volume (0 : ℝ) 1 := by
    exact (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_id.sub continuous_const)))).intervalIntegrable _ _
  have heq : gateFourierCoefficient n c.im (centered T c) =
      exp (-ω * c) * (∫ x : ℝ in (0 : ℝ)..1, G x - c * E x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only [centered]
    rw [hpoint, hweight]
    dsimp [G, E, weightedDifference]
    have hz : gatePoint c.im x = ((x - c.re : ℝ) : ℂ) + c := by
      linear_combination hpoint x
    rw [hz]
    ring
  rw [heq, intervalIntegral.integral_sub hG (hE.const_mul c),
    intervalIntegral.integral_const_mul, shifted_periodic_integral n T hp c.re]
  have hi : (∫ x : ℝ in (0 : ℝ)..1, E x) =
      exp (ω * (c.re : ℂ)) * (if n = 0 then 1 else 0) := by
    have he (x : ℝ) : E x = exp (ω * (c.re : ℂ)) * exp (-ω * (x : ℂ)) := by
      dsimp [E]
      rw [Complex.ofReal_sub]
      have hr : -ω * ((x : ℂ) - (c.re : ℂ)) = ω * (c.re : ℂ) + -ω * (x : ℂ) := by ring
      rw [hr, exp_add]
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul, integral_weight]
  rw [hi]
  by_cases hn : n = 0
  · simp [hn, ω, Kneser.fourierFrequency]
  · simp [hn, ω]

theorem horn_gauge_invariant (n : ℤ) (hn : n ≠ 0) (T : ℂ → ℂ) (c : ℂ)
    (hp : ∀ z : ℂ, T (z + 1) = T z + 1)
    (hc : Continuous (fun x : ℝ => T (x : ℂ))) :
    gateFourierCoefficient n c.im (centered T c) *
        exp (-Kneser.fourierFrequency n * gateFourierCoefficient 0 c.im (centered T c)) =
      gateFourierCoefficient n 0 T * exp (-Kneser.fourierFrequency n * gateFourierCoefficient 0 0 T) := by
  rw [coefficient_center_shift n T c hp hc, coefficient_center_shift 0 T c hp hc]
  simp only [hn, ↓reduceIte, Kneser.fourierFrequency, Int.cast_zero, mul_zero,
    neg_zero, zero_mul, exp_zero, one_mul, sub_zero]
  have he : -(2 * (Real.pi : ℂ) * I * (n : ℂ)) *
      (gateFourierCoefficient 0 0 T - c) =
      -(2 * (Real.pi : ℂ) * I * (n : ℂ)) * gateFourierCoefficient 0 0 T +
        (2 * (Real.pi : ℂ) * I * (n : ℂ)) * c := by ring
  rw [he, exp_add]
  have hx := exp_add (-(2 * (Real.pi : ℂ) * I * (n : ℂ)) * c)
    ((2 * (Real.pi : ℂ) * I * (n : ℂ)) * c)
  have hz : exp (-(2 * (Real.pi : ℂ) * I * (n : ℂ)) * c) *
      exp ((2 * (Real.pi : ℂ) * I * (n : ℂ)) * c) = 1 := by
    rw [← hx]
    simp
  linear_combination gateFourierCoefficient n 0 T *
    exp (-(2 * (Real.pi : ℂ) * I * (n : ℂ)) * gateFourierCoefficient 0 0 T) * hz

end Kneser.FourierCenterShift
end
