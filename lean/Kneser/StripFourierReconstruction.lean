import Kneser.GateFourierHeight
import Mathlib.Analysis.Fourier.AddCircle

/-!
Actual interval-integral Fourier coefficients reconstruct a continuous
translation-equivariant transition on every horizontal line on which the
weighted coefficients are absolutely summable. This identifies the series
with the transition itself, rather than defining a substitute by its series.
-/

set_option autoImplicit false
noncomputable section
namespace Kneser.StripFourierReconstruction

open Complex MeasureTheory Kneser.GateFourierDerivative
open scoped Interval

def displacement (T : ℂ → ℂ) (Y x : ℝ) : ℂ := T (gatePoint Y x) - gatePoint Y x

theorem displacement_periodic (T : ℂ → ℂ) (Y : ℝ)
    (hp : ∀ z, T (z + 1) = T z + 1) : Function.Periodic (displacement T Y) 1 := by
  intro x
  have hz : gatePoint Y (x + 1) = gatePoint Y x + 1 := by simp [gatePoint]; ring
  dsimp [displacement]
  rw [hz, hp]
  ring

def circleDisplacement (T : ℂ → ℂ) (Y : ℝ)
    (hp : ∀ z, T (z + 1) = T z + 1)
    (hc : Continuous (displacement T Y)) : C(AddCircle (1 : ℝ), ℂ) where
  toFun := (displacement_periodic T Y hp).lift
  continuous_toFun := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    exact hc

theorem circleDisplacement_coe (T : ℂ → ℂ) (Y : ℝ)
    (hp : ∀ z, T (z + 1) = T z + 1)
    (hc : Continuous (displacement T Y)) (x : ℝ) :
    circleDisplacement T Y hp hc (x : AddCircle (1 : ℝ)) = displacement T Y x := rfl

theorem circle_coefficient (T : ℂ → ℂ) (Y : ℝ)
    (hp : ∀ z, T (z + 1) = T z + 1)
    (hc : Continuous (displacement T Y)) (n : ℤ) :
    fourierCoeff (circleDisplacement T Y hp hc) n =
      exp (Kneser.fourierFrequency n * (I * (Y : ℂ))) * gateFourierCoefficient n Y T := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  rw [fourierCoeff_eq_intervalIntegral _ n 0]
  simp only [zero_add, div_self (by norm_num : (1 : ℝ) ≠ 0), one_smul]
  unfold gateFourierCoefficient
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [circleDisplacement_coe, fourier_coe_apply]
  simp only [smul_eq_mul, Complex.ofReal_one, div_one, Int.cast_neg]
  dsimp only [displacement]
  have he : exp (Kneser.fourierFrequency n * (I * (Y : ℂ))) * gateWeight n Y x =
      exp (-(2 * (Real.pi : ℂ) * I * (n : ℂ)) * (x : ℂ)) := by
    rw [gateWeight, ← exp_add]
    congr 1
    dsimp [gatePoint, Kneser.fourierFrequency]
    ring
  rw [← mul_assoc, mul_right_comm (exp (Kneser.fourierFrequency n * (I * (Y : ℂ))))
    (T (gatePoint Y x) - gatePoint Y x) (gateWeight n Y x), he]
  congr 1
  congr 1
  ring

theorem hasSum_gate_fourier (T : ℂ → ℂ) (Y x : ℝ)
    (hp : ∀ z, T (z + 1) = T z + 1)
    (hc : Continuous (displacement T Y))
    (hs : Summable (fun n : ℤ =>
      exp (Kneser.fourierFrequency n * (I * (Y : ℂ))) * gateFourierCoefficient n Y T)) :
    HasSum (fun n : ℤ => gateFourierCoefficient n Y T *
      exp (Kneser.fourierFrequency n * gatePoint Y x)) (displacement T Y x) := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hsum : Summable (fourierCoeff (circleDisplacement T Y hp hc)) := by
    have heq : fourierCoeff (circleDisplacement T Y hp hc) =
        (fun n : ℤ => exp (Kneser.fourierFrequency n * (I * (Y : ℂ))) * gateFourierCoefficient n Y T) :=
      funext (circle_coefficient T Y hp hc)
    rw [heq]
    exact hs
  have hh := has_pointwise_sum_fourier_series_of_summable hsum (x : AddCircle (1 : ℝ))
  rw [circleDisplacement_coe] at hh
  convert hh using 1
  funext n
  rw [circle_coefficient, fourier_coe_apply]
  simp only [smul_eq_mul, Complex.ofReal_one, div_one]
  have he : Kneser.fourierFrequency n * gatePoint Y x =
      Kneser.fourierFrequency n * (I * (Y : ℂ)) +
        2 * (Real.pi : ℂ) * I * (n : ℂ) * (x : ℂ) := by
    dsimp [gatePoint, Kneser.fourierFrequency]
    ring
  rw [he, exp_add]
  ring

theorem transition_eq_fourier (T : ℂ → ℂ) (Y x : ℝ)
    (hp : ∀ z, T (z + 1) = T z + 1)
    (hc : Continuous (displacement T Y))
    (hs : Summable (fun n : ℤ =>
      exp (Kneser.fourierFrequency n * (I * (Y : ℂ))) * gateFourierCoefficient n Y T)) :
    T (gatePoint Y x) = gatePoint Y x +
      ∑' n : ℤ, gateFourierCoefficient n Y T * exp (Kneser.fourierFrequency n * gatePoint Y x) := by
  rw [(hasSum_gate_fourier T Y x hp hc hs).tsum_eq]
  dsimp [displacement]
  ring

end Kneser.StripFourierReconstruction
end
