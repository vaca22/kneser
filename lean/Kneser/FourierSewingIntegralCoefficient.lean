import Kneser.WeightedFourierIntegral

/-!
The sewing coefficient used in the quantitative comparison is the actual
interval-integral Fourier coefficient of the normalized sewn coordinate.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.FourierSewing

open Set Filter Metric MeasureTheory
open scoped Topology Classical Interval
open Kneser.WeightedFourier

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def translatedCircle (H : ℝ) (P : Space) (z₀ : ℂ) : C(AddCircle (1 : ℝ), ℂ) :=
  ∑' m : ℤ, (coefficient H P m * mode m z₀) • fourier m

theorem summable_translatedCircle (H : ℝ) (P : Space)
    (hP : ∀ n : ℤ, n < 0 → P n = 0) (z₀ : ℂ) (hz₀ : 0 ≤ H + z₀.im) :
    Summable (fun m : ℤ =>
      (coefficient H P m * mode m z₀) • (fourier m : C(AddCircle (1 : ℝ), ℂ))) := by
  apply Summable.of_norm_bounded (summable_norm P)
  intro m
  rw [norm_smul, fourier_norm, mul_one]
  exact norm_positive_term_le H P hP z₀ hz₀ m

theorem translatedCircle_coe_real (H : ℝ) (P : Space)
    (hP : ∀ n : ℤ, n < 0 → P n = 0) (z₀ : ℂ) (hz₀ : 0 ≤ H + z₀.im) (x : ℝ) :
    translatedCircle H P z₀ (x : AddCircle (1 : ℝ)) =
      evaluate H P (z₀ + (x : ℂ)) := by
  change ContinuousMap.evalCLM ℂ (x : AddCircle (1 : ℝ))
    (∑' m : ℤ, (coefficient H P m * mode m z₀) • fourier m) = _
  rw [(ContinuousMap.evalCLM ℂ (x : AddCircle (1 : ℝ))).map_tsum
    (summable_translatedCircle H P hP z₀ hz₀)]
  simp only [map_smul, ContinuousMap.evalCLM_apply, fourier_coe_apply, smul_eq_mul,
    Complex.ofReal_one, div_one]
  unfold evaluate
  apply tsum_congr
  intro m
  change (coefficient H P m * mode m z₀) * mode m (x : ℂ) =
    coefficient H P m * mode m (z₀ + (x : ℂ))
  rw [mode, mode, mode, mul_add, Complex.exp_add, mul_assoc]

theorem translatedCircle_coefficient (H : ℝ) (P : Space)
    (hP : ∀ n : ℤ, n < 0 → P n = 0) (z₀ : ℂ) (hz₀ : 0 ≤ H + z₀.im) (n : ℤ) :
    circleCoefficientCLM n (translatedCircle H P z₀) = coefficient H P n * mode n z₀ := by
  rw [translatedCircle, (circleCoefficientCLM n).map_tsum
    (summable_translatedCircle H P hP z₀ hz₀)]
  simp only [map_smul, circleCoefficientCLM_apply, fourierCoeff_fourier]
  rw [tsum_eq_single n]
  · simp
  · intro m hm
    simp [hm.symm]

def sewnCoordinate (H h : ℝ) (P : Space) (t₀ ζ : ℂ) (z : ℂ) : ℂ :=
  (normalizingCentre h t₀ + ζ + z) + t₀ +
    evaluate H P (normalizingCentre h t₀ + ζ + z) - (h : ℂ) * Complex.I

def sewnDisplacement (H h : ℝ) (P : Space) (t₀ ζ : ℂ) (z : ℂ) : ℂ :=
  sewnCoordinate H h P t₀ ζ z - z

theorem sewnDisplacement_eq (H h : ℝ) (P : Space) (t₀ ζ z : ℂ) :
    sewnDisplacement H h P t₀ ζ z =
      ζ + evaluate H P (normalizingCentre h t₀ + ζ + z) := by
  unfold sewnDisplacement sewnCoordinate normalizingCentre
  ring

theorem sewnCoordinate_zero (H h : ℝ) (P : Space) (t₀ ζ : ℂ)
    (hroot : (normalizingCentre h t₀ + ζ) +
      evaluate H P (normalizingCentre h t₀ + ζ) = normalizingCentre h t₀) :
    sewnCoordinate H h P t₀ ζ 0 = 0 := by
  simp only [sewnCoordinate, add_zero]
  rw [show (normalizingCentre h t₀ + ζ) + t₀ +
      evaluate H P (normalizingCentre h t₀ + ζ) =
      ((normalizingCentre h t₀ + ζ) + evaluate H P (normalizingCentre h t₀ + ζ)) + t₀ by ring,
    hroot]
  unfold normalizingCentre
  ring

theorem sewnCoordinate_translation (H h : ℝ) (P : Space) (t₀ ζ z : ℂ) :
    sewnCoordinate H h P t₀ ζ (z + 1) = sewnCoordinate H h P t₀ ζ z + 1 := by
  unfold sewnCoordinate
  rw [show normalizingCentre h t₀ + ζ + (z + 1) =
    (normalizingCentre h t₀ + ζ + z) + 1 by ring, evaluate_periodic]
  ring

theorem translatedCoefficient_eq_intervalIntegral (H h : ℝ) (P : Space)
    (hP : ∀ n : ℤ, n < 0 → P n = 0) (t₀ ζ : ℂ)
    (hpoint : 0 ≤ H + (normalizingCentre h t₀ + ζ).im) (n : ℕ) (hn : 1 ≤ n) :
    translatedCoefficient H h P t₀ ζ n =
      ∫ x in (0 : ℝ)..1, sewnDisplacement H h P t₀ ζ (x : ℂ) *
        Complex.exp (-Kneser.fourierFrequency n * (x : ℂ)) := by
  let f : C(AddCircle (1 : ℝ), ℂ) :=
    ζ • fourier 0 + translatedCircle H P (normalizingCentre h t₀ + ζ)
  have hnzero : (n : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt (by omega : 0 < n))
  have hnNat : n ≠ 0 := by omega
  have hcoeft : circleCoefficientCLM n f = translatedCoefficient H h P t₀ ζ n := by
    dsimp [f]
    rw [map_add, map_smul, circleCoefficientCLM_apply, fourierCoeff_fourier,
      translatedCircle_coefficient H P hP _ hpoint]
    simp [Pi.single_apply, hnzero, hnNat, translatedCoefficient]
  rw [← hcoeft, circleCoefficientCLM_apply, fourierCoeff_eq_intervalIntegral _ n 0]
  simp only [zero_add, div_self (by norm_num : (1 : ℝ) ≠ 0), one_smul]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  have hfx : f (x : AddCircle (1 : ℝ)) = sewnDisplacement H h P t₀ ζ (x : ℂ) := by
    simp only [f, ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul,
      fourier_zero, mul_one, translatedCircle_coe_real H P hP _ hpoint, sewnDisplacement_eq]
  rw [hfx, fourier_coe_apply]
  simp only [smul_eq_mul, Complex.ofReal_one, div_one, Int.cast_natCast, Int.cast_neg]
  dsimp [Kneser.fourierFrequency]
  push_cast
  ring

end Kneser.FourierSewing

end
