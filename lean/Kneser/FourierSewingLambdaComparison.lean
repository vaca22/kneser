import Kneser.FourierSewingNormalization

/-!
Actual translated positive Fourier coefficients and their exponentially
small comparison with the original horn coefficients.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.FourierSewing

open Set Filter Metric
open scoped Topology Classical
open Kneser.WeightedFourier

def lambda (h : ℝ) : ℝ := Real.exp (-2 * Real.pi * h)

def normalizingCentre (h : ℝ) (t₀ : ℂ) : ℂ := (h : ℂ) * Complex.I - t₀

def hornPhase (t₀ : ℂ) (n : ℤ) : ℂ := Complex.exp (-Kneser.fourierFrequency n * t₀)

def translatedCoefficient (H h : ℝ) (P : Space) (t₀ ζ : ℂ) (n : ℕ) : ℂ :=
  coefficient H P n * mode n (normalizingCentre h t₀ + ζ)

theorem translated_mode_identity (h : ℝ) (t₀ ζ : ℂ) (n : ℕ) :
    mode n (normalizingCentre h t₀ + ζ) =
      (lambda h : ℂ) ^ n * hornPhase t₀ n * mode n ζ := by
  have he : Kneser.fourierFrequency n * (normalizingCentre h t₀ + ζ) =
      (n : ℂ) * ((-2 * Real.pi * h : ℝ) : ℂ) +
        (-Kneser.fourierFrequency n * t₀) + Kneser.fourierFrequency n * ζ := by
    dsimp only [normalizingCentre, Kneser.fourierFrequency]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [mode, he, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul,
    ← Complex.ofReal_exp]
  rfl

theorem translated_coefficient_identity (H h : ℝ) (P : Space) (t₀ ζ : ℂ) (n : ℕ) :
    translatedCoefficient H h P t₀ ζ n / (lambda h : ℂ) ^ n =
      coefficient H P n * hornPhase t₀ n * mode n ζ := by
  rw [translatedCoefficient, translated_mode_identity]
  have hl : (lambda h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  field_simp

theorem translated_coefficient_sub_identity (H h : ℝ) (P : Space)
    (t₀ ζ t : ℂ) (n : ℕ) :
    translatedCoefficient H h P t₀ ζ n / (lambda h : ℂ) ^ n - t * hornPhase t₀ n =
      (t * hornPhase t₀ n) * (mode n ζ - 1) +
        (coefficient H P n - t) * hornPhase t₀ n * mode n ζ := by
  rw [translated_coefficient_identity]
  ring

theorem norm_hornPhase (h : ℝ) (t₀ : ℂ) (ht₀ : t₀.im = h / 2) (n : ℤ) :
    ‖hornPhase t₀ n‖ = Real.exp (Real.pi * (n : ℝ) * h) := by
  rw [hornPhase, Complex.norm_exp]
  congr 1
  simp only [Kneser.fourierFrequency, Complex.neg_re, Complex.neg_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.intCast_re, Complex.intCast_im, ht₀]
  norm_num
  ring

theorem norm_mode_sub_one_le (n : ℤ) (ζ : ℂ) :
    ‖mode n ζ - 1‖ ≤ ‖Kneser.fourierFrequency n‖ * ‖ζ‖ *
      Real.exp (‖Kneser.fourierFrequency n‖ * ‖ζ‖) := by
  simpa only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, pow_one, norm_mul, mode] using
    Complex.norm_exp_sub_sum_le_norm_mul_exp (Kneser.fourierFrequency n * ζ) 1

/-- Algebraic coefficient comparison, with the actual translated
coefficient definition.  Later the displayed bounds are supplied by the
constructed sewing correction and normalization root. -/
theorem norm_translated_coefficient_sub_le (H h : ℝ) (P : Space)
    (t₀ ζ t : ℂ) (n : ℕ) (A E Cζ : ℝ)
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hCζ : 0 ≤ Cζ)
    (ht : ‖t * hornPhase t₀ n‖ ≤ A)
    (hp : ‖(coefficient H P n - t) * hornPhase t₀ n‖ ≤ E * lambda h)
    (hζ : ‖ζ‖ ≤ Cζ * lambda h) (hζone : ‖ζ‖ ≤ 1) :
    ‖translatedCoefficient H h P t₀ ζ n / (lambda h : ℂ) ^ n - t * hornPhase t₀ n‖ ≤
      ((A * ‖Kneser.fourierFrequency n‖ * Cζ + E) *
        Real.exp ‖Kneser.fourierFrequency n‖) * lambda h := by
  have hlambda : 0 < lambda h := Real.exp_pos _
  have hf := norm_nonneg (Kneser.fourierFrequency n)
  have he : ‖mode n ζ‖ ≤ Real.exp ‖Kneser.fourierFrequency n‖ := by
    have hn : ‖Kneser.fourierFrequency n * ζ‖ ≤ ‖Kneser.fourierFrequency n‖ := by
      rw [norm_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hζone hf
    exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hn)
  have hdiff : ‖mode n ζ - 1‖ ≤
      (‖Kneser.fourierFrequency n‖ * Cζ * lambda h) * Real.exp ‖Kneser.fourierFrequency n‖ := by
    have hnζ : ‖Kneser.fourierFrequency n‖ * ‖ζ‖ ≤ ‖Kneser.fourierFrequency n‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hζone hf
    exact (norm_mode_sub_one_le n ζ).trans
      (mul_le_mul
        (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hζ hf)
        (Real.exp_le_exp.mpr hnζ) (Real.exp_pos _).le (by positivity))
  rw [translated_coefficient_sub_identity]
  calc
    _ ≤ ‖(t * hornPhase t₀ n) * (mode n ζ - 1)‖ +
        ‖(coefficient H P n - t) * hornPhase t₀ n * mode n ζ‖ := norm_add_le _ _
    _ ≤ A * ((‖Kneser.fourierFrequency n‖ * Cζ * lambda h) * Real.exp ‖Kneser.fourierFrequency n‖) +
        (E * lambda h) * Real.exp ‖Kneser.fourierFrequency n‖ := by
      rw [norm_mul (t * hornPhase t₀ n) (mode n ζ - 1),
        norm_mul ((coefficient H P n - t) * hornPhase t₀ n) (mode n ζ)]
      exact add_le_add
        (mul_le_mul ht hdiff (norm_nonneg _) hA)
        (mul_le_mul hp he (norm_nonneg _) (mul_nonneg hE hlambda.le))
    _ = _ := by ring

end Kneser.FourierSewing

end
