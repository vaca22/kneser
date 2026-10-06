import Kneser.FourierSewingContraction
import Kneser.WeightedFourierSupport

/-!
The positive sewing coefficients are calculated from the constructed
composition.  Negative support of Q gives a genuine triangular series:
only Fourier modes strictly above n can alter its nth positive coefficient.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.FourierSewing

open Set Filter Metric
open scoped Topology Classical
open Kneser.WeightedFourier

def interaction (H : ℝ) (hH : 0 ≤ H) (t : ℤ → ℂ) (Q : Space) (n m : ℤ) : ℂ :=
  t m * coefficient H (exponential H hH (Kneser.fourierFrequency m • Q)) (n - m)

theorem coefficient_composition (H : ℝ) (hH : 0 ≤ H) (ρ : ℝ)
    (t : ℤ → ℂ) (hv : Summable (valueBudget H ρ t))
    (Q : Space) (hQ : ‖Q‖ ≤ ρ) (n : ℤ) :
    coefficient H (composition H hH t Q) n = ∑' m : ℤ, interaction H hH t Q n m := by
  rw [← coefficientCLM_apply]
  dsimp only [composition]
  rw [(coefficientCLM H n).map_tsum (summable_composition H hH ρ t hv Q hQ)]
  simp only [compositionTerm, map_smul, coefficientCLM_apply, coefficient_shift, smul_eq_mul, interaction]

theorem summable_interaction (H : ℝ) (hH : 0 ≤ H) (ρ : ℝ)
    (t : ℤ → ℂ) (hv : Summable (valueBudget H ρ t))
    (Q : Space) (hQ : ‖Q‖ ≤ ρ) (n : ℤ) : Summable (interaction H hH t Q n) := by
  have hs := (coefficientCLM H n).summable (summable_composition H hH ρ t hv Q hQ)
  change Summable (fun m : ℤ => t m *
    coefficient H (exponential H hH (Kneser.fourierFrequency m • Q)) (n - m))
  simpa only [compositionTerm, map_smul, coefficientCLM_apply, coefficient_shift,
    smul_eq_mul, interaction] using hs

theorem interaction_self (H : ℝ) (hH : 0 ≤ H) (t : ℤ → ℂ)
    (Q : Space) (hneg : Q ∈ Negative) (n : ℤ) : interaction H hH t Q n n = t n := by
  simp only [interaction, sub_self,
    coefficient_exponential_zero H hH _ (negative_smul Q hneg _), mul_one]

theorem interaction_below (H : ℝ) (hH : 0 ≤ H) (t : ℤ → ℂ)
    (Q : Space) (hneg : Q ∈ Negative) (n m : ℤ) (hm : m < n) :
    interaction H hH t Q n m = 0 := by
  rw [interaction, (coefficient_eq_zero_iff H _ (n - m)).mpr
    (exponential_nonpositive H hH _ (negative_smul Q hneg _) (n - m) (by omega)), mul_zero]

def positiveCorrection (H : ℝ) (hH : 0 ≤ H) (t : ℤ → ℂ) (Q : Space) (n : ℤ) : ℂ :=
  ∑' m : ℤ, if n < m then interaction H hH t Q n m else 0

/-- The exact W2 positive-mode formula.  This is derived from the actual
projection and exponential, including the constant coefficient one. -/
theorem positive_coefficient_eq (H : ℝ) (hH : 0 ≤ H) (ρ : ℝ)
    (t : ℤ → ℂ) (hv : Summable (valueBudget H ρ t))
    (Q : Space) (hQ : ‖Q‖ ≤ ρ) (hneg : Q ∈ Negative) (n : ℤ) (hn : 0 ≤ n) :
    coefficient H (positiveProjection (composition H hH t Q)) n =
      t n + positiveCorrection H hH t Q n := by
  have hproj : coefficient H (positiveProjection (composition H hH t Q)) n =
      coefficient H (composition H hH t Q) n := by
    simp [coefficient, positiveProjection_apply, hn]
  rw [hproj, coefficient_composition H hH ρ t hv Q hQ n,
    (summable_interaction H hH ρ t hv Q hQ n).tsum_eq_add_tsum_ite n,
    interaction_self H hH t Q hneg n]
  congr 1
  apply tsum_congr
  intro m
  by_cases hmn : m = n
  · simp [hmn]
  · by_cases hm : n < m
    · simp [hmn, hm]
    · simp [hmn, hm, interaction_below H hH t Q hneg n m (by omega)]

def coefficientErrorBudget (H ρ : ℝ) (t : ℤ → ℂ) (n m : ℤ) : ℝ :=
  if n < m then
    ‖t m‖ * Real.exp (‖Kneser.fourierFrequency m‖ * ρ) / weight H (n - m)
  else 0

theorem coefficientErrorBudget_le (H : ℝ) (hH : 0 ≤ H) (ρ : ℝ)
    (t : ℤ → ℂ) (n m : ℤ) :
    coefficientErrorBudget H ρ t n m ≤ valueBudget H ρ t m / weight H n := by
  by_cases hm : n < m
  · simp only [coefficientErrorBudget, ite_eq_left hm, valueBudget]
    apply (div_le_div_iff₀ (weight_pos H _) (weight_pos H _)).mpr
    have hw : weight H n ≤ weight H m * weight H (n - m) := by
      simpa only [add_sub_cancel] using weight_submultiplicative H hH m (n - m)
    have hh := mul_le_mul_of_nonneg_left hw
      (mul_nonneg (norm_nonneg (t m))
        (Real.exp_pos (‖Kneser.fourierFrequency m‖ * ρ)).le)
    nlinarith only [hh]
  · simp only [coefficientErrorBudget, ite_eq_right hm]
    unfold valueBudget
    have hw := weight_pos H m
    have hwn := weight_pos H n
    positivity

theorem summable_coefficientErrorBudget (H : ℝ) (hH : 0 ≤ H) (ρ : ℝ)
    (t : ℤ → ℂ) (hv : Summable (valueBudget H ρ t)) (n : ℤ) :
    Summable (coefficientErrorBudget H ρ t n) :=
  (hv.div_const (weight H n)).of_nonneg_of_le
    (fun m => by
      unfold coefficientErrorBudget
      have hw := weight_pos H (n - m)
      split_ifs <;> positivity)
    (coefficientErrorBudget_le H hH ρ t n)

theorem norm_interaction_le (H : ℝ) (hH : 0 ≤ H) (ρ : ℝ)
    (t : ℤ → ℂ) (Q : Space) (hQ : ‖Q‖ ≤ ρ) (n m : ℤ) :
    ‖interaction H hH t Q n m‖ ≤
      ‖t m‖ * Real.exp (‖Kneser.fourierFrequency m‖ * ρ) / weight H (n - m) := by
  rw [interaction, norm_mul]
  have hb : ‖exponential H hH (Kneser.fourierFrequency m • Q)‖ ≤
      Real.exp (‖Kneser.fourierFrequency m‖ * ρ) :=
    (norm_exponential_le H hH _).trans (Real.exp_le_exp.mpr (by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left hQ (norm_nonneg _)))
  calc
    _ ≤ ‖t m‖ * (Real.exp (‖Kneser.fourierFrequency m‖ * ρ) / weight H (n - m)) :=
      mul_le_mul_of_nonneg_left
        ((norm_coefficient_le H _ _).trans (div_le_div_of_nonneg_right hb (weight_pos H _).le))
        (norm_nonneg _)
    _ = _ := by ring

/-- A coefficient error estimate from a summable explicit decay budget.
The coefficient difference itself is calculated, rather than assumed. -/
theorem norm_positive_coefficient_sub_le (H : ℝ) (hH : 0 ≤ H) (ρ : ℝ)
    (t : ℤ → ℂ) (hv : Summable (valueBudget H ρ t))
    (Q : Space) (hQ : ‖Q‖ ≤ ρ) (hneg : Q ∈ Negative) (n : ℤ) (hn : 0 ≤ n)
    (he : Summable (coefficientErrorBudget H ρ t n)) :
    ‖coefficient H (positiveProjection (composition H hH t Q)) n - t n‖ ≤
      ∑' m : ℤ, coefficientErrorBudget H ρ t n m := by
  have hb (m : ℤ) : ‖if n < m then interaction H hH t Q n m else 0‖ ≤
      coefficientErrorBudget H ρ t n m := by
    by_cases hm : n < m
    · simpa only [if_pos hm, coefficientErrorBudget] using norm_interaction_le H hH ρ t Q hQ n m
    · simp [coefficientErrorBudget, hm]
  have hs := he.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  rw [positive_coefficient_eq H hH ρ t hv Q hQ hneg n hn, add_sub_cancel_left]
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hb he)

end Kneser.FourierSewing

end
