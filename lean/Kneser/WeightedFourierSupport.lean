import Kneser.WeightedFourierExponential

/-! Triangular Fourier support of the actual convolution exponential. -/

set_option autoImplicit false
noncomputable section

namespace Kneser.WeightedFourier

open Set Filter Metric
open scoped Topology Classical

def Nonpositive : Set Space := {a | ∀ n : ℤ, 0 < n → a n = 0}

theorem coefficient_eq_zero_iff (H : ℝ) (a : Space) (n : ℤ) :
    coefficient H a n = 0 ↔ a n = 0 := by
  rw [coefficient, div_eq_iff (Complex.ofReal_ne_zero.mpr (weight_pos H n).ne')]
  simp

theorem negative_nonpositive (a : Space) (ha : a ∈ Negative) : a ∈ Nonpositive :=
  fun n hn => ha n hn.le

theorem atom_zero_nonpositive (H : ℝ) : atom H 0 ∈ Nonpositive := by
  intro n hn
  apply (coefficient_eq_zero_iff H _ n).mp
  simp [ne_of_gt hn]

theorem product_negative_nonpositive (H : ℝ) (hH : 0 ≤ H) (a b : Space)
    (ha : a ∈ Negative) (hb : b ∈ Nonpositive) : product H hH a b ∈ Negative := by
  intro n hn
  apply (coefficient_eq_zero_iff H _ n).mp
  rw [coefficient_product]
  trans ∑' m : ℤ, (0 : ℂ)
  · apply tsum_congr
    intro m
    by_cases hm : 0 ≤ m
    · rw [(coefficient_eq_zero_iff H a m).mpr (ha m hm), zero_mul]
    · rw [(coefficient_eq_zero_iff H b (n - m)).mpr (hb (n - m) (by omega)), mul_zero]
  · exact tsum_zero

theorem product_nonpositive_nonpositive (H : ℝ) (hH : 0 ≤ H) (a b : Space)
    (ha : a ∈ Nonpositive) (hb : b ∈ Nonpositive) : product H hH a b ∈ Nonpositive := by
  intro n hn
  apply (coefficient_eq_zero_iff H _ n).mp
  rw [coefficient_product]
  trans ∑' m : ℤ, (0 : ℂ)
  · apply tsum_congr
    intro m
    by_cases hm : 0 < m
    · rw [(coefficient_eq_zero_iff H a m).mpr (ha m hm), zero_mul]
    · rw [(coefficient_eq_zero_iff H b (n - m)).mpr (hb (n - m) (by omega)), mul_zero]
  · exact tsum_zero

theorem power_nonpositive (H : ℝ) (hH : 0 ≤ H) (a : Space) (ha : a ∈ Negative)
    (n : ℕ) : power H hH a n ∈ Nonpositive := by
  induction n with
  | zero => exact atom_zero_nonpositive H
  | succ n hn => exact product_nonpositive_nonpositive H hH a _ (negative_nonpositive a ha) hn

theorem power_succ_negative (H : ℝ) (hH : 0 ≤ H) (a : Space) (ha : a ∈ Negative)
    (n : ℕ) : power H hH a (n + 1) ∈ Negative :=
  product_negative_nonpositive H hH a _ ha (power_nonpositive H hH a ha n)

theorem negative_smul (a : Space) (ha : a ∈ Negative) (c : ℂ) : c • a ∈ Negative := by
  intro n hn
  simp only [lp.coeFn_smul, Pi.smul_apply, ha n hn, smul_zero]

theorem exponential_nonpositive (H : ℝ) (hH : 0 ≤ H) (a : Space) (ha : a ∈ Negative) :
    exponential H hH a ∈ Nonpositive := by
  intro m hm
  apply (coefficient_eq_zero_iff H _ m).mp
  rw [← coefficientCLM_apply]
  dsimp only [exponential]
  rw [(coefficientCLM H m).map_tsum (summable_exponential_norm H hH a).of_norm]
  trans ∑' n : ℕ, (0 : ℂ)
  · apply tsum_congr
    intro n
    simp only [exponentialTerm, map_smul, coefficientCLM_apply]
    rw [(coefficient_eq_zero_iff H _ m).mpr (power_nonpositive H hH a ha n m hm), smul_zero]
  · exact tsum_zero

theorem coefficient_exponential_zero (H : ℝ) (hH : 0 ≤ H) (a : Space)
    (ha : a ∈ Negative) : coefficient H (exponential H hH a) 0 = 1 := by
  rw [← coefficientCLM_apply]
  dsimp only [exponential]
  rw [(coefficientCLM H 0).map_tsum (summable_exponential_norm H hH a).of_norm]
  have hs := ((coefficientCLM H 0).summable
    (summable_exponential_norm H hH a).of_norm)
  rw [hs.tsum_eq_zero_add]
  have hz (n : ℕ) : coefficientCLM H 0 (exponentialTerm H hH a (n + 1)) = 0 := by
    simp only [exponentialTerm, map_smul, coefficientCLM_apply]
    rw [(coefficient_eq_zero_iff H _ 0).mpr (power_succ_negative H hH a ha n 0 le_rfl), smul_zero]
  rw [tsum_congr hz, tsum_zero, add_zero]
  simp [exponentialTerm, power_zero]

end Kneser.WeightedFourier

end
