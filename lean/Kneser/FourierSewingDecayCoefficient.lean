import Kneser.FourierSewingCoefficient
import Kneser.WeightedFourierDecay

/-! The W2 exponential estimate for the actual positive sewing modes. -/

set_option autoImplicit false
noncomputable section

namespace Kneser.FourierSewing

open Set Filter Metric
open scoped Topology Classical
open Kneser.WeightedFourier

def upperGeometric (q : ℝ) (m : ℤ) : ℝ := if 0 < m then q ^ m.toNat else 0

theorem upperGeometric_nat (q : ℝ) (j : ℕ) :
    upperGeometric q j = nonzeroGeometric q j := by
  by_cases hj : j = 0
  · subst j; simp [upperGeometric, nonzeroGeometric]
  · simp [upperGeometric, nonzeroGeometric, Nat.pos_of_ne_zero hj, hj]

theorem upperGeometric_negSucc (q : ℝ) (j : ℕ) :
    upperGeometric q (-(j + 1 : ℤ)) = 0 := by
  simp only [upperGeometric]
  rw [ite_eq_right (by omega : ¬ (0 : ℤ) < -(j + 1 : ℤ))]

theorem summable_upperGeometric (q : ℝ) (hq : 0 ≤ q) (hqlt : q < 1) :
    Summable (upperGeometric q) := by
  have hn : Summable (fun j : ℕ => upperGeometric q j) := by
    simpa only [upperGeometric_nat, Function.comp_def] using
      ((summable_nonzeroGeometric q hq hqlt).comp_injective
        (i := fun j : ℕ => (j : ℤ)) Nat.cast_injective)
  have hm : Summable (fun j : ℕ => upperGeometric q (-(j + 1 : ℤ))) := by
    simp only [upperGeometric_negSucc]
    exact summable_zero
  exact hn.of_nat_of_neg_add_one hm

theorem tsum_upperGeometric (q : ℝ) (hq : 0 ≤ q) (hqlt : q < 1) :
    (∑' m : ℤ, upperGeometric q m) = q / (1 - q) := by
  have hs := summable_upperGeometric q hq hqlt
  have hn : Summable (fun j : ℕ => upperGeometric q j) :=
    hs.comp_injective (i := fun j : ℕ => (j : ℤ)) Nat.cast_injective
  have hm : Summable (fun j : ℕ => upperGeometric q (-(j + 1 : ℤ))) :=
    hs.comp_injective (i := fun j : ℕ => -(j + 1 : ℤ)) (by intro i j hij; dsimp at hij; omega)
  rw [tsum_of_nat_of_neg_add_one hn hm, hn.tsum_eq_zero_add]
  have hsucc (j : ℕ) : upperGeometric q (j + 1 : ℕ) = q ^ (j + 1) := by
    rw [upperGeometric_nat, nonzeroGeometric_nat]
    simp
  simp only [hsucc, upperGeometric_negSucc, tsum_zero, add_zero, Int.natCast_zero]
  simp only [upperGeometric, lt_self_iff_false, ite_false, zero_add, pow_succ', tsum_mul_left]
  rw [tsum_geometric_of_lt_one hq hqlt]
  ring

theorem coefficient_decay_identity (H ρ d : ℝ) (n m : ℤ) (hn : 0 ≤ n) (hm : n < m) :
    Real.exp (-2 * Real.pi * |(m : ℝ)| * d) *
        Real.exp (‖Kneser.fourierFrequency m‖ * ρ) / weight H (n - m) =
      Real.exp (-2 * Real.pi * (n : ℝ) * (d - ρ)) *
        Real.exp (-2 * Real.pi * (d + H - ρ)) ^ (m - n).toNat := by
  have hmpos : (0 : ℤ) < m := lt_of_le_of_lt hn hm
  have hmreal : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos.le
  have hnmreal : (n : ℝ) - m ≤ 0 := by exact_mod_cast (sub_nonpos.mpr hm.le)
  have hcast : ((m - n).toNat : ℝ) = (m : ℝ) - n := by
    have h := Int.toNat_of_nonneg (sub_nonneg.mpr hm.le)
    have hc := congrArg (fun z : ℤ => (z : ℝ)) h
    simpa only [Int.cast_natCast, Int.cast_sub] using hc
  rw [norm_fourierFrequency, weight, abs_of_nonneg hmreal, Int.cast_sub,
    abs_of_nonpos hnmreal, ← Real.exp_add, ← Real.exp_sub, ← Real.exp_nat_mul,
    ← Real.exp_add, hcast]
  congr 1
  ring

theorem coefficientErrorBudget_decay_le (H ρ d M : ℝ) (hM : 0 ≤ M)
    (t : ℤ → ℂ)
    (ht : ∀ m : ℤ, m ≠ 0 → ‖t m‖ ≤ M * Real.exp (-2 * Real.pi * |(m : ℝ)| * d))
    (n : ℤ) (hn : 0 ≤ n) (m : ℤ) :
    coefficientErrorBudget H ρ t n m ≤
      (M * Real.exp (-2 * Real.pi * (n : ℝ) * (d - ρ))) *
        upperGeometric (Real.exp (-2 * Real.pi * (d + H - ρ))) (m - n) := by
  by_cases hm : n < m
  · have hmne : m ≠ 0 := by omega
    simp only [coefficientErrorBudget, ite_eq_left hm, upperGeometric,
      ite_eq_left (by omega : (0 : ℤ) < m - n)]
    calc
      _ ≤ M * Real.exp (-2 * Real.pi * |(m : ℝ)| * d) *
          Real.exp (‖Kneser.fourierFrequency m‖ * ρ) / weight H (n - m) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (ht m hmne) (Real.exp_pos _).le) (weight_pos H _).le
      _ = _ := by
        rw [mul_assoc, mul_div_assoc, coefficient_decay_identity H ρ d n m hn hm, mul_assoc]
        ring
  · simp only [coefficientErrorBudget, ite_eq_right hm, upperGeometric,
      ite_eq_right (by omega : ¬ (0 : ℤ) < m - n), mul_zero]
    exact le_rfl

/-- Explicit exponential control of the constructed positive sewing
coefficient.  The higher-mode tail is summed as a geometric series. -/
theorem norm_positive_coefficient_sub_le_decay (H : ℝ) (hH : 0 ≤ H)
    (ρ d M : ℝ) (hM : 0 ≤ M) (hgap : 0 < d + H - ρ)
    (t : ℤ → ℂ) (hv : Summable (valueBudget H ρ t))
    (ht : ∀ m : ℤ, m ≠ 0 → ‖t m‖ ≤ M * Real.exp (-2 * Real.pi * |(m : ℝ)| * d))
    (Q : Space) (hQ : ‖Q‖ ≤ ρ) (hneg : Q ∈ Negative) (n : ℤ) (hn : 0 ≤ n) :
    ‖coefficient H (positiveProjection (composition H hH t Q)) n - t n‖ ≤
      M * Real.exp (-2 * Real.pi * (n : ℝ) * (d - ρ)) *
        Real.exp (-2 * Real.pi * (d + H - ρ)) /
          (1 - Real.exp (-2 * Real.pi * (d + H - ρ))) := by
  let q := Real.exp (-2 * Real.pi * (d + H - ρ))
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hqlt : q < 1 := by
    change Real.exp (-2 * Real.pi * (d + H - ρ)) < 1
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have hu : Summable (fun m : ℤ => upperGeometric q (m - n)) :=
    (summable_upperGeometric q hq hqlt).comp_injective
      (i := fun m : ℤ => m - n) (sub_left_injective (b := n))
  have hb := coefficientErrorBudget_decay_le H ρ d M hM t ht n hn
  have hmajor := hu.mul_left (M * Real.exp (-2 * Real.pi * (n : ℝ) * (d - ρ)))
  have he := summable_coefficientErrorBudget H hH ρ t hv n
  have hsum : (∑' m : ℤ, upperGeometric q (m - n)) = q / (1 - q) := by
    rw [show (∑' m : ℤ, upperGeometric q (m - n)) = ∑' m : ℤ, upperGeometric q m by
      simpa only [Equiv.coe_addRight, sub_eq_add_neg] using
        (Equiv.addRight (-n)).tsum_eq (upperGeometric q)]
    exact tsum_upperGeometric q hq hqlt
  exact (norm_positive_coefficient_sub_le H hH ρ t hv Q hQ hneg n hn he).trans
    ((he.tsum_le_tsum hb hmajor).trans_eq (by rw [tsum_mul_left, hsum]; dsimp [q]; ring))

end Kneser.FourierSewing

end
