import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Algebra of the head/tail balance

This module checks the exact exponents used in the higher-order parabolic
orbit-sum argument.  It does not assume or prove the analytic estimates
whose powers these exponents balance.
-/

noncomputable section

namespace Kneser.AsymptoticBalance

/-- The common denominator in the higher-order balance. -/
def denominator (m N : ℕ) : ℝ := 2 * (N : ℝ) + 2 * (m : ℝ) + 1

/-- The truncation exponent, corresponding to `J` of order `s⁻ᵝ`. -/
def beta (m N : ℕ) : ℝ := ((m : ℝ) + 1) / denominator m N

/-- The positive gain beyond differentiability of order `m`. -/
def gamma (m N : ℕ) : ℝ :=
  1 - 2 * ((m : ℝ) + 1) ^ 2 / denominator m N

/-- The exponent in `s^(m+1) J^(2m+2)` after the balance. -/
def headExponent (m N : ℕ) : ℝ :=
  (m : ℝ) + 1 - (2 * (m : ℝ) + 2) * beta m N

/-- The exponent in `J^(1-2N)` after the balance. -/
def tailExponent (m N : ℕ) : ℝ := (2 * (N : ℝ) - 1) * beta m N

theorem denominator_pos (m N : ℕ) : 0 < denominator m N := by
  unfold denominator
  positivity

theorem beta_pos (m N : ℕ) : 0 < beta m N := by
  exact div_pos (by positivity) (denominator_pos m N)

/-- The paper's preparation order ensures that the parameter disc is admissible. -/
theorem beta_lt_half (m N : ℕ) (hm : 1 ≤ m) (hN : m * m + m + 1 ≤ N) :
    beta m N < 1 / 2 := by
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hN' : (m : ℝ) * (m : ℝ) + (m : ℝ) + 1 ≤ (N : ℝ) := by
    exact_mod_cast hN
  unfold beta
  rw [div_lt_iff₀ (denominator_pos m N)]
  unfold denominator
  nlinarith

/-- `N ≥ m²+m+1` makes the gain strictly positive. -/
theorem gamma_pos (m N : ℕ) (hN : m * m + m + 1 ≤ N) :
    0 < gamma m N := by
  have hN' : (m : ℝ) * (m : ℝ) + (m : ℝ) + 1 ≤ (N : ℝ) := by
    exact_mod_cast hN
  unfold gamma
  rw [sub_pos, div_lt_iff₀ (denominator_pos m N)]
  unfold denominator
  nlinarith

/-- The head and tail powers agree exactly. -/
theorem headExponent_eq_tailExponent (m N : ℕ) :
    headExponent m N = tailExponent m N := by
  have hD : denominator m N ≠ 0 := ne_of_gt (denominator_pos m N)
  unfold headExponent tailExponent beta
  field_simp [hD]
  unfold denominator
  ring

/-- The balanced exponent is `m+γ`. -/
theorem headExponent_eq_order_add_gamma (m N : ℕ) :
    headExponent m N = (m : ℝ) + gamma m N := by
  have hD : denominator m N ≠ 0 := ne_of_gt (denominator_pos m N)
  unfold headExponent beta gamma
  field_simp [hD]
  ring

theorem tailExponent_eq_order_add_gamma (m N : ℕ) :
    tailExponent m N = (m : ℝ) + gamma m N := by
  rw [← headExponent_eq_tailExponent, headExponent_eq_order_add_gamma]

/-- The higher-order remainder exponent exceeds the requested derivative order. -/
theorem headExponent_gt_order (m N : ℕ) (hN : m * m + m + 1 ≤ N) :
    (m : ℝ) < headExponent m N := by
  rw [headExponent_eq_order_add_gamma]
  exact lt_add_of_pos_right _ (gamma_pos m N hN)

theorem beta_one_three : beta 1 3 = 2 / 9 := by
  norm_num [beta, denominator]

theorem gamma_one_three : gamma 1 3 = 1 / 9 := by
  norm_num [gamma, denominator]

theorem headExponent_one_three : headExponent 1 3 = 10 / 9 := by
  norm_num [headExponent, beta, denominator]

theorem tailExponent_one_three : tailExponent 1 3 = 10 / 9 := by
  rw [← headExponent_eq_tailExponent, headExponent_one_three]

end Kneser.AsymptoticBalance

end
