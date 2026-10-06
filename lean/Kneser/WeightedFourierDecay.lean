import Kneser.FourierSewingContraction
import Mathlib.Analysis.SpecificLimits.Normed

/-!
Exponential Fourier decay implies the explicit value and derivative
budgets used by the sewing construction.  Both sums are evaluated.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.FourierSewing

open Set Filter Metric
open scoped Topology Classical
open Kneser.WeightedFourier

theorem norm_fourierFrequency (m : ℤ) :
    ‖Kneser.fourierFrequency m‖ = 2 * Real.pi * |(m : ℝ)| := by
  simp [Kneser.fourierFrequency, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]

def nonzeroGeometric (q : ℝ) (m : ℤ) : ℝ := if m = 0 then 0 else q ^ m.natAbs

theorem nonzeroGeometric_nat (q : ℝ) (j : ℕ) :
    nonzeroGeometric q j = if j = 0 then 0 else q ^ j := by
  simp [nonzeroGeometric]

theorem nonzeroGeometric_negSucc (q : ℝ) (j : ℕ) :
    nonzeroGeometric q (-(j + 1 : ℤ)) = q ^ (j + 1) := by
  rw [show -(j + 1 : ℤ) = Int.negSucc j by omega]
  simp [nonzeroGeometric]

theorem summable_nonzeroGeometric (q : ℝ) (hq : 0 ≤ q) (hqlt : q < 1) :
    Summable (nonzeroGeometric q) := by
  have hs := summable_geometric_of_lt_one hq hqlt
  have hn : Summable (fun j : ℕ => nonzeroGeometric q j) := by
    apply hs.of_nonneg_of_le
    · intro j
      rw [nonzeroGeometric_nat]
      split_ifs <;> positivity
    · intro j
      rw [nonzeroGeometric_nat]
      split_ifs <;> simp_all
  have hm : Summable (fun j : ℕ => nonzeroGeometric q (-(j + 1 : ℤ))) := by
    simpa only [nonzeroGeometric_negSucc, Function.comp_def] using
      (hs.comp_injective (i := fun j : ℕ => j + 1) (by intro i j hij; exact Nat.add_right_cancel hij))
  exact hn.of_nat_of_neg_add_one hm

theorem tsum_nonzeroGeometric (q : ℝ) (hq : 0 ≤ q) (hqlt : q < 1) :
    (∑' m : ℤ, nonzeroGeometric q m) = 2 * q / (1 - q) := by
  have hs := summable_nonzeroGeometric q hq hqlt
  have hn : Summable (fun j : ℕ => nonzeroGeometric q j) :=
    hs.comp_injective (i := fun j : ℕ => (j : ℤ)) Nat.cast_injective
  have hm : Summable (fun j : ℕ => nonzeroGeometric q (-(j + 1 : ℤ))) :=
    hs.comp_injective (i := fun j : ℕ => -(j + 1 : ℤ)) (by
      intro i j hij
      dsimp at hij
      omega)
  have hsucc : (∑' j : ℕ, q ^ (j + 1)) = q / (1 - q) := by
    simp only [pow_succ', tsum_mul_left]
    rw [tsum_geometric_of_lt_one hq hqlt]
    ring
  have hnat (j : ℕ) : nonzeroGeometric q (j + 1 : ℕ) = q ^ (j + 1) := by
    rw [nonzeroGeometric_nat]
    simp
  rw [tsum_of_nat_of_neg_add_one hn hm, hn.tsum_eq_zero_add]
  simp only [hnat, nonzeroGeometric_negSucc, hsucc, Int.natCast_zero]
  simp only [nonzeroGeometric, ite_true, zero_add]
  ring

def firstGeometric (q : ℝ) (m : ℤ) : ℝ := |(m : ℝ)| * nonzeroGeometric q m

theorem firstGeometric_nat (q : ℝ) (j : ℕ) :
    firstGeometric q j = (j : ℝ) * q ^ j := by
  by_cases hj : j = 0
  · subst j; simp [firstGeometric, nonzeroGeometric]
  · simp [firstGeometric, nonzeroGeometric, hj]

theorem firstGeometric_negSucc (q : ℝ) (j : ℕ) :
    firstGeometric q (-(j + 1 : ℤ)) = (j + 1 : ℝ) * q ^ (j + 1) := by
  rw [firstGeometric, nonzeroGeometric_negSucc]
  simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, abs_neg]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1)]

theorem summable_firstGeometric (q : ℝ) (hq : 0 ≤ q) (hqlt : q < 1) :
    Summable (firstGeometric q) := by
  have hnorm : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hq] using hqlt
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable
  have hn : Summable (fun j : ℕ => firstGeometric q j) := by
    simpa only [firstGeometric_nat] using hs
  have hm : Summable (fun j : ℕ => firstGeometric q (-(j + 1 : ℤ))) := by
    simpa only [firstGeometric_negSucc, Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (hs.comp_injective (i := fun j : ℕ => j + 1) (by intro i j hij; exact Nat.add_right_cancel hij))
  exact hn.of_nat_of_neg_add_one hm

theorem tsum_firstGeometric (q : ℝ) (hq : 0 ≤ q) (hqlt : q < 1) :
    (∑' m : ℤ, firstGeometric q m) = 2 * q / (1 - q) ^ 2 := by
  have hnorm : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hq] using hqlt
  have hs := summable_firstGeometric q hq hqlt
  have hn : Summable (fun j : ℕ => firstGeometric q j) :=
    hs.comp_injective (i := fun j : ℕ => (j : ℤ)) Nat.cast_injective
  have hm : Summable (fun j : ℕ => firstGeometric q (-(j + 1 : ℤ))) :=
    hs.comp_injective (i := fun j : ℕ => -(j + 1 : ℤ)) (by
      intro i j hij
      dsimp at hij
      omega)
  have hsum := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).tsum_eq
  have hsucc : (∑' j : ℕ, (j + 1 : ℝ) * q ^ (j + 1)) = q / (1 - q) ^ 2 := by
    have h := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable.tsum_eq_zero_add
    simp only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_add, Nat.cast_one] at h
    exact h.symm.trans hsum
  rw [tsum_of_nat_of_neg_add_one hn hm]
  simp only [firstGeometric_nat, firstGeometric_negSucc, hsum, hsucc]
  ring

/-- The real exponent identity connecting the strip width with the
weighted composition budget. -/
theorem exponential_budget_identity (H ρ D : ℝ) (m : ℤ) :
    Real.exp (-2 * Real.pi * |(m : ℝ)| * (H + ρ + D)) * weight H m *
      Real.exp (‖Kneser.fourierFrequency m‖ * ρ) =
        Real.exp (-2 * Real.pi * D) ^ m.natAbs := by
  rw [weight, norm_fourierFrequency, ← Real.exp_add, ← Real.exp_add]
  rw [← Real.exp_nat_mul]
  congr 1
  have hcast : (m.natAbs : ℝ) = |(m : ℝ)| := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs m)
    simpa only [Int.cast_natCast, Int.cast_abs] using h
  rw [hcast]
  ring

theorem decay_valueBudget_le (H ρ D M : ℝ) (t : ℤ → ℂ)
    (ht₀ : t 0 = 0)
    (ht : ∀ m : ℤ, m ≠ 0 → ‖t m‖ ≤
      M * Real.exp (-2 * Real.pi * |(m : ℝ)| * (H + ρ + D))) (m : ℤ) :
    valueBudget H ρ t m ≤ M * nonzeroGeometric (Real.exp (-2 * Real.pi * D)) m := by
  by_cases hm : m = 0
  · subst m
    simp [valueBudget, ht₀, nonzeroGeometric]
  · simp only [valueBudget, nonzeroGeometric, ite_eq_right hm]
    calc
      _ ≤ (M * Real.exp (-2 * Real.pi * |(m : ℝ)| * (H + ρ + D))) * weight H m *
          Real.exp (‖Kneser.fourierFrequency m‖ * ρ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (ht m hm) (weight_pos H m).le) (Real.exp_pos _).le
      _ = _ := by
        calc
          _ = M * (Real.exp (-2 * Real.pi * |(m : ℝ)| * (H + ρ + D)) * weight H m *
              Real.exp (‖Kneser.fourierFrequency m‖ * ρ)) := by ring
          _ = _ := by rw [exponential_budget_identity]

/-- The usual strip mode decay quantitatively supplies the two Banach
budgets.  The displayed sums coincide with the bounds in W2. -/
theorem budgets_of_mode_decay (H ρ D M : ℝ) (hD : 0 < D) (hM : 0 ≤ M)
    (t : ℤ → ℂ) (ht₀ : t 0 = 0)
    (ht : ∀ m : ℤ, m ≠ 0 → ‖t m‖ ≤
      M * Real.exp (-2 * Real.pi * |(m : ℝ)| * (H + ρ + D))) :
    Summable (valueBudget H ρ t) ∧ Summable (derivativeBudget H ρ t) ∧
      (∑' m : ℤ, valueBudget H ρ t m) ≤
        2 * M * Real.exp (-2 * Real.pi * D) / (1 - Real.exp (-2 * Real.pi * D)) ∧
      (∑' m : ℤ, derivativeBudget H ρ t m) ≤
        4 * Real.pi * M * Real.exp (-2 * Real.pi * D) /
          (1 - Real.exp (-2 * Real.pi * D)) ^ 2 := by
  let q := Real.exp (-2 * Real.pi * D)
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hqlt : q < 1 := by
    change Real.exp (-2 * Real.pi * D) < 1
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have hvb := decay_valueBudget_le H ρ D M t ht₀ ht
  have hdb (m : ℤ) : derivativeBudget H ρ t m ≤ (2 * Real.pi * M) * firstGeometric q m := by
    rw [derivativeBudget, norm_fourierFrequency]
    exact (mul_le_mul_of_nonneg_right (hvb m) (by positivity)).trans_eq (by
      unfold firstGeometric
      ring)
  have hvs := (summable_nonzeroGeometric q hq hqlt).mul_left M
  have hds := (summable_firstGeometric q hq hqlt).mul_left (2 * Real.pi * M)
  have hv := hvs.of_nonneg_of_le (fun m => by unfold valueBudget; have hw := weight_pos H m; positivity) hvb
  have hd := hds.of_nonneg_of_le (fun m => by unfold derivativeBudget valueBudget; have hw := weight_pos H m; positivity) hdb
  refine ⟨hv, hd, ?_, ?_⟩
  · exact (hv.tsum_le_tsum hvb hvs).trans_eq (by
      rw [tsum_mul_left, tsum_nonzeroGeometric q hq hqlt]
      dsimp [q]
      ring)
  · exact (hd.tsum_le_tsum hdb hds).trans_eq (by
      rw [tsum_mul_left, tsum_firstGeometric q hq hqlt]
      dsimp [q]
      ring)

end Kneser.FourierSewing

end
