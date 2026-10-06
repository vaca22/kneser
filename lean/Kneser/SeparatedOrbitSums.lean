import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
Uniform kernel sums along a genuine separated real orbit. Splitting at
the first nonnegative orbit point reduces the two tails to one monotone
sampled kernel; its bound is independent of the initial orbit position.
-/

set_option autoImplicit false
noncomputable section
namespace Kneser.SeparatedOrbitSums

open Filter Set MeasureTheory
open scoped Topology BigOperators

theorem separation_of_step (x : ℕ → ℝ) (c : ℝ)
    (hstep : ∀ k, x k + c ≤ x (k + 1)) :
    ∀ i j : ℕ, i ≤ j → x i + c * (j - i : ℕ) ≤ x j := by
  intro i j hij
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  simp only [Nat.add_sub_cancel_left]
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := hstep (i + k)
    push_cast
    simpa only [Nat.add_assoc, Nat.add_comm 1] using (show
      x i + c * ((k : ℝ) + 1) ≤ x (i + k + 1) by linarith)

theorem exists_nonnegative_entry (x : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hsep : ∀ i j : ℕ, i ≤ j → x i + c * (j - i : ℕ) ≤ x j) :
    ∃ m : ℕ, 0 ≤ x m := by
  obtain ⟨m, hm⟩ := exists_nat_gt (-x 0 / c)
  have hh := hsep 0 m (Nat.zero_le _)
  simp only [Nat.sub_zero] at hh
  have hm' := (div_lt_iff₀ hc).mp hm
  exact ⟨m, by nlinarith⟩

theorem sum_kernel_le_two_sampled (x : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hsep : ∀ i j : ℕ, i ≤ j → x i + c * (j - i : ℕ) ≤ x j)
    (f : ℝ → ℝ) (hf : AntitoneOn f (Ici 0)) (hfn : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t)
    (hs : Summable (fun k : ℕ => f (c * k))) :
    Summable (fun k : ℕ => f |x k|) ∧
      (∑' k : ℕ, f |x k|) ≤ 2 * ∑' k : ℕ, f (c * k) := by
  have hex := exists_nonnegative_entry x c hc hsep
  let m : ℕ := Nat.find hex
  have hm : 0 ≤ x m := Nat.find_spec hex
  have hneg : ∀ k : ℕ, k < m → x k < 0 := by
    intro k hk
    exact lt_of_not_ge (Nat.find_min hex hk)
  have htail : ∀ k : ℕ, c * (k : ℝ) ≤ |x (k + m)| := by
    intro k
    have hh := hsep m (k + m) (Nat.le_add_left _ _)
    simp only [Nat.add_sub_cancel_right] at hh
    have hn : 0 ≤ c * (k : ℝ) := mul_nonneg hc.le (Nat.cast_nonneg _)
    have hx : 0 ≤ x (k + m) := by linarith
    rw [abs_of_nonneg hx]
    linarith
  have hhead : ∀ k : ℕ, k < m → c * ((m - 1 - k : ℕ) : ℝ) ≤ |x k| := by
    intro k hk
    have hkm : k ≤ m - 1 := by omega
    have hh := hsep k (m - 1) hkm
    have hhneg := hneg (m - 1) (by omega)
    rw [abs_of_neg (hneg k hk)]
    linarith
  have htail_le : ∀ k : ℕ, f |x (k + m)| ≤ f (c * k) := by
    intro k
    exact hf (show c * (k : ℝ) ∈ Ici 0 from mul_nonneg hc.le (Nat.cast_nonneg _))
      (Set.mem_Ici.mpr (abs_nonneg (x (k + m)))) (htail k)
  have hst : Summable (fun k : ℕ => f |x (k + m)|) :=
    hs.of_nonneg_of_le (fun k => hfn _ (abs_nonneg _)) htail_le
  have hsx : Summable (fun k : ℕ => f |x k|) :=
    (summable_nat_add_iff (f := fun k : ℕ => f |x k|) m).mp hst
  refine ⟨hsx, ?_⟩
  rw [← hsx.sum_add_tsum_nat_add m]
  have hh : (∑ k ∈ Finset.range m, f |x k|) ≤ ∑' k : ℕ, f (c * k) := by
    calc
      _ ≤ ∑ k ∈ Finset.range m, f (c * ((m - 1 - k : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hf (show c * ((m - 1 - k : ℕ) : ℝ) ∈ Ici 0 from mul_nonneg hc.le (Nat.cast_nonneg _))
          (Set.mem_Ici.mpr (abs_nonneg (x k)))
          (hhead k (Finset.mem_range.mp hk))
      _ = ∑ k ∈ Finset.range m, f (c * k) :=
        Finset.sum_range_reflect (fun j : ℕ => f (c * (j : ℝ))) m
      _ ≤ _ := hs.sum_le_tsum (Finset.range m) (fun k _ => hfn _ (mul_nonneg hc.le (Nat.cast_nonneg _)))
  have ht : (∑' k : ℕ, f |x (k + m)|) ≤ ∑' k : ℕ, f (c * k) :=
    hst.tsum_le_tsum htail_le hs
  linarith

end Kneser.SeparatedOrbitSums
end
