import Kneser.ParabolicOrbitSum

/-!
A quantitative tail estimate for every integer power majorant. Partitioning
the tail into residue classes gives the required `J^(1-p)` bound without
assuming an integral comparison or a tail estimate.
-/

noncomputable section

namespace Kneser.PowerSeriesTail

open scoped BigOperators

def powerConstant (p : ℕ) : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ p

theorem powerConstant_nonneg (p : ℕ) : 0 ≤ powerConstant p :=
  tsum_nonneg (fun _ => by positivity)

theorem power_majorant_tail {p : ℕ} (hp : 2 ≤ p) (J : ℕ) (hJ : 0 < J) :
    (∑' k : ℕ, 1 / (((k + J : ℕ) : ℝ) + 1) ^ p) ≤
      powerConstant p / (J : ℝ) ^ (p - 1) := by
  let : NeZero J := ⟨hJ.ne'⟩
  have hJr : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hbase := summable_parabolic_majorant (1 : ℝ) hp
  have htail := (summable_nat_add_iff J).mpr hbase
  let f : ℕ → ℝ := fun k => 1 / (((k + J : ℕ) : ℝ) + 1) ^ p
  have hf : Summable f := htail
  have hpart := Nat.sumByResidueClasses hf J
  change (∑' k : ℕ, f k) ≤ _
  rw [hpart]
  have hslice : ∀ j : ZMod J,
      (∑' k : ℕ, f (j.val + J * k)) ≤ powerConstant p / (J : ℝ) ^ p := by
    intro j
    have hbound : ∀ k : ℕ,
        f (j.val + J * k) ≤ ((J : ℝ) ^ p)⁻¹ / ((k : ℝ) + 1) ^ p := by
      intro k
      have hd : (J : ℝ) * ((k : ℝ) + 1) ≤
          (((j.val + J * k + J : ℕ) : ℝ) + 1) := by
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) j.val]
      have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (J : ℝ) * ((k : ℝ) + 1)) hd p
      change 1 / _ ≤ _
      calc
        1 / (((j.val + J * k + J : ℕ) : ℝ) + 1) ^ p ≤
            1 / ((J : ℝ) * ((k : ℝ) + 1)) ^ p :=
          one_div_le_one_div_of_le (by positivity) hpow
        _ = ((J : ℝ) ^ p)⁻¹ / ((k : ℝ) + 1) ^ p := by
          rw [mul_pow]
          field_simp
    have hg := summable_parabolic_majorant (((J : ℝ) ^ p)⁻¹) hp
    have hfs : Summable (fun k => f (j.val + J * k)) :=
      hg.of_nonneg_of_le (fun _ => by dsimp [f]; positivity) hbound
    apply (hfs.tsum_le_tsum hbound hg).trans_eq
    rw [show (fun k : ℕ => ((J : ℝ) ^ p)⁻¹ / ((k : ℝ) + 1) ^ p) =
      fun k : ℕ => ((J : ℝ) ^ p)⁻¹ * (1 / ((k : ℝ) + 1) ^ p) by funext k; ring,
      tsum_mul_left]
    dsimp [powerConstant]
    ring
  calc
    (∑ j : ZMod J, ∑' k : ℕ, f (j.val + J * k)) ≤
        ∑ _j : ZMod J, powerConstant p / (J : ℝ) ^ p :=
      Finset.sum_le_sum (fun j _ => hslice j)
    _ = powerConstant p / (J : ℝ) ^ (p - 1) := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      have hps : p = (p - 1) + 1 := by omega
      rw [show (J : ℝ) ^ p = (J : ℝ) ^ (p - 1) * (J : ℝ) by
        conv_lhs => rw [hps, pow_succ]]
      field_simp


/-- Absolute summability and the quantitative complex tail bound follow
from the term bound itself. -/
theorem norm_tsum_tail_le (a : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C) {p : ℕ}
    (hp : 2 ≤ p) (ha : ∀ k, ‖a k‖ ≤ C / ((k : ℝ) + 1) ^ p)
    (J : ℕ) (hJ : 0 < J) :
    ‖∑' k : ℕ, a (k + J)‖ ≤ C * powerConstant p / (J : ℝ) ^ (p - 1) := by
  have hnorm := summable_norm_of_parabolic_bound a C hp ha
  have hnormtail := (summable_nat_add_iff J).mpr hnorm
  have hmaj := (summable_nat_add_iff J).mpr (summable_parabolic_majorant C hp)
  calc
    ‖∑' k : ℕ, a (k + J)‖ ≤ ∑' k : ℕ, ‖a (k + J)‖ := norm_tsum_le_tsum_norm hnormtail
    _ ≤ ∑' k : ℕ, C / (((k + J : ℕ) : ℝ) + 1) ^ p :=
      hnormtail.tsum_le_tsum (fun k => ha (k + J)) hmaj
    _ = C * (∑' k : ℕ, 1 / (((k + J : ℕ) : ℝ) + 1) ^ p) := by
      rw [← tsum_mul_left]
      congr 1
      funext k
      ring
    _ ≤ C * (powerConstant p / (J : ℝ) ^ (p - 1)) :=
      mul_le_mul_of_nonneg_left (power_majorant_tail hp J hJ) hC
    _ = C * powerConstant p / (J : ℝ) ^ (p - 1) := by ring

end Kneser.PowerSeriesTail

end
