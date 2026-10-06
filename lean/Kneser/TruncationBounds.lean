import Kneser.AsymptoticBalance
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Algebra.Order.Floor.Semiring

/-!
The integer cutoff in the orbit proof, including the effects of rounding.
These are numerical inequalities, not assumptions about the dynamics.
-/

noncomputable section

namespace Kneser.TruncationBounds

open Filter Set
open scoped Topology

def cutoff (s β : ℝ) : ℕ := Nat.ceil (s ^ (-β))

theorem cutoff_lower (s β : ℝ) : s ^ (-β) ≤ (cutoff s β : ℝ) := Nat.le_ceil _

theorem cutoff_pos {s β : ℝ} (hs : 0 < s) : 0 < cutoff s β := by
  apply Nat.one_le_ceil_iff.mpr
  exact Real.rpow_pos_of_pos hs _

theorem cutoff_upper {s β : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hβ : 0 ≤ β) :
    (cutoff s β : ℝ) ≤ 2 * s ^ (-β) := by
  have hone : 1 ≤ s ^ (-β) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs hs1 (neg_nonpos.mpr hβ)
  have hround := (Nat.ceil_lt_add_one (Real.rpow_nonneg hs.le (-β))).le
  change (Nat.ceil (s ^ (-β)) : ℝ) ≤ _
  linarith

theorem cutoff_head_bound {s β a b : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hβ : 0 ≤ β) (ha : 0 ≤ a) :
    s ^ b * (cutoff s β : ℝ) ^ a ≤ 2 ^ a * s ^ (b - β * a) := by
  have h := Real.rpow_le_rpow (by positivity : 0 ≤ (cutoff s β : ℝ))
    (cutoff_upper hs hs1 hβ) ha
  calc
    s ^ b * (cutoff s β : ℝ) ^ a ≤ s ^ b * (2 * s ^ (-β)) ^ a :=
      mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hs.le _)
    _ = 2 ^ a * s ^ (b - β * a) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hs.le _)]
      rw [← Real.rpow_mul hs.le]
      rw [show b - β * a = b + (-β) * a by ring, Real.rpow_add hs]
      ring

theorem cutoff_tail_bound {s β d : ℝ} (hs : 0 < s) (hd : 0 ≤ d) :
    (cutoff s β : ℝ) ^ (-d) ≤ s ^ (β * d) := by
  have h := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hs (-β))
    (cutoff_lower s β) (neg_nonpos.mpr hd)
  calc
    (cutoff s β : ℝ) ^ (-d) ≤ (s ^ (-β)) ^ (-d) := h
    _ = s ^ (β * d) := by rw [← Real.rpow_mul hs.le]; congr 1; ring

theorem cutoff_scaled_tail_bound {s β d b : ℝ} (hs : 0 < s) (hd : 0 ≤ d) :
    s ^ b * (cutoff s β : ℝ) ^ (-d) ≤ s ^ (b + β * d) := by
  calc
    s ^ b * (cutoff s β : ℝ) ^ (-d) ≤ s ^ b * s ^ (β * d) :=
      mul_le_mul_of_nonneg_left (cutoff_tail_bound hs hd) (Real.rpow_nonneg hs.le _)
    _ = s ^ (b + β * d) := (Real.rpow_add hs _ _).symm

theorem cutoff_admissible {β c : ℝ} (hβ : 0 ≤ β) (hβhalf : β < 1 / 2)
    (hc : 0 < c) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ c / (2 * (cutoff s β : ℝ) ^ 2) := by
  have hq : 0 < 1 - β * 2 := by linarith
  have hp : Tendsto (fun s : ℝ => s ^ (1 - β * 2)) (𝓝[>] 0)
      (𝓝 ((0 : ℝ) ^ (1 - β * 2))) :=
    (Real.continuousAt_rpow_const (0 : ℝ) (1 - β * 2)
    (Or.inr hq.le)).tendsto.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun s : ℝ => 4 * s ^ (1 - β * 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hq.ne', mul_zero] using tendsto_const_nhds.mul hp
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, 4 * s ^ (1 - β * 2) < c / 2 :=
    ht.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < c / 2))
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono (fun _ h => h.le) |>
      fun h => h.filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall, hpos, hle] with s hsmall hs hs1
  have hb := cutoff_head_bound (a := 2) (b := 1) hs hs1 hβ (by norm_num)
  norm_num [Real.rpow_natCast] at hb
  have hj : 0 < (cutoff s β : ℝ) := by exact_mod_cast cutoff_pos hs
  apply (le_div_iff₀ (by positivity : 0 < 2 * (cutoff s β : ℝ) ^ 2)).mpr
  nlinarith

theorem first_order_head {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    s ^ (2 : ℕ) * (cutoff s (2 / 9) : ℝ) ^ (4 : ℕ) ≤ 16 * s ^ (10 / 9 : ℝ) := by
  have h := cutoff_head_bound (β := 2 / 9) (a := 4) (b := 2) hs hs1
    (by norm_num) (by norm_num)
  norm_num [Real.rpow_natCast] at h ⊢
  exact h

theorem first_order_tail {s : ℝ} (hs : 0 < s) :
    (cutoff s (2 / 9) : ℝ) ^ (-(5 : ℝ)) ≤ s ^ (10 / 9 : ℝ) := by
  have h := cutoff_tail_bound (β := 2 / 9) (d := 5) hs (by norm_num)
  norm_num at h ⊢
  exact h

theorem first_order_derivative_tail {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    s * (cutoff s (2 / 9) : ℝ) ^ (-(3 : ℝ)) ≤ s ^ (10 / 9 : ℝ) := by
  have h := cutoff_scaled_tail_bound (β := 2 / 9) (d := 3) (b := 1) hs (by norm_num)
  have hcompare : s ^ (5 / 3 : ℝ) ≤ s ^ (10 / 9 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by norm_num)
  norm_num [Real.rpow_one] at h ⊢
  exact h.trans hcompare

end Kneser.TruncationBounds

end
