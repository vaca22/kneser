import Kneser.AllOrderMovingInverse

/-! Local integer expansions glue by coefficient uniqueness.  A finite
open cover then gives a genuine compact uniform expansion on the common
image domain, with globally coherent holomorphic coefficients. -/

set_option autoImplicit false
noncomputable section

namespace Kneser.FiniteLocalExpansionGluing

open Filter Set Metric
open scoped Topology BigOperators
open Kneser.FiniteExpansionHolomorphy

theorem coefficients_unique_integer (f : ℝ → ℂ) (c d : ℕ → ℂ)
    (m : ℕ) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hc : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖f s - Kneser.AsymptoticCoefficientUniqueness.polynomial c m s‖ ≤ C * s ^ (m + 1))
    (hd : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖f s - Kneser.AsymptoticCoefficientUniqueness.polynomial d m s‖ ≤ D * s ^ (m + 1)) :
    ∀ j ≤ m, c j = d j := by
  apply Kneser.AsymptoticCoefficientUniqueness.coefficients_unique_of_common_expansions
    f c d m C D 1 1 hC hD (by norm_num) (by norm_num)
  · simpa only [show (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast] using hc
  · simpa only [show (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast] using hd

def LocalFiniteExpansion (F : ℝ → ℂ → ℂ) (m : ℕ) (U : Set ℂ) : Prop :=
  ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ U ∧
    ∃ c : ℕ → ℂ → ℂ, ∃ C : ℝ, 0 ≤ C ∧
      (∀ j ≤ m, AnalyticOnNhd ℂ (c j) (ball x r)) ∧
      (∀ z ∈ closedBall x r, c 0 z = F 0 z) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ closedBall x r,
        ‖F s z - complexPolynomial c m (s : ℂ) z‖ ≤ C * s ^ (m + 1))

theorem exists_global_finite_expansion (F : ℝ → ℂ → ℂ) (m : ℕ) (U : Set ℂ)
    (hlocal : LocalFiniteExpansion F m U) :
    ∃ a : ℕ → ℂ → ℂ,
      (∀ j ≤ m, AnalyticOnNhd ℂ (a j) U) ∧
      (∀ z ∈ U, a 0 z = F 0 z) ∧
      (∀ K : Set ℂ, IsCompact K → K ⊆ U →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ K,
          ‖F s z - complexPolynomial a m (s : ℂ) z‖ ≤ C * s ^ (m + 1)) := by
  classical
  have hpacket (x : U) := hlocal x x.property
  choose r hr hclosed c C hC ha hbase hb using hpacket
  let a : ℕ → ℂ → ℂ := fun j z => if hz : z ∈ U then c ⟨z, hz⟩ j z else 0
  have hagree (x : U) (z : ℂ) (hz : z ∈ closedBall x.val (r x)) (j : ℕ) (hj : j ≤ m) :
      a j z = c x j z := by
    have hzU : z ∈ U := hclosed x hz
    let y : U := ⟨z, hzU⟩
    have hxbound := (hb x).mono fun s hs => hs z hz
    have hybound := (hb y).mono fun s hs => hs z (mem_closedBall_self (hr y).le)
    have he := coefficients_unique_integer (fun s => F s z) (fun k => c x k z) (fun k => c y k z)
      m (C x) (C y) (hC x) (hC y) hxbound hybound j hj
    simpa only [a, dif_pos hzU] using he.symm
  refine ⟨a, ?_, ?_, ?_⟩
  · intro j hj z hz
    let x : U := ⟨z, hz⟩
    have he : a j =ᶠ[𝓝 z] c x j := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (hr x))] with w hw
      exact hagree x w (ball_subset_closedBall hw) j hj
    exact (ha x j hj z (mem_ball_self (hr x))).congr he.symm
  · intro z hz
    let x : U := ⟨z, hz⟩
    exact (hagree x z (mem_closedBall_self (hr x).le) 0 (Nat.zero_le m)).trans
      (hbase x z (mem_closedBall_self (hr x).le))
  · intro K hK hKU
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : U => ball x.val (r x))
      (fun _ => isOpen_ball) (by
        intro z hz
        exact mem_iUnion.mpr ⟨⟨z, hKU hz⟩, mem_ball_self (hr ⟨z, hKU hz⟩)⟩)
    let D := ∑ x ∈ t, C x
    have hD : 0 ≤ D := Finset.sum_nonneg (fun x _ => hC x)
    have hfinite : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ x ∈ t, ∀ z ∈ closedBall x.val (r x),
        ‖F s z - complexPolynomial (c x) m (s : ℂ) z‖ ≤ C x * s ^ (m + 1) :=
      (eventually_all_finset t).mpr (fun x _ => hb x)
    refine ⟨D, hD, ?_⟩
    filter_upwards [hfinite, self_mem_nhdsWithin] with s hs hsp
    change 0 < s at hsp
    intro z hz
    obtain ⟨x, hxt, hxz⟩ := mem_iUnion₂.mp (ht hz)
    have he : complexPolynomial a m (s : ℂ) z = complexPolynomial (c x) m (s : ℂ) z := by
      unfold complexPolynomial
      apply Finset.sum_congr rfl
      intro j hj
      rw [hagree x z (ball_subset_closedBall hxz) j (by have h := Finset.mem_range.mp hj; omega)]
    rw [he]
    have hCx : C x ≤ D := Finset.single_le_sum (fun y _ => hC y) hxt
    exact (hs x hxt z (ball_subset_closedBall hxz)).trans
      (mul_le_mul_of_nonneg_right hCx (pow_nonneg hsp.le _))

end Kneser.FiniteLocalExpansionGluing

end
