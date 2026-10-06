import Kneser.AsymptoticCoefficientUniqueness

/-! Finite expansions may be truncated without changing their lower
coefficients. An expansion one order further gives an integer-power
remainder, including the retained last Taylor monomial. -/

noncomputable section
namespace Kneser.AsymptoticCoefficientUniqueness

open Filter Set
open scoped Topology BigOperators

theorem polynomial_last (c : ℕ → ℂ) (m : ℕ) (s : ℝ) :
    polynomial c (m + 1) s = polynomial c m s + (s : ℂ) ^ (m + 1) * c (m + 1) := by
  exact Finset.sum_range_succ _ (m + 1)

theorem truncate_one (f : ℝ → ℂ) (c : ℕ → ℂ) (m : ℕ) (C γ : ℝ)
    (hC : 0 ≤ C) (hγ : 0 < γ)
    (hbound : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖f s - polynomial c (m + 1) s‖ ≤ C * s ^ (((m + 1 : ℕ) : ℝ) + γ)) :
    ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖f s - polynomial c m s‖ ≤ (C + ‖c (m + 1)‖) * s ^ ((m : ℝ) + 1) := by
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ h => h.le).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hle, hbound] with s hs hs1 hb
  have he : f s - polynomial c m s =
      (f s - polynomial c (m + 1) s) + (s : ℂ) ^ (m + 1) * c (m + 1) := by
    rw [polynomial_last]
    ring
  have hpow : s ^ (((m + 1 : ℕ) : ℝ) + γ) ≤ s ^ ((m : ℝ) + 1) := by
    apply Real.rpow_le_rpow_of_exponent_ge hs hs1
    push_cast
    linarith
  have hn : ‖(s : ℂ) ^ (m + 1) * c (m + 1)‖ =
      s ^ ((m : ℝ) + 1) * ‖c (m + 1)‖ := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    rw [show (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add
    (hb.trans (mul_le_mul_of_nonneg_left hpow hC)) hn.le).trans_eq (by ring))

theorem exists_truncated_expansion (f : ℝ → ℂ) (c : ℕ → ℂ) (M m : ℕ)
    (hmM : m ≤ M) (C γ : ℝ) (hC : 0 ≤ C) (hγ : 0 < γ)
    (hbound : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖f s - polynomial c M s‖ ≤ C * s ^ ((M : ℝ) + γ)) :
    ∃ D δ : ℝ, 0 ≤ D ∧ 0 < δ ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖f s - polynomial c m s‖ ≤ D * s ^ ((m : ℝ) + δ) := by
  induction M generalizing C γ with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    exact ⟨C, γ, hC, hγ, hbound⟩
  | succ M ih =>
    by_cases hm : m = M + 1
    · subst m
      exact ⟨C, γ, hC, hγ, hbound⟩
    · exact ih (by omega) (C + ‖c (M + 1)‖) 1 (by positivity) (by norm_num)
        (truncate_one f c M C γ hC hγ hbound)

theorem coefficients_unique_of_different_orders (f : ℝ → ℂ)
    (c d : ℕ → ℂ) (m M : ℕ) (hmM : m ≤ M) (C D γ δ : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hγ : 0 < γ) (hδ : 0 < δ)
    (hc : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖f s - polynomial c m s‖ ≤ C * s ^ ((m : ℝ) + γ))
    (hd : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖f s - polynomial d M s‖ ≤ D * s ^ ((M : ℝ) + δ)) :
    ∀ j ≤ m, c j = d j := by
  obtain ⟨D', δ', hD', hδ', hd'⟩ :=
    exists_truncated_expansion f d M m hmM D δ hD hδ hd
  exact coefficients_unique_of_common_expansions f c d m C D' γ δ' hC hD' hγ hδ' hc hd'

end Kneser.AsymptoticCoefficientUniqueness
