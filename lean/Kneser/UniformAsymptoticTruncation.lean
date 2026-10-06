import Kneser.FinitePolynomialCoefficientBounds

/-! One additional finite expansion gives a compact-uniform integer-power
remainder. Bounds for its last coefficient are proved by finite sampling.
-/

noncomputable section
namespace Kneser.AsymptoticCoefficientUniqueness

open Filter Set Kneser.FinitePolynomialCoefficientBounds
open scoped Topology

theorem truncate_one_uniform {α : Type*} (f : ℝ → α → ℂ)
    (c : ℕ → α → ℂ) (m : ℕ) (S : Set α) (C γ : ℝ) (hC : 0 ≤ C) (hγ : 0 < γ)
    (hbound : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
      ‖f s u - polynomial (fun j => c j u) (m + 1) s‖ ≤
        C * s ^ (((m + 1 : ℕ) : ℝ) + γ))
    (hf : ∀ᶠ s : ℝ in 𝓝[>] 0, ∃ B : ℝ, ∀ u ∈ S, ‖f s u‖ ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
      ‖f s u - polynomial (fun j => c j u) m s‖ ≤ D * s ^ ((m : ℝ) + 1) := by
  obtain ⟨B, hB, hcoeff⟩ := exists_uniform_coefficient_bound f c (m + 1) S C γ hC hbound hf
  refine ⟨C + B, by positivity, ?_⟩
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ h => h.le).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hle, hbound] with s hs hs1 hb u hu
  have he : f s u - polynomial (fun j => c j u) m s =
      (f s u - polynomial (fun j => c j u) (m + 1) s) +
        (s : ℂ) ^ (m + 1) * c (m + 1) u := by
    rw [polynomial_last]
    ring
  have hpow : s ^ (((m + 1 : ℕ) : ℝ) + γ) ≤ s ^ ((m : ℝ) + 1) := by
    apply Real.rpow_le_rpow_of_exponent_ge hs hs1
    push_cast
    linarith
  have hn : ‖(s : ℂ) ^ (m + 1) * c (m + 1) u‖ ≤ s ^ ((m : ℝ) + 1) * B := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    rw [show (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_left (hcoeff u hu (m + 1) le_rfl) (pow_nonneg hs.le _)
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add
    ((hb u hu).trans (mul_le_mul_of_nonneg_left hpow hC)) hn).trans_eq (by ring))

theorem truncate_uniform_integer {α : Type*} (f : ℝ → α → ℂ)
    (c : ℕ → α → ℂ) (M m : ℕ) (hmM : m ≤ M) (S : Set α) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
      ‖f s u - polynomial (fun j => c j u) M s‖ ≤ C * s ^ ((M : ℝ) + 1))
    (hf : ∀ᶠ s : ℝ in 𝓝[>] 0, ∃ B : ℝ, ∀ u ∈ S, ‖f s u‖ ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
      ‖f s u - polynomial (fun j => c j u) m s‖ ≤ D * s ^ ((m : ℝ) + 1) := by
  induction M generalizing C with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    exact ⟨C, hC, hbound⟩
  | succ M ih =>
    by_cases hm : m = M + 1
    · subst m
      exact ⟨C, hC, hbound⟩
    · obtain ⟨D, hD, hd⟩ := truncate_one_uniform f c M S C 1 hC (by norm_num) hbound hf
      exact ih (by omega) D hD hd

end Kneser.AsymptoticCoefficientUniqueness
