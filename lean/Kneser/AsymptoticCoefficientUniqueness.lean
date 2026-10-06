import Kneser.UniformActualHigherCoordinate

/-! A finite polynomial cannot be smaller than all of its monomials on
the positive real axis.  Consequently finite asymptotic coefficients are
unique even when the two remainders have different positive gains. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Kneser.AsymptoticCoefficientUniqueness

open Filter Set
open scoped Topology BigOperators

def polynomial (c : ℕ → ℂ) (m : ℕ) (s : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (m + 1), (s : ℂ) ^ j * c j

theorem polynomial_zero (c : ℕ → ℂ) (m : ℕ) : polynomial c m 0 = c 0 := by
  simp [polynomial, Finset.sum_range_succ', pow_succ]

theorem polynomial_succ (c : ℕ → ℂ) (m : ℕ) (s : ℝ) :
    polynomial c (m + 1) s = c 0 + (s : ℂ) * polynomial (fun j => c (j + 1)) m s := by
  unfold polynomial
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul]
  rw [Finset.mul_sum, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_succ]
  ring

theorem coefficient_zero_of_remainder (c : ℕ → ℂ) (m : ℕ) (C γ : ℝ)
    (hγ : 0 < γ)
    (hbound : ∀ᶠ s : ℝ in 𝓝[>] 0, ‖polynomial c m s‖ ≤ C * s ^ ((m : ℝ) + γ)) :
    c 0 = 0 := by
  have hα : 0 < (m : ℝ) + γ := by positivity
  have hp : Tendsto (fun s : ℝ => s ^ ((m : ℝ) + γ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hα.ne'] using
      (Real.continuousAt_rpow_const (0 : ℝ) ((m : ℝ) + γ) (Or.inr hα.le)).tendsto.mono_left
        nhdsWithin_le_nhds
  have hmaj : Tendsto (fun s : ℝ => C * s ^ ((m : ℝ) + γ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hp
  have hz : Tendsto (polynomial c m) (𝓝[>] 0) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hbound hmaj)
  have hcont : ContinuousAt (polynomial c m) 0 := by
    change ContinuousAt (fun s : ℝ => ∑ j ∈ Finset.range (m + 1), (s : ℂ) ^ j * c j) 0
    fun_prop
  have hc : Tendsto (polynomial c m) (𝓝[>] 0) (𝓝 (c 0)) := by
    simpa only [polynomial_zero] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hc hz

/-- Every coefficient vanishes if a degree-m polynomial has a positive
gain beyond order m on the positive real axis. -/
theorem coefficients_zero_of_remainder (c : ℕ → ℂ) (m : ℕ) (C γ : ℝ)
    (hγ : 0 < γ)
    (hbound : ∀ᶠ s : ℝ in 𝓝[>] 0, ‖polynomial c m s‖ ≤ C * s ^ ((m : ℝ) + γ)) :
    ∀ j ≤ m, c j = 0 := by
  induction m generalizing c with
  | zero =>
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    exact coefficient_zero_of_remainder c 0 C γ hγ hbound
  | succ m ih =>
    have hc0 := coefficient_zero_of_remainder c (m + 1) C γ hγ hbound
    have hshift : ∀ᶠ s : ℝ in 𝓝[>] 0,
        ‖polynomial (fun j => c (j + 1)) m s‖ ≤ C * s ^ ((m : ℝ) + γ) := by
      filter_upwards [self_mem_nhdsWithin, hbound] with s hs hb
      rw [polynomial_succ, hc0, zero_add, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hs] at hb
      have hpow : s ^ (((m + 1 : ℕ) : ℝ) + γ) = s * s ^ ((m : ℝ) + γ) := by
        calc
          s ^ (((m + 1 : ℕ) : ℝ) + γ) = s ^ (1 + ((m : ℝ) + γ)) := by
            congr 1
            push_cast
            ring
          _ = s ^ (1 : ℝ) * s ^ ((m : ℝ) + γ) := Real.rpow_add hs _ _
          _ = _ := by rw [Real.rpow_one]
      rw [hpow] at hb
      exact (mul_le_mul_iff_right₀ hs).mp (by nlinarith [hb])
    have hsucc := ih (fun j => c (j + 1)) hshift
    intro j hj
    rcases j with _ | j
    · exact hc0
    · exact hsucc j (by omega)

/-- The same function has only one degree-m asymptotic coefficient list.
The two positive remainder gains need not be equal. -/
theorem coefficients_unique_of_common_expansions (f : ℝ → ℂ)
    (c d : ℕ → ℂ) (m : ℕ) (C₁ C₂ γ₁ γ₂ : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂)
    (hc : ∀ᶠ s : ℝ in 𝓝[>] 0, ‖f s - polynomial c m s‖ ≤ C₁ * s ^ ((m : ℝ) + γ₁))
    (hd : ∀ᶠ s : ℝ in 𝓝[>] 0, ‖f s - polynomial d m s‖ ≤ C₂ * s ^ ((m : ℝ) + γ₂)) :
    ∀ j ≤ m, c j = d j := by
  let γ : ℝ := min γ₁ γ₂
  have hγ : 0 < γ := lt_min hγ₁ hγ₂
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ h => h.le).filter_mono
      nhdsWithin_le_nhds
  have hdiff : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖polynomial (fun j => c j - d j) m s‖ ≤ (C₁ + C₂) * s ^ ((m : ℝ) + γ) := by
    filter_upwards [self_mem_nhdsWithin, hle, hc, hd] with s hs hs1 hcs hds
    have hp₁ : s ^ ((m : ℝ) + γ₁) ≤ s ^ ((m : ℝ) + γ) :=
      Real.rpow_le_rpow_of_exponent_ge hs hs1 (by have hh : γ ≤ γ₁ := min_le_left _ _; linarith)
    have hp₂ : s ^ ((m : ℝ) + γ₂) ≤ s ^ ((m : ℝ) + γ) :=
      Real.rpow_le_rpow_of_exponent_ge hs hs1 (by have hh : γ ≤ γ₂ := min_le_right _ _; linarith)
    have hp : polynomial (fun j => c j - d j) m s =
        (f s - polynomial d m s) - (f s - polynomial c m s) := by
      simp only [polynomial, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [hp]
    exact (norm_sub_le _ _).trans ((add_le_add hds hcs).trans
      ((add_le_add (mul_le_mul_of_nonneg_left hp₂ hC₂)
        (mul_le_mul_of_nonneg_left hp₁ hC₁)).trans_eq (by ring)))
  intro j hj
  exact sub_eq_zero.mp (coefficients_zero_of_remainder (fun j => c j - d j) m
    (C₁ + C₂) γ hγ hdiff j hj)

end Kneser.AsymptoticCoefficientUniqueness

end
