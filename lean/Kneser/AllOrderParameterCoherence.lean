import Kneser.AllOrderParameterExpansion
import Kneser.AllOrderScalarCoherence

/-! Coefficient uniqueness and a single all-orders coefficient sequence
in the actual complex multiplier parameter. The parameter's approach to
zero and eventual nonvanishing are derived from its actual derivative 2;
no real-valued parameter or positivity assumption is used. -/

set_option autoImplicit false
noncomputable section

namespace Kneser.AllOrderParameterCoherence

open Filter Set
open scoped Topology BigOperators
open Kneser.AllOrderGateFourier Kneser.AllOrderScalarAnalytic
open Kneser.AllOrderParameterExpansion

theorem scalarPolynomial_succ (c : ℕ → ℂ) (m : ℕ) (z : ℂ) :
    scalarPolynomial c (m + 1) z = c 0 + z * scalarPolynomial (fun j => c (j + 1)) m z := by
  unfold scalarPolynomial
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul]
  rw [Finset.mul_sum, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ]
  ring

theorem scalarPolynomial_last (c : ℕ → ℂ) (m : ℕ) (z : ℂ) :
    scalarPolynomial c (m + 1) z = scalarPolynomial c m z + z ^ (m + 1) * c (m + 1) := by
  exact Finset.sum_range_succ _ _

theorem parameter_curve_tendsto (p : ℂ → ℂ) (hpa : AnalyticAt ℂ p 0) (hp0 : p 0 = 0) :
    Tendsto (fun s : ℝ => p (s : ℂ)) (𝓝[>] 0) (𝓝 0) := by
  convert hpa.continuousAt.tendsto.comp tendsto_real_parameter using 1
  · rfl
  · rw [hp0]

theorem parameter_curve_eventually_ne_zero (p : ℂ → ℂ) (hp0 : p 0 = 0) (hp : HasDerivAt p 2 0) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, p (s : ℂ) ≠ 0 := by
  filter_upwards [Kneser.QuantitativeHornExpansion.parameter_norm_comparison p hp0 hp,
    self_mem_nhdsWithin] with s hs hsp
  change 0 < s at hsp
  exact norm_pos_iff.mp (hsp.trans_le hs)

theorem coefficient_zero_of_parameter_bound (p : ℂ → ℂ) (hpa : AnalyticAt ℂ p 0)
    (hp0 : p 0 = 0) (c : ℕ → ℂ) (m : ℕ) (C : ℝ)
    (hBound : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖scalarPolynomial c m (p (s : ℂ))‖ ≤ C * ‖p (s : ℂ)‖ ^ (m + 1)) : c 0 = 0 := by
  have hp := parameter_curve_tendsto p hpa hp0
  have hmaj : Tendsto (fun s : ℝ => C * ‖p (s : ℂ)‖ ^ (m + 1)) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (hp.norm.pow (m + 1))
  have hz : Tendsto (fun s : ℝ => scalarPolynomial c m (p (s : ℂ))) (𝓝[>] 0) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hBound hmaj)
  have hc : Tendsto (fun s : ℝ => scalarPolynomial c m (p (s : ℂ))) (𝓝[>] 0) (𝓝 (c 0)) := by
    convert (analyticAt_scalarPolynomial c m 0).continuousAt.tendsto.comp hp using 1
    · rfl
    · rw [scalarPolynomial_zero]
  exact tendsto_nhds_unique hc hz

theorem coefficients_zero_of_parameter_bound (p : ℂ → ℂ) (hpa : AnalyticAt ℂ p 0)
    (hp0 : p 0 = 0) (hp : HasDerivAt p 2 0) (c : ℕ → ℂ) (m : ℕ) (C : ℝ)
    (hBound : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖scalarPolynomial c m (p (s : ℂ))‖ ≤ C * ‖p (s : ℂ)‖ ^ (m + 1)) :
    ∀ j ≤ m, c j = 0 := by
  induction m generalizing c with
  | zero =>
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    exact coefficient_zero_of_parameter_bound p hpa hp0 c 0 C hBound
  | succ m ih =>
    have hc0 := coefficient_zero_of_parameter_bound p hpa hp0 c (m + 1) C hBound
    have hshift : ∀ᶠ s : ℝ in 𝓝[>] 0,
        ‖scalarPolynomial (fun j => c (j + 1)) m (p (s : ℂ))‖ ≤
          C * ‖p (s : ℂ)‖ ^ (m + 1) := by
      filter_upwards [hBound, parameter_curve_eventually_ne_zero p hp0 hp] with s hs hn
      rw [scalarPolynomial_succ, hc0, zero_add, norm_mul] at hs
      have hpow : C * ‖p (s : ℂ)‖ ^ (m + 1 + 1) =
          ‖p (s : ℂ)‖ * (C * ‖p (s : ℂ)‖ ^ (m + 1)) := by
        rw [pow_succ]
        ring
      rw [hpow] at hs
      exact (mul_le_mul_iff_right₀ (norm_pos_iff.mpr hn)).mp hs
    have hh := ih (fun j => c (j + 1)) hshift
    intro j hj
    rcases j with _ | j
    · exact hc0
    · exact hh j (by omega)

theorem parameterExpansion_unique {f : ℝ → ℂ} {p : ℂ → ℂ} {c d : ℕ → ℂ} {m : ℕ}
    (hpa : AnalyticAt ℂ p 0) (hp0 : p 0 = 0) (hp : HasDerivAt p 2 0)
    (hc : ParameterExpansion f p c m) (hd : ParameterExpansion f p d m) :
    ∀ j ≤ m, c j = d j := by
  obtain ⟨C, _, hec⟩ := hc.2
  obtain ⟨D, _, hed⟩ := hd.2
  have hdiff : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖scalarPolynomial (fun j => c j - d j) m (p (s : ℂ))‖ ≤
        (C + D) * ‖p (s : ℂ)‖ ^ (m + 1) := by
    filter_upwards [hec, hed] with s hs ht
    have heq : scalarPolynomial (fun j => c j - d j) m (p (s : ℂ)) =
        (f s - scalarPolynomial d m (p (s : ℂ))) -
          (f s - scalarPolynomial c m (p (s : ℂ))) := by
      simp only [scalarPolynomial, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [heq]
    exact (norm_sub_le _ _).trans ((add_le_add ht hs).trans_eq (by ring))
  intro j hj
  exact sub_eq_zero.mp (coefficients_zero_of_parameter_bound p hpa hp0 hp
    (fun j => c j - d j) m (C + D) hdiff j hj)

theorem parameterExpansion_truncate {f : ℝ → ℂ} {p : ℂ → ℂ} {c : ℕ → ℂ} {M m : ℕ}
    (hpa : AnalyticAt ℂ p 0) (hp0 : p 0 = 0)
    (hf : ParameterExpansion f p c M) (hm : m ≤ M) : ParameterExpansion f p c m := by
  induction M generalizing m with
  | zero =>
    have hm0 : m = 0 := by omega
    subst m
    exact hf
  | succ M ih =>
    by_cases hsame : m = M + 1
    · subst m
      exact hf
    · obtain ⟨C, hC, he⟩ := hf.2
      have hb : ∀ᶠ s : ℝ in 𝓝[>] 0, ‖p (s : ℂ)‖ ≤ 1 :=
        ((parameter_curve_tendsto p hpa hp0).norm.eventually
          (gt_mem_nhds (by norm_num : ‖(0 : ℂ)‖ < (1 : ℝ)))).mono fun _ hs => hs.le
      have hLower : ParameterExpansion f p c M := by
        refine ⟨hf.1, C + ‖c (M + 1)‖, by positivity, ?_⟩
        filter_upwards [he, hb] with s hs hps
        have heq : f s - scalarPolynomial c M (p (s : ℂ)) =
            (f s - scalarPolynomial c (M + 1) (p (s : ℂ))) +
              (p (s : ℂ)) ^ (M + 1) * c (M + 1) := by
          rw [scalarPolynomial_last]
          ring
        have hpow : ‖p (s : ℂ)‖ ^ (M + 1 + 1) ≤ ‖p (s : ℂ)‖ ^ (M + 1) := by
          rw [pow_succ]
          exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) hps
        rw [heq]
        apply (norm_add_le _ _).trans
        rw [norm_mul, norm_pow]
        exact (add_le_add (hs.trans (mul_le_mul_of_nonneg_left hpow hC)) le_rfl).trans_eq (by ring)
      exact ih hLower (by omega)

theorem exists_coherent_parameter_coefficients (f : ℝ → ℂ) (p : ℂ → ℂ)
    (hpa : AnalyticAt ℂ p 0) (hp0 : p 0 = 0) (hp : HasDerivAt p 2 0)
    (h : ∀ m : ℕ, ∃ c : ℕ → ℂ, ParameterExpansion f p c m) :
    ∃ c : ℕ → ℂ, ∀ m : ℕ, ParameterExpansion f p c m := by
  choose a ha using h
  let c : ℕ → ℂ := fun j => a j j
  have hc (m j : ℕ) (hj : j ≤ m) : c j = a m j :=
    parameterExpansion_unique hpa hp0 hp (ha j) (parameterExpansion_truncate hpa hp0 (ha m) hj)
      j le_rfl
  refine ⟨c, ?_⟩
  intro m
  have hpoly (z : ℂ) : scalarPolynomial c m z = scalarPolynomial (a m) m z := by
    unfold scalarPolynomial
    apply Finset.sum_congr rfl
    intro j hj
    rw [hc m j (by simpa using Finset.mem_range.mp hj)]
  obtain ⟨C, hC, he⟩ := (ha m).2
  refine ⟨(hc m 0 (Nat.zero_le m)).trans (ha m).1, C, hC, ?_⟩
  simpa only [hpoly] using he

theorem exists_coherent_positive_parameter_orders (f : ℝ → ℂ) (p : ℂ → ℂ)
    (hpa : AnalyticAt ℂ p 0) (hp0 : p 0 = 0) (hp : HasDerivAt p 2 0)
    (h : ∀ m : ℕ, 1 ≤ m → ∃ c : ℕ → ℂ, ParameterExpansion f p c m) :
    ∃ c : ℕ → ℂ, ∀ m : ℕ, ParameterExpansion f p c m := by
  apply exists_coherent_parameter_coefficients f p hpa hp0 hp
  intro m
  by_cases hm : 1 ≤ m
  · exact h m hm
  · obtain ⟨c, hc⟩ := h 1 le_rfl
    exact ⟨c, parameterExpansion_truncate hpa hp0 hc (by omega)⟩

end Kneser.AllOrderParameterCoherence

end
