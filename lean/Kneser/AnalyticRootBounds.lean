import Kneser.ExponentialRootPolynomial

/-!
The quadratic estimate used on the Cauchy circles is derived from the actual
analytic root polynomial, rather than supplied as an independent bound.
-/

noncomputable section

namespace Kneser.AnalyticRootBounds

open Filter Kneser.ExponentialRootPolynomial
open scoped Topology

theorem exists_linear_norm_bound {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ s : ℂ, ‖s‖ < r → ‖f s‖ ≤ C * ‖s‖ := by
  obtain ⟨G, hGa, hG⟩ := hf.exists_eq_sum_add_pow_mul 1
  have hfactor : ∀ s, f s = s * G s := by
    intro s
    simpa [Finset.sum_range_succ, hf0, smul_eq_mul] using hG s
  have hbound : ∀ᶠ s in 𝓝 0, ‖G s‖ < ‖G 0‖ + 1 :=
    hGa.continuousAt.norm.eventually (gt_mem_nhds (by linarith : ‖G 0‖ < ‖G 0‖ + 1))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hbound
  refine ⟨r, ‖G 0‖ + 1, hr, by positivity, ?_⟩
  intro s hs
  rw [hfactor, norm_mul]
  exact (mul_le_mul_of_nonneg_left (hball (by simpa using hs)).le
    (norm_nonneg s)).trans_eq (by ring)

theorem rootPolynomial_norm_bound {a b : ℂ → ℂ}
    (ha : AnalyticAt ℂ a 0) (hb : AnalyticAt ℂ b 0) (ha0 : a 0 = 0) (hb0 : b 0 = 0) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ s u : ℂ, ‖s‖ < r → ‖u‖ ≤ 1 / 2 →
      ‖rootPolynomial a b s u‖ ≤ ‖u‖ ^ 2 + C * ‖s‖ := by
  obtain ⟨ra, Ca, hra, hCa, hab⟩ := exists_linear_norm_bound ha ha0
  obtain ⟨rb, Cb, hrb, hCb, hbb⟩ := exists_linear_norm_bound hb hb0
  refine ⟨min ra rb, Ca / 2 + Cb, lt_min hra hrb, by positivity, ?_⟩
  intro s u hs hu
  have has := hab s (lt_of_lt_of_le hs (min_le_left _ _))
  have hbs := hbb s (lt_of_lt_of_le hs (min_le_right _ _))
  have hmul := mul_le_mul has hu (norm_nonneg u) (by positivity : 0 ≤ Ca * ‖s‖)
  have ht := norm_add_le (u ^ 2 - a s * u) (b s)
  have ht2 := norm_sub_le (u ^ 2) (a s * u)
  rw [norm_pow, norm_mul] at ht2
  change ‖u ^ 2 - a s * u + b s‖ ≤ _
  nlinarith

/-- The actual exponential unfolding has an analytic root polynomial with the
required local norm estimate. No root or coefficient bound is assumed. -/
theorem exists_actual_rootPolynomial_bound :
    ∃ U a b : ℂ → ℂ, ∃ r C : ℝ,
      AnalyticAt ℂ U 0 ∧ U 0 = 0 ∧ AnalyticAt ℂ a 0 ∧ AnalyticAt ℂ b 0 ∧
      a 0 = 0 ∧ b 0 = 0 ∧ 0 < r ∧ 0 ≤ C ∧
      (∀ s u : ℂ, ‖s‖ < r → ‖u‖ ≤ 1 / 2 →
        ‖rootPolynomial a b s u‖ ≤ ‖u‖ ^ 2 + C * ‖s‖) ∧
      (∀ x u, rootPolynomial a b (x ^ 2) u = (u - U x) * (u - U (-x))) := by
  obtain ⟨U, a, b, hUa, hU0, hUd, haa, hba, ha0, hb0, ha, hb, hq, hroots, hdistinct⟩ :=
    exists_analytic_rootPolynomial
  obtain ⟨r, C, hr, hC, hbound⟩ := rootPolynomial_norm_bound haa hba ha0 hb0
  exact ⟨U, a, b, r, C, hUa, hU0, haa, hba, ha0, hb0, hr, hC, hbound, hq⟩

end Kneser.AnalyticRootBounds

end
