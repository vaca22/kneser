import Kneser.AllOrderGateFourier
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Finite scalar expansions are transported through analytic functions.
The analytic reference is the finite Taylor polynomial, not an analytic
extension of the actual one-sided parameter family. All transformed
remainders follow from local analytic Lipschitz estimates and Taylor's
theorem. -/

set_option autoImplicit false
noncomputable section

namespace Kneser.AllOrderScalarAnalytic

open Filter Set Metric
open scoped Topology BigOperators
open Kneser.AllOrderGateFourier Kneser.CauchyHigherTaylor

theorem scalarPolynomial_zero (c : ℕ → ℂ) (m : ℕ) : scalarPolynomial c m 0 = c 0 := by
  unfold scalarPolynomial
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    simp [zero_pow hj]
  · simp

theorem tendsto_real_parameter :
    Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
  exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

theorem analyticAt_scalarPolynomial (c : ℕ → ℂ) (m : ℕ) (z : ℂ) :
    AnalyticAt ℂ (scalarPolynomial c m) z := by
  have he : scalarPolynomial c m =
      ∑ j ∈ Finset.range (m + 1), (fun z : ℂ => z ^ j * c j) := by
    funext z
    simp [scalarPolynomial, Finset.sum_apply]
  rw [he]
  apply Finset.analyticAt_sum
  intro j _
  exact (analyticAt_id.pow j).mul analyticAt_const

theorem coefficient_scalarPolynomial (c : ℕ → ℂ) (m j : ℕ) (hj : j ≤ m) :
    coefficient (scalarPolynomial c m) j = c j := by
  unfold coefficient scalarPolynomial
  rw [iteratedDeriv_fun_sum]
  · simp only [iteratedDeriv_mul_const_field, iteratedDeriv_fun_pow_zero]
    simp only [apply_ite, Nat.cast_zero, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq_of_mem _ _ _ (Finset.mem_range.mpr (by omega : j < m + 1))]
    have hfact : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    field_simp
  · intro k _
    exact ((analyticAt_id.pow k).mul analyticAt_const).contDiffAt

theorem scalarPolynomial_hasDerivAt_zero (c : ℕ → ℂ) (m : ℕ) (hm : 1 ≤ m) :
    HasDerivAt (scalarPolynomial c m) (c 1) 0 := by
  have he := coefficient_scalarPolynomial c m 1 hm
  have hd : deriv (scalarPolynomial c m) 0 = c 1 := by
    simpa [coefficient, iteratedDeriv_one] using he
  exact hd ▸ (analyticAt_scalarPolynomial c m 0).differentiableAt.hasDerivAt

theorem tendsto_of_reference_bound (f : ℝ → ℂ × ℂ) (g : ℂ → ℂ × ℂ)
    (m : ℕ) (C : ℝ) (hga : AnalyticAt ℂ g 0)
    (he : ∀ᶠ s : ℝ in 𝓝[>] 0, ‖f s - g (s : ℂ)‖ ≤ C * s ^ (m + 1)) :
    Tendsto f (𝓝[>] 0) (𝓝 (g 0)) := by
  have hsid : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hpow : Tendsto (fun s : ℝ => C * s ^ (m + 1)) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (hsid.pow (m + 1))
  have herr : Tendsto (fun s : ℝ => f s - g (s : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) he hpow
  have hg := hga.continuousAt.tendsto.comp tendsto_real_parameter
  have ht := herr.add hg
  simpa using ht

theorem analytic_transform_reference (f : ℝ → ℂ × ℂ) (g : ℂ → ℂ × ℂ)
    (m : ℕ) (C : ℝ) (hC : 0 ≤ C) (hga : AnalyticAt ℂ g 0)
    (he : ∀ᶠ s : ℝ in 𝓝[>] 0, ‖f s - g (s : ℂ)‖ ≤ C * s ^ (m + 1))
    (G : ℂ × ℂ → ℂ) (hG : AnalyticAt ℂ G (g 0)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖G (f s) - G (g (s : ℂ))‖ ≤ D * s ^ (m + 1) := by
  obtain ⟨L, U, hU, hLip⟩ := hG.hasStrictFDerivAt.exists_lipschitzOnWith
  have hfU := (tendsto_of_reference_bound f g m C hga he).eventually hU
  have hgU := (hga.continuousAt.tendsto.comp tendsto_real_parameter).eventually hU
  refine ⟨(L : ℝ) * C, mul_nonneg L.coe_nonneg hC, ?_⟩
  filter_upwards [hfU, hgU, he] with s hfs hgs hs
  have h := hLip.dist_le_mul (f s) hfs (g (s : ℂ)) hgs
  rw [dist_eq_norm, dist_eq_norm] at h
  exact h.trans ((mul_le_mul_of_nonneg_left hs L.coe_nonneg).trans_eq (by ring))

theorem analytic_reference_taylor (g : ℂ → ℂ) (m : ℕ) (hga : AnalyticAt ℂ g 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖g (s : ℂ) - scalarPolynomial (coefficient g) m (s : ℂ)‖ ≤ C * s ^ (m + 1) := by
  obtain ⟨R, hRa, hR⟩ := hga.exists_eq_sum_add_pow_mul (m + 1)
  let C := ‖R 0‖ + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hBound : ∀ᶠ s : ℝ in 𝓝[>] 0, ‖R (s : ℂ)‖ ≤ C := by
    have ht := hRa.continuousAt.tendsto.comp tendsto_real_parameter
    exact (ht.norm.eventually (gt_mem_nhds (by dsimp [C]; linarith : ‖R 0‖ < C))).mono
      fun _ hs => hs.le
  refine ⟨C, hC, ?_⟩
  filter_upwards [hBound, self_mem_nhdsWithin] with s hs hsp
  change 0 < s at hsp
  have hpol : (∑ j ∈ Finset.range (m + 1), ((s : ℂ) ^ j / (j.factorial : ℂ)) • iteratedDeriv j g 0) =
      scalarPolynomial (coefficient g) m (s : ℂ) := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [coefficient, smul_eq_mul, div_eq_mul_inv]
    ring
  have heq : g (s : ℂ) - scalarPolynomial (coefficient g) m (s : ℂ) =
      (s : ℂ) ^ (m + 1) * R (s : ℂ) := by
    rw [hR, hpol, smul_eq_mul]
    ring
  rw [heq, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsp]
  exact (mul_le_mul_of_nonneg_left hs (pow_nonneg hsp.le _)).trans_eq (by ring)

theorem scalarExpansion_of_analytic_reference (f : ℝ → ℂ) (g : ℂ → ℂ) (m : ℕ)
    (hga : AnalyticAt ℂ g 0) (hbase : g 0 = f 0)
    (hError : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖f s - g (s : ℂ)‖ ≤ C * s ^ (m + 1)) :
    ScalarExpansion f (coefficient g) m := by
  obtain ⟨C, hC, he⟩ := hError
  obtain ⟨D, hD, hd⟩ := analytic_reference_taylor g m hga
  refine ⟨?_, C + D, add_nonneg hC hD, ?_⟩
  · simpa [coefficient] using hbase
  · filter_upwards [he, hd] with s hs hds
    have h : ‖f s - scalarPolynomial (coefficient g) m (s : ℂ)‖ ≤
        ‖f s - g (s : ℂ)‖ + ‖g (s : ℂ) - scalarPolynomial (coefficient g) m (s : ℂ)‖ := by
      convert norm_add_le (f s - g (s : ℂ))
        (g (s : ℂ) - scalarPolynomial (coefficient g) m (s : ℂ)) using 1
      congr 1
      ring
    exact h.trans ((add_le_add hs hds).trans_eq (by ring))

theorem scalar_pair_reference (f g : ℝ → ℂ) (c d : ℕ → ℂ) (m : ℕ)
    (hf : ScalarExpansion f c m) (hg : ScalarExpansion g d m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖(f s, g s) - (scalarPolynomial c m (s : ℂ), scalarPolynomial d m (s : ℂ))‖ ≤
        C * s ^ (m + 1) := by
  obtain ⟨C, hC, he⟩ := hf.2
  obtain ⟨D, hD, hd⟩ := hg.2
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  filter_upwards [he, hd, self_mem_nhdsWithin] with s hs hds hsp
  change 0 < s at hsp
  change max ‖f s - scalarPolynomial c m (s : ℂ)‖ ‖g s - scalarPolynomial d m (s : ℂ)‖ ≤ _
  apply max_le
  · exact hs.trans (by nlinarith [pow_nonneg hsp.le (m + 1)])
  · exact hds.trans (by nlinarith [pow_nonneg hsp.le (m + 1)])

end Kneser.AllOrderScalarAnalytic

end
