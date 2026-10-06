import Kneser.AllOrderParameterCoherence

/-!
A sewing error that is smaller than every power preserves the entire
coherent multiplier-parameter logarithm expansion.  The sewn coefficient
does not have to be analytic in the parameter.  Its actual convergence,
principal-logarithm branch and logarithm remainder are proved from the
coefficient comparison and the existing true horn branch.
-/

set_option autoImplicit false
noncomputable section
namespace Kneser.FlatSewingLogTransfer

open Filter Set Metric Complex
open Kneser.AllOrderGateFourier Kneser.AllOrderScalarAnalytic
open Kneser.AllOrderParameterExpansion Kneser.AllOrderParameterCoherence
open scoped Topology

theorem tendsto_of_parameterExpansion_zero (f : ℝ → ℂ) (p : ℂ → ℂ)
    (a : ℕ → ℂ) (hpa : AnalyticAt ℂ p 0) (hp0 : p 0 = 0)
    (he : ParameterExpansion f p a 0) :
    Tendsto f (𝓝[>] 0) (𝓝 (f 0)) := by
  obtain ⟨C, _hC, hC⟩ := he.2
  have hb : ∀ᶠ s : ℝ in 𝓝[>] 0, ‖f s - f 0‖ ≤ C * ‖p (s : ℂ)‖ := by
    simpa only [scalarPolynomial, Finset.sum_range_one, pow_zero, one_mul,
      he.1, zero_add, pow_one] using hC
  have ht : Tendsto (fun s : ℝ => C * ‖p (s : ℂ)‖) (𝓝[>] 0) (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using
      (parameter_curve_tendsto p hpa hp0).norm.const_mul C
  have hz : Tendsto (fun s : ℝ => f s - f 0) (𝓝[>] 0) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hb ht)
  simpa only [sub_add_cancel, zero_add] using hz.add_const (f 0)

/-- The actual horn branch rules out the exceptional totalized value
`log 0 = 0`, so its normalized logarithm really determines its limit. -/
theorem coefficient_tendsto_of_log_expansion (g : ℝ → ℂ) (p : ℂ → ℂ)
    (a : ℕ → ℂ) (hg0 : g 0 ≠ 0)
    (hpa : AnalyticAt ℂ p 0) (hp0 : p 0 = 0)
    (hlog : ParameterExpansion (fun s => log (g s / g 0)) p a 0)
    (hbranch : ∀ᶠ s : ℝ in 𝓝[>] 0, g s / g 0 ∈ slitPlane) :
    Tendsto g (𝓝[>] 0) (𝓝 (g 0)) := by
  have hzero : log (g 0 / g 0) = 0 := by rw [div_self hg0, log_one]
  have hl : Tendsto (fun s : ℝ => log (g s / g 0)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [hzero] using
      tendsto_of_parameterExpansion_zero _ p a hpa hp0 hlog
  have he := (continuous_exp.continuousAt.tendsto.comp hl).mul_const (g 0)
  have hi : (fun s : ℝ => exp (log (g s / g 0)) * g 0) =ᶠ[𝓝[>] 0] g := by
    filter_upwards [hbranch] with s hs
    rw [exp_log (slitPlane_ne_zero hs)]
    exact div_mul_cancel₀ _ hg0
  simpa only [exp_zero, one_mul] using he.congr' hi

theorem tendsto_of_flat_comparison (f g : ℝ → ℂ) (Λ : ℝ → ℝ)
    (D : ℝ) (hD : 0 ≤ D) (hg : Tendsto g (𝓝[>] 0) (𝓝 (g 0)))
    (he : ∀ᶠ s : ℝ in 𝓝[>] 0, ‖f s - g s‖ ≤ D * Λ s)
    (hflat : ∀ᶠ s : ℝ in 𝓝[>] 0, Λ s ≤ s) :
    Tendsto f (𝓝[>] 0) (𝓝 (g 0)) := by
  have hb : ∀ᶠ s : ℝ in 𝓝[>] 0, ‖f s - g s‖ ≤ D * s := by
    filter_upwards [he, hflat] with s hs hΛ
    exact hs.trans (mul_le_mul_of_nonneg_left hΛ hD)
  have ht : Tendsto (fun s : ℝ => D * s) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, id_eq] using
      (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0)).const_mul D
  have hz : Tendsto (fun s : ℝ => f s - g s) (𝓝[>] 0) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hb ht)
  simpa only [sub_add_cancel, zero_add] using hz.add hg

/-- Genuine local analyticity gives a uniform Lipschitz constant near the
common limit. The logarithm comparison is therefore a conclusion. -/
theorem analytic_comparison_of_flat_error (f g : ℝ → ℂ) (Λ : ℝ → ℝ)
    (D : ℝ) (hD : 0 ≤ D) (z₀ : ℂ)
    (hf : Tendsto f (𝓝[>] 0) (𝓝 z₀))
    (hg : Tendsto g (𝓝[>] 0) (𝓝 z₀))
    (he : ∀ᶠ s : ℝ in 𝓝[>] 0, ‖f s - g s‖ ≤ D * Λ s)
    (G : ℂ → ℂ) (hG : AnalyticAt ℂ G z₀) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖G (f s) - G (g s)‖ ≤ E * Λ s := by
  obtain ⟨L, W, hW, hLip⟩ := hG.hasStrictFDerivAt.exists_lipschitzOnWith
  refine ⟨(L : ℝ) * D, mul_nonneg L.coe_nonneg hD, ?_⟩
  filter_upwards [hf.eventually hW, hg.eventually hW, he] with s hfs hgs hs
  have h := hLip.dist_le_mul (f s) hfs (g s) hgs
  rw [dist_eq_norm, dist_eq_norm] at h
  exact h.trans ((mul_le_mul_of_nonneg_left hs L.coe_nonneg).trans_eq (by ring))

theorem parameterExpansion_of_flat_comparison (f g : ℝ → ℂ)
    (Λ : ℝ → ℝ) (p : ℂ → ℂ) (a : ℕ → ℂ) (m : ℕ)
    (hp0 : p 0 = 0) (hp : HasDerivAt p 2 0) (hbase : f 0 = g 0)
    (hg : ParameterExpansion g p a m)
    (D : ℝ) (hD : 0 ≤ D)
    (he : ∀ᶠ s : ℝ in 𝓝[>] 0, ‖f s - g s‖ ≤ D * Λ s)
    (hflat : ∀ᶠ s : ℝ in 𝓝[>] 0, Λ s ≤ s ^ (m + 1)) :
    ParameterExpansion f p a m := by
  obtain ⟨C, hC, hc⟩ := hg.2
  refine ⟨hg.1.trans hbase.symm, D + C, add_nonneg hD hC, ?_⟩
  filter_upwards [hc, he, hflat,
    Kneser.QuantitativeHornExpansion.parameter_norm_comparison p hp0 hp,
    self_mem_nhdsWithin] with s hs hes hΛ hcomp hsp
  change 0 < s at hsp
  have hpow := pow_le_pow_left₀ hsp.le hcomp (m + 1)
  have herr : ‖f s - g s‖ ≤ D * ‖p (s : ℂ)‖ ^ (m + 1) :=
    hes.trans ((mul_le_mul_of_nonneg_left hΛ hD).trans
      (mul_le_mul_of_nonneg_left hpow hD))
  calc
    ‖f s - scalarPolynomial a m (p (s : ℂ))‖ ≤
        ‖f s - g s‖ + ‖g s - scalarPolynomial a m (p (s : ℂ))‖ := by
      convert norm_add_le (f s - g s) (g s - scalarPolynomial a m (p (s : ℂ))) using 1
      congr 1
      ring
    _ ≤ D * ‖p (s : ℂ)‖ ^ (m + 1) + C * ‖p (s : ℂ)‖ ^ (m + 1) :=
      add_le_add herr hs
    _ = _ := by ring

/-- One coherent sequence, including its first coefficient, is preserved
by the sewing error.  Both the common coefficient limit and the valid
principal-logarithm branch for the sewn quantity are derived here. -/
theorem all_orders_log_of_flat_comparison (f g : ℝ → ℂ) (Λ : ℝ → ℝ)
    (p : ℂ → ℂ) (a : ℕ → ℂ) (hg0 : g 0 ≠ 0) (hbase : f 0 = g 0)
    (hpa : AnalyticAt ℂ p 0) (hp0 : p 0 = 0) (hp : HasDerivAt p 2 0)
    (hlog : ∀ m : ℕ, ParameterExpansion (fun s => log (g s / g 0)) p a m)
    (hbranch : ∀ᶠ s : ℝ in 𝓝[>] 0, g s / g 0 ∈ slitPlane)
    (D : ℝ) (hD : 0 ≤ D)
    (he : ∀ᶠ s : ℝ in 𝓝[>] 0, ‖f s - g s‖ ≤ D * Λ s)
    (hflat : ∀ m : ℕ, ∀ᶠ s : ℝ in 𝓝[>] 0, Λ s ≤ s ^ m) :
    Tendsto f (𝓝[>] 0) (𝓝 (g 0)) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0, f s / g 0 ∈ slitPlane) ∧
      ∀ m : ℕ, ParameterExpansion (fun s => log (f s / g 0)) p a m := by
  have hg := coefficient_tendsto_of_log_expansion g p a hg0 hpa hp0 (hlog 0) hbranch
  have hf := tendsto_of_flat_comparison f g Λ D hD hg he
    (by simpa only [pow_one] using hflat 1)
  have hr : Tendsto (fun s : ℝ => f s / g 0) (𝓝[>] 0) (𝓝 (1 : ℂ)) := by
    simpa only [div_self hg0] using hf.div_const (g 0)
  have hb : ∀ᶠ s : ℝ in 𝓝[>] 0, f s / g 0 ∈ slitPlane :=
    hr.eventually (isOpen_slitPlane.mem_nhds one_mem_slitPlane)
  have hG : AnalyticAt ℂ (fun z : ℂ => log (z / g 0)) (g 0) := by
    apply (analyticAt_id.div_const).clog
    change g 0 / g 0 ∈ slitPlane
    simpa only [div_self hg0] using one_mem_slitPlane
  obtain ⟨E, hE, herror⟩ := analytic_comparison_of_flat_error f g Λ D hD (g 0) hf hg he _ hG
  refine ⟨hf, hb, fun m => ?_⟩
  apply parameterExpansion_of_flat_comparison (fun s => log (f s / g 0))
    (fun s => log (g s / g 0)) Λ p a m hp0 hp
    (by rw [hbase]) (hlog m) E hE herror (hflat (m + 1))

end Kneser.FlatSewingLogTransfer
end
