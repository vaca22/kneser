import Kneser.FiniteExpansionHolomorphy
import Kneser.StableHolomorphicInverse
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! The finite analytic Taylor family has a genuine joint analytic inverse.
It is constructed by the analytic implicit function theorem; no moving
inverse or its continuity is a hypothesis. -/

set_option autoImplicit false
noncomputable section

namespace Kneser.FiniteTaylorImplicitInverse

open Filter Set Metric
open scoped Topology ContDiff
open Kneser.FiniteExpansionHolomorphy

theorem exists_analytic_implicit_inverse (G : ℂ × ℂ → ℂ) (v₀ z₀ : ℂ)
    (hG : AnalyticAt ℂ G (0, v₀)) (hbase : G (0, v₀) = z₀)
    (hderiv : deriv (fun v : ℂ => G (0, v)) v₀ ≠ 0) :
    ∃ W : ℂ × ℂ → ℂ, AnalyticAt ℂ W (0, z₀) ∧ W (0, z₀) = v₀ ∧
      ∀ᶠ p : ℂ × ℂ in 𝓝 (0, z₀), G (p.1, W p) = p.2 := by
  let f : (ℂ × ℂ) × ℂ → ℂ := fun p => G (p.1.1, p.2) - p.1.2
  have hf : AnalyticAt ℂ f ((0, z₀), v₀) := by
    have hfirst : AnalyticAt ℂ (fun p : (ℂ × ℂ) × ℂ => p.1.1) ((0, z₀), v₀) :=
      analyticAt_fst.comp analyticAt_fst
    have hsecond : AnalyticAt ℂ (fun p : (ℂ × ℂ) × ℂ => p.2) ((0, z₀), v₀) := analyticAt_snd
    have htarget : AnalyticAt ℂ (fun p : (ℂ × ℂ) × ℂ => p.1.2) ((0, z₀), v₀) :=
      analyticAt_snd.comp analyticAt_fst
    have hgcomp : AnalyticAt ℂ (fun p : (ℂ × ℂ) × ℂ => G (p.1.1, p.2)) ((0, z₀), v₀) :=
      hG.comp_of_eq (hfirst.prod hsecond) rfl
    exact hgcomp.sub htarget
  have hspatial : AnalyticAt ℂ (fun v : ℂ => G (0, v)) v₀ :=
    hG.comp (analyticAt_const.prod analyticAt_id)
  let i : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ
    (Units.mk0 (deriv (fun v : ℂ => G (0, v)) v₀) hderiv)
  have hd : HasFDerivAt (fun v : ℂ => f ((0, z₀), v)) i.toContinuousLinearMap v₀ := by
    rw [hasFDerivAt_iff_hasDerivAt]
    simpa [f, i] using hspatial.differentiableAt.hasDerivAt.sub_const z₀
  have hpartial := hf.differentiableAt.hasFDerivAt.comp v₀
    (hasFDerivAt_prodMk_right (0, z₀) v₀)
  have hinvertible : (fderiv ℂ f ((0, z₀), v₀) ∘L
      ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ).IsInvertible := by
    exact ⟨i, (hpartial.unique hd).symm⟩
  let hc : ContDiffAt ℂ ω f ((0, z₀), v₀) := hf.contDiffAt
  let W := hc.implicitFunction (by simp : (ω : ℕ∞ω) ≠ 0) hinvertible
  refine ⟨W, (hc.contDiffAt_implicitFunction (by simp) hinvertible).analyticAt,
    hc.implicitFunction_apply_self (by simp) hinvertible, ?_⟩
  have he := hc.eventually_apply_implicitFunction (by simp) hinvertible
  filter_upwards [he] with p hp
  change G (p.1, W p) - p.2 = G (0, v₀) - z₀ at hp
  rw [hbase, sub_self] at hp
  exact sub_eq_zero.mp hp

theorem complexPolynomial_zero (c : ℕ → ℂ → ℂ) (m : ℕ) (v : ℂ) :
    complexPolynomial c m 0 v = c 0 v := by
  rw [complexPolynomial, Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    simp [zero_pow hj]
  · simp

theorem exists_polynomial_implicit_inverse (c : ℕ → ℂ → ℂ) (m : ℕ)
    (v₀ z₀ : ℂ) (hc : ∀ j ≤ m, AnalyticAt ℂ (c j) v₀)
    (hbase : c 0 v₀ = z₀) (hderiv : deriv (c 0) v₀ ≠ 0) :
    ∃ W : ℂ × ℂ → ℂ, AnalyticAt ℂ W (0, z₀) ∧ W (0, z₀) = v₀ ∧
      ∀ᶠ p : ℂ × ℂ in 𝓝 (0, z₀), complexPolynomial c m p.1 (W p) = p.2 := by
  apply exists_analytic_implicit_inverse
    (fun p : ℂ × ℂ => complexPolynomial c m p.1 p.2) v₀ z₀
    (analyticAt_complexPolynomial c m 0 v₀ hc)
  · simpa only [complexPolynomial_zero] using hbase
  · have he : (fun v : ℂ => complexPolynomial c m 0 v) = c 0 := by
      funext v
      exact complexPolynomial_zero c m v
    rwa [he]

end Kneser.FiniteTaylorImplicitInverse

end
