import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block

/-! Finite analytic linear systems are solved by actual Cramer determinants. -/

set_option autoImplicit false
noncomputable section

namespace Kneser.AnalyticFiniteLinearSystem

open Filter Matrix
open scoped Topology BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem analyticAt_det (M : ℂ → Matrix ι ι ℂ)
    (hM : ∀ i j, AnalyticAt ℂ (fun s => M s i j) 0) :
    AnalyticAt ℂ (fun s => (M s).det) 0 := by
  simp_rw [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ hσ
  apply AnalyticAt.mul analyticAt_const
  exact Finset.analyticAt_fun_prod _ (fun i _ => hM (σ i) i)

theorem analyticAt_cramer (M : ℂ → Matrix ι ι ℂ) (v : ℂ → ι → ℂ)
    (hM : ∀ i j, AnalyticAt ℂ (fun s => M s i j) 0)
    (hv : ∀ i, AnalyticAt ℂ (fun s => v s i) 0) (i : ι) :
    AnalyticAt ℂ (fun s => Matrix.cramer (M s) (v s) i) 0 := by
  simp_rw [Matrix.cramer_apply]
  apply analyticAt_det
  intro j k
  by_cases hk : k = i
  · subst k
    simpa only [Matrix.updateCol_self] using hv j
  · simpa only [Matrix.updateCol_ne hk] using hM j k

/-- No invertible-matrix witness is assumed: a nonzero determinant at the
base point gives constructed analytic coefficients and their actual system. -/
theorem exists_analytic_solution (M : ℂ → Matrix ι ι ℂ) (v : ℂ → ι → ℂ)
    (hM : ∀ i j, AnalyticAt ℂ (fun s => M s i j) 0)
    (hv : ∀ i, AnalyticAt ℂ (fun s => v s i) 0)
    (hdet : (M 0).det ≠ 0) :
    ∃ e : ℂ → ι → ℂ, (∀ i, AnalyticAt ℂ (fun s => e s i) 0) ∧
      (∀ᶠ s in 𝓝 0, M s *ᵥ e s = v s) := by
  let e : ℂ → ι → ℂ := fun s i => Matrix.cramer (M s) (v s) i / (M s).det
  have hd := analyticAt_det M hM
  refine ⟨e, fun i => (analyticAt_cramer M v hM hv i).div hd hdet, ?_⟩
  filter_upwards [hd.continuousAt.eventually_ne hdet] with s hs
  have he : e s = ((M s).det)⁻¹ • Matrix.cramer (M s) (v s) := by
    funext i
    dsimp [e]
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [he, Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul, inv_mul_cancel₀ hs, one_smul]

end Kneser.AnalyticFiniteLinearSystem

end
