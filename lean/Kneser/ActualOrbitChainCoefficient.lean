import Kneser.PreparedActualFirstOrder
import Kneser.EvenDescentChainRule

/-!
The actual derivative term in the prepared orbit series is identified with
the paper's parameter derivative plus spatial derivative times the genuine
orbit tangent.  Joint holomorphy of the descended parameter is not assumed.
-/

noncomputable section

namespace Kneser.ActualOrbitChainCoefficient

open Filter Kneser.ExponentialUnfolding Kneser.ExponentialRootPolynomial
open Kneser.EvenPreparedOrbitDiscs Kneser.ParabolicExponentialOrbit
open scoped Topology

def splitResidual (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  rootPolynomial A B (p.1 ^ 2) p.2 ^ 2 * Γ p

def parameterPartial (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (v : ℂ) : ℂ :=
  deriv (fun s => splitResidual A B Γ (Complex.sqrt s, v)) 0

def spatialPartial (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (v : ℂ) : ℂ :=
  deriv (fun w => splitResidual A B Γ (0, w)) v

def explicitTerm (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (u : ℂ) (k : ℕ) : ℂ :=
  parameterPartial A B Γ (orbit u 0 k) +
    spatialPartial A B Γ (orbit u 0 k) * orbitTangent u k

theorem analyticAt_splitResidual (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (v : ℂ)
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0)
    (hΓ : AnalyticAt ℂ Γ (0, v)) : AnalyticAt ℂ (splitResidual A B Γ) (0, v) := by
  have hs : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1 ^ 2) (0, v) := analyticAt_fst.pow 2
  have hAp := hA.comp_of_eq hs (by simp)
  have hBp := hB.comp_of_eq hs (by simp)
  exact ((((analyticAt_snd.pow 2).sub (hAp.mul analyticAt_snd)).add hBp).pow 2).mul hΓ

theorem splitResidual_even (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (hEven : ∀ x v, Γ (-x, v) = Γ (x, v)) (p : ℂ × ℂ) :
    splitResidual A B Γ (PreparedTwoRootDivision.reflectFirst p) = splitResidual A B Γ p := by
  simp only [splitResidual, PreparedTwoRootDivision.reflectFirst, neg_sq, hEven]

/-- The actual residual derivative equals the explicit chain-rule term at
each true finite orbit point. -/
theorem actual_prepared_orbit_derivative (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0)
    (hEven : ∀ x v, Γ (-x, v) = Γ (x, v)) (u : ℂ) (k : ℕ)
    (hΓ : AnalyticAt ℂ Γ (0, orbit u 0 k)) :
    deriv (fun s => descendedTerm A B Γ 2 u s k) 0 = explicitTerm A B Γ u k := by
  have h := EvenDescentChainRule.deriv_even_descent_curve
    (analyticAt_splitResidual A B Γ (orbit u 0 k) hA hB hΓ)
    (splitResidual_even A B Γ hEven)
    ((PerturbedExponentialOrbit.differentiable_orbit_parameter u k).analyticAt 0)
  simpa only [descendedTerm, splitTerm, splitResidual,
    AnalyticEvenDescent.square_sqrt, parameterPartial, spatialPartial, explicitTerm,
    deriv_orbit_parameter_zero] using h

/-- Analytic preparation at the parabolic point supplies every required
joint derivative along a sufficiently deep actual petal orbit. -/
theorem exists_deep_petal_chain_identity (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) (hΓ : AnalyticAt ℂ Γ 0)
    (hEven : ∀ x v, Γ (-x, v) = Γ (x, v)) :
    ∃ R : ℝ, 32 ≤ R ∧ ∀ u : ℂ, R ≤ (inverseCoordinate u).re →
      ∀ k : ℕ, deriv (fun s => descendedTerm A B Γ 2 u s k) 0 = explicitTerm A B Γ u k := by
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp hΓ.eventually_analyticAt
  refine ⟨max 32 (4 / η), le_max_left _ _, ?_⟩
  intro u hu k
  have h32 : 32 ≤ (inverseCoordinate u).re := (le_max_left _ _).trans hu
  have hηR : 4 / η ≤ (inverseCoordinate u).re := (le_max_right _ _).trans hu
  have hnorm := iterate_norm_bound u h32 k
  have hord : orbit u 0 k = (parabolicMap^[k]) u := unfolding_orbit_zero_eq_iterate u k
  have hden : 0 < (inverseCoordinate u).re + (k : ℝ) / 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hmul : 4 ≤ (inverseCoordinate u).re * η := (div_le_iff₀ hη).mp hηR
  have hsmall : ‖orbit u 0 k‖ < η := by
    rw [hord]
    apply hnorm.trans_lt
    apply (div_lt_iff₀ hden).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  apply actual_prepared_orbit_derivative A B Γ hA hB hEven u k
  apply hball (y := ((0 : ℂ), orbit u 0 k))
  simpa only [dist_zero_right, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] using hsmall

theorem coefficient_eq_explicit_series (U H e₁ e₂ A B : ℂ → ℂ)
    (Γ : ℂ × ℂ → ℂ) (u : ℂ)
    (hchain : ∀ k, deriv (fun s => descendedTerm A B Γ 2 u s k) 0 = explicitTerm A B Γ u k) :
    PreparedActualFirstOrder.actualPreparedCoefficient U H e₁ e₂ A B Γ u =
      deriv (fun s => ExponentialModelTime.preparedModelTime U H e₁ e₂ s u) 0 +
        ∑' k : ℕ, explicitTerm A B Γ u k := by
  exact congrArg (fun z => deriv (fun s => ExponentialModelTime.preparedModelTime U H e₁ e₂ s u) 0 + z)
    (tsum_congr hchain)

end Kneser.ActualOrbitChainCoefficient

end
