import Kneser.ReflectedPreparedSpatialHolomorphy
import Kneser.ReflectedLocalAbel
import Kneser.ReflectedCoefficientSpatialHolomorphy
import Kneser.ReflectedCanonicalAtZero

/-!
One set of actual exponential preparation germs simultaneously supplies
the reflected holomorphic coordinate, its proved local inverse Abel
equation, and its absolutely convergent explicit first parameter coefficient
with common compact remainder bounds.
-/

noncomputable section

namespace Kneser.ActualRepellingCoordinate

open Filter Set Kneser.ParabolicExponentialOrbit Kneser.RepellingExponentialOrbit
open Kneser.ReflectedPreparedFirstOrder Kneser.ReflectedOrbitChainCoefficient
open Kneser.UniformRepellingFirstOrder Kneser.ReflectedPreparedSpatialHolomorphy
open scoped Topology

/-- The local inverse Abel equation includes the true model defect and
absolute convergence at the initial point and its actual inverse image. -/
def LocalInverseAbel (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R₀ : ℝ) : Prop :=
  ∀ v₀ : ℂ, R₀ + 2 ≤ (inverseCoordinate v₀).re →
    ∃ ρ s₀ : ℝ, 0 < ρ ∧ 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∀ v ∈ Metric.ball v₀ ρ,
        Summable (fun k => ‖shiftedTerm A B Γ 2 v s k‖) ∧
        Summable (fun k => ‖shiftedTerm A B Γ 2 (reflectedInverse s v) s k‖) ∧
        (ExponentialModelTime.preparedModelTime (-U) (-H) e₁ (-e₂) s (reflectedInverse s v) -
          ExponentialModelTime.preparedModelTime (-U) (-H) e₁ (-e₂) s v - 1 =
            shiftedTerm A B Γ 2 v s 0) ∧
        actualInversePreparedCoordinate U H e₁ e₂ A B Γ (reflectedInverse s v) s =
          actualInversePreparedCoordinate U H e₁ e₂ A B Γ v s + 1

/-- The actual exponential germs and the same actual reflected coordinate
have spatial holomorphy, a proved local inverse Abel equation, and the
uniform compact first-order expansion with explicit absolutely convergent
orbit coefficients.  No preparation, branch, orbit or convergence
hypothesis is supplied. -/
theorem exists_actual_holomorphic_abel_repelling_first_order :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      ActualPreparationData U H e₁ e₂ A B K F Γ ∧
      ∃ R₀ : ℝ, 0 < R₀ ∧ CompactFirstOrder U H e₁ e₂ A B Γ R₀ ∧
        ExplicitCompactFirstOrder U H e₁ e₂ A B Γ R₀ ∧
        SpatialHolomorphy U H e₁ e₂ A B Γ R₀ ∧
        (∀ v, R₀ + 1 ≤ (inverseCoordinate v).re → ∀ k,
          deriv (fun s => shiftedTerm A B Γ 2 v s k) 0 = explicitTerm A B Γ v k) ∧
        (∀ R : ℝ, R₀ ≤ R → ∀ Z : ℝ, 0 ≤ Z →
          DifferentiableOn ℂ (actualInversePreparedCoefficient U H e₁ e₂ A B Γ)
            (PreparedSpatialHolomorphy.boundedPetal R Z) ∧
          ContinuousOn (actualInversePreparedCoefficient U H e₁ e₂ A B Γ)
            (PreparedSpatialHolomorphy.boundedPetal R Z) ∧
          ∀ v ∈ PreparedSpatialHolomorphy.boundedPetal R Z,
            ContinuousAt (actualInversePreparedCoefficient U H e₁ e₂ A B Γ) v) ∧
        (∀ v : ℂ, R₀ + 1 ≤ (inverseCoordinate v).re →
          actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0 =
            Kneser.correctedCoordinate RepellingExponentialOrbit.parabolicInverse
              RepellingFatouCoordinate.model
                (Kneser.coordinateDefect RepellingExponentialOrbit.parabolicInverse
                  RepellingFatouCoordinate.model) v) ∧
        LocalInverseAbel U H e₁ e₂ A B Γ R₀ := by
  obtain ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, R₁, hR₁, hcompact, hchain,
    hexplicit, hspatial⟩ := exists_actual_holomorphic_repelling_explicit_coefficient
  have hdata' := hdata
  rcases hdata with ⟨hU, hU0, hUd, hH, hHne, hHlog, hA, hB, hA0, hB0, he₁, he₂,
    hF, hΓ, hΓeven, hK0, hK, hq, hroots, hfactor, hprepared, hresidue⟩
  have hcofactor := ExponentialMatrixDividedDifference.eventually_symmetricCofactor_factor
    hU hroots (PreparedLocalAbel.eventually_distinct_roots U hU hUd)
  obtain ⟨R₂, _hR₂, habel⟩ := ReflectedLocalAbel.exists_local_inverse_prepared_abel
    U H e₁ e₂ A B K F Γ hU hU0 hH hHne hHlog hΓ.continuousAt hK
      (by rw [hK0]; norm_num) hfactor hcofactor hprepared hresidue
  obtain ⟨R₃, _hR₃, hcoef⟩ :=
    ReflectedCoefficientSpatialHolomorphy.exists_holomorphic_actualInversePreparedCoefficient
      U H e₁ e₂ A B Γ hU hU0 hH hHne he₁ he₂ hA hB hA0 hB0 hΓ
        (fun x v => hΓeven (x, v))
  obtain ⟨R₄, _hR₄, hcanonical⟩ :=
    ReflectedCanonicalAtZero.exists_reflected_canonical_at_zero U H e₁ e₂ A B K F Γ hdata'
  let R₀ : ℝ := max R₁ (max R₂ (max R₃ (R₄ + 1)))
  have h₁ : R₁ ≤ R₀ := le_max_left _ _
  have h₂ : R₂ ≤ R₀ := (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : R₃ ≤ R₀ :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have h₄ : R₄ + 1 ≤ R₀ :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hlower : ∀ S : Set ℂ, (∀ v ∈ S, R₀ + 1 ≤ (inverseCoordinate v).re) →
      ∀ v ∈ S, R₁ + 1 ≤ (inverseCoordinate v).re := by
    intro S hp v hv
    linarith [hp v hv]
  refine ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata', R₀, hR₁.trans_le h₁,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S hS hp
    exact hcompact S hS (hlower S hp)
  · intro S hS hp
    exact hexplicit S hS (hlower S hp)
  · intro R hR Z hZ
    exact hspatial R (h₁.trans hR) Z hZ
  · intro v hv
    exact hchain v (by linarith)
  · intro R hR Z hZ
    obtain ⟨CD, _hCD, _hbound, hd, hc, hca, _huni, _hsum⟩ := hcoef R (h₃.trans hR) Z hZ
    exact ⟨hd, hc, hca⟩
  · intro v hv
    exact hcanonical v (by linarith)
  · intro v₀ hv₀
    exact habel v₀ (by linarith)

end Kneser.ActualRepellingCoordinate

end
