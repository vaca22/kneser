import Kneser.ActualAttractingCoordinate
import Kneser.ActualRepellingCoordinate

/-!
The attracting and reflected inverse first coefficients are proved for one
common actual preparation. This prevents independently chosen existence
witnesses from being silently mixed in future gate constructions.
-/

noncomputable section

namespace Kneser.BilateralFirstOrder

open Filter Set Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.PreparedActualFirstOrder Kneser.ReflectedOrbitChainCoefficient
open Kneser.UniformRepellingFirstOrder
open scoped Topology

def AttractingCompactFirstOrder (U H e₁ e₂ A B : ℂ → ℂ)
    (Γ : ℂ × ℂ → ℂ) (R : ℝ) : Prop :=
  ∀ S : Set ℂ, IsCompact S →
        (∀ u ∈ S, R + 1 ≤ (inverseCoordinate u).re) →
        (∀ u ∈ S, Summable (fun k => ‖ActualOrbitChainCoefficient.explicitTerm A B Γ u k‖)) ∧
        (∀ u ∈ S, actualPreparedCoefficient U H e₁ e₂ A B Γ u =
          UniformActualAttracting.explicitCoefficient U H e₁ e₂ A B Γ u) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          (∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
            ‖actualPreparedCoordinate U H e₁ e₂ A B Γ u s -
              actualPreparedCoordinate U H e₁ e₂ A B Γ u 0 -
              s • UniformActualAttracting.explicitCoefficient U H e₁ e₂ A B Γ u‖ ≤ C * s ^ (6 / 5 : ℝ)) ∧
          (∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
            ‖actualPreparedCoordinate U H e₁ e₂ A B Γ u s -
              actualPreparedCoordinate U H e₁ e₂ A B Γ u 0 -
              s • UniformActualAttracting.explicitCoefficient U H e₁ e₂ A B Γ u‖ ≤ C * s ^ (10 / 9 : ℝ)) ∧
          ∀ u ∈ S, HasDerivWithinAt (actualPreparedCoordinate U H e₁ e₂ A B Γ u)
            (UniformActualAttracting.explicitCoefficient U H e₁ e₂ A B Γ u) (Ici 0) 0

/-- Both actual one-sided coordinate expansions use the same root, model,
correction and residual germs, with explicit absolutely convergent series. -/
theorem exists_actual_bilateral_explicit_first_order :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      ActualPreparationData U H e₁ e₂ A B K F Γ ∧
      ∃ R : ℝ, 0 < R ∧ AttractingCompactFirstOrder U H e₁ e₂ A B Γ R ∧
        ExplicitCompactFirstOrder U H e₁ e₂ A B Γ R ∧
        (∀ u : ℂ, R + 1 ≤ (inverseCoordinate u).re →
          actualPreparedCoordinate U H e₁ e₂ A B Γ u 0 =
            Kneser.correctedCoordinate parabolicMap ParabolicFatouCoordinate.model
              (Kneser.coordinateDefect parabolicMap ParabolicFatouCoordinate.model) u) ∧
        ∀ v : ℂ, R + 1 ≤ (inverseCoordinate v).re →
          ReflectedPreparedFirstOrder.actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0 =
            Kneser.correctedCoordinate RepellingExponentialOrbit.parabolicInverse
              RepellingFatouCoordinate.model
                (Kneser.coordinateDefect RepellingExponentialOrbit.parabolicInverse
                  RepellingFatouCoordinate.model) v := by
  obtain ⟨U, H, e₁, e₂, A, B, K, F, Γ, hU, hU0, hUd, hH, hHne, hHlog,
    hA, hB, hA0, hB0, he₁, he₂, hF, hΓ, hΓeven, hK0, hK, hq, hroots,
    hfactor, hprepared, hresidue, R₁, hR₁, _habel, _hspatial, _hcoef,
    hcanonical, hattract⟩ :=
    ActualAttractingCoordinate.exists_actual_holomorphic_abel_first_order_coordinate
  have hEven : ∀ x v, Γ (-x, v) = Γ (x, v) := fun x v => hΓeven (x, v)
  obtain ⟨R₂, _hR₂, hrepel⟩ := prepared_model_compact_first_order
    U H e₁ e₂ A B K Γ hU hU0 hH hHne he₁ he₂ hA hB hA0 hB0 hΓ hEven hK
      (by rw [hK0]; norm_num) hfactor
  obtain ⟨R₃, _hR₃, hchain⟩ := ReflectedOrbitChainCoefficient.exists_deep_petal_chain_identity
    A B Γ hA hB hΓ hEven
  have hdata : ActualPreparationData U H e₁ e₂ A B K F Γ :=
    ⟨hU, hU0, hUd, hH, hHne, hHlog, hA, hB, hA0, hB0, he₁, he₂,
      hF, hΓ, hΓeven, hK0, hK, hq, hroots, hfactor, hprepared, hresidue⟩
  obtain ⟨R₄, _hR₄, hrepCanonical⟩ :=
    ReflectedCanonicalAtZero.exists_reflected_canonical_at_zero U H e₁ e₂ A B K F Γ hdata
  let R : ℝ := max R₁ (max R₂ (max R₃ (R₄ + 1)))
  have h₁ : R₁ ≤ R := le_max_left _ _
  have h₂ : R₂ ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : R₃ ≤ R :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have h₄ : R₄ + 1 ≤ R :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hc : CompactFirstOrder U H e₁ e₂ A B Γ R := by
    intro S hS hp
    exact hrepel S hS (fun v hv => by linarith [hp v hv])
  have ht : ∀ v, R + 1 ≤ (inverseCoordinate v).re → ∀ k,
      deriv (fun s => ReflectedPreparedFirstOrder.shiftedTerm A B Γ 2 v s k) 0 =
        ReflectedOrbitChainCoefficient.explicitTerm A B Γ v k := by
    intro v hv
    exact hchain v (by linarith)
  refine ⟨U, H, e₁, e₂, A, B, K, F, Γ,
    ⟨hU, hU0, hUd, hH, hHne, hHlog, hA, hB, hA0, hB0, he₁, he₂,
      hF, hΓ, hΓeven, hK0, hK, hq, hroots, hfactor, hprepared, hresidue⟩,
    R, hR₁.trans_le h₁, ?_, explicit_compact_first_order_of_chain U H e₁ e₂ A B Γ R hc ht, ?_, ?_⟩
  · intro S hS hp
    exact hattract S hS (fun u hu => by linarith [hp u hu])
  · intro u hu
    exact hcanonical u (by linarith)
  · intro v hv
    exact hrepCanonical v (by linarith)

end Kneser.BilateralFirstOrder

end
