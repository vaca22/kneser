import Kneser.ActualDeepCoordinateData
import Kneser.RealNormalizationAnchor
import Kneser.UniformFiniteCoordinateTransport
import Kneser.ActualAttractingGateTransport

/-!
The manuscript's real normalization anchor is transported by its genuine
finite exponential orbit into the same prepared attracting coordinate.
Its first coefficient and quantitative error are derived, so subtraction
at an anchor outside the local inverse chart needs no extra assumption.
-/

noncomputable section
namespace Kneser.ActualNormalizationAnchorExpansion

open Set Filter Kneser.ExponentialUnfolding Kneser.RealNormalizationAnchor
open Kneser.ParabolicFatouHolomorphic Kneser.ParabolicCoordinateJacobian
open Kneser.PreparedActualFirstOrder Kneser.ReflectedOrbitChainCoefficient
open Kneser.ActualDeepCoordinateData Kneser.QuantitativeHornExpansion
open scoped Topology

def anchorValue (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (M : ℕ) (s : ℝ) : ℂ :=
  actualPreparedCoordinate U H e₁ e₂ A B Γ (orbit normalizationAnchor s M) s - (M : ℂ)

def anchorCoefficient (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (M : ℕ) : ℂ :=
  actualPreparedCoefficient U H e₁ e₂ A B Γ (orbit normalizationAnchor 0 M) +
    deriv attractingCoordinate (orbit normalizationAnchor 0 M) * orbitTangent normalizationAnchor M

/-- A single actual preparation supplies the normalization anchor value and
its explicit first coefficient; the entry time and the error are outputs. -/
theorem exists_anchor_expansion_of_deep
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R : ℝ)
    (hd : DeepCoordinateData U H e₁ e₂ A B Γ R) :
    ∃ M : ℕ, orbit normalizationAnchor 0 M ∈ petal (R + 1) ∧
      anchorValue U H e₁ e₂ A B Γ M 0 =
        attractingCoordinate (orbit normalizationAnchor 0 M) - (M : ℂ) ∧
      PowerExpansion (anchorValue U H e₁ e₂ A B Γ M)
        (anchorCoefficient U H e₁ e₂ A B Γ M) (6 / 5) := by
  obtain ⟨M, hentry, hWjoint⟩ := exists_anchor_enters_petal (R + 1)
  have hp : orbit normalizationAnchor 0 M ∈ petal (R + 1) := hentry
  let W : ℂ × ℂ → ℂ := fun p => orbit p.2 p.1 M
  let Q : ℝ → ℂ → ℂ := fun s u => actualPreparedCoordinate U H e₁ e₂ A B Γ u s
  let D : ℂ → ℂ := actualPreparedCoefficient U H e₁ e₂ A B Γ
  have hW : ∀ u ∈ ({normalizationAnchor} : Set ℂ), AnalyticAt ℂ W (0, u) := by
    intro u hu
    rcases Set.mem_singleton_iff.mp hu with rfl
    exact hWjoint
  have hWV : ∀ u ∈ ({normalizationAnchor} : Set ℂ), W (0, u) ∈ petal (R + 1) := by
    intro u hu
    rcases Set.mem_singleton_iff.mp hu with rfl
    exact hp
  obtain ⟨C, hC, he⟩ := UniformFiniteCoordinateTransport.uniform_moving_evaluation Q D W
    ({normalizationAnchor} : Set ℂ) (petal (R + 1)) isCompact_singleton
    (petal_isOpen (by linarith [hd.depth])) hW hWV
    hd.attracting_analytic hd.attracting_coefficient_analytic hd.attracting_error
  have hder : deriv (fun z : ℂ => Q 0 (W (z, normalizationAnchor))) 0 =
      deriv attractingCoordinate (orbit normalizationAnchor 0 M) * orbitTangent normalizationAnchor M := by
    have h := (hd.attracting_analytic _ hp).hasStrictDerivAt.hasDerivAt.comp 0
      (hasDerivAt_orbit_parameter_zero normalizationAnchor M)
    have heq := h.deriv
    change deriv (fun z : ℂ => Q 0 (W (z, normalizationAnchor))) 0 =
      deriv (fun v => actualPreparedCoordinate U H e₁ e₂ A B Γ v 0)
        (orbit normalizationAnchor 0 M) * orbitTangent normalizationAnchor M at heq
    rwa [hd.attracting_derivative _ hp] at heq
  have hex : PowerExpansion
      (fun s : ℝ => actualPreparedCoordinate U H e₁ e₂ A B Γ (orbit normalizationAnchor s M) s)
      (anchorCoefficient U H e₁ e₂ A B Γ M) (6 / 5) := by
    refine ⟨C, hC, ?_⟩
    filter_upwards [he] with s hs
    have h := hs normalizationAnchor (mem_singleton normalizationAnchor)
    simpa only [Q, D, W, Complex.ofReal_zero, hder, anchorCoefficient] using h
  refine ⟨M, hp, ?_, ?_⟩
  · exact congrArg (fun z : ℂ => z - (M : ℂ)) (hd.attracting_canonical _ hp)
  · exact ActualAttractingGateTransport.powerExpansion_sub_const _ _ (M : ℂ) _ hex

end Kneser.ActualNormalizationAnchorExpansion
end
