import Kneser.ActualNormalizationAnchorExpansion

/-! The genuine anchor expansion works at any proved sufficiently deep
finite entry, allowing one entry length to serve all finite orders. -/

noncomputable section
namespace Kneser.ActualAnchorFixedEntry

open Filter Set Kneser.ExponentialUnfolding Kneser.RealNormalizationAnchor
open Kneser.ActualDeepCoordinateData Kneser.ParabolicFatouHolomorphic
open Kneser.PreparedActualFirstOrder Kneser.ActualNormalizationAnchorExpansion
open Kneser.QuantitativeHornExpansion Kneser.ParabolicCoordinateJacobian
open scoped Topology

theorem anchor_expansion_of_entry (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (R : ℝ) (hd : DeepCoordinateData U H e₁ e₂ A B Γ R) (M : ℕ)
    (hentry : orbit normalizationAnchor 0 M ∈ petal (R + 1)) :
    PowerExpansion (anchorValue U H e₁ e₂ A B Γ M)
      (anchorCoefficient U H e₁ e₂ A B Γ M) (6 / 5) := by
  let W : ℂ × ℂ → ℂ := fun p => orbit p.2 p.1 M
  let Q : ℝ → ℂ → ℂ := fun s u => actualPreparedCoordinate U H e₁ e₂ A B Γ u s
  let D : ℂ → ℂ := actualPreparedCoefficient U H e₁ e₂ A B Γ
  have hW : ∀ u ∈ ({normalizationAnchor} : Set ℂ), AnalyticAt ℂ W (0, u) := by
    intro u hu
    rcases Set.mem_singleton_iff.mp hu with rfl
    exact Kneser.ParabolicOverlapGate.analyticAt_forward_orbit_joint _ 0 M
  have hWV : ∀ u ∈ ({normalizationAnchor} : Set ℂ), W (0, u) ∈ petal (R + 1) := by
    intro u hu
    rcases Set.mem_singleton_iff.mp hu with rfl
    exact hentry
  obtain ⟨C, hC, he⟩ := Kneser.UniformFiniteCoordinateTransport.uniform_moving_evaluation Q D W
    ({normalizationAnchor} : Set ℂ) (petal (R + 1)) isCompact_singleton
    (petal_isOpen (by linarith [hd.depth])) hW hWV
    hd.attracting_analytic hd.attracting_coefficient_analytic hd.attracting_error
  have hder : deriv (fun z : ℂ => Q 0 (W (z, normalizationAnchor))) 0 =
      deriv attractingCoordinate (orbit normalizationAnchor 0 M) * orbitTangent normalizationAnchor M := by
    have h := (hd.attracting_analytic _ hentry).hasStrictDerivAt.hasDerivAt.comp 0
      (hasDerivAt_orbit_parameter_zero normalizationAnchor M)
    have heq := h.deriv
    change deriv (fun z : ℂ => Q 0 (W (z, normalizationAnchor))) 0 =
      deriv (fun v => actualPreparedCoordinate U H e₁ e₂ A B Γ v 0)
        (orbit normalizationAnchor 0 M) * orbitTangent normalizationAnchor M at heq
    rwa [hd.attracting_derivative _ hentry] at heq
  have hex : PowerExpansion
      (fun s : ℝ => actualPreparedCoordinate U H e₁ e₂ A B Γ (orbit normalizationAnchor s M) s)
      (anchorCoefficient U H e₁ e₂ A B Γ M) (6 / 5) := by
    refine ⟨C, hC, ?_⟩
    filter_upwards [he] with s hs
    simpa only [Q, D, W, Complex.ofReal_zero, hder, anchorCoefficient] using
      hs normalizationAnchor (mem_singleton normalizationAnchor)
  exact Kneser.ActualAttractingGateTransport.powerExpansion_sub_const _ _ (M : ℂ) _ hex

end Kneser.ActualAnchorFixedEntry
