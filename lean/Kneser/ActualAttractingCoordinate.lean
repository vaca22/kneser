import Kneser.UniformActualAttracting
import Kneser.PreparedLocalAbel
import Kneser.ActualPreparedSpatialHolomorphy
import Kneser.PreparedCoefficientSpatialHolomorphy
import Kneser.PreparedCanonicalAtZero

/-!
One set of actual exponential germs simultaneously has a holomorphic
positive-parameter coordinate, a proved local Abel equation, and the
absolutely convergent explicit first coefficient with compact uniform error.
-/

noncomputable section

namespace Kneser.ActualAttractingCoordinate

open Filter Set Kneser.ExponentialUnfolding Kneser.ExponentialRootPolynomial
open Kneser.ParabolicExponentialOrbit Kneser.EvenPreparedOrbitDiscs
open Kneser.PreparedActualFirstOrder Kneser.ActualOrbitChainCoefficient
open Kneser.UniformActualAttracting
open scoped Topology

/-- The local analytic coordinate and the explicit first-order expansion
are properties of the same constructed preparation and the same coordinate. -/
theorem exists_actual_holomorphic_abel_first_order_coordinate :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      AnalyticAt ℂ U 0 ∧ U 0 = 0 ∧ deriv U 0 ≠ 0 ∧ AnalyticAt ℂ H 0 ∧ H 0 ≠ 0 ∧
      (∀ x, Complex.log (ExponentialPreparedModel.rootMultiplier U x) = x * H x) ∧
      AnalyticAt ℂ A 0 ∧ AnalyticAt ℂ B 0 ∧ A 0 = 0 ∧ B 0 = 0 ∧
      AnalyticAt ℂ e₁ 0 ∧ AnalyticAt ℂ e₂ 0 ∧ AnalyticAt ℂ F 0 ∧ AnalyticAt ℂ Γ 0 ∧
      (∀ p : ℂ × ℂ, Γ (-p.1, p.2) = Γ p) ∧
      K 0 0 = 1 / 2 ∧ ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0 ∧
      (∀ x u, rootPolynomial A B (x ^ 2) u = (u - U x) * (u - U (-x))) ∧
      (∀ᶠ x in 𝓝 (0 : ℂ), unfolding (x ^ 2) (U x) = U x ∧
        unfolding (x ^ 2) (U (-x)) = U (-x)) ∧
      (∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
        unfolding s u - u = rootPolynomial A B s u * K s u) ∧
      (∀ᶠ p in 𝓝 (0 : ℂ × ℂ),
        F p + ExponentialPreparedModel.polynomialCorrection e₁ e₂ (p.1 ^ 2)
            (unfolding (p.1 ^ 2) p.2) -
          ExponentialPreparedModel.polynomialCorrection e₁ e₂ (p.1 ^ 2) p.2 =
            rootPolynomial A B (p.1 ^ 2) p.2 ^ 2 * Γ p) ∧
      (∀ᶠ p in 𝓝 (0 : ℂ × ℂ), p.1 ≠ 0 → F p =
        Complex.log (1 + (p.2 - U (-p.1)) *
          ExponentialMatrixDividedDifference.symmetricCofactor U p.1 p.2) /
          Complex.log (ExponentialPreparedModel.rootMultiplier U p.1) +
        Complex.log (1 + (p.2 - U p.1) *
          ExponentialMatrixDividedDifference.symmetricCofactor U p.1 p.2) /
          Complex.log (ExponentialPreparedModel.rootMultiplier U (-p.1)) - 1) ∧
      ∃ R₀ : ℝ, 0 < R₀ ∧
        (∀ u₀ : ℂ, R₀ + 2 ≤ (inverseCoordinate u₀).re →
          ∃ ρ s₀ : ℝ, 0 < ρ ∧ 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
            ∀ u ∈ Metric.ball u₀ ρ,
              Summable (fun k => ‖descendedTerm A B Γ 2 u s k‖) ∧
              Summable (fun k => ‖descendedTerm A B Γ 2 (unfolding s u) s k‖) ∧
              (ExponentialModelTime.preparedModelTime U H e₁ e₂ s (unfolding s u) -
                ExponentialModelTime.preparedModelTime U H e₁ e₂ s u - 1 =
                  descendedTerm A B Γ 2 u s 0) ∧
              actualPreparedCoordinate U H e₁ e₂ A B Γ (unfolding s u) s =
                actualPreparedCoordinate U H e₁ e₂ A B Γ u s + 1) ∧
        (∀ Z : ℝ, 0 ≤ Z → ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
          DifferentiableOn ℂ (fun u => actualPreparedCoordinate U H e₁ e₂ A B Γ u s)
            (PreparedSpatialHolomorphy.boundedPetal R₀ Z)) ∧
        (∀ Z : ℝ, 0 ≤ Z →
          DifferentiableOn ℂ (actualPreparedCoefficient U H e₁ e₂ A B Γ)
            (PreparedSpatialHolomorphy.boundedPetal R₀ Z) ∧
          ContinuousOn (actualPreparedCoefficient U H e₁ e₂ A B Γ)
            (PreparedSpatialHolomorphy.boundedPetal R₀ Z) ∧
          ∀ u ∈ PreparedSpatialHolomorphy.boundedPetal R₀ Z,
            ContinuousAt (actualPreparedCoefficient U H e₁ e₂ A B Γ) u) ∧
        (∀ u : ℂ, R₀ + 1 ≤ (inverseCoordinate u).re →
          actualPreparedCoordinate U H e₁ e₂ A B Γ u 0 =
            Kneser.correctedCoordinate parabolicMap ParabolicFatouCoordinate.model
              (Kneser.coordinateDefect parabolicMap ParabolicFatouCoordinate.model) u) ∧
        ∀ S : Set ℂ, IsCompact S →
        (∀ u ∈ S, R₀ + 1 ≤ (inverseCoordinate u).re) →
        (∀ u ∈ S, Summable (fun k => ‖explicitTerm A B Γ u k‖)) ∧
        (∀ u ∈ S, actualPreparedCoefficient U H e₁ e₂ A B Γ u =
          explicitCoefficient U H e₁ e₂ A B Γ u) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          (∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
            ‖actualPreparedCoordinate U H e₁ e₂ A B Γ u s -
              actualPreparedCoordinate U H e₁ e₂ A B Γ u 0 -
              s • explicitCoefficient U H e₁ e₂ A B Γ u‖ ≤ C * s ^ (6 / 5 : ℝ)) ∧
          (∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
            ‖actualPreparedCoordinate U H e₁ e₂ A B Γ u s -
              actualPreparedCoordinate U H e₁ e₂ A B Γ u 0 -
              s • explicitCoefficient U H e₁ e₂ A B Γ u‖ ≤ C * s ^ (10 / 9 : ℝ)) ∧
          ∀ u ∈ S, HasDerivWithinAt (actualPreparedCoordinate U H e₁ e₂ A B Γ u)
            (explicitCoefficient U H e₁ e₂ A B Γ u) (Ici 0) 0 := by
  obtain ⟨U, H, e₁, e₂, A, B, K, F, Γ, hU, hU0, hUd, hH, hHne, hHlog,
    hA, hB, hA0, hB0, he₁, he₂, hF, hΓ, hΓeven, hK0, hK, hq, hroots,
    hfactor, hprepared, hresidue, R₁, hR₁, hfirst⟩ :=
    UniformActualAttracting.exists_actual_attracting_uniform_explicit_first_order
  have hcofactor := ExponentialMatrixDividedDifference.eventually_symmetricCofactor_factor
    hU hroots (PreparedLocalAbel.eventually_distinct_roots U hU hUd)
  obtain ⟨R₂, _hR₂, habel⟩ := PreparedLocalAbel.exists_local_prepared_abel
    U H e₁ e₂ A B K F Γ hU hU0 hH hHne hHlog hΓ.continuousAt hK
      (by rw [hK0]; norm_num) hfactor hcofactor hprepared hresidue
  obtain ⟨R₃, _hR₃, hhol⟩ :=
    ActualPreparedSpatialHolomorphy.exists_holomorphic_actualPreparedCoordinate
      U H e₁ e₂ A B K Γ hU hU0 hK (by rw [hK0]; norm_num) hfactor hΓ
  obtain ⟨R₄, _hR₄, hcoef⟩ :=
    PreparedCoefficientSpatialHolomorphy.exists_holomorphic_actualPreparedCoefficient
      U H e₁ e₂ A B Γ hU hU0 hH hHne he₁ he₂ hA hB hA0 hB0 hΓ
        (fun x v => hΓeven (x, v))
  obtain ⟨R₅, _hR₅, hcanonical⟩ :=
    PreparedCanonicalAtZero.exists_prepared_canonical_at_zero
      U H e₁ e₂ A B F Γ hU hU0 hUd (hroots.mono fun _ h => h.1)
        hH hHne hHlog he₁ he₂ hA hB hA0 hB0 hΓ
          (fun x v => hΓeven (x, v)) hcofactor hprepared hresidue
  let R : ℝ := max R₁ (max R₂ (max R₃ (max R₄ (R₅ + 1))))
  have h₁ : R₁ ≤ R := le_max_left _ _
  have h₂ : R₂ ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : R₃ ≤ R :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have h₄ : R₄ ≤ R :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)
  have h₅ : R₅ + 1 ≤ R :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)
  refine ⟨U, H, e₁, e₂, A, B, K, F, Γ, hU, hU0, hUd, hH, hHne, hHlog,
    hA, hB, hA0, hB0, he₁, he₂, hF, hΓ, hΓeven, hK0, hK, hq, hroots,
    hfactor, hprepared, hresidue, R, hR₁.trans_le h₁, ?_, ?_, ?_, ?_, ?_⟩
  · intro u₀ hu₀
    exact habel u₀ (by linarith)
  · intro Z hZ
    obtain ⟨s₀, C, hs₀, _hC, h⟩ := hhol R h₃ Z hZ
    exact ⟨s₀, hs₀, fun s hs hss => (h s hs hss).1⟩
  · intro Z hZ
    obtain ⟨CD, _hCD, _hbound, hd, hc, hca, _huni, _hsum⟩ := hcoef R h₄ Z hZ
    exact ⟨hd, hc, hca⟩
  · intro u hu
    exact hcanonical u (by linarith)
  · intro S hS hpetal
    exact hfirst S hS (fun u hu => by linarith [hpetal u hu])

end Kneser.ActualAttractingCoordinate

end
