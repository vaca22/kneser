import Kneser.UniformAttractingFirstOrder
import Kneser.ActualOrbitChainCoefficient

/-!
An unconditional certificate for the actual exponential preparation, the
explicit parameter-plus-orbit-tangent first coefficient, and one common
remainder constant on each compact initial subset of the attracting petal.
-/

noncomputable section

namespace Kneser.UniformActualAttracting

open Filter Set Kneser.ExponentialUnfolding Kneser.ExponentialRootPolynomial
open Kneser.ParabolicExponentialOrbit Kneser.EvenPreparedOrbitDiscs
open Kneser.PreparedActualFirstOrder Kneser.ActualOrbitChainCoefficient
open scoped Topology

def explicitCoefficient (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (u : ℂ) : ℂ :=
  deriv (fun s => ExponentialModelTime.preparedModelTime U H e₁ e₂ s u) 0 +
    ∑' k : ℕ, explicitTerm A B Γ u k

/-- All analytic germs and dynamical estimates in this certificate are
constructed. Its only quantified input is a compact set in the deep petal. -/
theorem exists_actual_attracting_uniform_explicit_first_order :
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
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ S : Set ℂ, IsCompact S →
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
  obtain ⟨U, A, B, e₁, e₂, K, F, Γ, hU, hU0, hUd, hA, hB, hA0, hB0,
    he₁, he₂, hF, hΓ, hK0, hK, _hFeven, hΓeven, hfactor, hprepared, hresidue, hq, hroots⟩ :=
    ExponentialPreparedQuadratic.exists_actual_prepared_quadratic
  obtain ⟨H, hH, hH0, hHlog⟩ := ExponentialPreparedModel.exists_log_multiplier_factor hU hU0
  have hHne : H 0 ≠ 0 := hH0 ▸ hUd
  have hEven : ∀ x v, Γ (-x, v) = Γ (x, v) := fun x v => hΓeven (x, v)
  obtain ⟨R₁, hR₁, hfirst⟩ := UniformAttractingFirstOrder.prepared_model_compact_first_order
    U H e₁ e₂ A B K Γ hU hU0 hH hHne he₁ he₂ hA hB hA0 hB0 hΓ hEven
      hK (by rw [hK0]; norm_num) hfactor
  obtain ⟨R₂, hR₂, hchain⟩ := exists_deep_petal_chain_identity A B Γ hA hB hΓ hEven
  refine ⟨U, H, e₁, e₂, A, B, K, F, Γ, hU, hU0, hUd, hH, hHne, hHlog,
    hA, hB, hA0, hB0, he₁, he₂, hF, hΓ, hΓeven, hK0, hK, hq, hroots,
    hfactor, hprepared, hresidue, max R₁ R₂, hR₁.trans_le (le_max_left _ _), ?_⟩
  intro S hS hpetal
  have hp₁ : ∀ u ∈ S, R₁ + 1 ≤ (inverseCoordinate u).re := by
    intro u hu
    linarith [hpetal u hu, le_max_left R₁ R₂]
  have hp₂ : ∀ u ∈ S, R₂ ≤ (inverseCoordinate u).re := by
    intro u hu
    linarith [hpetal u hu, le_max_right R₁ R₂]
  have hc : ∀ u ∈ S, ∀ k,
      deriv (fun s => descendedTerm A B Γ 2 u s k) 0 = explicitTerm A B Γ u k :=
    fun u hu => hchain u (hp₂ u hu)
  have hd : ∀ u ∈ S, actualPreparedCoefficient U H e₁ e₂ A B Γ u =
      explicitCoefficient U H e₁ e₂ A B Γ u := by
    intro u hu
    exact coefficient_eq_explicit_series U H e₁ e₂ A B Γ u (hc u hu)
  obtain ⟨C, hC, he₆, he₁₀, hsum, hder⟩ := hfirst S hS hp₁
  refine ⟨?_, hd, C, hC, ?_, ?_, ?_⟩
  · intro u hu
    simpa only [← hc u hu] using hsum u hu
  · filter_upwards [he₆] with s hs u hu
    simpa only [hd u hu] using hs u hu
  · filter_upwards [he₁₀] with s hs u hu
    simpa only [hd u hu] using hs u hu
  · intro u hu
    simpa only [hd u hu] using hder u hu

end Kneser.UniformActualAttracting

end
