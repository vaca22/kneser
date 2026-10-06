import Kneser.ReflectedCommonPreparedFamily
import Kneser.ReflectedOrbitChainCoefficient

/-! A single actual quadratic baseline and its entire family of higher
corrections support compact uniform expansions on both sides. The common
degree-one member is tied to the existing actual coordinate definitions. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Kneser.ActualBilateralHigherPreparation

open Filter Kneser.ExponentialUnfolding Kneser.ExponentialRootPolynomial
open Kneser.ExponentialPreparedModel Kneser.ExponentialMatrixDividedDifference
open Kneser.ExponentialPreparedQuadratic Kneser.CommonPreparedFamily
open Kneser.CommonQuadraticBaseline Kneser.ReflectedOrbitChainCoefficient
open scoped Topology

theorem quadratic_data_of_common_preparation
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : Fin 2 → ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0) (hUd : deriv U 0 ≠ 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (hHlog : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    (hK0 : K 0 0 = 1 / 2) (hK : ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0)
    (hF : AnalyticAt ℂ F 0)
    (hq : ∀ x u, rootPolynomial A B (x ^ 2) u = rootProduct U x u)
    (hroots : ∀ᶠ x in 𝓝 0, unfolding (x ^ 2) (U x) = U x ∧
      unfolding (x ^ 2) (U (-x)) = U (-x))
    (hfactor : ∀ᶠ s in 𝓝 0, ∀ u, unfolding s u - u = rootPolynomial A B s u * K s u)
    (hresidue : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ), p.1 ≠ 0 → F p =
      Complex.log (1 + (p.2 - U (-p.1)) * symmetricCofactor U p.1 p.2) /
        Complex.log (rootMultiplier U p.1) +
      Complex.log (1 + (p.2 - U p.1) * symmetricCofactor U p.1 p.2) /
        Complex.log (rootMultiplier U (-p.1)) - 1)
    (hp : Prepared A B F 1 e Γ) :
    ActualPreparationData U H (first e) (second e) A B K F Γ := by
  obtain ⟨he, hΓ, hEven, hprep⟩ := hp
  exact ⟨hU, hU0, hUd, hH, hHne, hHlog, hA, hB, hA0, hB0,
    he 0, he 1, hF, hΓ, hEven, hK0, hK, hq, hroots, hfactor,
    by simpa only [correction_one] using hprep, hresidue⟩

theorem exists_actual_bilateral_common_all_orders :
    ∃ U H A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F : ℂ × ℂ → ℂ,
    ∃ e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ, ∃ Γ : ℕ → ℂ × ℂ → ℂ,
      ActualPreparationData U H (first (e 1)) (second (e 1)) A B K F (Γ 1) ∧
      (∀ n, Prepared A B F n (e n) (Γ n)) ∧
      Kneser.UniformActualHigherCoordinate.CompactAllFiniteExpansions U H A B e Γ ∧
      Kneser.ReflectedCommonPreparedFamily.CompactAllFiniteExpansions U H A B e Γ ∧
      Kneser.SharedPreparedConsistency.CoefficientConsistent U H A B e Γ ∧
      Kneser.ReflectedCommonPreparedFamily.CoefficientConsistent U H A B e Γ := by
  obtain ⟨U, H, A, B, K, F, e, Γ, hU, hU0, hUd, hH, hHne, hHlog,
    hA, hB, hA0, hB0, hK0, hK, hF, hq, hroots, hfactor, hresidue,
    hprep, hAexp, _hzero, hAconsistent, _hzeroN⟩ :=
    Kneser.SharedPreparedConsistency.exists_actual_consistent_compact_all_orders
  have hRexp := Kneser.ReflectedCommonPreparedFamily.compactAllFiniteExpansions_of_common_preparations
    U H A B K F e Γ hU hU0 hH hHne hA hB hA0 hB0 hK
      (by rw [hK0]; norm_num) hfactor hprep
  exact ⟨U, H, A, B, K, F, e, Γ,
    quadratic_data_of_common_preparation U H A B K F (e 1) (Γ 1)
      hU hU0 hUd hH hHne hHlog hA hB hA0 hB0 hK0 hK hF hq hroots hfactor hresidue (hprep 1),
    hprep, hAexp, hRexp, hAconsistent,
    Kneser.ReflectedCommonPreparedFamily.coefficientConsistent_of_compact_expansions
      U H A B e Γ hRexp⟩

end Kneser.ActualBilateralHigherPreparation

end
