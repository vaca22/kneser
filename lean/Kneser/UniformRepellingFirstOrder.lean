import Kneser.ReflectedPreparedFirstOrder
import Kneser.UniformModelTime

/-!
The actual reflected prepared model and orbit sum have first-order
parameter expansions with common constants on compact initial petal sets.
Model discs, finite complex orbits and real infinite tails are constructed.
-/

noncomputable section

namespace Kneser.UniformRepellingFirstOrder

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ExponentialRootPolynomial
open Kneser.ParabolicExponentialOrbit Kneser.ReflectedPreparedFirstOrder
open scoped Topology

/-- The remainder constant and coefficient majorant are shared by the whole
compact initial set.  The coefficient is the actual derivative orbit sum. -/
def CompactFirstOrder (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R₀ : ℝ) : Prop :=
  ∀ S : Set ℂ, IsCompact S → (∀ v ∈ S, R₀ + 1 ≤ (inverseCoordinate v).re) →
    ∃ C CD : ℝ, 0 ≤ C ∧ 0 ≤ CD ∧
      (∀ v ∈ S, ∀ k, ‖deriv (fun s => shiftedTerm A B Γ 2 v s k) 0‖ ≤
        CD / ((k : ℝ) + 1) ^ 2) ∧
      (∀ v ∈ S, Summable (fun k => ‖deriv (fun s => shiftedTerm A B Γ 2 v s k) 0‖)) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0, ∀ v ∈ S,
        ‖actualInversePreparedCoordinate U H e₁ e₂ A B Γ v s -
          actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0 -
          s • actualInversePreparedCoefficient U H e₁ e₂ A B Γ v‖ ≤ C * s ^ (6 / 5 : ℝ)) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0, ∀ v ∈ S,
        ‖actualInversePreparedCoordinate U H e₁ e₂ A B Γ v s -
          actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0 -
          s • actualInversePreparedCoefficient U H e₁ e₂ A B Γ v‖ ≤ C * s ^ (10 / 9 : ℝ)) ∧
      ∀ v ∈ S, HasDerivWithinAt (actualInversePreparedCoordinate U H e₁ e₂ A B Γ v)
        (actualInversePreparedCoefficient U H e₁ e₂ A B Γ v) (Ici 0) 0

/-- Compactness supplies both the spatial inverse-coordinate bound and the
common disc for the true reflected logarithmic model. -/
theorem prepared_model_compact_first_order
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0) (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (he₁ : AnalyticAt ℂ e₁ 0) (he₂ : AnalyticAt ℂ e₂ 0)
    (hAa : AnalyticAt ℂ A 0) (hBa : AnalyticAt ℂ B 0)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0) (hΓa : AnalyticAt ℂ Γ 0)
    (hEven : ∀ x v, Γ (-x, v) = Γ (x, v))
    (hK : ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0) (hK0 : K 0 0 ≠ 0)
    (hfactor : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
      unfolding s u - u = rootPolynomial A B s u * K s u) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ CompactFirstOrder U H e₁ e₂ A B Γ R₀ := by
  obtain ⟨R₀, hR₀, hcommon⟩ := prepared_inverse_quadratic_first_order_uniform A B K Γ
    hAa hBa hA0 hB0 hΓa hEven hK hK0 hfactor
  refine ⟨R₀, hR₀, ?_⟩
  intro S hS hpetal
  have hvne : ∀ v ∈ S, v ≠ 0 := by
    intro v hv heq
    have h := hpetal v hv
    simp only [heq, inverseCoordinate, div_zero, Complex.zero_re] at h
    linarith
  have hi : ContinuousOn inverseCoordinate S := by
    intro v hv
    exact (continuousAt_const.div continuousAt_id (hvne v hv)).continuousWithinAt
  obtain ⟨Z₁, hZ₁⟩ := hS.exists_bound_of_continuousOn hi
  let Z : ℝ := max Z₁ 0
  have hZ : 0 ≤ Z := le_max_right _ _
  have hSin : ∀ v ∈ S, R₀ + 1 ≤ (inverseCoordinate v).re ∧ ‖inverseCoordinate v‖ ≤ Z := by
    intro v hv
    exact ⟨hpetal v hv, (hZ₁ v hv).trans (le_max_left _ _)⟩
  have hneg : ∀ v ∈ S, v.re < 0 := by
    intro v hv
    have hp : 0 < (inverseCoordinate v).re := by linarith [hpetal v hv]
    simpa only [Complex.neg_re, neg_pos] using
      ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos hp
  obtain ⟨r, Mψ, hr, hMψ, hmodel⟩ :=
    UniformModelTime.exists_compact_preparedModelTime_boundary_bounds
      hU.neg (by simp only [Pi.neg_apply, hU0, neg_zero]) hH.neg
      (by simpa only [Pi.neg_apply, neg_ne_zero] using hHne) he₁ he₂.neg S hS hneg
  exact hcommon R₀ (le_refl _) Z hZ S hSin
    (fun v s => ExponentialModelTime.preparedModelTime (-U) (-H) e₁ (-e₂) s v)
    r Mψ hr hMψ (fun v hv => (hmodel v hv).1) (fun v hv => (hmodel v hv).2)

set_option maxHeartbeats 1000000 in
/-- An unconditional actual exponential certificate with uniform compact
first-order conclusions.  Root, cofactor and prepared-defect identities
are retained in the certificate, preventing arbitrary surrogate witnesses. -/
theorem exists_actual_compact_repelling_first_order :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      AnalyticAt ℂ U 0 ∧ U 0 = 0 ∧ deriv U 0 ≠ 0 ∧
      AnalyticAt ℂ H 0 ∧ H 0 ≠ 0 ∧
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
        Complex.log (1 + (p.2 - U (-p.1)) * ExponentialMatrixDividedDifference.symmetricCofactor U p.1 p.2) /
          Complex.log (ExponentialPreparedModel.rootMultiplier U p.1) +
        Complex.log (1 + (p.2 - U p.1) * ExponentialMatrixDividedDifference.symmetricCofactor U p.1 p.2) /
          Complex.log (ExponentialPreparedModel.rootMultiplier U (-p.1)) - 1) ∧
      ∃ R₀ : ℝ, 0 < R₀ ∧ CompactFirstOrder U H e₁ e₂ A B Γ R₀ := by
  obtain ⟨U, A, B, e₁, e₂, K, F, Γ, hU, hU0, hUd, hA, hB, hA0, hB0,
    he₁, he₂, hF, hΓ, hK0, hK, _hFeven, hΓeven, hfactor, hprepared, hresidue, hq, hroots⟩ :=
    ExponentialPreparedQuadratic.exists_actual_prepared_quadratic
  obtain ⟨H, hH, hH0, hHlog⟩ := ExponentialPreparedModel.exists_log_multiplier_factor hU hU0
  have hHne : H 0 ≠ 0 := hH0 ▸ hUd
  have hΓeven' : ∀ x v, Γ (-x, v) = Γ (x, v) := by
    intro x v
    exact hΓeven (x, v)
  have hKne : K 0 0 ≠ 0 := by rw [hK0]; norm_num
  obtain ⟨R₀, hR₀, hresult⟩ := prepared_model_compact_first_order U H e₁ e₂ A B K Γ
    hU hU0 hH hHne he₁ he₂ hA hB hA0 hB0 hΓ hΓeven' hK hKne hfactor
  exact ⟨U, H, e₁, e₂, A, B, K, F, Γ, hU, hU0, hUd, hH, hHne, hHlog,
    hA, hB, hA0, hB0, he₁, he₂, hF, hΓ, hΓeven, hK0, hK, hq, hroots,
    hfactor, hprepared, hresidue, R₀, hR₀, hresult⟩

end Kneser.UniformRepellingFirstOrder

end
