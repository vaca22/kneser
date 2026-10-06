import Kneser.AsymptoticCoefficientUniqueness

/-! Preparation degrees share the exact zero-parameter coordinate and the
same normalized finite asymptotic coefficients.  All witnesses belong to
one actual root/log-defect family. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Kneser.SharedPreparedConsistency

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.ExponentialRootPolynomial Kneser.EvenPreparedOrbitDiscs
open Kneser.ExponentialPreparedHigher Kneser.HigherPreparedModelTime
open Kneser.PreparedDegreeCompatibility Kneser.CommonPreparedFamily
open Kneser.UniformActualHigherCoordinate Kneser.HigherOrderCutoff Kneser.AsymptoticBalance
open Kneser.ExponentialPreparedModel Kneser.ExponentialMatrixDividedDifference
open Kneser.ExponentialPreparedQuadratic
open scoped Topology BigOperators

theorem familyCoefficient_zero_eq_preparedSeries (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (n : ℕ) (u : ℂ) :
    familyCoefficient U H A B e Γ n 0 u = preparedSeries U H n (e n) A B (Γ n) u 0 := by
  simp only [familyCoefficient, coordinateCoefficient, CauchyHigherTaylor.coefficient,
    iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, termCoefficient,
    preparedSeries, Kneser.coordinateSeries, Complex.ofReal_zero]

/-- At the parabolic parameter every actual correction telescopes to zero
along the actual orbit.  Original residual series convergence is derived
from the constructed shrinking discs. -/
theorem exists_parabolic_preparation_equality
    (U H A B : ℂ → ℂ) (F Γ₁ Γ₂ : ℂ × ℂ → ℂ) (n₁ n₂ : ℕ)
    (e₁ : Fin (2 * n₁) → ℂ → ℂ) (e₂ : Fin (2 * n₂) → ℂ → ℂ)
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    (hΓ₁ : AnalyticAt ℂ Γ₁ 0) (hΓ₂ : AnalyticAt ℂ Γ₂ 0)
    (hEven₁ : ∀ x v, Γ₁ (-x, v) = Γ₁ (x, v))
    (hEven₂ : ∀ x v, Γ₂ (-x, v) = Γ₂ (x, v))
    (hprep₁ : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ),
      F p + correction n₁ e₁ (p.1 ^ 2) (unfolding (p.1 ^ 2) p.2) -
        correction n₁ e₁ (p.1 ^ 2) p.2 =
          rootPolynomial A B (p.1 ^ 2) p.2 ^ (n₁ + 1) * Γ₁ p)
    (hprep₂ : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ),
      F p + correction n₂ e₂ (p.1 ^ 2) (unfolding (p.1 ^ 2) p.2) -
        correction n₂ e₂ (p.1 ^ 2) p.2 =
          rootPolynomial A B (p.1 ^ 2) p.2 ^ (n₂ + 1) * Γ₂ p) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ u : ℂ, R₀ + 1 ≤ (inverseCoordinate u).re →
      preparedSeries U H n₁ e₁ A B Γ₁ u 0 = preparedSeries U H n₂ e₂ A B Γ₂ u 0 := by
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff.mp (hprep₁.and hprep₂)
  obtain ⟨R₁, hR₁, hdiscs₁⟩ := exists_prepared_orbit_disc_bounds A B Γ₁ (n₁ + 1)
    hA hB hA0 hB0 hΓ₁ hEven₁
  obtain ⟨R₂, hR₂, hdiscs₂⟩ := exists_prepared_orbit_disc_bounds A B Γ₂ (n₂ + 1)
    hA hB hA0 hB0 hΓ₂ hEven₂
  let R₀ : ℝ := max R₁ (max R₂ (max 32 (4 / δ)))
  have hR₀ : 0 < R₀ := hR₁.trans_le (le_max_left _ _)
  have hR32 : 32 ≤ R₀ := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hRδ : 4 / δ ≤ R₀ := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨R₀, hR₀, ?_⟩
  intro u hu
  have hu' : R₀ ≤ (inverseCoordinate u).re := by linarith
  have hu32 : 32 ≤ (inverseCoordinate u).re := by linarith
  let Z : ℝ := ‖inverseCoordinate u‖
  have hZ : 0 ≤ Z := norm_nonneg _
  obtain ⟨c₁, M₁, hc₁, hM₁, _hd₁, hb₁⟩ :=
    hdiscs₁ R₀ (le_max_left _ _) Z hZ u hu' (le_refl _)
  obtain ⟨c₂, M₂, hc₂, hM₂, _hd₂, hb₂⟩ :=
    hdiscs₂ R₀ ((le_max_left _ _).trans (le_max_right _ _)) Z hZ u hu' (le_refl _)
  have hs₁ : Summable (fun k => ‖descendedTerm A B Γ₁ (n₁ + 1) u 0 k‖) := by
    apply summable_norm_of_parabolic_bound _ M₁ (q := 2 * (n₁ + 1)) (by omega)
    intro k
    exact hb₁ k 0 (by simp only [norm_zero]; positivity)
  have hs₂ : Summable (fun k => ‖descendedTerm A B Γ₂ (n₂ + 1) u 0 k‖) := by
    apply summable_norm_of_parabolic_bound _ M₂ (q := 2 * (n₂ + 1)) (by omega)
    intro k
    exact hb₂ k 0 (by simp only [norm_zero]; positivity)
  have horbit := PreparedCanonicalAtZero.actual_parabolic_orbit_tendsto_zero u hu32
  have hdefect : ∀ k, descendedTerm A B Γ₁ (n₁ + 1) u 0 k -
      descendedTerm A B Γ₂ (n₂ + 1) u 0 k =
        (correction n₁ e₁ 0 (orbit u 0 (k + 1)) - correction n₂ e₂ 0 (orbit u 0 (k + 1))) -
        (correction n₁ e₁ 0 (orbit u 0 k) - correction n₂ e₂ 0 (orbit u 0 k)) := by
    intro k
    have hnorm : ‖orbit u 0 k‖ < δ := by
      apply (unfolding_orbit_zero_norm_bound u R₀ hR32 hu' k).trans_lt
      apply (div_lt_iff₀ (by positivity : 0 < R₀ + (k : ℝ) / 2)).mpr
      have hm := (div_le_iff₀ hδ).mp hRδ
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have hpδ : dist ((0 : ℂ), orbit u 0 k) (0 : ℂ × ℂ) < δ := by
      simpa only [dist_zero_right, Prod.norm_def, norm_zero,
        max_eq_right (norm_nonneg _)] using hnorm
    obtain ⟨h₁, h₂⟩ := hδball hpδ
    have hd := residual_difference_of_common_preparation A B F Γ₁ Γ₂ n₁ n₂ e₁ e₂ u 0 k
      (by simpa using h₁) (by simpa using h₂)
    simpa only [Complex.ofReal_zero] using hd
  have hdiff := preparedSeries_difference_of_orbit_limit U H A B n₁ n₂ e₁ e₂ Γ₁ Γ₂
    u 0 0 (by simpa using hs₁) (by simpa using hs₂) (by simpa using horbit) (by simpa using hdefect)
  simp only [correction_zero, sub_self] at hdiff
  exact sub_eq_zero.mp hdiff

def ZeroConsistent (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ) : Prop :=
  ∀ n₁ n₂, ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ u : ℂ, R₀ + 1 ≤ (inverseCoordinate u).re →
    preparedSeries U H n₁ (e n₁) A B (Γ n₁) u 0 =
      preparedSeries U H n₂ (e n₂) A B (Γ n₂) u 0

theorem zeroConsistent_of_common_preparations (U H A B : ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    (hprepared : ∀ n, Prepared A B F n (e n) (Γ n)) : ZeroConsistent U H A B e Γ := by
  intro n₁ n₂
  obtain ⟨_he₁, hΓ₁, hEven₁, hp₁⟩ := hprepared n₁
  obtain ⟨_he₂, hΓ₂, hEven₂, hp₂⟩ := hprepared n₂
  exact exists_parabolic_preparation_equality U H A B F (Γ n₁) (Γ n₂) n₁ n₂
    (e n₁) (e n₂) hA hB hA0 hB0 hΓ₁ hΓ₂
    (fun x v => hEven₁ (x, v)) (fun x v => hEven₂ (x, v)) hp₁ hp₂

def CoefficientConsistent (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ n₁ n₂ : ℕ,
    m * m + m + 1 ≤ n₁ + 1 → m * m + m + 1 ≤ n₂ + 1 →
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ u v : ℂ,
      R₀ + 1 ≤ (inverseCoordinate u).re → R₀ + 1 ≤ (inverseCoordinate v).re →
      ∀ j ≤ m,
        familyCoefficient U H A B e Γ n₁ j u - familyCoefficient U H A B e Γ n₁ j v =
          familyCoefficient U H A B e Γ n₂ j u - familyCoefficient U H A B e Γ n₂ j v

theorem coefficientConsistent_of_compact_expansions (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (hexp : CompactAllFiniteExpansions U H A B e Γ) : CoefficientConsistent U H A B e Γ := by
  intro m hm n₁ n₂ hN₁ hN₂
  obtain ⟨R₁, hR₁, hExp₁⟩ := hexp m hm n₁ hN₁
  obtain ⟨R₂, hR₂, hExp₂⟩ := hexp m hm n₂ hN₂
  let R₀ : ℝ := max R₁ R₂
  refine ⟨R₀, hR₁.trans_le (le_max_left _ _), ?_⟩
  intro u v hu hv
  let S : Set ℂ := {u, v}
  have hS : IsCompact S := ((Set.finite_singleton v).insert u).isCompact
  have hpetal₁ : ∀ w ∈ S, R₁ + 1 ≤ (inverseCoordinate w).re := by
    intro w hw
    have hh : R₁ ≤ R₀ := le_max_left _ _
    rcases Set.mem_insert_iff.mp hw with hwu | hwv
    · subst w; linarith
    · have hwv' : w = v := Set.mem_singleton_iff.mp hwv
      subst w; linarith
  have hpetal₂ : ∀ w ∈ S, R₂ + 1 ≤ (inverseCoordinate w).re := by
    intro w hw
    have hh : R₂ ≤ R₀ := le_max_right _ _
    rcases Set.mem_insert_iff.mp hw with hwu | hwv
    · subst w; linarith
    · have hwv' : w = v := Set.mem_singleton_iff.mp hwv
      subst w; linarith
  obtain ⟨_hsum₁, C₁, hC₁, hRem₁⟩ := hExp₁ S hS hpetal₁
  obtain ⟨_hsum₂, C₂, hC₂, hRem₂⟩ := hExp₂ S hS hpetal₂
  have hrem₁ : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖normalizedCoordinate U H A B e Γ u v s -
        AsymptoticCoefficientUniqueness.polynomial (fun j =>
          familyCoefficient U H A B e Γ n₁ j u - familyCoefficient U H A B e Γ n₁ j v) m s‖ ≤
          C₁ * s ^ ((m : ℝ) + gamma m (n₁ + 1)) := by
    filter_upwards [hRem₁] with s hs
    simpa only [normalizedPolynomial, AsymptoticCoefficientUniqueness.polynomial] using
      hs u (by simp [S]) v (by simp [S])
  have hrem₂ : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖normalizedCoordinate U H A B e Γ u v s -
        AsymptoticCoefficientUniqueness.polynomial (fun j =>
          familyCoefficient U H A B e Γ n₂ j u - familyCoefficient U H A B e Γ n₂ j v) m s‖ ≤
          C₂ * s ^ ((m : ℝ) + gamma m (n₂ + 1)) := by
    filter_upwards [hRem₂] with s hs
    simpa only [normalizedPolynomial, AsymptoticCoefficientUniqueness.polynomial] using
      hs u (by simp [S]) v (by simp [S])
  exact AsymptoticCoefficientUniqueness.coefficients_unique_of_common_expansions
    (normalizedCoordinate U H A B e Γ u v) _ _ m C₁ C₂ (gamma m (n₁ + 1)) (gamma m (n₂ + 1))
    hC₁ hC₂ (gamma_pos m (n₁ + 1) hN₁) (gamma_pos m (n₂ + 1) hN₂) hrem₁ hrem₂

theorem normalizedPolynomial_zero_eq_baseline
    (U H A B : ℂ → ℂ) (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ)
    (Γ : ℕ → ℂ × ℂ → ℂ) (n m : ℕ) (u v : ℂ)
    (hu : preparedSeries U H n (e n) A B (Γ n) u 0 =
      preparedSeries U H 1 (e 1) A B (Γ 1) u 0)
    (hv : preparedSeries U H n (e n) A B (Γ n) v 0 =
      preparedSeries U H 1 (e 1) A B (Γ 1) v 0) :
    normalizedPolynomial U H A B e Γ n m u v 0 = normalizedCoordinate U H A B e Γ u v 0 := by
  have hp : normalizedPolynomial U H A B e Γ n m u v 0 =
      familyCoefficient U H A B e Γ n 0 u - familyCoefficient U H A B e Γ n 0 v := by
    simpa only [AsymptoticCoefficientUniqueness.polynomial, normalizedPolynomial,
      Complex.ofReal_zero] using AsymptoticCoefficientUniqueness.polynomial_zero
        (fun j => familyCoefficient U H A B e Γ n j u - familyCoefficient U H A B e Γ n j v) m
  rw [hp, familyCoefficient_zero_eq_preparedSeries, familyCoefficient_zero_eq_preparedSeries, hu, hv]
  rfl

def ZeroNormalizedConsistent (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ) : Prop :=
  ∀ n m, ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ u v : ℂ,
    R₀ + 1 ≤ (inverseCoordinate u).re → R₀ + 1 ≤ (inverseCoordinate v).re →
    normalizedPolynomial U H A B e Γ n m u v 0 = normalizedCoordinate U H A B e Γ u v 0

theorem zeroNormalizedConsistent_of_zeroConsistent (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (hzero : ZeroConsistent U H A B e Γ) : ZeroNormalizedConsistent U H A B e Γ := by
  intro n m
  obtain ⟨R₀, hR₀, hsame⟩ := hzero n 1
  exact ⟨R₀, hR₀, fun u v hu hv => normalizedPolynomial_zero_eq_baseline
    U H A B e Γ n m u v (hsame u hu) (hsame v hv)⟩

/-- One actual normalized attracting family has compact uniform expansions,
preparation-independent coefficients, and its correct zero-parameter value.
All consistency assertions are proved from the constructed actual data. -/
theorem exists_actual_consistent_compact_all_orders :
    ∃ U H A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F : ℂ × ℂ → ℂ,
    ∃ e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ, ∃ Γ : ℕ → ℂ × ℂ → ℂ,
      AnalyticAt ℂ U 0 ∧ U 0 = 0 ∧ deriv U 0 ≠ 0 ∧
      AnalyticAt ℂ H 0 ∧ H 0 ≠ 0 ∧
      (∀ x, Complex.log (rootMultiplier U x) = x * H x) ∧
      AnalyticAt ℂ A 0 ∧ AnalyticAt ℂ B 0 ∧ A 0 = 0 ∧ B 0 = 0 ∧
      K 0 0 = 1 / 2 ∧ ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0 ∧
      AnalyticAt ℂ F 0 ∧
      (∀ x u, rootPolynomial A B (x ^ 2) u = rootProduct U x u) ∧
      (∀ᶠ x in 𝓝 0, unfolding (x ^ 2) (U x) = U x ∧ unfolding (x ^ 2) (U (-x)) = U (-x)) ∧
      (∀ᶠ s in 𝓝 0, ∀ u, unfolding s u - u = rootPolynomial A B s u * K s u) ∧
      (∀ᶠ p in 𝓝 (0 : ℂ × ℂ), p.1 ≠ 0 → F p =
        Complex.log (1 + (p.2 - U (-p.1)) * symmetricCofactor U p.1 p.2) /
          Complex.log (rootMultiplier U p.1) +
        Complex.log (1 + (p.2 - U p.1) * symmetricCofactor U p.1 p.2) /
          Complex.log (rootMultiplier U (-p.1)) - 1) ∧
      (∀ n, Prepared A B F n (e n) (Γ n)) ∧
      CompactAllFiniteExpansions U H A B e Γ ∧
      ZeroConsistent U H A B e Γ ∧ CoefficientConsistent U H A B e Γ ∧
      ZeroNormalizedConsistent U H A B e Γ := by
  obtain ⟨U, H, A, B, K, F, e, Γ, hU, hU0, hUd, hH, hHne, hHlog,
    hA, hB, hA0, hB0, hK0, hK, hF, hq, hroots, hfactor, hresidue, hprepared, hexp⟩ :=
    exists_actual_normalized_compact_all_orders
  have hzero := zeroConsistent_of_common_preparations U H A B F e Γ hA hB hA0 hB0 hprepared
  exact ⟨U, H, A, B, K, F, e, Γ, hU, hU0, hUd, hH, hHne, hHlog,
    hA, hB, hA0, hB0, hK0, hK, hF, hq, hroots, hfactor, hresidue, hprepared, hexp,
    hzero, coefficientConsistent_of_compact_expansions U H A B e Γ hexp,
    zeroNormalizedConsistent_of_zeroConsistent U H A B e Γ hzero⟩

end Kneser.SharedPreparedConsistency

end
