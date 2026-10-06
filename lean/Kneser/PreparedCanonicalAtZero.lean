import Kneser.PreparedParabolicAbel
import Kneser.PreparedModelAtZero
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Canonical identification at the parabolic parameter

The actual prepared orbit limit agrees with the canonical attracting Fatou
coordinate because its model differs from the canonical model by a
polynomial that tends to zero along the true parabolic orbit.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.PreparedCanonicalAtZero

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ExponentialRootPolynomial
open Kneser.ExponentialPreparedQuadratic Kneser.ExponentialPreparedModel
open Kneser.ExponentialMatrixDividedDifference Kneser.ExponentialModelTime
open Kneser.EvenPreparedOrbitDiscs Kneser.ParabolicExponentialOrbit
open Kneser.PreparedActualFirstOrder Kneser.PreparedLocalAbel Kneser.PreparedParabolicAbel
open scoped Topology BigOperators

/-- The genuine parabolic exponential orbit tends to the parabolic point. -/
theorem actual_parabolic_orbit_tendsto_zero (u : ℂ) (hu : 32 ≤ (inverseCoordinate u).re) :
    Tendsto (fun k : ℕ => orbit u 0 k) atTop (𝓝 0) := by
  have hbound : ∀ k : ℕ, ‖orbit u 0 k‖ ≤ 4 / ((k : ℝ) + 1) := by
    intro k
    apply (unfolding_orbit_zero_norm_bound u 32 (by norm_num) hu k).trans
    apply (div_le_div_iff₀ (by positivity : 0 < 32 + (k : ℝ) / 2)
      (by positivity : 0 < (k : ℝ) + 1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hmajorant : Tendsto (fun k : ℕ => (4 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    convert (tendsto_const_nhds (x := (4 : ℝ))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) using 1 <;> simp [div_eq_mul_inv]
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) hbound hmajorant)

/-- The actual preparation polynomial has no constant term, and therefore
vanishes along the true attracting orbit. -/
theorem polynomialCorrection_orbit_tendsto_zero (e₁ e₂ : ℂ → ℂ) (u : ℂ)
    (hu : 32 ≤ (inverseCoordinate u).re) :
    Tendsto (fun k : ℕ => polynomialCorrection e₁ e₂ 0 (orbit u 0 k)) atTop (𝓝 0) := by
  have hpoly : ContinuousAt (fun v : ℂ => polynomialCorrection e₁ e₂ 0 v) 0 := by
    unfold polynomialCorrection
    fun_prop
  simpa [Function.comp_def, polynomialCorrection] using
    hpoly.tendsto.comp (actual_parabolic_orbit_tendsto_zero u hu)

/-- Two actual normalized orbit limits agree when their models differ by the
preparation polynomial. This lemma does not assume a coordinate equality. -/
theorem prepared_eq_canonical_of_model_and_limits
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (u : ℂ)
    (hu : 32 ≤ (inverseCoordinate u).re)
    (hmodel : ∀ v : ℂ, v.re < 0 →
      preparedModelTime U H e₁ e₂ 0 v =
        Kneser.ParabolicFatouCoordinate.model v + polynomialCorrection e₁ e₂ 0 v)
    (hprepared : Tendsto (fun n : ℕ => preparedModelTime U H e₁ e₂ 0 (orbit u 0 n) - (n : ℂ))
      atTop (𝓝 (actualPreparedCoordinate U H e₁ e₂ A B Γ u 0)))
    (hcanonical : Tendsto (fun n : ℕ => Kneser.ParabolicFatouCoordinate.model ((parabolicMap^[n]) u) - (n : ℂ))
      atTop (𝓝 (Kneser.correctedCoordinate parabolicMap Kneser.ParabolicFatouCoordinate.model
        (Kneser.coordinateDefect parabolicMap Kneser.ParabolicFatouCoordinate.model) u))) :
    actualPreparedCoordinate U H e₁ e₂ A B Γ u 0 =
      Kneser.correctedCoordinate parabolicMap Kneser.ParabolicFatouCoordinate.model
        (Kneser.coordinateDefect parabolicMap Kneser.ParabolicFatouCoordinate.model) u := by
  have hcanonical' : Tendsto
      (fun n : ℕ => Kneser.ParabolicFatouCoordinate.model (orbit u 0 n) - (n : ℂ)) atTop
      (𝓝 (Kneser.correctedCoordinate parabolicMap Kneser.ParabolicFatouCoordinate.model
        (Kneser.coordinateDefect parabolicMap Kneser.ParabolicFatouCoordinate.model) u)) := by
    simpa only [unfolding_orbit_zero_eq_iterate] using hcanonical
  have hcombined := hcanonical'.add (polynomialCorrection_orbit_tendsto_zero e₁ e₂ u hu)
  have hcombined' : Tendsto
      (fun n : ℕ => preparedModelTime U H e₁ e₂ 0 (orbit u 0 n) - (n : ℂ)) atTop
      (𝓝 (Kneser.correctedCoordinate parabolicMap Kneser.ParabolicFatouCoordinate.model
        (Kneser.coordinateDefect parabolicMap Kneser.ParabolicFatouCoordinate.model) u)) := by
    simpa only [add_zero] using hcombined.congr' (Eventually.of_forall (fun n => by
      have hre : 0 < (inverseCoordinate (orbit u 0 n)).re := by
        have h := iterate_inverse_re u hu n
        rw [← unfolding_orbit_zero_eq_iterate] at h
        linarith [Nat.cast_nonneg (α := ℝ) n]
      have hneg : (orbit u 0 n).re < 0 := by
        have h := Kneser.ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos hre
        simpa only [Complex.neg_re, neg_pos] using h
      rw [hmodel _ hneg]
      ring))
  exact tendsto_nhds_unique hprepared hcombined'

/-- The actual convergent prepared series agrees with the existing canonical
coordinate after the model decomposition is established. -/
theorem exists_prepared_canonical_at_zero_of_model (U H e₁ e₂ A B : ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (hHlog : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (he₁ : AnalyticAt ℂ e₁ 0) (he₂ : AnalyticAt ℂ e₂ 0)
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    (hΓ : AnalyticAt ℂ Γ 0) (hEven : ∀ x v, Γ (-x, v) = Γ (x, v))
    (hcofactor : ∀ᶠ x in 𝓝 (0 : ℂ), ∀ u,
      unfolding (x ^ 2) u - u = rootProduct U x u * symmetricCofactor U x u)
    (hprepared : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ),
      F p + polynomialCorrection e₁ e₂ (p.1 ^ 2) (unfolding (p.1 ^ 2) p.2) -
        polynomialCorrection e₁ e₂ (p.1 ^ 2) p.2 =
        rootPolynomial A B (p.1 ^ 2) p.2 ^ 2 * Γ p)
    (hresidue : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ), p.1 ≠ 0 → F p =
      Complex.log (1 + (p.2 - U (-p.1)) * symmetricCofactor U p.1 p.2) /
        Complex.log (rootMultiplier U p.1) +
      Complex.log (1 + (p.2 - U p.1) * symmetricCofactor U p.1 p.2) /
        Complex.log (rootMultiplier U (-p.1)) - 1)
    (hmodel : ∀ v : ℂ, v.re < 0 →
      preparedModelTime U H e₁ e₂ 0 v =
        Kneser.ParabolicFatouCoordinate.model v + polynomialCorrection e₁ e₂ 0 v) :
    ∃ R₀ : ℝ, 32 ≤ R₀ ∧ ∀ u : ℂ, R₀ + 2 ≤ (inverseCoordinate u).re →
      actualPreparedCoordinate U H e₁ e₂ A B Γ u 0 =
        Kneser.correctedCoordinate parabolicMap Kneser.ParabolicFatouCoordinate.model
          (Kneser.coordinateDefect parabolicMap Kneser.ParabolicFatouCoordinate.model) u := by
  obtain ⟨R₁, hR₁, hpreparedZero⟩ := exists_prepared_parabolic_abel U H e₁ e₂ A B F Γ
    hU hU0 hH hHne hHlog he₁ he₂ hA hB hA0 hB0 hΓ hEven hcofactor hprepared hresidue
  obtain ⟨R₂, C, hR₂, _hC, hcanonical⟩ :=
    Kneser.ParabolicFatouCoordinate.exists_attracting_fatou_coordinate
  refine ⟨max R₁ R₂, hR₁.trans (le_max_left _ _), ?_⟩
  intro u hu
  have hu₁ : R₁ + 2 ≤ (inverseCoordinate u).re := by
    have h := le_max_left R₁ R₂
    linarith
  have hu₂ : R₂ ≤ (inverseCoordinate u).re := by
    have h := le_max_right R₁ R₂
    linarith
  exact prepared_eq_canonical_of_model_and_limits U H e₁ e₂ A B Γ u (hR₂.trans hu₂)
    hmodel (hpreparedZero u hu₁).2.2.2 (hcanonical u hu₂).2.2.2

/-- The actual root and logarithmic germs derive the model decomposition,
so canonical identification is a conclusion rather than an input. -/
theorem exists_prepared_canonical_at_zero (U H e₁ e₂ A B : ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hUd : deriv U 0 ≠ 0)
    (hroots : ∀ᶠ x in 𝓝 (0 : ℂ), unfolding (x ^ 2) (U x) = U x)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (hHlog : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (he₁ : AnalyticAt ℂ e₁ 0) (he₂ : AnalyticAt ℂ e₂ 0)
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    (hΓ : AnalyticAt ℂ Γ 0) (hEven : ∀ x v, Γ (-x, v) = Γ (x, v))
    (hcofactor : ∀ᶠ x in 𝓝 (0 : ℂ), ∀ u,
      unfolding (x ^ 2) u - u = rootProduct U x u * symmetricCofactor U x u)
    (hprepared : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ),
      F p + polynomialCorrection e₁ e₂ (p.1 ^ 2) (unfolding (p.1 ^ 2) p.2) -
        polynomialCorrection e₁ e₂ (p.1 ^ 2) p.2 =
        rootPolynomial A B (p.1 ^ 2) p.2 ^ 2 * Γ p)
    (hresidue : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ), p.1 ≠ 0 → F p =
      Complex.log (1 + (p.2 - U (-p.1)) * symmetricCofactor U p.1 p.2) /
        Complex.log (rootMultiplier U p.1) +
      Complex.log (1 + (p.2 - U p.1) * symmetricCofactor U p.1 p.2) /
        Complex.log (rootMultiplier U (-p.1)) - 1) :
    ∃ R₀ : ℝ, 32 ≤ R₀ ∧ ∀ u : ℂ, R₀ + 2 ≤ (inverseCoordinate u).re →
      actualPreparedCoordinate U H e₁ e₂ A B Γ u 0 =
        Kneser.correctedCoordinate parabolicMap Kneser.ParabolicFatouCoordinate.model
          (Kneser.coordinateDefect parabolicMap Kneser.ParabolicFatouCoordinate.model) u := by
  exact exists_prepared_canonical_at_zero_of_model U H e₁ e₂ A B F Γ
    hU hU0 hH hHne hHlog he₁ he₂ hA hB hA0 hB0 hΓ hEven hcofactor hprepared hresidue
    (Kneser.PreparedModelAtZero.preparedModelTime_zero_eq_model U H e₁ e₂
      hU hU0 hUd hroots hH hHlog)

/-- All actual preparation witnesses are constructed together with the
proved canonical coordinate identification at `s=0`. -/
theorem exists_actual_prepared_canonical_at_zero :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      AnalyticAt ℂ U 0 ∧ U 0 = 0 ∧ deriv U 0 ≠ 0 ∧
      AnalyticAt ℂ H 0 ∧ H 0 ≠ 0 ∧
      (∀ x, Complex.log (rootMultiplier U x) = x * H x) ∧
      AnalyticAt ℂ A 0 ∧ AnalyticAt ℂ B 0 ∧ A 0 = 0 ∧ B 0 = 0 ∧
      AnalyticAt ℂ e₁ 0 ∧ AnalyticAt ℂ e₂ 0 ∧
      AnalyticAt ℂ F 0 ∧ AnalyticAt ℂ Γ 0 ∧
      (∀ p : ℂ × ℂ, Γ (-p.1, p.2) = Γ p) ∧
      K 0 0 = 1 / 2 ∧ ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0 ∧
      (∀ x u, rootPolynomial A B (x ^ 2) u = (u - U x) * (u - U (-x))) ∧
      (∀ᶠ x in 𝓝 (0 : ℂ), unfolding (x ^ 2) (U x) = U x ∧
        unfolding (x ^ 2) (U (-x)) = U (-x)) ∧
      (∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
        unfolding s u - u = rootPolynomial A B s u * K s u) ∧
      (∀ᶠ p in 𝓝 (0 : ℂ × ℂ),
        F p + polynomialCorrection e₁ e₂ (p.1 ^ 2) (unfolding (p.1 ^ 2) p.2) -
          polynomialCorrection e₁ e₂ (p.1 ^ 2) p.2 =
          rootPolynomial A B (p.1 ^ 2) p.2 ^ 2 * Γ p) ∧
      (∀ᶠ p in 𝓝 (0 : ℂ × ℂ), p.1 ≠ 0 → F p =
        Complex.log (1 + (p.2 - U (-p.1)) * symmetricCofactor U p.1 p.2) /
          Complex.log (rootMultiplier U p.1) +
        Complex.log (1 + (p.2 - U p.1) * symmetricCofactor U p.1 p.2) /
          Complex.log (rootMultiplier U (-p.1)) - 1) ∧
      ∃ R₀ : ℝ, 32 ≤ R₀ ∧ ∀ u : ℂ, R₀ + 2 ≤ (inverseCoordinate u).re →
        actualPreparedCoordinate U H e₁ e₂ A B Γ u 0 =
          Kneser.correctedCoordinate parabolicMap Kneser.ParabolicFatouCoordinate.model
            (Kneser.coordinateDefect parabolicMap Kneser.ParabolicFatouCoordinate.model) u := by
  obtain ⟨U, H, e₁, e₂, A, B, K, F, Γ, hU, hU0, hUd, hH, hHne, hHlog,
      hA, hB, hA0, hB0, he₁, he₂, hF, hΓ, hΓeven, hK0, hK, hq, hroots,
      hfactor, hprepared, hresidue, _hparabolic⟩ := exists_actual_prepared_parabolic_abel
  have hcofactor : ∀ᶠ x in 𝓝 (0 : ℂ), ∀ u,
      unfolding (x ^ 2) u - u = rootProduct U x u * symmetricCofactor U x u :=
    eventually_symmetricCofactor_factor hU hroots (eventually_distinct_roots U hU hUd)
  have hEven : ∀ x v, Γ (-x, v) = Γ (x, v) := fun x v => hΓeven (x, v)
  have hcanonical := exists_prepared_canonical_at_zero U H e₁ e₂ A B F Γ
    hU hU0 hUd (hroots.mono fun _ h => h.1) hH hHne hHlog he₁ he₂ hA hB hA0 hB0 hΓ hEven
    hcofactor hprepared hresidue
  exact ⟨U, H, e₁, e₂, A, B, K, F, Γ, hU, hU0, hUd, hH, hHne, hHlog,
    hA, hB, hA0, hB0, he₁, he₂, hF, hΓ, hΓeven, hK0, hK, hq, hroots,
    hfactor, hprepared, hresidue, hcanonical⟩

end Kneser.PreparedCanonicalAtZero

end
