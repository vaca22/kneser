import Kneser.PreparedDegreeCompatibility

/-! A single actual logarithmic defect admits constructed preparations of
every degree.  Their common spatially normalized coordinate inherits every
finite-order expansion. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Kneser.CommonPreparedFamily

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.ExponentialRootPolynomial Kneser.EvenPreparedOrbitDiscs
open Kneser.ExponentialPreparedHigher Kneser.HigherPreparedModelTime
open Kneser.ExponentialPreparedQuadratic
open Kneser.ActualHigherPreparedCoordinate Kneser.PreparedDegreeCompatibility
open Kneser.ExponentialLogDefect Kneser.ExponentialPreparedModel
open Kneser.ExponentialMatrixDividedDifference Kneser.PreparedTwoRootDivision
open Kneser.ActualCorrectionDirections Kneser.HigherOrderCutoff Kneser.AsymptoticBalance
open scoped Topology BigOperators

def Prepared (A B : ℂ → ℂ) (F : ℂ × ℂ → ℂ) (n : ℕ)
    (e : Fin (2 * n) → ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) : Prop :=
  (∀ i, AnalyticAt ℂ (e i) 0) ∧ AnalyticAt ℂ Γ 0 ∧
  (∀ p : ℂ × ℂ, Γ (-p.1, p.2) = Γ p) ∧
  (∀ᶠ p in 𝓝 (0 : ℂ × ℂ),
    F p + correction n e (p.1 ^ 2) (unfolding (p.1 ^ 2) p.2) -
      correction n e (p.1 ^ 2) p.2 = rootPolynomial A B (p.1 ^ 2) p.2 ^ (n + 1) * Γ p)

theorem exists_preparation_of_fixed_defect {U A B : ℂ → ℂ} {F φ : ℂ × ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0) (hUd : deriv U 0 ≠ 0)
    (hroots : ∀ᶠ x in 𝓝 0,
      unfolding (x ^ 2) (U x) = U x ∧ unfolding (x ^ 2) (U (-x)) = U (-x))
    (hdistinct : ∀ᶠ x in 𝓝 0, U x = U (-x) ↔ x = 0)
    (hq : ∀ x u, rootPolynomial A B (x ^ 2) u = rootProduct U x u)
    (hφ : AnalyticAt ℂ φ 0) (hφeven : ∀ p, φ (reflectFirst p) = φ p)
    (hFfactor : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ), F p = rootProduct U p.1 p.2 * φ p)
    (n : ℕ) : ∃ e Γ, Prepared A B F n e Γ := by
  have hK0 := symmetricCofactor_zero hU hU0 hroots hdistinct
  obtain ⟨e, Γ, he, hΓ, hΓeven, hprepared⟩ :=
    exists_correction_to_power hU hU0 hUd hdistinct hK0 hφ hφeven n
  refine ⟨e, Γ, he, hΓ, hΓeven, ?_⟩
  have hfst : Tendsto (fun p : ℂ × ℂ => p.1) (𝓝 0) (𝓝 (0 : ℂ)) := continuous_fst.tendsto 0
  have hfactor := eventually_symmetricCofactor_factor hU hroots hdistinct
  filter_upwards [hFfactor, hprepared, hfst.eventually hfactor] with p hFp hprep hfac
  have hP := correction_difference U n e p.1 p.2 (hfac p.2)
  rw [hFp]
  have hleft : rootProduct U p.1 p.2 * φ p +
      correction n e (p.1 ^ 2) (unfolding (p.1 ^ 2) p.2) - correction n e (p.1 ^ 2) p.2 =
      rootProduct U p.1 p.2 *
        (φ p + ∑ i : Fin (2 * n), e i (p.1 ^ 2) * direction U i.val p) := by
    linear_combination hP
  rw [hleft, hprep, hq, pow_succ]
  ring

/-- One actual root polynomial and one actual paired logarithmic defect
serve all finite correction orders simultaneously. -/
theorem exists_actual_common_preparations :
    ∃ U H A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F : ℂ × ℂ → ℂ,
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
      ∀ n, ∃ e Γ, Prepared A B F n e Γ := by
  obtain ⟨U, A, B, hU, hU0, hUd, hA, hB, hA0, hB0, _hAsum, _hBprod, hq,
    hroots, hdistinct⟩ := ExponentialRootPolynomial.exists_analytic_rootPolynomial
  obtain ⟨H, hH, hH0, hHlog⟩ := exists_log_multiplier_factor hU hU0
  have hHne : H 0 ≠ 0 := hH0 ▸ hUd
  obtain ⟨F, φ, hF, hφ, _hFeven, hφeven, hFfactor, hresidue⟩ :=
    exists_analytic_log_defect hU hU0 hUd hroots hdistinct
  refine ⟨U, H, A, B, descendedCofactor U, F, hU, hU0, hUd, hH, hHne, hHlog,
    hA, hB, hA0, hB0, ?_, continuousAt_descendedCofactor hU 0, hF, hq, hroots,
    ?_, hresidue, ?_⟩
  · simpa only [descendedCofactor, Complex.sqrt_zero] using
      symmetricCofactor_zero hU hU0 hroots hdistinct
  · have hsqrt : Tendsto Complex.sqrt (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
      simpa only [Complex.sqrt_zero] using
        (Complex.continuousAt_sqrt (Or.inl (by simp : (0 : ℝ) ≤ (0 : ℂ).re))).tendsto
    filter_upwards [hsqrt.eventually (eventually_symmetricCofactor_factor hU hroots hdistinct)] with s hs u
    have hf := hs u
    rw [← hq (Complex.sqrt s) u, AnalyticEvenDescent.square_sqrt] at hf
    exact hf
  · intro n
    exact exists_preparation_of_fixed_defect hU hU0 hUd hroots hdistinct hq hφ hφeven hFfactor n

def familyCoefficient (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (n j : ℕ) (u : ℂ) : ℂ :=
  coordinateCoefficient (fun s => modelTime U H n (e n) s u)
    (descendedTerm A B (Γ n) (n + 1) u) j

def normalizedCoordinate (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (u v : ℂ) (s : ℝ) : ℂ :=
  preparedSeries U H 1 (e 1) A B (Γ 1) u s - preparedSeries U H 1 (e 1) A B (Γ 1) v s

def normalizedPolynomial (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (n m : ℕ) (u v : ℂ) (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (m + 1), s ^ j *
    (familyCoefficient U H A B e Γ n j u - familyCoefficient U H A B e Γ n j v)

theorem normalizedPolynomial_eq_difference (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (n m : ℕ) (u v s : ℂ) :
    normalizedPolynomial U H A B e Γ n m u v s =
      coordinatePolynomial (fun s => modelTime U H n (e n) s u)
        (descendedTerm A B (Γ n) (n + 1) u) m s -
      coordinatePolynomial (fun s => modelTime U H n (e n) s v)
        (descendedTerm A B (Γ n) (n + 1) v) m s := by
  simp only [normalizedPolynomial, coordinatePolynomial, familyCoefficient, mul_sub,
    Finset.sum_sub_distrib]

def AllFiniteExpansions (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ n : ℕ, m * m + m + 1 ≤ n + 1 →
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ u v : ℂ,
      R₀ + 1 ≤ (inverseCoordinate u).re → R₀ + 1 ≤ (inverseCoordinate v).re →
        (∀ j ≤ m, Summable (fun k => ‖termCoefficient
          (descendedTerm A B (Γ n) (n + 1) u) j k‖)) ∧
        (∀ j ≤ m, Summable (fun k => ‖termCoefficient
          (descendedTerm A B (Γ n) (n + 1) v) j k‖)) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
          ‖normalizedCoordinate U H A B e Γ u v s -
            normalizedPolynomial U H A B e Γ n m u v s‖ ≤
              C * s ^ ((m : ℝ) + gamma m (n + 1))

/-- A common actual defect and every constructed correction suffice to
transfer every higher expansion to one and the same normalized baseline. -/
theorem allFiniteExpansions_of_common_preparations
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    (hK : ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0) (hK0 : K 0 0 ≠ 0)
    (hfactor : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
      unfolding s u - u = rootPolynomial A B s u * K s u)
    (hprepared : ∀ n, Prepared A B F n (e n) (Γ n)) :
    AllFiniteExpansions U H A B e Γ := by
  intro m hm n hN
  obtain ⟨he, hΓ, hΓeven, hprep⟩ := hprepared n
  obtain ⟨_hebase, hΓbase, _hΓbaseeven, hprepbase⟩ := hprepared 1
  obtain ⟨Rexp, hRexp, hexp⟩ := prepared_higher_expansion A B K (Γ n)
    hA hB hA0 hB0 hΓ (fun x u => hΓeven (x, u)) hK hK0 hfactor m (n + 1) hm hN
  obtain ⟨Rcomp, hRcomp, hcomp⟩ := exists_actual_normalized_compatibility U H A B K
    F (Γ n) (Γ 1) n 1 (e n) (e 1) hK hK0 hfactor hΓ hΓbase hprep hprepbase
  let R₀ : ℝ := max Rexp Rcomp
  have hR₀ : 0 < R₀ := hRexp.trans_le (le_max_left _ _)
  refine ⟨R₀, hR₀, ?_⟩
  intro u v hu hv
  have huExp : Rexp + 1 ≤ (inverseCoordinate u).re := by
    have hh : Rexp ≤ R₀ := le_max_left _ _
    linarith
  have hvExp : Rexp + 1 ≤ (inverseCoordinate v).re := by
    have hh : Rexp ≤ R₀ := le_max_left _ _
    linarith
  have huRe : u.re < 0 := by
    have hh := ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos
      (show 0 < (inverseCoordinate u).re by linarith)
    simpa only [Complex.neg_re, neg_pos] using hh
  have hvRe : v.re < 0 := by
    have hh := ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos
      (show 0 < (inverseCoordinate v).re by linarith)
    simpa only [Complex.neg_re, neg_pos] using hh
  obtain ⟨huSum, Cu, hCu, huRem⟩ := hexp u huExp
    (fun s => modelTime U H n (e n) s u)
    (analyticAt_modelTime_parameter n (e n) hU hU0 hH hHne he u huRe)
  obtain ⟨hvSum, Cv, hCv, hvRem⟩ := hexp v hvExp
    (fun s => modelTime U H n (e n) s v)
    (analyticAt_modelTime_parameter n (e n) hU hU0 hH hHne he v hvRe)
  let Z : ℝ := max ‖inverseCoordinate u‖ ‖inverseCoordinate v‖
  have hZ : 0 ≤ Z := (norm_nonneg _).trans (le_max_left _ _)
  have hcompat := hcomp R₀ (le_max_right _ _) Z hZ
  refine ⟨huSum, hvSum, Cu + Cv, add_nonneg hCu hCv, ?_⟩
  filter_upwards [huRem, hvRem, hcompat] with s hus hvs hcs
  have heq := hcs u v hu (le_max_left _ _) hv (le_max_right _ _)
  change preparedSeries U H n (e n) A B (Γ n) u s -
      preparedSeries U H n (e n) A B (Γ n) v s =
        normalizedCoordinate U H A B e Γ u v s at heq
  rw [← heq, normalizedPolynomial_eq_difference]
  have hr :
      preparedSeries U H n (e n) A B (Γ n) u s -
          preparedSeries U H n (e n) A B (Γ n) v s -
        (coordinatePolynomial (fun s => modelTime U H n (e n) s u)
            (descendedTerm A B (Γ n) (n + 1) u) m s -
          coordinatePolynomial (fun s => modelTime U H n (e n) s v)
            (descendedTerm A B (Γ n) (n + 1) v) m s) =
      (preparedSeries U H n (e n) A B (Γ n) u s -
        coordinatePolynomial (fun s => modelTime U H n (e n) s u)
          (descendedTerm A B (Γ n) (n + 1) u) m s) -
      (preparedSeries U H n (e n) A B (Γ n) v s -
        coordinatePolynomial (fun s => modelTime U H n (e n) s v)
          (descendedTerm A B (Γ n) (n + 1) v) m s) := by ring
  rw [hr]
  exact (norm_sub_le _ _).trans ((add_le_add hus hvs).trans_eq (by ring))

/-- Unconditional existence of one actual normalized attracting coordinate
family with all finite-degree expansions and absolutely convergent orbit
coefficients.  Its local depth may depend on the requested degree. -/
theorem exists_actual_normalized_all_finite_expansions :
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
      AllFiniteExpansions U H A B e Γ := by
  obtain ⟨U, H, A, B, K, F, hU, hU0, hUd, hH, hHne, hHlog,
    hA, hB, hA0, hB0, hK0, hK, hF, hq, hroots, hfactor, hresidue, hfamily⟩ :=
    exists_actual_common_preparations
  choose e Γ hprepared using hfamily
  exact ⟨U, H, A, B, K, F, e, Γ, hU, hU0, hUd, hH, hHne, hHlog,
    hA, hB, hA0, hB0, hK0, hK, hF, hq, hroots, hfactor, hresidue,
    hprepared, allFiniteExpansions_of_common_preparations U H A B K F e Γ
      hU hU0 hH hHne hA hB hA0 hB0 hK (by rw [hK0]; norm_num) hfactor hprepared⟩

end Kneser.CommonPreparedFamily

end
