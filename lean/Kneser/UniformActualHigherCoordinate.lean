import Kneser.CommonPreparedFamily
import Kneser.UniformHigherOrderCutoff

/-! Compact uniform all-order expansions of one spatially normalized
actual attracting prepared coordinate.  The depth of the local petal may
depend on the requested order; no transport to a fixed outer gate is claimed. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Kneser.UniformActualHigherCoordinate

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.ExponentialRootPolynomial Kneser.EvenPreparedOrbitDiscs
open Kneser.ExponentialPreparedHigher Kneser.HigherPreparedModelTime
open Kneser.ActualHigherPreparedCoordinate Kneser.PreparedDegreeCompatibility
open Kneser.CommonPreparedFamily Kneser.HigherOrderCutoff Kneser.AsymptoticBalance
open Kneser.UniformHigherOrderCutoff Kneser.ExponentialPreparedModel
open Kneser.ExponentialMatrixDividedDifference Kneser.ExponentialPreparedQuadratic
open scoped Topology BigOperators

theorem prepared_model_compact_higher_expansion
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (n : ℕ) (e : Fin (2 * n) → ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0) (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (he : ∀ i, AnalyticAt ℂ (e i) 0)
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    (hΓ : AnalyticAt ℂ Γ 0) (hEven : ∀ x v, Γ (-x, v) = Γ (x, v))
    (hK : ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0) (hK0 : K 0 0 ≠ 0)
    (hfactor : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
      unfolding s u - u = rootPolynomial A B s u * K s u)
    (m : ℕ) (hm : 1 ≤ m) (hN : m * m + m + 1 ≤ n + 1) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ S : Set ℂ, IsCompact S →
      (∀ u ∈ S, R₀ + 1 ≤ (inverseCoordinate u).re) →
      (∀ u ∈ S, ∀ j ≤ m, Summable (fun k =>
        ‖termCoefficient (descendedTerm A B Γ (n + 1) u) j k‖)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
        ‖preparedSeries U H n e A B Γ u s -
          coordinatePolynomial (fun s => modelTime U H n e s u)
            (descendedTerm A B Γ (n + 1) u) m s‖ ≤ C * s ^ ((m : ℝ) + gamma m (n + 1)) := by
  obtain ⟨R₁, hR₁, hdiscs⟩ := exists_uniform_prepared_orbit_disc_bounds A B Γ (n + 1)
    hA hB hA0 hB0 hΓ hEven
  obtain ⟨R₂, CT, hR₂, hCT, hreal⟩ :=
    ActualRootPolynomialOrbit.exists_actual_prepared_real_majorant A B K
      (descendedFactor Γ) (n + 1) hK hK0 hfactor
      (continuousAt_descendedFactor Γ hΓ.continuousAt)
  let R₀ : ℝ := max R₁ R₂
  have hR₀ : 0 < R₀ := hR₁.trans_le (le_max_left _ _)
  refine ⟨R₀, hR₀, ?_⟩
  intro S hS hpetal
  have hune : ∀ u ∈ S, u ≠ 0 := by
    intro u hu heq
    have hh := hpetal u hu
    simp only [heq, inverseCoordinate, div_zero, Complex.zero_re] at hh
    linarith
  have hi : ContinuousOn inverseCoordinate S := by
    intro u hu
    exact (continuousAt_const.div continuousAt_id (hune u hu)).continuousWithinAt
  obtain ⟨Z₁, hZ₁⟩ := hS.exists_bound_of_continuousOn hi
  let Z : ℝ := max Z₁ 0
  have hZ : 0 ≤ Z := le_max_right _ _
  have hZu : ∀ u ∈ S, ‖inverseCoordinate u‖ ≤ Z :=
    fun u hu => (hZ₁ u hu).trans (le_max_left _ _)
  have hneg : ∀ u ∈ S, u.re < 0 := by
    intro u hu
    have hh := ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos
      (show 0 < (inverseCoordinate u).re by linarith [hpetal u hu])
    simpa only [Complex.neg_re, neg_pos] using hh
  obtain ⟨r, Mψ, hr, hMψ, hmodel⟩ :=
    exists_compact_modelTime_disc_bounds n e hU hU0 hH hHne he S hS hneg
  obtain ⟨c, M, hc, hM, hcommon⟩ := hdiscs R₀ (le_max_left _ _) Z hZ
  have hcommonS : ∀ u ∈ S,
      (∀ k, DiffContOnCl ℂ (fun s => descendedTerm A B Γ (n + 1) u s k)
        (ball 0 (c / ((k : ℝ) + 1) ^ 2))) ∧
      (∀ (k : ℕ) (s : ℂ), ‖s‖ ≤ c / ((k : ℝ) + 1) ^ 2 →
        ‖descendedTerm A B Γ (n + 1) u s k‖ ≤ M / ((k : ℝ) + 1) ^ (2 * (n + 1))) := by
    intro u hu
    exact hcommon u (by linarith [hpetal u hu]) (hZu u hu)
  obtain ⟨s₀, hs₀, hterms⟩ := hreal R₀ (le_max_right _ _) Z hZ
  have htermS : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S, ∀ k,
      ‖descendedTerm A B Γ (n + 1) u s k‖ ≤ CT / ((k : ℝ) + 1) ^ (2 * (n + 1)) := by
    have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < s₀ :=
      (eventually_lt_nhds hs₀).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with s hs hss u hu k
    simpa only [descendedTerm_eq] using hterms s hs hss u (hpetal u hu) (hZu u hu) k
  exact coordinate_expansion_uniform_from_bounds S (fun u s => modelTime U H n e s u)
    (fun u => descendedTerm A B Γ (n + 1) u) m (n + 1) r Mψ c M CT
    hm hN hr hMψ hc hM hCT (fun u hu => (hmodel u hu).1)
    (fun u hu z hz => (hmodel u hu).2 z (mem_closedBall.mpr (mem_sphere.mp hz).le))
    (fun u hu => (hcommonS u hu).1) (fun u hu => (hcommonS u hu).2) htermS

def CompactAllFiniteExpansions (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ n : ℕ, m * m + m + 1 ≤ n + 1 →
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ S : Set ℂ, IsCompact S →
      (∀ u ∈ S, R₀ + 1 ≤ (inverseCoordinate u).re) →
      (∀ u ∈ S, ∀ j ≤ m, Summable (fun k => ‖termCoefficient
        (descendedTerm A B (Γ n) (n + 1) u) j k‖)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S, ∀ v ∈ S,
        ‖normalizedCoordinate U H A B e Γ u v s -
          normalizedPolynomial U H A B e Γ n m u v s‖ ≤
            C * s ^ ((m : ℝ) + gamma m (n + 1))

/-- One constant and one positive-parameter threshold work for every pair
of initial points in the chosen compact set. -/
theorem compactAllFiniteExpansions_of_common_preparations
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    (hK : ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0) (hK0 : K 0 0 ≠ 0)
    (hfactor : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
      unfolding s u - u = rootPolynomial A B s u * K s u)
    (hprepared : ∀ n, Prepared A B F n (e n) (Γ n)) :
    CompactAllFiniteExpansions U H A B e Γ := by
  intro m hm n hN
  obtain ⟨he, hΓ, hΓeven, hprep⟩ := hprepared n
  obtain ⟨_hebase, hΓbase, _hΓbaseeven, hprepbase⟩ := hprepared 1
  obtain ⟨Rexp, hRexp, hexp⟩ := prepared_model_compact_higher_expansion U H A B K (Γ n)
    n (e n) hU hU0 hH hHne he hA hB hA0 hB0 hΓ (fun x u => hΓeven (x, u))
    hK hK0 hfactor m hm hN
  obtain ⟨Rcomp, hRcomp, hcomp⟩ := exists_actual_normalized_compatibility U H A B K
    F (Γ n) (Γ 1) n 1 (e n) (e 1) hK hK0 hfactor hΓ hΓbase hprep hprepbase
  let R₀ : ℝ := max Rexp Rcomp
  have hR₀ : 0 < R₀ := hRexp.trans_le (le_max_left _ _)
  refine ⟨R₀, hR₀, ?_⟩
  intro S hS hpetal
  have hpetalExp : ∀ u ∈ S, Rexp + 1 ≤ (inverseCoordinate u).re := by
    intro u hu
    have hh : Rexp ≤ R₀ := le_max_left _ _
    linarith [hpetal u hu]
  obtain ⟨hsum, C, hC, hrem⟩ := hexp S hS hpetalExp
  have hune : ∀ u ∈ S, u ≠ 0 := by
    intro u hu heq
    have hh := hpetal u hu
    simp only [heq, inverseCoordinate, div_zero, Complex.zero_re] at hh
    linarith
  have hi : ContinuousOn inverseCoordinate S := by
    intro u hu
    exact (continuousAt_const.div continuousAt_id (hune u hu)).continuousWithinAt
  obtain ⟨Z₁, hZ₁⟩ := hS.exists_bound_of_continuousOn hi
  let Z : ℝ := max Z₁ 0
  have hZ : 0 ≤ Z := le_max_right _ _
  have hZu : ∀ u ∈ S, ‖inverseCoordinate u‖ ≤ Z :=
    fun u hu => (hZ₁ u hu).trans (le_max_left _ _)
  have hcompat := hcomp R₀ (le_max_right _ _) Z hZ
  refine ⟨hsum, 2 * C, by positivity, ?_⟩
  filter_upwards [hrem, hcompat] with s hs hcs u hu v hv
  have heq := hcs u v (hpetal u hu) (hZu u hu) (hpetal v hv) (hZu v hv)
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
  exact (norm_sub_le _ _).trans ((add_le_add (hs u hu) (hs v hv)).trans_eq (by ring))

/-- Actual roots, one actual logarithmic defect, and all polynomial
corrections are constructed; compact uniform higher expansions concern the
same normalized baseline coordinate at every order. -/
theorem exists_actual_normalized_compact_all_orders :
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
      CompactAllFiniteExpansions U H A B e Γ := by
  obtain ⟨U, H, A, B, K, F, hU, hU0, hUd, hH, hHne, hHlog,
    hA, hB, hA0, hB0, hK0, hK, hF, hq, hroots, hfactor, hresidue, hfamily⟩ :=
    exists_actual_common_preparations
  choose e Γ hprepared using hfamily
  exact ⟨U, H, A, B, K, F, e, Γ, hU, hU0, hUd, hH, hHne, hHlog,
    hA, hB, hA0, hB0, hK0, hK, hF, hq, hroots, hfactor, hresidue,
    hprepared, compactAllFiniteExpansions_of_common_preparations U H A B K F e Γ
      hU hU0 hH hHne hA hB hA0 hB0 hK (by rw [hK0]; norm_num) hfactor hprepared⟩

end Kneser.UniformActualHigherCoordinate

end
