import Kneser.HigherMovingOrbitDiscs
import Kneser.ReflectedHigherMovingOrbitDiscs

/-! Compact uniform all-order expansions after a genuine analytic moving
initial point. In particular the Taylor coefficients differentiate both the
parameter and the finite orbit transport. Neither moving term holomorphy
nor an infinite real-tail estimate is an input of the final theorem. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Kneser.HigherMovingPreparedCoordinate

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.ExponentialRootPolynomial Kneser.ExponentialPreparedHigher
open Kneser.HigherPreparedModelTime Kneser.HigherMovingSeed
open Kneser.HigherOrderCutoff Kneser.AsymptoticBalance Kneser.UniformHigherOrderCutoff
open scoped Topology BigOperators

theorem exists_moving_model_disc_bounds
    (U H : ℂ → ℂ) (n : ℕ) (e : Fin (2 * n) → ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0) (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (he : ∀ i, AnalyticAt ℂ (e i) 0)
    (W : ℂ × ℂ → ℂ) (S : Set ℂ) (hS : IsCompact S)
    (hW : ∀ u ∈ S, AnalyticAt ℂ W (0, u))
    (hneg : ∀ u ∈ S, (W (0, u)).re < 0) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧ ∀ u ∈ S,
      DiffContOnCl ℂ (fun s => modelTime U H n e s (W (s, u))) (ball 0 r) ∧
      (∀ s ∈ closedBall (0 : ℂ) r, ‖modelTime U H n e s (W (s, u))‖ ≤ M) := by
  let Q : ℂ × ℂ → ℂ := fun p => splitModelTime U H n e (p.1, W (p.1 ^ 2, p.2))
  have hQa : ∀ u ∈ S, AnalyticAt ℂ Q (0, u) := by
    intro u hu
    have hw : AnalyticAt ℂ (fun p : ℂ × ℂ => W (p.1 ^ 2, p.2)) (0, u) :=
      (hW u hu).comp_of_eq ((analyticAt_fst.pow 2).prod analyticAt_snd) (by simp)
    exact (analyticAt_splitModelTime n e hU hU0 hH hHne he (W (0, u)) (hneg u hu)).comp_of_eq
      (analyticAt_fst.prod hw) (by simp)
  have hEven : ∀ x u, Q (-x, u) = Q (x, u) := by
    intro x u
    dsimp [Q]
    rw [neg_sq, splitModelTime_even]
  obtain ⟨r, M, hr, hM, hdisc⟩ := exists_compact_even_disc_bounds Q S hS hQa hEven
  refine ⟨r, M, hr, hM, ?_⟩
  intro u hu
  simpa only [Q, AnalyticEvenDescent.square_sqrt, splitModelTime_sqrt] using hdisc u hu

def movingCoordinate (U H : ℂ → ℂ) (n : ℕ) (e : Fin (2 * n) → ℂ → ℂ)
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (W : ℂ × ℂ → ℂ) (u : ℂ) (s : ℝ) : ℂ :=
  Kneser.coordinateSeries (fun s : ℝ => modelTime U H n e s (W (s, u)))
    (fun s : ℝ => HigherMovingOrbitDiscs.descendedTerm A B Γ (n + 1) W u s) s

def movingCoefficient (U H : ℂ → ℂ) (n : ℕ) (e : Fin (2 * n) → ℂ → ℂ)
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (W : ℂ × ℂ → ℂ) (u : ℂ) (j : ℕ) : ℂ :=
  coordinateCoefficient (fun s => modelTime U H n e s (W (s, u)))
    (HigherMovingOrbitDiscs.descendedTerm A B Γ (n + 1) W u) j

theorem movingCoordinate_eq (U H : ℂ → ℂ) (n : ℕ) (e : Fin (2 * n) → ℂ → ℂ)
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (W : ℂ × ℂ → ℂ) (u : ℂ) (s : ℝ) :
    movingCoordinate U H n e A B Γ W u s =
      PreparedDegreeCompatibility.preparedSeries U H n e A B Γ (W (s, u)) s := by
  simp only [movingCoordinate, PreparedDegreeCompatibility.preparedSeries,
    Kneser.coordinateSeries, HigherMovingOrbitDiscs.descendedTerm_eq]

theorem exists_moving_higher_expansion
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
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ W : ℂ × ℂ → ℂ, ∀ S : Set ℂ, IsCompact S →
      (∀ u ∈ S, AnalyticAt ℂ W (0, u)) →
      (∀ u ∈ S, R₀ + 2 ≤ (inverseCoordinate (W (0, u))).re) →
      (∀ u ∈ S, ∀ j ≤ m, Summable (fun k => ‖termCoefficient
        (HigherMovingOrbitDiscs.descendedTerm A B Γ (n + 1) W u) j k‖)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
        ‖movingCoordinate U H n e A B Γ W u s -
          ∑ j ∈ Finset.range (m + 1), (s : ℂ) ^ j *
            movingCoefficient U H n e A B Γ W u j‖ ≤
          C * s ^ ((m : ℝ) + gamma m (n + 1)) := by
  obtain ⟨R₁, hR₁, hdiscs⟩ := HigherMovingOrbitDiscs.exists_moving_orbit_disc_bounds
    A B Γ (n + 1) hA hB hA0 hB0 hΓ hEven
  obtain ⟨R₂, CT, hR₂, hCT, hreal⟩ :=
    ActualRootPolynomialOrbit.exists_actual_prepared_real_majorant A B K
      (EvenPreparedOrbitDiscs.descendedFactor Γ) (n + 1) hK hK0 hfactor
      (EvenPreparedOrbitDiscs.continuousAt_descendedFactor Γ hΓ.continuousAt)
  let R₀ : ℝ := max R₁ R₂
  have hR₀ : 0 < R₀ := hR₁.trans_le (le_max_left _ _)
  refine ⟨R₀, hR₀, ?_⟩
  intro W S hS hW hdeep
  obtain ⟨c, M, hc, hM, hdisc, hbound⟩ := hdiscs W S hS hW
    (fun u hu => by have hh : R₁ ≤ R₀ := le_max_left _ _; linarith [hdeep u hu])
  have hneg : ∀ u ∈ S, (W (0, u)).re < 0 := by
    intro u hu
    have hh := ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos
      (show 0 < (inverseCoordinate (W (0, u))).re by linarith [hdeep u hu])
    simpa only [Complex.neg_re, neg_pos] using hh
  obtain ⟨r, Mψ, hr, hMψ, hmodel⟩ :=
    exists_moving_model_disc_bounds U H n e hU hU0 hH hHne he W S hS hW hneg
  obtain ⟨rW, T, hrW, hT, hTV, hWT⟩ := exists_compact_complex_image_neighborhood
    W S (ParabolicFatouHolomorphic.petal (R₀ + 1)) hS
      (ParabolicFatouHolomorphic.petal_isOpen (by positivity)) hW
      (fun u hu => by change R₀ + 1 < _; linarith [hdeep u hu])
  have hne : ∀ v ∈ T, v ≠ 0 := by
    intro v hv heq
    have hh := hTV hv
    change R₀ + 1 < (inverseCoordinate v).re at hh
    simp only [heq, inverseCoordinate, div_zero, Complex.zero_re] at hh
    linarith
  have hi : ContinuousOn inverseCoordinate T := by
    intro v hv; exact (continuousAt_const.div continuousAt_id (hne v hv)).continuousWithinAt
  obtain ⟨Z₁, hZ₁⟩ := hT.exists_bound_of_continuousOn hi
  let Z : ℝ := max Z₁ 0
  have hZ : 0 ≤ Z := le_max_right _ _
  have hZT : ∀ v ∈ T, ‖inverseCoordinate v‖ ≤ Z :=
    fun v hv => (hZ₁ v hv).trans (le_max_left _ _)
  obtain ⟨s₀, hs₀, hterms⟩ := hreal R₀ (le_max_right _ _) Z hZ
  have hterms' : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S, ∀ k,
      ‖HigherMovingOrbitDiscs.descendedTerm A B Γ (n + 1) W u (s : ℂ) k‖ ≤
        CT / ((k : ℝ) + 1) ^ (2 * (n + 1)) := by
    have hs₀' : ∀ᶠ s : ℝ in 𝓝[>] 0, s < min s₀ rW :=
      (eventually_lt_nhds (lt_min hs₀ hrW)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hs₀'] with s hs hss u hu k
    have hspos : 0 < s := hs
    have hwT := (hWT (s : ℂ) (by
      simp only [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hspos]
      exact (hss.trans_le (min_le_right _ _)).le) u hu).2
    have hd := hTV hwT
    change R₀ + 1 < _ at hd
    rw [HigherMovingOrbitDiscs.descendedTerm_eq, EvenPreparedOrbitDiscs.descendedTerm_eq]
    exact hterms s hs (hss.trans_le (min_le_left _ _)) (W (s, u)) hd.le (hZT _ hwT) k
  exact coordinate_expansion_uniform_from_bounds S (fun u s => modelTime U H n e s (W (s, u)))
    (fun u => HigherMovingOrbitDiscs.descendedTerm A B Γ (n + 1) W u)
    m (n + 1) r Mψ c M CT hm hN hr hMψ hc hM hCT
    (fun u hu => (hmodel u hu).1)
    (fun u hu z hz => (hmodel u hu).2 z (sphere_subset_closedBall hz))
    hdisc hbound hterms'

end Kneser.HigherMovingPreparedCoordinate

end
