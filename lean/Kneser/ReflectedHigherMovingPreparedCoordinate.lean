import Kneser.HigherMovingPreparedCoordinate

/-! All-order compact uniform expansions after actual reflected finite
transport. Every inverse residual is evaluated at iterate k+1, and the
parameter-dependent initial point is included in all Taylor coefficients. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Kneser.ReflectedHigherMovingPreparedCoordinate

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.ExponentialRootPolynomial Kneser.ExponentialPreparedHigher
open Kneser.HigherMovingSeed Kneser.HigherOrderCutoff Kneser.AsymptoticBalance
open Kneser.UniformHigherOrderCutoff
open scoped Topology BigOperators

def shiftedTerm (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ)
    (W : ℂ × ℂ → ℂ) (u s : ℂ) (k : ℕ) : ℂ :=
  ReflectedHigherMovingOrbitDiscs.descendedTerm A B Γ N W u s (k + 1)

def movingCoordinate (U H : ℂ → ℂ) (n : ℕ) (e : Fin (2 * n) → ℂ → ℂ)
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (W : ℂ × ℂ → ℂ) (u : ℂ) (s : ℝ) : ℂ :=
  Kneser.coordinateSeries (fun s : ℝ => ReflectedHigherModelTime.modelTime U H n e s (W (s, u)))
    (fun s : ℝ => shiftedTerm A B Γ (n + 1) W u s) s

def movingCoefficient (U H : ℂ → ℂ) (n : ℕ) (e : Fin (2 * n) → ℂ → ℂ)
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (W : ℂ × ℂ → ℂ) (u : ℂ) (j : ℕ) : ℂ :=
  coordinateCoefficient (fun s => ReflectedHigherModelTime.modelTime U H n e s (W (s, u)))
    (shiftedTerm A B Γ (n + 1) W u) j

theorem movingCoordinate_eq (U H : ℂ → ℂ) (n : ℕ) (e : Fin (2 * n) → ℂ → ℂ)
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (W : ℂ × ℂ → ℂ) (u : ℂ) (s : ℝ) :
    movingCoordinate U H n e A B Γ W u s =
      ReflectedHigherPreparedCoordinate.preparedSeries U H n e A B Γ (W (s, u)) s := by
  simp only [movingCoordinate, ReflectedHigherPreparedCoordinate.preparedSeries,
    Kneser.coordinateSeries, shiftedTerm, ReflectedHigherPreparedCoordinate.shiftedTerm,
    ReflectedHigherMovingOrbitDiscs.descendedTerm_eq]

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
        (shiftedTerm A B Γ (n + 1) W u) j k‖)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
        ‖movingCoordinate U H n e A B Γ W u s -
          ∑ j ∈ Finset.range (m + 1), (s : ℂ) ^ j *
            movingCoefficient U H n e A B Γ W u j‖ ≤
          C * s ^ ((m : ℝ) + gamma m (n + 1)) := by
  obtain ⟨R₁, hR₁, hdiscs⟩ := ReflectedHigherMovingOrbitDiscs.exists_moving_orbit_disc_bounds
    A B Γ (n + 1) hA hB hA0 hB0 hΓ hEven
  obtain ⟨R₂, CT, hR₂, hCT, hreal⟩ :=
    ReflectedPreparedRealMajorant.exists_actual_prepared_real_majorant A B K
      (ReflectedEvenOrbitDiscs.descendedFactor Γ) (n + 1) hK hK0 hfactor
      (ReflectedEvenOrbitDiscs.continuousAt_descendedFactor Γ hΓ.continuousAt)
  let R₀ : ℝ := max R₁ R₂
  have hR₀ : 0 < R₀ := hR₁.trans_le (le_max_left _ _)
  refine ⟨R₀, hR₀, ?_⟩
  intro W S hS hW hdeep
  obtain ⟨c, M, hc, hM, hdisc₀, hbound₀⟩ := hdiscs W S hS hW
    (fun u hu => by have hh : R₁ ≤ R₀ := le_max_left _ _; linarith [hdeep u hu])
  have hneg : ∀ u ∈ S, (W (0, u)).re < 0 := by
    intro u hu
    have hh := ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos
      (show 0 < (inverseCoordinate (W (0, u))).re by linarith [hdeep u hu])
    simpa only [Complex.neg_re, neg_pos] using hh
  obtain ⟨r, Mψ, hr, hMψ, hmodel⟩ :=
    HigherMovingPreparedCoordinate.exists_moving_model_disc_bounds (-U) (-H) n
      (ReflectedHigherModelTime.reflectedCorrection n e) hU.neg (by simpa using hU0)
      hH.neg (by simpa using hHne) (ReflectedHigherModelTime.reflectedCorrection_analytic n e he)
      W S hS hW hneg
  have hdisc : ∀ u ∈ S, ∀ k, DiffContOnCl ℂ (fun z => shiftedTerm A B Γ (n + 1) W u z k)
      (ball 0 ((c / 4) / ((k : ℝ) + 1) ^ 2)) := by
    intro u hu
    exact (ReflectedHigherPreparedCoordinate.shifted_disc_bounds
      (ReflectedHigherMovingOrbitDiscs.descendedTerm A B Γ (n + 1) W u)
      c M (n + 1) hc hM (hdisc₀ u hu) (hbound₀ u hu)).1
  have hbound : ∀ u ∈ S, ∀ (k : ℕ) (z : ℂ), ‖z‖ ≤ (c / 4) / ((k : ℝ) + 1) ^ 2 →
      ‖shiftedTerm A B Γ (n + 1) W u z k‖ ≤ M / ((k : ℝ) + 1) ^ (2 * (n + 1)) := by
    intro u hu
    exact (ReflectedHigherPreparedCoordinate.shifted_disc_bounds
      (ReflectedHigherMovingOrbitDiscs.descendedTerm A B Γ (n + 1) W u)
      c M (n + 1) hc hM (hdisc₀ u hu) (hbound₀ u hu)).2
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
      ‖shiftedTerm A B Γ (n + 1) W u (s : ℂ) k‖ ≤
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
    rw [shiftedTerm, ReflectedHigherMovingOrbitDiscs.descendedTerm_eq,
      ReflectedEvenOrbitDiscs.descendedTerm_eq]
    apply (hterms s hs (hss.trans_le (min_le_left _ _)) (W (s, u)) hd.le (hZT _ hwT) (k + 1)).trans
    apply div_le_div_of_nonneg_left hCT (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith) (2 * (n + 1))
  exact coordinate_expansion_uniform_from_bounds S (fun u s => ReflectedHigherModelTime.modelTime U H n e s (W (s, u)))
    (fun u => shiftedTerm A B Γ (n + 1) W u)
    m (n + 1) r Mψ (c / 4) M CT hm hN hr hMψ (by positivity) hM hCT
    (fun u hu => (hmodel u hu).1)
    (fun u hu z hz => (hmodel u hu).2 z (sphere_subset_closedBall hz))
    hdisc hbound hterms'


end Kneser.ReflectedHigherMovingPreparedCoordinate

end
