import Kneser.PositiveOrbitRootLimit
import Kneser.PreparedLocalAbel

/-! Finite correction differences telescope to their value at the actual
attracting root.  A common spatial normalization cancels this constant. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Kneser.PreparedDegreeCompatibility

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.ExponentialRootPolynomial Kneser.EvenPreparedOrbitDiscs
open Kneser.HigherPreparedModelTime Kneser.ExponentialPreparedHigher
open Kneser.ActualHigherPreparedCoordinate Kneser.PreparedLocalAbel
open scoped Topology BigOperators

def preparedSeries (U H : ℂ → ℂ) (n : ℕ) (e : Fin (2 * n) → ℂ → ℂ)
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (u : ℂ) (s : ℝ) : ℂ :=
  coordinateSeries (fun s : ℝ => modelTime U H n e s u)
    (fun s : ℝ => descendedTerm A B Γ (n + 1) u s) s

theorem residual_difference_telescope
    (term₁ term₂ : ℕ → ℂ) (P : ℂ → ℂ) (w : ℕ → ℂ)
    (hdefect : ∀ k, term₁ k - term₂ k = P (w (k + 1)) - P (w k)) (n : ℕ) :
    ∑ k ∈ Finset.range n, (term₁ k - term₂ k) = P (w n) - P (w 0) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, hdefect]; ring

theorem preparedSeries_difference_of_orbit_limit
    (U H A B : ℂ → ℂ) (n₁ n₂ : ℕ)
    (e₁ : Fin (2 * n₁) → ℂ → ℂ) (e₂ : Fin (2 * n₂) → ℂ → ℂ)
    (Γ₁ Γ₂ : ℂ × ℂ → ℂ) (u : ℂ) (s : ℝ) (a : ℂ)
    (hs₁ : Summable (fun k => ‖descendedTerm A B Γ₁ (n₁ + 1) u s k‖))
    (hs₂ : Summable (fun k => ‖descendedTerm A B Γ₂ (n₂ + 1) u s k‖))
    (horbit : Tendsto (fun k : ℕ => orbit u s k) atTop (𝓝 a))
    (hdefect : ∀ k, descendedTerm A B Γ₁ (n₁ + 1) u s k -
      descendedTerm A B Γ₂ (n₂ + 1) u s k =
        (correction n₁ e₁ s (orbit u s (k + 1)) - correction n₂ e₂ s (orbit u s (k + 1))) -
        (correction n₁ e₁ s (orbit u s k) - correction n₂ e₂ s (orbit u s k))) :
    preparedSeries U H n₁ e₁ A B Γ₁ u s - preparedSeries U H n₂ e₂ A B Γ₂ u s =
      correction n₁ e₁ s a - correction n₂ e₂ s a := by
  let P : ℂ → ℂ := fun v => correction n₁ e₁ s v - correction n₂ e₂ s v
  have hP : ContinuousAt P a := by
    dsimp [P, correction]
    fun_prop
  have hsum := (hs₁.of_norm.sub hs₂.of_norm).tendsto_sum_tsum_nat
  have htel : ∀ n : ℕ,
      (∑ k ∈ Finset.range n, (descendedTerm A B Γ₁ (n₁ + 1) u s k -
        descendedTerm A B Γ₂ (n₂ + 1) u s k)) = P (orbit u s n) - P u := by
    intro n
    simpa only [orbit_zero] using residual_difference_telescope _ _ P (orbit u s) hdefect n
  have hlim : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n, (descendedTerm A B Γ₁ (n₁ + 1) u s k -
        descendedTerm A B Γ₂ (n₂ + 1) u s k)) atTop (𝓝 (P a - P u)) :=
    ((hP.tendsto.comp horbit).sub_const (P u)).congr' (Eventually.of_forall fun n => (htel n).symm)
  have heq := tendsto_nhds_unique hsum hlim
  rw [Summable.tsum_sub hs₁.of_norm hs₂.of_norm] at heq
  dsimp only [preparedSeries, Kneser.coordinateSeries, modelTime, P] at *
  linear_combination heq

/-- Actual residual preparations sharing the same logarithmic defect have
the exact polynomial coboundary as their residual difference. -/
theorem residual_difference_of_common_preparation
    (A B : ℂ → ℂ) (F Γ₁ Γ₂ : ℂ × ℂ → ℂ) (n₁ n₂ : ℕ)
    (e₁ : Fin (2 * n₁) → ℂ → ℂ) (e₂ : Fin (2 * n₂) → ℂ → ℂ)
    (u : ℂ) (s : ℝ) (k : ℕ)
    (h₁ : F (Complex.sqrt s, orbit u s k) +
      correction n₁ e₁ s (unfolding s (orbit u s k)) - correction n₁ e₁ s (orbit u s k) =
        rootPolynomial A B s (orbit u s k) ^ (n₁ + 1) * Γ₁ (Complex.sqrt s, orbit u s k))
    (h₂ : F (Complex.sqrt s, orbit u s k) +
      correction n₂ e₂ s (unfolding s (orbit u s k)) - correction n₂ e₂ s (orbit u s k) =
        rootPolynomial A B s (orbit u s k) ^ (n₂ + 1) * Γ₂ (Complex.sqrt s, orbit u s k)) :
    descendedTerm A B Γ₁ (n₁ + 1) u s k - descendedTerm A B Γ₂ (n₂ + 1) u s k =
      (correction n₁ e₁ s (orbit u s (k + 1)) - correction n₂ e₂ s (orbit u s (k + 1))) -
      (correction n₁ e₁ s (orbit u s k) - correction n₂ e₂ s (orbit u s k)) := by
  simp only [descendedTerm, splitTerm, AnalyticEvenDescent.square_sqrt, orbit_succ]
  linear_combination -h₁ + h₂

/-- All dynamical and summability hypotheses of telescoping are derived
for the actual exponential map.  On a common bounded buffered petal, the
spatially normalized preparations of any two degrees agree exactly. -/
theorem exists_actual_normalized_compatibility
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ₁ Γ₂ : ℂ × ℂ → ℂ)
    (n₁ n₂ : ℕ) (e₁ : Fin (2 * n₁) → ℂ → ℂ) (e₂ : Fin (2 * n₂) → ℂ → ℂ)
    (hK : ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0) (hK0 : K 0 0 ≠ 0)
    (hfactor : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
      unfolding s u - u = rootPolynomial A B s u * K s u)
    (hΓ₁ : AnalyticAt ℂ Γ₁ 0) (hΓ₂ : AnalyticAt ℂ Γ₂ 0)
    (hprep₁ : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ),
      F p + correction n₁ e₁ (p.1 ^ 2) (unfolding (p.1 ^ 2) p.2) -
        correction n₁ e₁ (p.1 ^ 2) p.2 =
          rootPolynomial A B (p.1 ^ 2) p.2 ^ (n₁ + 1) * Γ₁ p)
    (hprep₂ : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ),
      F p + correction n₂ e₂ (p.1 ^ 2) (unfolding (p.1 ^ 2) p.2) -
        correction n₂ e₂ (p.1 ^ 2) p.2 =
          rootPolynomial A B (p.1 ^ 2) p.2 ^ (n₂ + 1) * Γ₂ p) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ Z : ℝ, 0 ≤ Z →
      ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u v : ℂ,
        R + 1 ≤ (inverseCoordinate u).re → ‖inverseCoordinate u‖ ≤ Z →
        R + 1 ≤ (inverseCoordinate v).re → ‖inverseCoordinate v‖ ≤ Z →
          preparedSeries U H n₁ e₁ A B Γ₁ u s - preparedSeries U H n₁ e₁ A B Γ₁ v s =
            preparedSeries U H n₂ e₂ A B Γ₂ u s - preparedSeries U H n₂ e₂ A B Γ₂ v s := by
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff.mp (hprep₁.and hprep₂)
  obtain ⟨Rlim, hRlim, hlimit⟩ := PositiveOrbitRootLimit.exists_uniform_actual_orbit_root_limit
  obtain ⟨Rorb, hRorb, horbits⟩ :=
    ActualRootPolynomialOrbit.eventually_actual_rootPolynomial_orbit_bound A B K
      hK hK0 hfactor (δ / 2) (by positivity)
  obtain ⟨R₁, CT₁, hR₁, hCT₁, hreal₁⟩ :=
    ActualRootPolynomialOrbit.exists_actual_prepared_real_majorant A B K
      (descendedFactor Γ₁) (n₁ + 1) hK hK0 hfactor
      (continuousAt_descendedFactor Γ₁ hΓ₁.continuousAt)
  obtain ⟨R₂, CT₂, hR₂, hCT₂, hreal₂⟩ :=
    ActualRootPolynomialOrbit.exists_actual_prepared_real_majorant A B K
      (descendedFactor Γ₂) (n₂ + 1) hK hK0 hfactor
      (continuousAt_descendedFactor Γ₂ hΓ₂.continuousAt)
  let R₀ : ℝ := max Rlim (max Rorb (max R₁ R₂))
  refine ⟨R₀, hRlim.trans_le (le_max_left _ _), ?_⟩
  intro R hR Z hZ
  have hRl : Rlim ≤ R := (le_max_left _ _).trans hR
  have hRo : Rorb ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hRt₁ : R₁ ≤ R := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hR))
  have hRt₂ : R₂ ≤ R := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hR))
  obtain ⟨sl, hsl, hlim⟩ := hlimit R hRl Z hZ
  obtain ⟨so, hso, hobs⟩ := horbits R hRo Z hZ
  obtain ⟨s₁, hs₁, ht₁⟩ := hreal₁ R hRt₁ Z hZ
  obtain ⟨s₂, hs₂, ht₂⟩ := hreal₂ R hRt₂ Z hZ
  have hsmall (t : ℝ) (ht : 0 < t) : ∀ᶠ s : ℝ in 𝓝[>] 0, s < t :=
    (eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall sl hsl, hsmall so hso,
    hsmall s₁ hs₁, hsmall s₂ hs₂, hsmall ((δ / 2) ^ 2) (by positivity)] with
      s hs hsslim hssorb hs₁' hs₂' hsδ
  obtain ⟨a, b, ha, hb, hfa, hfb, hconv⟩ := hlim s hs hsslim
  have hxsq : ‖Complex.sqrt (s : ℂ)‖ ^ 2 = s := by
    rw [← norm_pow, AnalyticEvenDescent.square_sqrt, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs]
  have hxr : ‖Complex.sqrt (s : ℂ)‖ < δ / 2 := by
    nlinarith [norm_nonneg (Complex.sqrt (s : ℂ))]
  have hdiff (u : ℂ) (hu : R + 1 ≤ (inverseCoordinate u).re)
      (hZu : ‖inverseCoordinate u‖ ≤ Z) :
      preparedSeries U H n₁ e₁ A B Γ₁ u s - preparedSeries U H n₂ e₂ A B Γ₂ u s =
        correction n₁ e₁ s (a : ℂ) - correction n₂ e₂ s (a : ℂ) := by
    have hsum₁ : Summable (fun k => ‖descendedTerm A B Γ₁ (n₁ + 1) u s k‖) := by
      apply summable_norm_of_parabolic_bound _ CT₁ (q := 2 * (n₁ + 1)) (by omega)
      intro k
      simpa only [descendedTerm_eq] using ht₁ s hs hs₁' u hu hZu k
    have hsum₂ : Summable (fun k => ‖descendedTerm A B Γ₂ (n₂ + 1) u s k‖) := by
      apply summable_norm_of_parabolic_bound _ CT₂ (q := 2 * (n₂ + 1)) (by omega)
      intro k
      simpa only [descendedTerm_eq] using ht₂ s hs hs₂' u hu hZu k
    apply preparedSeries_difference_of_orbit_limit U H A B n₁ n₂ e₁ e₂ Γ₁ Γ₂
      u s (a : ℂ) hsum₁ hsum₂ (hconv u hu hZu)
    intro k
    have hpδ : dist (Complex.sqrt (s : ℂ), orbit u s k) (0 : ℂ × ℂ) < δ := by
      rw [dist_zero_right, Prod.norm_def]
      exact max_lt (by linarith)
        ((hobs s hs hssorb u hu hZu k).2.trans (by linarith))
    obtain ⟨h₁, h₂⟩ := hδball hpδ
    simp only [AnalyticEvenDescent.square_sqrt] at h₁ h₂
    exact residual_difference_of_common_preparation A B F Γ₁ Γ₂ n₁ n₂ e₁ e₂ u s k h₁ h₂
  intro u v hu hZu hv hZv
  linear_combination hdiff u hu hZu - hdiff v hv hZv

end Kneser.PreparedDegreeCompatibility

end
