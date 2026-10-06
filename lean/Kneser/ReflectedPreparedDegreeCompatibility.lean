import Kneser.ReflectedPositiveOrbitRootLimit
import Kneser.PreparedDegreeCompatibility

/-! Corrections for the actual inverse dynamics telescope to the value at
the genuine repelling root. Spatial normalization cancels that constant,
so all preparation degrees describe one reflected coordinate family. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Kneser.ReflectedPreparedDegreeCompatibility

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.ExponentialRootPolynomial Kneser.ReflectedEvenOrbitDiscs
open Kneser.ExponentialPreparedHigher Kneser.ReflectedHigherPreparedCoordinate
open Kneser.RepellingExponentialOrbit Kneser.PreparedDegreeCompatibility
open scoped Topology BigOperators

theorem preparedSeries_difference_of_orbit_limit
    (U H A B : ℂ → ℂ) (n₁ n₂ : ℕ)
    (e₁ : Fin (2 * n₁) → ℂ → ℂ) (e₂ : Fin (2 * n₂) → ℂ → ℂ)
    (Γ₁ Γ₂ : ℂ × ℂ → ℂ) (v : ℂ) (s : ℝ) (b : ℂ)
    (hs₁ : Summable (fun k => ‖shiftedTerm A B Γ₁ (n₁ + 1) v s k‖))
    (hs₂ : Summable (fun k => ‖shiftedTerm A B Γ₂ (n₂ + 1) v s k‖))
    (horbit : Tendsto (fun k : ℕ => inverseOrbit v s k) atTop (𝓝 (-b)))
    (hdefect : ∀ k, shiftedTerm A B Γ₁ (n₁ + 1) v s k -
      shiftedTerm A B Γ₂ (n₂ + 1) v s k =
        (-correction n₁ e₁ s (-inverseOrbit v s (k + 1)) +
          correction n₂ e₂ s (-inverseOrbit v s (k + 1))) -
        (-correction n₁ e₁ s (-inverseOrbit v s k) +
          correction n₂ e₂ s (-inverseOrbit v s k))) :
    ReflectedHigherPreparedCoordinate.preparedSeries U H n₁ e₁ A B Γ₁ v s -
      ReflectedHigherPreparedCoordinate.preparedSeries U H n₂ e₂ A B Γ₂ v s =
      -correction n₁ e₁ s b + correction n₂ e₂ s b := by
  let P : ℂ → ℂ := fun w => -correction n₁ e₁ s (-w) + correction n₂ e₂ s (-w)
  have hP : ContinuousAt P (-b) := by dsimp [P, correction]; fun_prop
  have hsum := (hs₁.of_norm.sub hs₂.of_norm).tendsto_sum_tsum_nat
  have htel : ∀ n : ℕ,
      (∑ k ∈ Finset.range n, (shiftedTerm A B Γ₁ (n₁ + 1) v s k -
        shiftedTerm A B Γ₂ (n₂ + 1) v s k)) = P (inverseOrbit v s n) - P v := by
    intro n
    simpa only [inverseOrbit_zero] using
      residual_difference_telescope _ _ P (inverseOrbit v s) hdefect n
  have hlim : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n, (shiftedTerm A B Γ₁ (n₁ + 1) v s k -
        shiftedTerm A B Γ₂ (n₂ + 1) v s k)) atTop (𝓝 (P (-b) - P v)) :=
    ((hP.tendsto.comp horbit).sub_const (P v)).congr'
      (Eventually.of_forall fun n => (htel n).symm)
  have heq := tendsto_nhds_unique hsum hlim
  rw [Summable.tsum_sub hs₁.of_norm hs₂.of_norm] at heq
  dsimp only [ReflectedHigherPreparedCoordinate.preparedSeries, Kneser.coordinateSeries,
    ReflectedHigherModelTime.modelTime, HigherPreparedModelTime.modelTime, P] at *
  rw [ReflectedHigherModelTime.correction_reflected, ReflectedHigherModelTime.correction_reflected]
  simp only [neg_neg] at heq
  linear_combination heq

theorem residual_difference_of_common_preparation
    (A B : ℂ → ℂ) (F Γ₁ Γ₂ : ℂ × ℂ → ℂ) (n₁ n₂ : ℕ)
    (e₁ : Fin (2 * n₁) → ℂ → ℂ) (e₂ : Fin (2 * n₂) → ℂ → ℂ)
    (v : ℂ) (s : ℝ) (k : ℕ)
    (hinv : unfolding s (-inverseOrbit v s (k + 1)) = -inverseOrbit v s k)
    (h₁ : F (Complex.sqrt s, -inverseOrbit v s (k + 1)) +
      correction n₁ e₁ s (unfolding s (-inverseOrbit v s (k + 1))) -
        correction n₁ e₁ s (-inverseOrbit v s (k + 1)) =
        rootPolynomial A B s (-inverseOrbit v s (k + 1)) ^ (n₁ + 1) *
          Γ₁ (Complex.sqrt s, -inverseOrbit v s (k + 1)))
    (h₂ : F (Complex.sqrt s, -inverseOrbit v s (k + 1)) +
      correction n₂ e₂ s (unfolding s (-inverseOrbit v s (k + 1))) -
        correction n₂ e₂ s (-inverseOrbit v s (k + 1)) =
        rootPolynomial A B s (-inverseOrbit v s (k + 1)) ^ (n₂ + 1) *
          Γ₂ (Complex.sqrt s, -inverseOrbit v s (k + 1))) :
    shiftedTerm A B Γ₁ (n₁ + 1) v s k - shiftedTerm A B Γ₂ (n₂ + 1) v s k =
      (-correction n₁ e₁ s (-inverseOrbit v s (k + 1)) +
        correction n₂ e₂ s (-inverseOrbit v s (k + 1))) -
      (-correction n₁ e₁ s (-inverseOrbit v s k) + correction n₂ e₂ s (-inverseOrbit v s k)) := by
  simp only [shiftedTerm, descendedTerm, splitTerm, AnalyticEvenDescent.square_sqrt]
  rw [hinv] at h₁ h₂
  linear_combination -h₁ + h₂

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
          ReflectedHigherPreparedCoordinate.preparedSeries U H n₁ e₁ A B Γ₁ u s -
            ReflectedHigherPreparedCoordinate.preparedSeries U H n₁ e₁ A B Γ₁ v s =
          ReflectedHigherPreparedCoordinate.preparedSeries U H n₂ e₂ A B Γ₂ u s -
            ReflectedHigherPreparedCoordinate.preparedSeries U H n₂ e₂ A B Γ₂ v s := by
  obtain ⟨δ₁, hδ₁, hδball⟩ := Metric.eventually_nhds_iff.mp (hprep₁.and hprep₂)
  let δ : ℝ := min δ₁ 1
  have hδ : 0 < δ := lt_min hδ₁ (by norm_num)
  obtain ⟨Rlim, hRlim, hlimit⟩ :=
    ReflectedPositiveOrbitRootLimit.exists_uniform_actual_inverseOrbit_root_limit
  obtain ⟨Rorb, hRorb, horbits⟩ :=
    ReflectedPreparedRealMajorant.eventually_actual_rootPolynomial_orbit_bound A B K
      hK hK0 hfactor (δ / 2) (by positivity)
  obtain ⟨R₁, CT₁, hR₁, hCT₁, hreal₁⟩ :=
    ReflectedPreparedRealMajorant.exists_actual_prepared_real_majorant A B K
      (descendedFactor Γ₁) (n₁ + 1) hK hK0 hfactor
      (continuousAt_descendedFactor Γ₁ hΓ₁.continuousAt)
  obtain ⟨R₂, CT₂, hR₂, hCT₂, hreal₂⟩ :=
    ReflectedPreparedRealMajorant.exists_actual_prepared_real_majorant A B K
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
    hsmall s₁ hs₁, hsmall s₂ hs₂, hsmall ((δ / 2) ^ 2) (by positivity),
    hsmall 1 (by norm_num)] with s hs hsslim hssorb hs₁' hs₂' hsδ hsone
  obtain ⟨a, b, ha, hb, hfa, hfb, hconv⟩ := hlim s hs hsslim
  have hxsq : ‖Complex.sqrt (s : ℂ)‖ ^ 2 = s := by
    rw [← norm_pow, AnalyticEvenDescent.square_sqrt, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs]
  have hxr : ‖Complex.sqrt (s : ℂ)‖ < δ / 2 := by
    nlinarith [norm_nonneg (Complex.sqrt (s : ℂ))]
  have hdiff (u : ℂ) (hu : R + 1 ≤ (inverseCoordinate u).re)
      (hZu : ‖inverseCoordinate u‖ ≤ Z) :
      ReflectedHigherPreparedCoordinate.preparedSeries U H n₁ e₁ A B Γ₁ u s -
        ReflectedHigherPreparedCoordinate.preparedSeries U H n₂ e₂ A B Γ₂ u s =
      -correction n₁ e₁ s (b : ℂ) + correction n₂ e₂ s (b : ℂ) := by
    have hsum (Γ : ℂ × ℂ → ℂ) (n : ℕ) (CT : ℝ)
        (ht : ∀ k, ‖PreparedResidualEstimates.preparedResidual
          (fun p => rootPolynomial A B p.1 p.2) (descendedFactor Γ) (n + 1) s
            (-inverseOrbit u s k)‖ ≤ CT / ((k : ℝ) + 1) ^ (2 * (n + 1))) :
        Summable (fun k => ‖shiftedTerm A B Γ (n + 1) u s k‖) := by
      have hbnd : ∀ k, ‖descendedTerm A B Γ (n + 1) u s k‖ ≤
          CT / ((k : ℝ) + 1) ^ (2 * (n + 1)) := by simpa only [descendedTerm_eq] using ht
      have h := summable_norm_of_parabolic_bound _ CT (q := 2 * (n + 1)) (by omega) hbnd
      exact (summable_nat_add_iff 1).mpr h
    apply preparedSeries_difference_of_orbit_limit U H A B n₁ n₂ e₁ e₂ Γ₁ Γ₂
      u s (b : ℂ) (hsum Γ₁ n₁ CT₁ (ht₁ s hs hs₁' u hu hZu))
        (hsum Γ₂ n₂ CT₂ (ht₂ s hs hs₂' u hu hZu)) (hconv u hu hZu)
    intro k
    have hpδ : dist (Complex.sqrt (s : ℂ), -inverseOrbit u s (k + 1)) (0 : ℂ × ℂ) < δ₁ := by
      rw [dist_zero_right, Prod.norm_def]
      exact (max_lt (by linarith) ((hobs s hs hssorb u hu hZu (k + 1)).2.trans
        (by linarith))).trans_le (min_le_left _ _)
    obtain ⟨h₁, h₂⟩ := hδball hpδ
    simp only [AnalyticEvenDescent.square_sqrt] at h₁ h₂
    have hvnorm : ‖inverseOrbit u s k‖ < 1 := by
      have ht := (hobs s hs hssorb u hu hZu k).2
      rw [norm_neg] at ht
      have hd1 : δ ≤ 1 := min_le_right _ _
      linarith
    have hinv : unfolding s (-inverseOrbit u s (k + 1)) = -inverseOrbit u s k := by
      rw [inverseOrbit_succ]
      exact unfolding_reflectedInverse _ _ (by exact_mod_cast hsone.ne) hvnorm
    exact residual_difference_of_common_preparation A B F Γ₁ Γ₂ n₁ n₂ e₁ e₂
      u s k hinv h₁ h₂
  intro u v hu hZu hv hZv
  linear_combination hdiff u hu hZu - hdiff v hv hZv

end Kneser.ReflectedPreparedDegreeCompatibility

end
