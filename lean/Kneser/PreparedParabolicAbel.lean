import Kneser.PreparedLocalAbel

/-!
# Parabolic Abel equation and normalization of the constructed model

The model defect at `s=0` follows from its positive-parameter identity and
actual analytic continuity. True parabolic orbit bounds and genuine Cauchy
discs give absolute convergence. An orbit-restricted telescoping argument
identifies the model-minus-iterate limit with the prepared coordinate.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.PreparedParabolicAbel

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ExponentialRootPolynomial
open Kneser.ExponentialPreparedQuadratic Kneser.ExponentialPreparedModel
open Kneser.ExponentialMatrixDividedDifference Kneser.ExponentialModelTime
open Kneser.EvenPreparedOrbitDiscs Kneser.ParabolicExponentialOrbit
open Kneser.PreparedActualFirstOrder Kneser.PreparedLocalAbel
open scoped Topology BigOperators

theorem unfolding_zero_re_neg (u : ℂ) (hu : u.re < 0) : (unfolding 0 u).re < 0 := by
  have h : (Complex.exp u).re < 1 :=
    (Complex.re_le_norm _).trans_lt (by simpa only [Complex.norm_exp] using Real.exp_lt_one_iff.mpr hu)
  simpa only [unfolding_zero, Complex.sub_re, Complex.one_re, sub_lt_zero] using h

/-- The zero-parameter one-step model identity is obtained from the proved
positive-parameter identity by continuity, with no zero-step assumption. -/
theorem prepared_model_defect_zero (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (he₁ : AnalyticAt ℂ e₁ 0) (he₂ : AnalyticAt ℂ e₂ 0)
    (u : ℂ) (hu : u.re < 0)
    (hterm : ContinuousAt (fun s : ℂ => descendedTerm A B Γ 2 u s 0) 0)
    (hpositive : ∀ᶠ s : ℝ in 𝓝[>] 0,
      preparedModelTime U H e₁ e₂ s (unfolding s u) -
        preparedModelTime U H e₁ e₂ s u - 1 = descendedTerm A B Γ 2 u s 0) :
    preparedModelTime U H e₁ e₂ 0 (unfolding 0 u) -
      preparedModelTime U H e₁ e₂ 0 u - 1 = descendedTerm A B Γ 2 u 0 0 := by
  have hf : AnalyticAt ℂ (fun s : ℂ => unfolding s u) 0 := by
    unfold unfolding
    fun_prop
  have hmove := analyticAt_preparedModelTime_curve hU hU0 hH hHne he₁ he₂ hf
    (unfolding_zero_re_neg u hu)
  have hfixed := analyticAt_preparedModelTime_parameter hU hU0 hH hHne he₁ he₂ u hu
  have hleft : ContinuousAt (fun s : ℂ => preparedModelTime U H e₁ e₂ s (unfolding s u) -
      preparedModelTime U H e₁ e₂ s u - 1) 0 :=
    (hmove.continuousAt.sub hfixed.continuousAt).sub_const 1
  have hreal₀ : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝 0) (𝓝 (0 : ℂ)) :=
    by simpa using Complex.continuous_ofReal.continuousAt.tendsto (x := (0 : ℝ))
  have hreal := hreal₀.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  exact tendsto_nhds_unique (hleft.tendsto.comp hreal)
    ((hterm.tendsto.comp hreal).congr' (hpositive.mono fun _ h => h.symm))

/-- Orbit-restricted model defects telescope; a global defect identity away
from this orbit is unnecessary. -/
theorem prepared_orbit_telescoping (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (u : ℂ)
    (hdefect : ∀ k : ℕ,
      preparedModelTime U H e₁ e₂ 0 (orbit u 0 (k + 1)) -
        preparedModelTime U H e₁ e₂ 0 (orbit u 0 k) - 1 = descendedTerm A B Γ 2 u 0 k)
    (n : ℕ) :
    preparedModelTime U H e₁ e₂ 0 u + ∑ k ∈ Finset.range n, descendedTerm A B Γ 2 u 0 k =
      preparedModelTime U H e₁ e₂ 0 (orbit u 0 n) - (n : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rw [← add_assoc, ih]
    have h := hdefect n
    push_cast
    linear_combination -h

/-- Convergence of the prepared residual identifies the normalized actual
forward-orbit limit relative to the constructed model. -/
theorem actualPreparedCoordinate_parabolic_limit (U H e₁ e₂ A B : ℂ → ℂ)
    (Γ : ℂ × ℂ → ℂ) (u : ℂ)
    (hdefect : ∀ k : ℕ,
      preparedModelTime U H e₁ e₂ 0 (orbit u 0 (k + 1)) -
        preparedModelTime U H e₁ e₂ 0 (orbit u 0 k) - 1 = descendedTerm A B Γ 2 u 0 k)
    (hs : Summable (fun k => ‖descendedTerm A B Γ 2 u 0 k‖)) :
    Tendsto (fun n : ℕ => preparedModelTime U H e₁ e₂ 0 (orbit u 0 n) - (n : ℂ))
      atTop (𝓝 (actualPreparedCoordinate U H e₁ e₂ A B Γ u 0)) := by
  have ht : Tendsto
    (fun n : ℕ => preparedModelTime U H e₁ e₂ 0 u + ∑ k ∈ Finset.range n, descendedTerm A B Γ 2 u 0 k)
    atTop (𝓝 (actualPreparedCoordinate U H e₁ e₂ A B Γ u 0)) :=
    tendsto_const_nhds.add hs.of_norm.tendsto_sum_tsum_nat
  exact ht.congr' (Eventually.of_forall (prepared_orbit_telescoping U H e₁ e₂ A B Γ u hdefect))

/-- At sufficiently deep attracting points, the actual parabolic prepared
series converges, satisfies Abel, and is the model-minus-iterate limit.
All decay estimates and the zero-parameter model identity are conclusions. -/
theorem exists_prepared_parabolic_abel (U H e₁ e₂ A B : ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
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
        Complex.log (rootMultiplier U (-p.1)) - 1) :
    ∃ R₀ : ℝ, 32 ≤ R₀ ∧ ∀ u : ℂ, R₀ + 2 ≤ (inverseCoordinate u).re →
      Summable (fun k => ‖descendedTerm A B Γ 2 u 0 k‖) ∧
      (preparedModelTime U H e₁ e₂ 0 (unfolding 0 u) -
        preparedModelTime U H e₁ e₂ 0 u - 1 = descendedTerm A B Γ 2 u 0 0) ∧
      (actualPreparedCoordinate U H e₁ e₂ A B Γ (unfolding 0 u) 0 =
        actualPreparedCoordinate U H e₁ e₂ A B Γ u 0 + 1) ∧
      Tendsto (fun n : ℕ => preparedModelTime U H e₁ e₂ 0 (orbit u 0 n) - (n : ℂ))
        atTop (𝓝 (actualPreparedCoordinate U H e₁ e₂ A B Γ u 0)) := by
  obtain ⟨η, hη, hmodel⟩ := exists_local_model_defect U H e₁ e₂ A B F Γ
    hU hU0 hH hHne hHlog hcofactor hprepared hresidue
  obtain ⟨R₁, hR₁, hdiscs⟩ := exists_prepared_orbit_disc_bounds A B Γ 2
    hA hB hA0 hB0 hΓ hEven
  let R₀ : ℝ := max 32 (max R₁ (4 / η))
  have hR₀ : 32 ≤ R₀ := le_max_left _ _
  have hR₁₀ : R₁ ≤ R₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hRη : 4 / η ≤ R₀ := (le_max_right _ _).trans (le_max_right _ _)
  have hzero : ∀ u : ℂ, R₀ + 2 ≤ (inverseCoordinate u).re →
      Summable (fun k => ‖descendedTerm A B Γ 2 u 0 k‖) ∧
      preparedModelTime U H e₁ e₂ 0 (unfolding 0 u) -
        preparedModelTime U H e₁ e₂ 0 u - 1 = descendedTerm A B Γ 2 u 0 0 := by
    intro u hu
    have hre : 0 < (inverseCoordinate u).re := by linarith
    have hneg : u.re < 0 := by
      have h := Kneser.ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos hre
      simpa only [Complex.neg_re, neg_pos] using h
    have husmall : ‖u‖ < η := by
      apply (norm_le_two_div_re u hre).trans_lt
      apply (div_lt_iff₀ hre).mpr
      have hRmul : 4 ≤ R₀ * η := (div_le_iff₀ hη).mp hRη
      nlinarith
    obtain ⟨c, M, hc, _hM, hdisc, hbound⟩ := hdiscs R₀ hR₁₀
      ‖inverseCoordinate u‖ (norm_nonneg _) u (by linarith) (le_refl _)
    have hsum : Summable (fun k => ‖descendedTerm A B Γ 2 u 0 k‖) :=
      Kneser.summable_norm_of_parabolic_bound _ M (q := 4) (by norm_num)
        (fun k => hbound k 0 (by simp; positivity))
    have hcont : ContinuousAt (fun s : ℂ => descendedTerm A B Γ 2 u s 0) 0 :=
      ((hdisc 0).differentiableOn.analyticAt (isOpen_ball.mem_nhds (by simp; positivity))).continuousAt
    obtain ⟨ρ, s₀, hρ, hs₀, hpositive⟩ := hmodel u husmall hneg
    have hposid : ∀ᶠ s : ℝ in 𝓝[>] 0,
        preparedModelTime U H e₁ e₂ s (unfolding s u) -
          preparedModelTime U H e₁ e₂ s u - 1 = descendedTerm A B Γ 2 u s 0 := by
      have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < s₀ :=
        (eventually_lt_nhds hs₀).filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin, hsmall] with s hs hss
      exact hpositive s hs hss u (by simp [hρ])
    exact ⟨hsum, prepared_model_defect_zero U H e₁ e₂ A B Γ hU hU0 hH hHne he₁ he₂ u hneg hcont hposid⟩
  refine ⟨R₀, hR₀, ?_⟩
  intro u hu
  obtain ⟨hsum, hd⟩ := hzero u hu
  have horbit : ∀ k : ℕ, R₀ + 2 ≤ (inverseCoordinate (orbit u 0 k)).re := by
    intro k
    have h := iterate_inverse_re u (by linarith) k
    rw [← unfolding_orbit_zero_eq_iterate] at h
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hdefect : ∀ k : ℕ,
      preparedModelTime U H e₁ e₂ 0 (orbit u 0 (k + 1)) -
        preparedModelTime U H e₁ e₂ 0 (orbit u 0 k) - 1 = descendedTerm A B Γ 2 u 0 k := by
    intro k
    have hk := (hzero (orbit u 0 k) (horbit k)).2
    simpa only [orbit_succ, descendedTerm, splitTerm, AnalyticEvenDescent.square_sqrt, orbit_zero] using hk
  exact ⟨hsum, hd, actualPreparedCoordinate_abel U H e₁ e₂ A B Γ u 0 hd hsum,
    actualPreparedCoordinate_parabolic_limit U H e₁ e₂ A B Γ u hdefect hsum⟩

/-- The actual exponential preparation constructs a parabolic coordinate
whose convergence, Abel equation, and normalization are all proved. -/
theorem exists_actual_prepared_parabolic_abel :
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
        Summable (fun k => ‖descendedTerm A B Γ 2 u 0 k‖) ∧
        (preparedModelTime U H e₁ e₂ 0 (unfolding 0 u) -
          preparedModelTime U H e₁ e₂ 0 u - 1 = descendedTerm A B Γ 2 u 0 0) ∧
        (actualPreparedCoordinate U H e₁ e₂ A B Γ (unfolding 0 u) 0 =
          actualPreparedCoordinate U H e₁ e₂ A B Γ u 0 + 1) ∧
        Tendsto (fun n : ℕ => preparedModelTime U H e₁ e₂ 0 (orbit u 0 n) - (n : ℂ))
          atTop (𝓝 (actualPreparedCoordinate U H e₁ e₂ A B Γ u 0)) := by
  obtain ⟨U, H, e₁, e₂, A, B, K, F, Γ, hU, hU0, hUd, hH, hHne, hHlog,
      hA, hB, hA0, hB0, he₁, he₂, hF, hΓ, hΓeven, hK0, hK, hq, hroots,
      hfactor, hprepared, hresidue, _hlocal⟩ := exists_actual_local_prepared_abel
  have hcofactor : ∀ᶠ x in 𝓝 (0 : ℂ), ∀ u,
      unfolding (x ^ 2) u - u = rootProduct U x u * symmetricCofactor U x u :=
    eventually_symmetricCofactor_factor hU hroots (eventually_distinct_roots U hU hUd)
  have hEven : ∀ x v, Γ (-x, v) = Γ (x, v) := fun x v => hΓeven (x, v)
  have hzero := exists_prepared_parabolic_abel U H e₁ e₂ A B F Γ hU hU0 hH hHne hHlog
    he₁ he₂ hA hB hA0 hB0 hΓ hEven hcofactor hprepared hresidue
  exact ⟨U, H, e₁, e₂, A, B, K, F, Γ, hU, hU0, hUd, hH, hHne, hHlog,
    hA, hB, hA0, hB0, he₁, he₂, hF, hΓ, hΓeven, hK0, hK, hq, hroots,
    hfactor, hprepared, hresidue, hzero⟩

end Kneser.PreparedParabolicAbel

end
