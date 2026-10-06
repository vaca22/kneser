import Kneser.ReflectedPreparedSpatialHolomorphy
import Kneser.ReflectedLocalAbel
import Kneser.PreparedModelAtZero
import Kneser.RepellingFatouCoordinate
import Mathlib.Analysis.SpecificLimits.Basic

/-!
The actual reflected prepared coordinate at the merger is the canonical
repelling Fatou coordinate.  Its model, zero-parameter defect, convergence
and normalized inverse-orbit limit are all derived from actual germs.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.ReflectedCanonicalAtZero

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ExponentialRootPolynomial
open Kneser.ExponentialPreparedQuadratic Kneser.ExponentialPreparedModel
open Kneser.ExponentialMatrixDividedDifference Kneser.ExponentialModelTime
open Kneser.ParabolicExponentialOrbit Kneser.RepellingExponentialOrbit
open Kneser.ReflectedEvenOrbitDiscs Kneser.ReflectedPreparedFirstOrder
open Kneser.ReflectedLocalAbel
open scoped Topology BigOperators

/-- Reflection changes the multiplier-log derivative sign and gives the
canonical inverse model, without requiring reflected roots of the forward map. -/
theorem reflected_preparedModelTime_zero_eq_model (U H e₁ e₂ : ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0) (hUd : deriv U 0 ≠ 0)
    (hroots : ∀ᶠ x in 𝓝 (0 : ℂ), unfolding (x ^ 2) (U x) = U x)
    (hH : AnalyticAt ℂ H 0)
    (hHlog : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (v : ℂ) (hv : v.re < 0) :
    preparedModelTime (-U) (-H) e₁ (-e₂) 0 v = RepellingFatouCoordinate.model v +
      polynomialCorrection e₁ (-e₂) 0 v := by
  obtain ⟨hH0, hHsq, hHd⟩ := PreparedModelAtZero.actual_log_factor_coefficients
    U H hU hU0 hroots hH hHlog
  have hHne : H 0 ≠ 0 := hH0 ▸ hUd
  have hvne : v ≠ 0 := by intro heq; simp [heq] at hv
  have hslit : (-U) 0 - v ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simpa only [Pi.neg_apply, hU0, neg_zero, zero_sub, Complex.neg_re] using neg_pos.mpr hv
  have hUneg := hU.hasStrictDerivAt.hasDerivAt.neg
  have hHneg := hH.hasStrictDerivAt.hasDerivAt.neg
  have hA := ((hUneg.sub_const v).clog hslit).div hHneg (by simpa using hHne)
  have hUn := hUneg.comp_of_eq 0 (hasDerivAt_id (0 : ℂ)).neg (by simp)
  have hHn := hHneg.comp_of_eq 0 (hasDerivAt_id (0 : ℂ)).neg (by simp)
  change HasDerivAt (fun x => -U (-x)) (-deriv U 0 * -1) 0 at hUn
  change HasDerivAt (fun x => -H (-x)) (-deriv H 0 * -1) 0 at hHn
  have hB := ((hUn.sub_const v).clog (by simpa only [Pi.neg_apply, neg_zero] using hslit)).div hHn
    (by simpa using hHne)
  have hd := (hA.sub hB).deriv
  change deriv (fun x => modelNumerator (-U) (-H) x v) 0 = _ at hd
  have hmodel : deriv (fun x => modelNumerator (-U) (-H) x v) 0 =
      RepellingFatouCoordinate.model v := by
    rw [hd]
    simp only [Pi.neg_apply, neg_zero, hU0, zero_sub, hHd, ← hH0, mul_neg, mul_one]
    dsimp [RepellingFatouCoordinate.model]
    field_simp
    linear_combination (Complex.log (-v) * v) * hHsq
  rw [preparedModelTime, logarithmicModel, Complex.sqrt_zero, dslope_same, hmodel]

theorem inverseOrbit_add (v s : ℂ) (k j : ℕ) :
    inverseOrbit (inverseOrbit v s k) s j = inverseOrbit v s (k + j) := by
  simpa only [inverseOrbit, Nat.add_comm] using
    (Function.iterate_add_apply (reflectedInverse s) j k v).symm

theorem shiftedTerm_along_inverseOrbit (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (v s : ℂ) (k : ℕ) :
    shiftedTerm A B Γ 2 (inverseOrbit v s k) s 0 = shiftedTerm A B Γ 2 v s k := by
  simp only [shiftedTerm, descendedTerm, splitTerm, AnalyticEvenDescent.square_sqrt,
    inverseOrbit_add, zero_add]

/-- The zero-parameter inverse-step identity follows by continuity from
the proved positive-parameter local identity. -/
theorem reflected_model_defect_zero (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (he₁ : AnalyticAt ℂ e₁ 0) (he₂ : AnalyticAt ℂ e₂ 0)
    (v : ℂ) (hv : v.re < 0)
    (hterm : ContinuousAt (fun s : ℂ => shiftedTerm A B Γ 2 v s 0) 0)
    (hpositive : ∀ᶠ s : ℝ in 𝓝[>] 0,
      preparedModelTime (-U) (-H) e₁ (-e₂) s (reflectedInverse s v) -
        preparedModelTime (-U) (-H) e₁ (-e₂) s v - 1 = shiftedTerm A B Γ 2 v s 0) :
    preparedModelTime (-U) (-H) e₁ (-e₂) 0 (reflectedInverse 0 v) -
      preparedModelTime (-U) (-H) e₁ (-e₂) 0 v - 1 = shiftedTerm A B Γ 2 v 0 0 := by
  have hf : AnalyticAt ℂ (fun s : ℂ => reflectedInverse s v) 0 := by
    unfold reflectedInverse
    exact (analyticAt_const.add analyticAt_id).neg.div (analyticAt_const.sub analyticAt_id) (by simp)
  have hmove := analyticAt_preparedModelTime_curve hU.neg (by simp [hU0]) hH.neg
    (by simpa using hHne) he₁ he₂.neg hf
    (by simpa only [reflectedInverse_zero] using parabolicInverse_re_neg v hv)
  have hfixed := analyticAt_preparedModelTime_parameter hU.neg (by simp [hU0]) hH.neg
    (by simpa using hHne) he₁ he₂.neg v hv
  have hleft : ContinuousAt (fun s : ℂ => preparedModelTime (-U) (-H) e₁ (-e₂) s (reflectedInverse s v) -
      preparedModelTime (-U) (-H) e₁ (-e₂) s v - 1) 0 :=
    (hmove.continuousAt.sub hfixed.continuousAt).sub_const 1
  have hreal₀ : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝 0) (𝓝 (0 : ℂ)) :=
    by simpa using Complex.continuous_ofReal.continuousAt.tendsto (x := (0 : ℝ))
  have hreal := hreal₀.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  exact tendsto_nhds_unique (hleft.tendsto.comp hreal)
    ((hterm.tendsto.comp hreal).congr' (hpositive.mono fun _ h => h.symm))

theorem reflected_orbit_telescoping (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (v : ℂ)
    (hdefect : ∀ k : ℕ,
      preparedModelTime (-U) (-H) e₁ (-e₂) 0 (inverseOrbit v 0 (k + 1)) -
        preparedModelTime (-U) (-H) e₁ (-e₂) 0 (inverseOrbit v 0 k) - 1 = shiftedTerm A B Γ 2 v 0 k)
    (n : ℕ) :
    preparedModelTime (-U) (-H) e₁ (-e₂) 0 v + ∑ k ∈ Finset.range n, shiftedTerm A B Γ 2 v 0 k =
      preparedModelTime (-U) (-H) e₁ (-e₂) 0 (inverseOrbit v 0 n) - (n : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    have h := hdefect n
    push_cast
    linear_combination -h

theorem actualInversePreparedCoordinate_parabolic_limit (U H e₁ e₂ A B : ℂ → ℂ)
    (Γ : ℂ × ℂ → ℂ) (v : ℂ)
    (hdefect : ∀ k : ℕ,
      preparedModelTime (-U) (-H) e₁ (-e₂) 0 (inverseOrbit v 0 (k + 1)) -
        preparedModelTime (-U) (-H) e₁ (-e₂) 0 (inverseOrbit v 0 k) - 1 = shiftedTerm A B Γ 2 v 0 k)
    (hs : Summable (fun k => ‖shiftedTerm A B Γ 2 v 0 k‖)) :
    Tendsto (fun n : ℕ => preparedModelTime (-U) (-H) e₁ (-e₂) 0 (inverseOrbit v 0 n) - (n : ℂ))
      atTop (𝓝 (actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0)) := by
  have ht : Tendsto
      (fun n : ℕ => preparedModelTime (-U) (-H) e₁ (-e₂) 0 v + ∑ k ∈ Finset.range n, shiftedTerm A B Γ 2 v 0 k)
      atTop (𝓝 (actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0)) :=
    tendsto_const_nhds.add hs.of_norm.tendsto_sum_tsum_nat
  exact ht.congr' (Eventually.of_forall (reflected_orbit_telescoping U H e₁ e₂ A B Γ v hdefect))

/-- Actual parameter discs and local branch identities give the inverse
Abel equation and normalized prepared orbit limit at the merger. -/
theorem exists_reflected_parabolic_abel (U H e₁ e₂ A B : ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
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
    ∃ R₀ : ℝ, 64 ≤ R₀ ∧ ∀ v : ℂ, R₀ + 2 ≤ (inverseCoordinate v).re →
      Summable (fun k => ‖shiftedTerm A B Γ 2 v 0 k‖) ∧
      (preparedModelTime (-U) (-H) e₁ (-e₂) 0 (reflectedInverse 0 v) -
        preparedModelTime (-U) (-H) e₁ (-e₂) 0 v - 1 = shiftedTerm A B Γ 2 v 0 0) ∧
      (actualInversePreparedCoordinate U H e₁ e₂ A B Γ (reflectedInverse 0 v) 0 =
        actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0 + 1) ∧
      Tendsto (fun n : ℕ => preparedModelTime (-U) (-H) e₁ (-e₂) 0 (inverseOrbit v 0 n) - (n : ℂ))
        atTop (𝓝 (actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0)) := by
  obtain ⟨η, hη, hmodel⟩ := exists_local_inverse_model_defect U H e₁ e₂ A B F Γ
    hU hU0 hH hHne hHlog hcofactor hprepared hresidue
  obtain ⟨R₁, hR₁, hdiscs⟩ := exists_prepared_orbit_disc_bounds A B Γ 2
    hA hB hA0 hB0 hΓ hEven
  let R₀ : ℝ := max 64 (max R₁ (4 / η))
  have hR₀ : 64 ≤ R₀ := le_max_left _ _
  have hR₁₀ : R₁ ≤ R₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hRη : 4 / η ≤ R₀ := (le_max_right _ _).trans (le_max_right _ _)
  have hzero : ∀ v : ℂ, R₀ + 2 ≤ (inverseCoordinate v).re →
      Summable (fun k => ‖shiftedTerm A B Γ 2 v 0 k‖) ∧
      preparedModelTime (-U) (-H) e₁ (-e₂) 0 (reflectedInverse 0 v) -
        preparedModelTime (-U) (-H) e₁ (-e₂) 0 v - 1 = shiftedTerm A B Γ 2 v 0 0 := by
    intro v hv
    have hre : 0 < (inverseCoordinate v).re := by linarith
    have hneg : v.re < 0 := by
      have h := ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos hre
      simpa only [Complex.neg_re, neg_pos] using h
    have hvsmall : ‖v‖ < η := by
      apply (ParabolicExponentialOrbit.norm_le_two_div_re v hre).trans_lt
      apply (div_lt_iff₀ hre).mpr
      have hRmul : 4 ≤ R₀ * η := (div_le_iff₀ hη).mp hRη
      nlinarith
    obtain ⟨c, M, hc, hM, hdisc, hbound⟩ := hdiscs R₀ hR₁₀
      ‖inverseCoordinate v‖ (norm_nonneg _) v (by linarith) (le_refl _)
    obtain ⟨hdshift, hbshift⟩ := shifted_disc_bounds (descendedTerm A B Γ 2 v) c M hc hM hdisc hbound
    have hsum : Summable (fun k => ‖shiftedTerm A B Γ 2 v 0 k‖) :=
      summable_norm_of_parabolic_bound _ M (q := 4) (by norm_num)
        (fun k => hbshift k 0 (by simp; positivity))
    have hcont : ContinuousAt (fun s : ℂ => shiftedTerm A B Γ 2 v s 0) 0 :=
      ((hdshift 0).differentiableOn.analyticAt (isOpen_ball.mem_nhds (by simp; positivity))).continuousAt
    obtain ⟨ρ, s₀, hρ, hs₀, hpositive⟩ := hmodel v hvsmall hneg
    have hposid : ∀ᶠ s : ℝ in 𝓝[>] 0,
        preparedModelTime (-U) (-H) e₁ (-e₂) s (reflectedInverse s v) -
          preparedModelTime (-U) (-H) e₁ (-e₂) s v - 1 = shiftedTerm A B Γ 2 v s 0 := by
      have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < s₀ :=
        (eventually_lt_nhds hs₀).filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin, hsmall] with s hs hss
      exact hpositive s hs hss v (by simp [hρ])
    exact ⟨hsum, reflected_model_defect_zero U H e₁ e₂ A B Γ hU hU0 hH hHne he₁ he₂ v hneg hcont hposid⟩
  refine ⟨R₀, hR₀, ?_⟩
  intro v hv
  obtain ⟨hsum, hd⟩ := hzero v hv
  have horbit : ∀ k : ℕ, R₀ + 2 ≤ (inverseCoordinate (inverseOrbit v 0 k)).re := by
    intro k
    have h := RepellingFatouCoordinate.inverse_iterate_re v (inverseCoordinate v).re
      (by linarith) (le_refl _) k
    rw [← RepellingFatouCoordinate.inverseOrbit_zero_parameter] at h
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hdefect : ∀ k : ℕ,
      preparedModelTime (-U) (-H) e₁ (-e₂) 0 (inverseOrbit v 0 (k + 1)) -
        preparedModelTime (-U) (-H) e₁ (-e₂) 0 (inverseOrbit v 0 k) - 1 = shiftedTerm A B Γ 2 v 0 k := by
    intro k
    have hk := (hzero (inverseOrbit v 0 k) (horbit k)).2
    simpa only [← inverseOrbit_succ, shiftedTerm_along_inverseOrbit] using hk
  exact ⟨hsum, hd, actualInversePreparedCoordinate_abel U H e₁ e₂ A B Γ v 0 hd hsum,
    actualInversePreparedCoordinate_parabolic_limit U H e₁ e₂ A B Γ v hdefect hsum⟩

theorem actual_inverse_orbit_tendsto_zero (v : ℂ) (hv : 64 ≤ (inverseCoordinate v).re) :
    Tendsto (fun k : ℕ => inverseOrbit v 0 k) atTop (𝓝 0) := by
  have hbound : ∀ k : ℕ, ‖inverseOrbit v 0 k‖ ≤ 4 / ((k : ℝ) + 1) := by
    intro k
    rw [RepellingFatouCoordinate.inverseOrbit_zero_parameter]
    apply (RepellingFatouCoordinate.inverse_iterate_norm_bound v 64 (le_refl _) hv k).trans
    apply (div_le_div_iff₀ (by positivity : 0 < 64 + (k : ℝ) / 2)
      (by positivity : 0 < (k : ℝ) + 1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hmajorant : Tendsto (fun k : ℕ => (4 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    convert (tendsto_const_nhds (x := (4 : ℝ))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) using 1 <;> simp [div_eq_mul_inv]
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) hbound hmajorant)

theorem reflected_polynomial_orbit_tendsto_zero (e₁ e₂ : ℂ → ℂ) (v : ℂ)
    (hv : 64 ≤ (inverseCoordinate v).re) :
    Tendsto (fun k : ℕ => polynomialCorrection e₁ (-e₂) 0 (inverseOrbit v 0 k)) atTop (𝓝 0) := by
  have hpoly : ContinuousAt (fun u : ℂ => polynomialCorrection e₁ (-e₂) 0 u) 0 := by
    unfold polynomialCorrection
    fun_prop
  simpa [Function.comp_def, polynomialCorrection] using
    hpoly.tendsto.comp (actual_inverse_orbit_tendsto_zero v hv)

theorem reflected_eq_canonical_of_model_and_limits
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (v : ℂ)
    (hv : 64 ≤ (inverseCoordinate v).re)
    (hmodel : ∀ u : ℂ, u.re < 0 → preparedModelTime (-U) (-H) e₁ (-e₂) 0 u =
      RepellingFatouCoordinate.model u + polynomialCorrection e₁ (-e₂) 0 u)
    (hprepared : Tendsto (fun n : ℕ => preparedModelTime (-U) (-H) e₁ (-e₂) 0 (inverseOrbit v 0 n) - (n : ℂ))
      atTop (𝓝 (actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0)))
    (hcanonical : Tendsto (fun n : ℕ => RepellingFatouCoordinate.model ((parabolicInverse^[n]) v) - (n : ℂ))
      atTop (𝓝 (correctedCoordinate parabolicInverse RepellingFatouCoordinate.model
        (coordinateDefect parabolicInverse RepellingFatouCoordinate.model) v))) :
    actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0 =
      correctedCoordinate parabolicInverse RepellingFatouCoordinate.model
        (coordinateDefect parabolicInverse RepellingFatouCoordinate.model) v := by
  have hcanonical' : Tendsto
      (fun n : ℕ => RepellingFatouCoordinate.model (inverseOrbit v 0 n) - (n : ℂ)) atTop
      (𝓝 (correctedCoordinate parabolicInverse RepellingFatouCoordinate.model
        (coordinateDefect parabolicInverse RepellingFatouCoordinate.model) v)) := by
    simpa only [RepellingFatouCoordinate.inverseOrbit_zero_parameter] using hcanonical
  have hcombined := hcanonical'.add (reflected_polynomial_orbit_tendsto_zero e₁ e₂ v hv)
  have hcombined' : Tendsto
      (fun n : ℕ => preparedModelTime (-U) (-H) e₁ (-e₂) 0 (inverseOrbit v 0 n) - (n : ℂ)) atTop
      (𝓝 (correctedCoordinate parabolicInverse RepellingFatouCoordinate.model
        (coordinateDefect parabolicInverse RepellingFatouCoordinate.model) v)) := by
    simpa only [add_zero] using hcombined.congr' (Eventually.of_forall (fun n => by
      have hre : 0 < (inverseCoordinate (inverseOrbit v 0 n)).re := by
        have h := RepellingFatouCoordinate.inverse_iterate_re v 64 (le_refl _) hv n
        rw [← RepellingFatouCoordinate.inverseOrbit_zero_parameter] at h
        linarith [Nat.cast_nonneg (α := ℝ) n]
      have hneg : (inverseOrbit v 0 n).re < 0 := by
        simpa only [Complex.neg_re, neg_pos] using
          ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos hre
      rw [hmodel _ hneg]
      ring))
  exact tendsto_nhds_unique hprepared hcombined'

/-- Any actual preparation data derive canonical identification at zero.
There is no model decomposition or coordinate equality hypothesis. -/
theorem exists_reflected_canonical_at_zero
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ReflectedOrbitChainCoefficient.ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ R₀ : ℝ, 64 ≤ R₀ ∧ ∀ v : ℂ, R₀ + 2 ≤ (inverseCoordinate v).re →
      actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0 =
        correctedCoordinate parabolicInverse RepellingFatouCoordinate.model
          (coordinateDefect parabolicInverse RepellingFatouCoordinate.model) v := by
  rcases hdata with ⟨hU, hU0, hUd, hH, hHne, hHlog, hA, hB, hA0, hB0, he₁, he₂,
    hF, hΓ, hΓeven, hK0, hK, hq, hroots, hfactor, hprepared, hresidue⟩
  have hcofactor := eventually_symmetricCofactor_factor hU hroots
    (PreparedLocalAbel.eventually_distinct_roots U hU hUd)
  have hEven : ∀ x u, Γ (-x, u) = Γ (x, u) := fun x u => hΓeven (x, u)
  obtain ⟨R₁, hR₁, hzero⟩ := exists_reflected_parabolic_abel U H e₁ e₂ A B F Γ
    hU hU0 hH hHne hHlog he₁ he₂ hA hB hA0 hB0 hΓ hEven hcofactor hprepared hresidue
  obtain ⟨R₂, C, hR₂, _hC, hcanonical⟩ := RepellingFatouCoordinate.exists_repelling_fatou_coordinate
  refine ⟨max R₁ R₂, hR₁.trans (le_max_left _ _), ?_⟩
  intro v hv
  have hv₁ : R₁ + 2 ≤ (inverseCoordinate v).re := by
    have h := le_max_left R₁ R₂
    linarith
  have hv₂ : R₂ ≤ (inverseCoordinate v).re := by
    have h := le_max_right R₁ R₂
    linarith
  exact reflected_eq_canonical_of_model_and_limits U H e₁ e₂ A B Γ v (hR₂.trans hv₂)
    (reflected_preparedModelTime_zero_eq_model U H e₁ e₂ hU hU0 hUd
      (hroots.mono fun _ h => h.1) hH hHlog)
    (hzero v hv₁).2.2.2 (hcanonical v hv₂).2.2.2

/-- Actual constructed preparation witnesses retain all root, cofactor,
residue and preparation identities and give the canonical inverse
coordinate at zero without a canonical-identification input. -/
theorem exists_actual_reflected_canonical_at_zero :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      ReflectedOrbitChainCoefficient.ActualPreparationData U H e₁ e₂ A B K F Γ ∧
      ∃ R₀ : ℝ, 64 ≤ R₀ ∧ ∀ v : ℂ, R₀ + 2 ≤ (inverseCoordinate v).re →
          actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0 =
            correctedCoordinate parabolicInverse RepellingFatouCoordinate.model
              (coordinateDefect parabolicInverse RepellingFatouCoordinate.model) v := by
  obtain ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, _⟩ :=
    ReflectedPreparedSpatialHolomorphy.exists_actual_holomorphic_repelling_explicit_coefficient
  exact ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata,
    exists_reflected_canonical_at_zero U H e₁ e₂ A B K F Γ hdata⟩

end Kneser.ReflectedCanonicalAtZero

end
