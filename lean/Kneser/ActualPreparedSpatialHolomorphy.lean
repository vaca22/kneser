import Kneser.UniformModelTime
import Kneser.PreparedSpatialHolomorphy
import Kneser.PreparedActualFirstOrder

/-!
Spatial holomorphy of the actual logarithmic model and of its constructed
prepared orbit correction for a common interval of positive parameters.
The spatial analyticity of the model is proved from its explicit formula.
-/

noncomputable section

namespace Kneser.ActualPreparedSpatialHolomorphy

open Filter Set Metric Kneser.ExponentialUnfolding
open Kneser.ExponentialRootPolynomial Kneser.ExponentialModelTime
open Kneser.ExponentialPreparedModel Kneser.ParabolicExponentialOrbit
open Kneser.PreparedSpatialHolomorphy Kneser.EvenPreparedOrbitDiscs
open scoped Topology BigOperators

/-- The logarithmic model is spatially analytic whenever its two actual
logarithm arguments are in the principal slit plane. -/
theorem analyticAt_preparedModelTime_spatial_of_slit
    (U H e₁ e₂ : ℂ → ℂ) (s u : ℂ) (hs : s ≠ 0)
    (ha : U (Complex.sqrt s) - u ∈ Complex.slitPlane)
    (hb : U (-Complex.sqrt s) - u ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun v => preparedModelTime U H e₁ e₂ s v) u := by
  have hx : Complex.sqrt s ≠ 0 := by
    intro heq
    have h := AnalyticEvenDescent.square_sqrt s
    rw [heq, zero_pow (by norm_num : 2 ≠ 0)] at h
    exact hs h.symm
  have heq : (fun v => preparedModelTime U H e₁ e₂ s v) =
      (fun v => modelNumerator U H (Complex.sqrt s) v / Complex.sqrt s +
        polynomialCorrection e₁ e₂ s v) := by
    funext v
    rw [preparedModelTime, logarithmicModel, dslope_of_ne _ hx, slope_def_field,
      modelNumerator_zero]
    simp
  rw [heq]
  have hNa : AnalyticAt ℂ (fun v => modelNumerator U H (Complex.sqrt s) v) u :=
    (((analyticAt_const.sub analyticAt_id).clog ha).div_const).sub
      (((analyticAt_const.sub analyticAt_id).clog hb).div_const)
  have hP : AnalyticAt ℂ (fun v => polynomialCorrection e₁ e₂ s v) u :=
    (analyticAt_const.mul analyticAt_id).add (analyticAt_const.mul (analyticAt_id.pow 2))
  exact hNa.div_const.add hP

theorem inverseCoordinate_involutive (u : ℂ) :
    inverseCoordinate (inverseCoordinate u) = u := by
  by_cases hu : u = 0
  · simp [hu, inverseCoordinate]
  · dsimp [inverseCoordinate]
    field_simp

/-- A bounded inverse-coordinate petal stays a uniform positive distance
from the logarithm cut in the spatial variable. -/
theorem negative_re_lower_bound (u : ℂ) (R Z : ℝ) (hR : 0 < R) (hZ : 0 ≤ Z)
    (hu : R + 1 ≤ (inverseCoordinate u).re) (huZ : ‖inverseCoordinate u‖ ≤ Z) :
    2 * (R + 1) / (Z + 1) ^ 2 ≤ -u.re := by
  have hpos : 0 < (inverseCoordinate u).re := by linarith
  have hy : inverseCoordinate u ≠ 0 := by intro h; simp [h] at hpos
  have hnorm : 0 < ‖inverseCoordinate u‖ := norm_pos_iff.mpr hy
  have hnormSq : ‖inverseCoordinate u‖ ^ 2 ≤ (Z + 1) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (huZ.trans (by linarith)) 2
  have hre : -u.re = 2 * (inverseCoordinate u).re / ‖inverseCoordinate u‖ ^ 2 := by
    conv_lhs => rw [← inverseCoordinate_involutive u]
    change -((-2 : ℂ) / inverseCoordinate u).re = _
    rw [Complex.div_re, Complex.normSq_eq_norm_sq]
    norm_num
    ring
  rw [hre]
  apply (div_le_div_of_nonneg_right (show 2 * (R + 1) ≤
    2 * (inverseCoordinate u).re by linarith) (by positivity)).trans
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hnormSq

/-- One parameter interval makes the actual model spatially holomorphic on
the whole bounded initial petal; no spatial model hypothesis is supplied. -/
theorem exists_holomorphic_preparedModelTime
    {U H e₁ e₂ : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (R Z : ℝ) (hR : 0 < R) (hZ : 0 ≤ Z) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      DifferentiableOn ℂ (fun u => preparedModelTime U H e₁ e₂ s u)
        (boundedPetal R Z) := by
  let δ : ℝ := (R + 1) / (Z + 1) ^ 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : ∀ᶠ x in 𝓝 (0 : ℂ), ‖U x‖ < δ := by
    have h := hU.continuousAt.norm.eventually
      (gt_mem_nhds (show ‖U 0‖ < δ by simpa only [hU0, norm_zero] using hδ))
    exact h
  obtain ⟨η, hη, hηsmall⟩ := Metric.eventually_nhds_iff.mp hsmall
  refine ⟨η ^ 2, by positivity, ?_⟩
  intro s hs hss u hu
  have hsq : ‖Complex.sqrt (s : ℂ)‖ ^ 2 = s := by
    rw [← norm_pow, AnalyticEvenDescent.square_sqrt, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs]
  have hx : ‖Complex.sqrt (s : ℂ)‖ < η := by
    nlinarith [norm_nonneg (Complex.sqrt (s : ℂ))]
  have hUx : ‖U (Complex.sqrt (s : ℂ))‖ < δ :=
    hηsmall (by simpa only [dist_zero_right] using hx)
  have hUnx : ‖U (-Complex.sqrt (s : ℂ))‖ < δ :=
    hηsmall (by simpa only [dist_zero_right, norm_neg] using hx)
  have hure := negative_re_lower_bound u R Z hR hZ hu.1.le hu.2.le
  have hure' : 2 * δ ≤ -u.re := by
    convert hure using 1
    dsimp [δ]
    ring
  have ha : 0 < (U (Complex.sqrt (s : ℂ)) - u).re := by
    have hre : -(U (Complex.sqrt (s : ℂ))).re ≤ ‖U (Complex.sqrt (s : ℂ))‖ := by
      simpa only [Complex.neg_re, norm_neg] using
        Complex.re_le_norm (-U (Complex.sqrt (s : ℂ)))
    simp only [Complex.sub_re]
    linarith
  have hb : 0 < (U (-Complex.sqrt (s : ℂ)) - u).re := by
    have hre : -(U (-Complex.sqrt (s : ℂ))).re ≤ ‖U (-Complex.sqrt (s : ℂ))‖ := by
      simpa only [Complex.neg_re, norm_neg] using
        Complex.re_le_norm (-U (-Complex.sqrt (s : ℂ)))
    simp only [Complex.sub_re]
    linarith
  exact (analyticAt_preparedModelTime_spatial_of_slit U H e₁ e₂ s u
    (by exact_mod_cast hs.ne') (Complex.mem_slitPlane_iff.mpr (Or.inl ha))
      (Complex.mem_slitPlane_iff.mpr (Or.inl hb))).differentiableAt.differentiableWithinAt

/-- The explicit model plus its genuine prepared residual series is
spatially holomorphic for a common interval of positive parameters. -/
theorem exists_holomorphic_actualPreparedCoordinate
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hK : ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0) (hK0 : K 0 0 ≠ 0)
    (hfactor : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
      unfolding s u - u = rootPolynomial A B s u * K s u)
    (hΓa : AnalyticAt ℂ Γ 0) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ Z : ℝ, 0 ≤ Z →
      ∃ s₀ C : ℝ, 0 < s₀ ∧ 0 ≤ C ∧ ∀ s : ℝ, 0 < s → s < s₀ →
        DifferentiableOn ℂ
          (fun u => PreparedActualFirstOrder.actualPreparedCoordinate U H e₁ e₂ A B Γ u s)
          (boundedPetal R Z) ∧
        TendstoUniformlyOn
          (fun J : ℕ => fun u => ∑ k ∈ Finset.range J, descendedTerm A B Γ 2 u s k)
          (fun u => ∑' k : ℕ, descendedTerm A B Γ 2 u s k) atTop (boundedPetal R Z) ∧
        ∀ u ∈ boundedPetal R Z, Summable (fun k => ‖descendedTerm A B Γ 2 u s k‖) := by
  obtain ⟨R₀, hR₀, htail⟩ := exists_holomorphic_prepared_tail A B K Γ 2 (by norm_num)
    hK hK0 hfactor hΓa
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR Z hZ
  have hRpos : 0 < R := hR₀.trans_le hR
  obtain ⟨s₁, C, hs₁, hC, ht⟩ := htail R hR Z hZ
  obtain ⟨s₂, hs₂, hm⟩ := exists_holomorphic_preparedModelTime hU hU0 R Z hRpos hZ
  refine ⟨min s₁ s₂, C, lt_min hs₁ hs₂, hC, ?_⟩
  intro s hs hss
  obtain ⟨hhol, huni, hsum⟩ := ht s hs (hss.trans_le (min_le_left _ _))
  have hmodel := hm s hs (hss.trans_le (min_le_right _ _))
  refine ⟨?_, huni, hsum⟩
  convert hmodel.add hhol using 1 <;> rfl

/-- The constructed roots and residual preparation give an actual
holomorphic prepared coordinate; no spatial-holomorphy hypothesis appears. -/
theorem exists_actual_holomorphic_prepared_coordinate :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      AnalyticAt ℂ U 0 ∧ U 0 = 0 ∧ AnalyticAt ℂ H 0 ∧ H 0 ≠ 0 ∧
      (∀ x, Complex.log (rootMultiplier U x) = x * H x) ∧
      AnalyticAt ℂ e₁ 0 ∧ AnalyticAt ℂ e₂ 0 ∧ AnalyticAt ℂ F 0 ∧ AnalyticAt ℂ Γ 0 ∧
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
        Complex.log (1 + (p.2 - U (-p.1)) *
          ExponentialMatrixDividedDifference.symmetricCofactor U p.1 p.2) /
          Complex.log (rootMultiplier U p.1) +
        Complex.log (1 + (p.2 - U p.1) *
          ExponentialMatrixDividedDifference.symmetricCofactor U p.1 p.2) /
          Complex.log (rootMultiplier U (-p.1)) - 1) ∧
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ Z : ℝ, 0 ≤ Z →
        ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
          DifferentiableOn ℂ
            (fun u => PreparedActualFirstOrder.actualPreparedCoordinate U H e₁ e₂ A B Γ u s)
            (boundedPetal R Z) := by
  obtain ⟨U, A, B, e₁, e₂, K, F, Γ, hU, hU0, hUd, hA, hB, hA0, hB0,
    he₁, he₂, hF, hΓ, hK0, hK, hFeven, hΓeven, hfactor, hprepared, hresidue, hq, hroots⟩ :=
    ExponentialPreparedQuadratic.exists_actual_prepared_quadratic
  obtain ⟨H, hH, hH0, hHlog⟩ := exists_log_multiplier_factor hU hU0
  have hHne : H 0 ≠ 0 := hH0 ▸ hUd
  obtain ⟨R₀, hR₀, hfull⟩ := exists_holomorphic_actualPreparedCoordinate U H e₁ e₂ A B K Γ
    hU hU0 hK (by rw [hK0]; norm_num) hfactor hΓ
  refine ⟨U, H, e₁, e₂, A, B, K, F, Γ, hU, hU0, hH, hHne, hHlog,
    he₁, he₂, hF, hΓ, hK0, hK, hq, hroots, hfactor, hprepared, hresidue,
    R₀, hR₀, ?_⟩
  intro R hR Z hZ
  obtain ⟨s₀, C, hs₀, hC, h⟩ := hfull R hR Z hZ
  exact ⟨s₀, hs₀, fun s hs hss => (h s hs hss).1⟩

end Kneser.ActualPreparedSpatialHolomorphy

end
