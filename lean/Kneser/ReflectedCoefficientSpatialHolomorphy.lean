import Kneser.PreparedCoefficientSpatialHolomorphy
import Kneser.ReflectedPreparedSpatialHolomorphy

/-!
Spatial holomorphy and continuity of the actual reflected inverse first
coefficient.  The inverse tangent recurrence and the true principal-log
orbit bounds supply spatial analyticity; common Cauchy discs give uniform
absolute convergence of the displayed shifted coefficient series.
-/

noncomputable section

namespace Kneser.ReflectedCoefficientSpatialHolomorphy

open Filter Set Metric Kneser.ExponentialUnfolding
open Kneser.ExponentialRootPolynomial Kneser.ExponentialModelTime
open Kneser.ExponentialPreparedModel Kneser.ParabolicExponentialOrbit
open Kneser.PreparedSpatialHolomorphy Kneser.ReflectedEvenOrbitDiscs
open Kneser.RepellingExponentialOrbit Kneser.ReflectedPreparedFirstOrder
open Kneser.ReflectedOrbitChainCoefficient
open scoped Topology BigOperators

theorem zero_inverseOrbit_norm_lt_one (v : ℂ)
    (hv : 64 ≤ (inverseCoordinate v).re) (k : ℕ) :
    ‖inverseOrbit v 0 k‖ < 1 := by
  have hr := PerturbedExponentialOrbit.parameterRadius_pos ‖inverseCoordinate v‖
    (norm_nonneg _) k
  have hn := finite_inverseOrbit_norm_bound v 0 64 (le_refl _) hv k
    (by simpa only [norm_zero] using hr.le) k (le_refl k)
  apply hn.trans_lt
  apply (div_lt_iff₀ (by linarith [Nat.cast_nonneg (α := ℝ) k] :
    0 < 64 + (k : ℝ) / 2)).mpr
  linarith [Nat.cast_nonneg (α := ℝ) k]

theorem differentiableAt_inverseOrbit_zero_spatial (v : ℂ)
    (hv : 64 ≤ (inverseCoordinate v).re) (k : ℕ) :
    DifferentiableAt ℂ (fun u => inverseOrbit u 0 k) v :=
  ReflectedPreparedSpatialHolomorphy.differentiableAt_inverseOrbit_spatial 0 v k
    (zero_inverseOrbit_norm_lt_one v hv)

/-- Spatial analyticity of the true inverse tangent follows from its actual
recurrence and the nonvanishing logarithmic denominators. -/
theorem differentiableAt_inverseOrbitTangent_spatial (v : ℂ)
    (hv : 64 ≤ (inverseCoordinate v).re) (k : ℕ) :
    DifferentiableAt ℂ (fun u => inverseOrbitTangent u k) v := by
  induction k with
  | zero =>
    convert (differentiableAt_const (0 : ℂ)) using 1 <;> rfl
  | succ k ih =>
    have ho := differentiableAt_inverseOrbit_zero_spatial v hv k
    have hn := zero_inverseOrbit_norm_lt_one v hv k
    have hslit : 1 - inverseOrbit v 0 k ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      simp only [Complex.sub_re, Complex.one_re]
      linarith [Complex.re_le_norm (inverseOrbit v 0 k)]
    have h := ((ih.div ((differentiableAt_const (1 : ℂ)).sub ho)
      (Complex.slitPlane_ne_zero hslit)).add
        (differentiableAt_inverseOrbit_zero_spatial v hv (k + 1))).sub_const 1
    convert h using 1 <;> rfl

theorem exists_deep_explicitTerm_differentiable
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) (hΓ : AnalyticAt ℂ Γ 0)
    (hEven : ∀ x v, Γ (-x, v) = Γ (x, v)) :
    ∃ R : ℝ, 64 ≤ R ∧ ∀ v : ℂ, R ≤ (inverseCoordinate v).re →
      ∀ k : ℕ, DifferentiableAt ℂ (fun u => explicitTerm A B Γ u k) v := by
  have hp := PreparedCoefficientSpatialHolomorphy.analyticAt_parameterPartial hA hB hΓ hEven
  have hw := PreparedCoefficientSpatialHolomorphy.analyticAt_spatialPartial hA hB hΓ
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp
    (hp.eventually_analyticAt.and hw.eventually_analyticAt)
  refine ⟨max 64 (4 / η), le_max_left _ _, ?_⟩
  intro v hv k
  have h64 : 64 ≤ (inverseCoordinate v).re := (le_max_left _ _).trans hv
  have hηR : 4 / η ≤ (inverseCoordinate v).re := (le_max_right _ _).trans hv
  have hr := PerturbedExponentialOrbit.parameterRadius_pos ‖inverseCoordinate v‖
    (norm_nonneg _) (k + 1)
  have hnorm := finite_inverseOrbit_norm_bound v 0 (inverseCoordinate v).re h64 (le_refl _)
    (k + 1) (by simpa only [norm_zero] using hr.le) (k + 1) (le_refl _)
  have hden : 0 < (inverseCoordinate v).re + ((k + 1 : ℕ) : ℝ) / 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) (k + 1)]
  have hmul : 4 ≤ (inverseCoordinate v).re * η := (div_le_iff₀ hη).mp hηR
  have hsmall : ‖-inverseOrbit v 0 (k + 1)‖ < η := by
    rw [norm_neg]
    apply hnorm.trans_lt
    apply (div_lt_iff₀ hden).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) (k + 1)]
  obtain ⟨hpa, hwa⟩ := hball (by simpa only [dist_zero_right] using hsmall)
  have ho := (differentiableAt_inverseOrbit_zero_spatial v h64 (k + 1)).neg
  have ht := (differentiableAt_inverseOrbitTangent_spatial v h64 (k + 1)).neg
  have h := (hpa.differentiableAt.comp v ho).add
    ((hwa.differentiableAt.comp v ho).mul ht)
  convert h using 1 <;> rfl

/-- The reflected coefficient is genuinely spatially holomorphic and
continuous; its explicit shifted series has a common summable majorant. -/
theorem exists_holomorphic_actualInversePreparedCoefficient
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (he₁ : AnalyticAt ℂ e₁ 0) (he₂ : AnalyticAt ℂ e₂ 0)
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    (hΓ : AnalyticAt ℂ Γ 0) (hEven : ∀ x v, Γ (-x, v) = Γ (x, v)) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ Z : ℝ, 0 ≤ Z →
      ∃ CD : ℝ, 0 ≤ CD ∧
        (∀ v ∈ boundedPetal R Z, ∀ k,
          ‖explicitTerm A B Γ v k‖ ≤ CD / ((k : ℝ) + 1) ^ 2) ∧
        DifferentiableOn ℂ (actualInversePreparedCoefficient U H e₁ e₂ A B Γ)
          (boundedPetal R Z) ∧
        ContinuousOn (actualInversePreparedCoefficient U H e₁ e₂ A B Γ)
          (boundedPetal R Z) ∧
        (∀ v ∈ boundedPetal R Z, ContinuousAt
          (actualInversePreparedCoefficient U H e₁ e₂ A B Γ) v) ∧
        TendstoUniformlyOn
          (fun J : ℕ => fun v => ∑ k ∈ Finset.range J, explicitTerm A B Γ v k)
          (fun v => ∑' k : ℕ, explicitTerm A B Γ v k) atTop (boundedPetal R Z) ∧
        ∀ v ∈ boundedPetal R Z, Summable (fun k => ‖explicitTerm A B Γ v k‖) := by
  obtain ⟨R₁, hR₁, hterms⟩ := exists_deep_explicitTerm_differentiable A B Γ hA hB hΓ hEven
  obtain ⟨R₂, hR₂, hchain⟩ := ReflectedOrbitChainCoefficient.exists_deep_petal_chain_identity
    A B Γ hA hB hΓ hEven
  obtain ⟨R₃, hR₃, hdiscs⟩ := exists_uniform_prepared_orbit_disc_bounds A B Γ 2
    hA hB hA0 hB0 hΓ hEven
  let R₀ : ℝ := max R₁ (max R₂ R₃)
  have hR₀ : 0 < R₀ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR Z hZ
  have hRR₁ : R₁ ≤ R := (le_max_left _ _).trans hR
  have hRR₂ : R₂ ≤ R := ((le_max_left _ _).trans (le_max_right _ _)).trans hR
  have hRR₃ : R₃ ≤ R := ((le_max_right _ _).trans (le_max_right _ _)).trans hR
  have hRpos : 0 < R := hR₀.trans_le hR
  obtain ⟨c, M, hc, hM, hcommon⟩ := hdiscs R hRR₃ Z hZ
  let CD : ℝ := M / (c / 4)
  have hCD : 0 ≤ CD := by dsimp [CD]; positivity
  have hchain' : ∀ v ∈ boundedPetal R Z, ∀ k,
      deriv (fun s => shiftedTerm A B Γ 2 v s k) 0 = explicitTerm A B Γ v k := by
    intro v hv
    exact hchain v (hRR₂.trans (by linarith [hv.1]))
  have hbound : ∀ k : ℕ, ∀ v ∈ boundedPetal R Z,
      ‖explicitTerm A B Γ v k‖ ≤ CD / ((k : ℝ) + 1) ^ 2 := by
    intro k v hv
    obtain ⟨hd, hb⟩ := hcommon v (by linarith [hv.1]) hv.2.le
    obtain ⟨hd', hb'⟩ := shifted_disc_bounds (descendedTerm A B Γ 2 v) c M hc hM hd hb
    rw [← hchain' v hv k]
    exact N2FirstOrderCutoff.norm_deriv_term_le (shiftedTerm A B Γ 2 v)
      (c / 4) M (by positivity) hd' hb' k
  have hdiff : ∀ k : ℕ, DifferentiableOn ℂ (fun v => explicitTerm A B Γ v k)
      (boundedPetal R Z) := by
    intro k v hv
    exact (hterms v (hRR₁.trans (by linarith [hv.1])) k).differentiableWithinAt
  have hsum := Complex.differentiableOn_tsum_of_summable_norm
    (summable_parabolic_majorant CD (by norm_num : 2 ≤ (2 : ℕ))) hdiff
    (boundedPetal_isOpen hRpos) hbound
  have hmodel : DifferentiableOn ℂ
      (fun v => deriv (fun s => preparedModelTime (-U) (-H) e₁ (-e₂) s v) 0)
      (boundedPetal R Z) := by
    intro v hv
    have hp : 0 < (inverseCoordinate v).re := by linarith [hv.1]
    have hneg : v.re < 0 := by
      simpa only [Complex.neg_re, neg_pos] using
        ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos hp
    exact (PreparedCoefficientSpatialHolomorphy.analyticAt_preparedModelTime_parameterDerivative
      hU.neg (by simp only [Pi.neg_apply, hU0, neg_zero]) hH.neg
      (by simpa only [Pi.neg_apply, neg_ne_zero] using hHne) he₁ he₂.neg v hneg).differentiableAt.differentiableWithinAt
  have hfull : DifferentiableOn ℂ (actualInversePreparedCoefficient U H e₁ e₂ A B Γ)
      (boundedPetal R Z) := by
    apply (hmodel.add hsum).congr
    intro v hv
    exact coefficient_eq_explicit_series U H e₁ e₂ A B Γ v (hchain' v hv)
  have huni := tendstoUniformlyOn_tsum
    (summable_parabolic_majorant CD (by norm_num : 2 ≤ (2 : ℕ))) hbound
  refine ⟨CD, hCD, (fun v hv k => hbound k v hv), hfull, hfull.continuousOn, ?_, ?_, ?_⟩
  · intro v hv
    exact (hfull.differentiableAt ((boundedPetal_isOpen hRpos).mem_nhds hv)).continuousAt
  · intro v hv
    exact (tendsto_finset_range : Tendsto Finset.range atTop atTop).eventually (huni v hv)
  · intro v hv
    exact summable_norm_of_parabolic_bound _ CD (q := 2) (by norm_num)
      (fun k => hbound k v hv)

end Kneser.ReflectedCoefficientSpatialHolomorphy

end
