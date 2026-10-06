import Kneser.UniformModelTime
import Kneser.ActualOrbitChainCoefficient
import Kneser.PreparedSpatialHolomorphy

/-!
Spatial holomorphy of the actual first parameter coefficient.  The
parameter partial is a genuine joint second splitting-variable derivative;
the actual orbit tangents are entire and the coefficient series has a
common summable majorant on each bounded deep petal.
-/

noncomputable section

namespace Kneser.PreparedCoefficientSpatialHolomorphy

open Filter Set Metric Kneser.ExponentialUnfolding
open Kneser.ExponentialRootPolynomial Kneser.ExponentialModelTime
open Kneser.ExponentialPreparedModel Kneser.ParabolicExponentialOrbit
open Kneser.PreparedSpatialHolomorphy Kneser.EvenPreparedOrbitDiscs
open Kneser.ActualOrbitChainCoefficient Kneser.JointAnalyticDivision
open scoped Topology BigOperators

def secondFirstPartial (Q : Pair → ℂ) (p : Pair) : ℂ := partialFirst (partialFirst Q) p

theorem analyticAt_partialFirst_at {Q : Pair → ℂ} {p : Pair}
    (hQ : AnalyticAt ℂ Q p) : AnalyticAt ℂ (partialFirst Q) p :=
  ((ContinuousLinearMap.apply ℂ ℂ ((1 : ℂ), (0 : ℂ))).analyticAt _).comp hQ.fderiv

theorem analyticAt_secondFirstPartial {Q : Pair → ℂ} {p : Pair}
    (hQ : AnalyticAt ℂ Q p) : AnalyticAt ℂ (secondFirstPartial Q) p :=
  analyticAt_partialFirst_at (analyticAt_partialFirst_at hQ)

theorem hasDerivAt_firstPartial_curve {Q : Pair → ℂ} {x u : ℂ}
    (hQ : DifferentiableAt ℂ Q (x, u)) :
    HasDerivAt (fun z : ℂ => Q (z, u)) (partialFirst Q (x, u)) x := by
  have hc : HasDerivAt (fun z : ℂ => (z, u)) ((1 : ℂ), 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x u)
  exact hQ.hasFDerivAt.comp_hasDerivAt_of_eq x hc rfl

theorem iteratedDeriv_two_eq_secondFirstPartial {Q : Pair → ℂ} {u : ℂ}
    (hQ : AnalyticAt ℂ Q (0, u)) :
    iteratedDeriv 2 (fun x : ℂ => Q (x, u)) 0 = secondFirstPartial Q (0, u) := by
  have ht : Tendsto (fun x : ℂ => (x, u)) (𝓝 0) (𝓝 ((0 : ℂ), u)) :=
    continuous_id.continuousAt.prodMk continuousAt_const |>.tendsto
  have heq : deriv (fun x : ℂ => Q (x, u)) =ᶠ[𝓝 0]
      (fun x => partialFirst Q (x, u)) := by
    filter_upwards [ht.eventually hQ.eventually_analyticAt] with x hx
    exact (hasDerivAt_firstPartial_curve hx.differentiableAt).deriv
  simp only [iteratedDeriv_succ', iteratedDeriv_zero]
  rw [heq.deriv_eq]
  exact (hasDerivAt_firstPartial_curve
    (analyticAt_partialFirst_at hQ).differentiableAt).deriv

theorem even_parameterDerivative_eq_secondFirstPartial {Q : Pair → ℂ} {u : ℂ}
    (hQ : AnalyticAt ℂ Q (0, u)) (hEven : ∀ x v, Q (-x, v) = Q (x, v)) :
    deriv (fun s : ℂ => Q (Complex.sqrt s, u)) 0 = secondFirstPartial Q (0, u) / 2 := by
  have ha : AnalyticAt ℂ (fun x : ℂ => Q (x, u)) 0 :=
    hQ.comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
  rw [EvenDescentChainRule.deriv_even_descent ha (fun x => hEven x u),
    iteratedDeriv_two_eq_secondFirstPartial hQ]

/-- The actual descended parameter derivative is spatially analytic;
joint holomorphy in the descended parameter is not an input. -/
theorem analyticAt_even_parameterDerivative {Q : Pair → ℂ} {u : ℂ}
    (hQ : AnalyticAt ℂ Q (0, u)) (hEven : ∀ x v, Q (-x, v) = Q (x, v)) :
    AnalyticAt ℂ (fun v => deriv (fun s : ℂ => Q (Complex.sqrt s, v)) 0) u := by
  have hpart : AnalyticAt ℂ (fun v => secondFirstPartial Q (0, v) / 2) u :=
    ((analyticAt_secondFirstPartial hQ).comp_of_eq
      (f := fun v : ℂ => (0, v)) (analyticAt_const.prod analyticAt_id) rfl).div_const
  have ht : Tendsto (fun v : ℂ => (0, v)) (𝓝 u) (𝓝 ((0 : ℂ), u)) :=
    continuousAt_const.prodMk continuous_id.continuousAt |>.tendsto
  have heq : (fun v => secondFirstPartial Q (0, v) / 2) =ᶠ[𝓝 u]
      (fun v => deriv (fun s : ℂ => Q (Complex.sqrt s, v)) 0) := by
    filter_upwards [ht.eventually hQ.eventually_analyticAt] with v hv
    exact (even_parameterDerivative_eq_secondFirstPartial hv hEven).symm
  exact hpart.congr heq

theorem analyticAt_preparedModelTime_parameterDerivative {U H e₁ e₂ : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (he₁ : AnalyticAt ℂ e₁ 0) (he₂ : AnalyticAt ℂ e₂ 0)
    (u : ℂ) (hu : u.re < 0) :
    AnalyticAt ℂ (fun v => deriv (fun s => preparedModelTime U H e₁ e₂ s v) 0) u := by
  simpa only [UniformModelTime.splitModel_sqrt] using
    analyticAt_even_parameterDerivative
      (UniformModelTime.analyticAt_splitModel hU hU0 hH hHne he₁ he₂ u hu)
      (UniformModelTime.splitModel_even U H e₁ e₂)

theorem analyticAt_parameterPartial {A B : ℂ → ℂ} {Γ : Pair → ℂ}
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) (hΓ : AnalyticAt ℂ Γ 0)
    (hEven : ∀ x v, Γ (-x, v) = Γ (x, v)) :
    AnalyticAt ℂ (parameterPartial A B Γ) 0 := by
  exact analyticAt_even_parameterDerivative
    (analyticAt_splitResidual A B Γ 0 hA hB hΓ)
    (fun x v => by simp [splitResidual, neg_sq, hEven])

theorem analyticAt_spatialPartial {A B : ℂ → ℂ} {Γ : Pair → ℂ}
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) (hΓ : AnalyticAt ℂ Γ 0) :
    AnalyticAt ℂ (spatialPartial A B Γ) 0 := by
  have hq : AnalyticAt ℂ (fun u => splitResidual A B Γ (0, u)) 0 :=
    (analyticAt_splitResidual A B Γ 0 hA hB hΓ).comp_of_eq
      (f := fun u : ℂ => (0, u)) (analyticAt_const.prod analyticAt_id) rfl
  exact hq.deriv

/-- The genuine parameter tangent is an entire function of the initial point. -/
theorem differentiable_orbitTangent_spatial (k : ℕ) :
    Differentiable ℂ (fun u => orbitTangent u k) := by
  induction k with
  | zero =>
    convert (differentiable_const (0 : ℂ)) using 1 <;> rfl
  | succ k ih =>
    have ho := differentiable_orbit_spatial (0 : ℂ) k
    have h := (ho.cexp.mul ih).sub ((ho.const_add 1).mul ho.cexp)
    convert h using 1 <;> rfl

theorem exists_deep_explicitTerm_differentiable
    (A B : ℂ → ℂ) (Γ : Pair → ℂ)
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) (hΓ : AnalyticAt ℂ Γ 0)
    (hEven : ∀ x v, Γ (-x, v) = Γ (x, v)) :
    ∃ R : ℝ, 32 ≤ R ∧ ∀ u : ℂ, R ≤ (inverseCoordinate u).re →
      ∀ k : ℕ, DifferentiableAt ℂ (fun v => explicitTerm A B Γ v k) u := by
  have hp := analyticAt_parameterPartial hA hB hΓ hEven
  have hv := analyticAt_spatialPartial hA hB hΓ
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp
    (hp.eventually_analyticAt.and hv.eventually_analyticAt)
  refine ⟨max 32 (4 / η), le_max_left _ _, ?_⟩
  intro u hu k
  have h32 : 32 ≤ (inverseCoordinate u).re := (le_max_left _ _).trans hu
  have hηR : 4 / η ≤ (inverseCoordinate u).re := (le_max_right _ _).trans hu
  have hnorm := iterate_norm_bound u h32 k
  have hord : orbit u 0 k = (parabolicMap^[k]) u := unfolding_orbit_zero_eq_iterate u k
  have hden : 0 < (inverseCoordinate u).re + (k : ℝ) / 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hmul : 4 ≤ (inverseCoordinate u).re * η := (div_le_iff₀ hη).mp hηR
  have hsmall : ‖orbit u 0 k‖ < η := by
    rw [hord]
    apply hnorm.trans_lt
    apply (div_lt_iff₀ hden).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  obtain ⟨hpa, hva⟩ := hball (by simpa only [dist_zero_right] using hsmall)
  have ho := (differentiable_orbit_spatial (0 : ℂ) k).differentiableAt (x := u)
  have h := (hpa.differentiableAt.comp u ho).add
    ((hva.differentiableAt.comp u ho).mul
      (differentiable_orbitTangent_spatial k).differentiableAt)
  convert h using 1 <;> rfl

/-- The entire actual first-order coefficient is holomorphic and continuous
on every bounded deep petal. Its explicit orbit sum converges uniformly
there under a constructed common `k⁻²` bound. -/
theorem exists_holomorphic_actualPreparedCoefficient
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : Pair → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (he₁ : AnalyticAt ℂ e₁ 0) (he₂ : AnalyticAt ℂ e₂ 0)
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    (hΓ : AnalyticAt ℂ Γ 0) (hEven : ∀ x v, Γ (-x, v) = Γ (x, v)) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ Z : ℝ, 0 ≤ Z →
      ∃ CD : ℝ, 0 ≤ CD ∧
        (∀ u ∈ boundedPetal R Z, ∀ k,
          ‖explicitTerm A B Γ u k‖ ≤ CD / ((k : ℝ) + 1) ^ 2) ∧
        DifferentiableOn ℂ
          (PreparedActualFirstOrder.actualPreparedCoefficient U H e₁ e₂ A B Γ)
          (boundedPetal R Z) ∧
        ContinuousOn
          (PreparedActualFirstOrder.actualPreparedCoefficient U H e₁ e₂ A B Γ)
          (boundedPetal R Z) ∧
        (∀ u ∈ boundedPetal R Z, ContinuousAt
          (PreparedActualFirstOrder.actualPreparedCoefficient U H e₁ e₂ A B Γ) u) ∧
        TendstoUniformlyOn
          (fun J : ℕ => fun u => ∑ k ∈ Finset.range J, explicitTerm A B Γ u k)
          (fun u => ∑' k : ℕ, explicitTerm A B Γ u k) atTop (boundedPetal R Z) ∧
        ∀ u ∈ boundedPetal R Z, Summable (fun k => ‖explicitTerm A B Γ u k‖) := by
  obtain ⟨R₁, hR₁, hterms⟩ := exists_deep_explicitTerm_differentiable A B Γ hA hB hΓ hEven
  obtain ⟨R₂, hR₂, hchain⟩ := exists_deep_petal_chain_identity A B Γ hA hB hΓ hEven
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
  let CD : ℝ := M / c
  have hCD : 0 ≤ CD := div_nonneg hM hc.le
  have hchain' : ∀ u ∈ boundedPetal R Z, ∀ k,
      deriv (fun s => descendedTerm A B Γ 2 u s k) 0 = explicitTerm A B Γ u k := by
    intro u hu
    exact hchain u (hRR₂.trans (by linarith [hu.1]))
  have hbound : ∀ k : ℕ, ∀ u ∈ boundedPetal R Z,
      ‖explicitTerm A B Γ u k‖ ≤ CD / ((k : ℝ) + 1) ^ 2 := by
    intro k u hu
    obtain ⟨hd, hb⟩ := hcommon u (by linarith [hu.1]) hu.2.le
    rw [← hchain' u hu k]
    exact N2FirstOrderCutoff.norm_deriv_term_le (descendedTerm A B Γ 2 u) c M hc hd hb k
  have hdiff : ∀ k : ℕ, DifferentiableOn ℂ (fun u => explicitTerm A B Γ u k)
      (boundedPetal R Z) := by
    intro k u hu
    exact (hterms u (hRR₁.trans (by linarith [hu.1])) k).differentiableWithinAt
  have hsum := Complex.differentiableOn_tsum_of_summable_norm
    (summable_parabolic_majorant CD (by norm_num : 2 ≤ (2 : ℕ))) hdiff
    (boundedPetal_isOpen hRpos) hbound
  have hmodel : DifferentiableOn ℂ
      (fun u => deriv (fun s => preparedModelTime U H e₁ e₂ s u) 0)
      (boundedPetal R Z) := by
    intro u hu
    have hp : 0 < (inverseCoordinate u).re := by linarith [hu.1]
    have hneg : u.re < 0 := by
      simpa only [Complex.neg_re, neg_pos] using
        ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos hp
    exact (analyticAt_preparedModelTime_parameterDerivative hU hU0 hH hHne he₁ he₂ u hneg).differentiableAt.differentiableWithinAt
  have hfull : DifferentiableOn ℂ
      (PreparedActualFirstOrder.actualPreparedCoefficient U H e₁ e₂ A B Γ)
      (boundedPetal R Z) := by
    apply (hmodel.add hsum).congr
    intro u hu
    exact coefficient_eq_explicit_series U H e₁ e₂ A B Γ u (hchain' u hu)
  have huni := tendstoUniformlyOn_tsum
    (summable_parabolic_majorant CD (by norm_num : 2 ≤ (2 : ℕ))) hbound
  refine ⟨CD, hCD, (fun u hu k => hbound k u hu), hfull, hfull.continuousOn, ?_, ?_, ?_⟩
  · intro u hu
    exact (hfull.differentiableAt ((boundedPetal_isOpen hRpos).mem_nhds hu)).continuousAt
  · intro v hv
    exact (tendsto_finset_range : Tendsto Finset.range atTop atTop).eventually (huni v hv)
  · intro u hu
    exact summable_norm_of_parabolic_bound _ CD (q := 2) (by norm_num)
      (fun k => hbound k u hu)

end Kneser.PreparedCoefficientSpatialHolomorphy

end
