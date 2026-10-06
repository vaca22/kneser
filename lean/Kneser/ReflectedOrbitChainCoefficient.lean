import Kneser.UniformRepellingFirstOrder
import Kneser.ActualOrbitChainCoefficient

/-!
The genuine parameter tangent of the reflected inverse orbit gives the
explicit parameter-plus-spatial coefficient of each prepared residual term.
-/

noncomputable section

namespace Kneser.ReflectedOrbitChainCoefficient

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ExponentialRootPolynomial
open Kneser.ParabolicExponentialOrbit Kneser.RepellingExponentialOrbit
open Kneser.ReflectedPreparedFirstOrder Kneser.ActualOrbitChainCoefficient
open Kneser.UniformRepellingFirstOrder
open scoped Topology

/-- This recurrence is the true inverse-orbit parameter tangent at zero. -/
def inverseOrbitTangent (v : ℂ) : ℕ → ℂ
  | 0 => 0
  | k + 1 => inverseOrbitTangent v k / (1 - inverseOrbit v 0 k) +
      inverseOrbit v 0 (k + 1) - 1

theorem hasDerivAt_reflectedInverse_curve {w : ℂ → ℂ} {w' : ℂ}
    (hw : HasDerivAt w w' 0) (hn : ‖w 0‖ < 1) :
    HasDerivAt (fun s => reflectedInverse s (w s))
      (w' / (1 - w 0) + reflectedInverse 0 (w 0) - 1) 0 := by
  have hslit : 1 - w 0 ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Complex.sub_re, Complex.one_re]
    linarith [Complex.re_le_norm (w 0)]
  have hden : 1 - w 0 ≠ 0 := Complex.slitPlane_ne_zero hslit
  have hnum := (((hasDerivAt_const 0 (1 : ℂ)).sub hw).clog hslit |>.add
    (hasDerivAt_id (0 : ℂ))).neg
  have hd := hnum.div ((hasDerivAt_const 0 (1 : ℂ)).sub (hasDerivAt_id 0)) (by norm_num)
  change HasDerivAt (fun s => reflectedInverse s (w s))
    ((-((0 - w') / (1 - w 0) + 1) * (1 - 0) -
      (-(Complex.log (1 - w 0) + 0)) * (0 - 1)) / (1 - 0) ^ 2) 0 at hd
  convert hd using 1
  simp [reflectedInverse]
  ring

theorem hasDerivAt_inverseOrbit_parameter_zero (v : ℂ)
    (hv : 64 ≤ (inverseCoordinate v).re) (k : ℕ) :
    HasDerivAt (fun s => inverseOrbit v s k) (inverseOrbitTangent v k) 0 := by
  induction k with
  | zero => exact hasDerivAt_const 0 v
  | succ k ih =>
    have hr := PerturbedExponentialOrbit.parameterRadius_pos ‖inverseCoordinate v‖ (norm_nonneg _) k
    have hn := finite_inverseOrbit_norm_bound v 0 64 (le_refl _) hv k
      (by simpa only [norm_zero] using hr.le) k (le_refl k)
    have hnorm : ‖inverseOrbit v 0 k‖ < 1 := by
      apply hn.trans_lt
      apply (div_lt_iff₀ (by linarith [Nat.cast_nonneg (α := ℝ) k] :
        0 < 64 + (k : ℝ) / 2)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) k]
    have h := hasDerivAt_reflectedInverse_curve ih hnorm
    simpa only [← inverseOrbit_succ, inverseOrbitTangent] using h

theorem deriv_inverseOrbit_parameter_zero (v : ℂ)
    (hv : 64 ≤ (inverseCoordinate v).re) (k : ℕ) :
    deriv (fun s => inverseOrbit v s k) 0 = inverseOrbitTangent v k :=
  (hasDerivAt_inverseOrbit_parameter_zero v hv k).deriv

theorem analyticAt_inverseOrbit_parameter_zero (v : ℂ)
    (hv : 64 ≤ (inverseCoordinate v).re) (k : ℕ) :
    AnalyticAt ℂ (fun s => inverseOrbit v s k) 0 := by
  apply analyticAt_inverseOrbit_parameter v 0 64 ‖inverseCoordinate v‖
    (le_refl _) hv (le_refl _) k
    (by simpa only [norm_zero] using
      PerturbedExponentialOrbit.parameterRadius_pos ‖inverseCoordinate v‖ (norm_nonneg _) k)
    k (le_refl k)

theorem inverseOrbitTangent_bound (v : ℂ) (R Z : ℝ) (hR : 64 ≤ R)
    (hv : R ≤ (inverseCoordinate v).re) (hZ : ‖inverseCoordinate v‖ ≤ Z) (k : ℕ) :
    ‖inverseOrbitTangent v k‖ ≤ 384 * (Z + 2) ^ 2 * ((k : ℝ) + 1) := by
  rw [← deriv_inverseOrbit_parameter_zero v (hR.trans hv)]
  exact inverseOrbit_parameter_derivative_bound v R Z hR hv hZ k

def explicitTerm (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (v : ℂ) (k : ℕ) : ℂ :=
  parameterPartial A B Γ (-inverseOrbit v 0 (k + 1)) +
    spatialPartial A B Γ (-inverseOrbit v 0 (k + 1)) * -inverseOrbitTangent v (k + 1)

/-- The shift by one is the actual inverse-step residual, and its spatial
tangent carries the reflection sign. -/
theorem actual_prepared_inverse_orbit_derivative (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0)
    (hEven : ∀ x v, Γ (-x, v) = Γ (x, v)) (v : ℂ) (k : ℕ)
    (hv : 64 ≤ (inverseCoordinate v).re)
    (hΓ : AnalyticAt ℂ Γ (0, -inverseOrbit v 0 (k + 1))) :
    deriv (fun s => shiftedTerm A B Γ 2 v s k) 0 = explicitTerm A B Γ v k := by
  have h := EvenDescentChainRule.deriv_even_descent_curve
    (analyticAt_splitResidual A B Γ (-inverseOrbit v 0 (k + 1)) hA hB hΓ)
    (splitResidual_even A B Γ hEven)
    (analyticAt_inverseOrbit_parameter_zero v hv (k + 1)).neg
  have hd := (hasDerivAt_inverseOrbit_parameter_zero v hv (k + 1)).neg.deriv
  simpa only [shiftedTerm, ReflectedEvenOrbitDiscs.descendedTerm,
    ReflectedEvenOrbitDiscs.splitTerm, splitResidual, AnalyticEvenDescent.square_sqrt,
    parameterPartial, spatialPartial, explicitTerm, Pi.neg_apply, hd] using h

/-- Joint analytic preparation applies along every actual inverse orbit
once the initial point lies in a sufficiently deep petal. -/
theorem exists_deep_petal_chain_identity (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) (hΓ : AnalyticAt ℂ Γ 0)
    (hEven : ∀ x v, Γ (-x, v) = Γ (x, v)) :
    ∃ R : ℝ, 64 ≤ R ∧ ∀ v : ℂ, R ≤ (inverseCoordinate v).re →
      ∀ k : ℕ, deriv (fun s => shiftedTerm A B Γ 2 v s k) 0 = explicitTerm A B Γ v k := by
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp hΓ.eventually_analyticAt
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
  apply actual_prepared_inverse_orbit_derivative A B Γ hA hB hEven v k h64
  apply hball (y := ((0 : ℂ), -inverseOrbit v 0 (k + 1)))
  simpa only [dist_zero_right, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] using hsmall

theorem coefficient_eq_explicit_series (U H e₁ e₂ A B : ℂ → ℂ)
    (Γ : ℂ × ℂ → ℂ) (v : ℂ)
    (hchain : ∀ k, deriv (fun s => shiftedTerm A B Γ 2 v s k) 0 = explicitTerm A B Γ v k) :
    actualInversePreparedCoefficient U H e₁ e₂ A B Γ v =
      deriv (fun s => ExponentialModelTime.preparedModelTime (-U) (-H) e₁ (-e₂) s v) 0 +
        ∑' k : ℕ, explicitTerm A B Γ v k := by
  exact congrArg (fun z =>
    deriv (fun s => ExponentialModelTime.preparedModelTime (-U) (-H) e₁ (-e₂) s v) 0 + z)
    (tsum_congr hchain)

theorem summable_norm_explicitTerm (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (v : ℂ)
    (hchain : ∀ k, deriv (fun s => shiftedTerm A B Γ 2 v s k) 0 = explicitTerm A B Γ v k)
    (hsum : Summable (fun k => ‖deriv (fun s => shiftedTerm A B Γ 2 v s k) 0‖)) :
    Summable (fun k => ‖explicitTerm A B Γ v k‖) := by
  simpa only [hchain] using hsum

theorem parameterPartial_eq_second (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (v : ℂ)
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0)
    (hΓ : AnalyticAt ℂ Γ (0, v)) (hEven : ∀ x w, Γ (-x, w) = Γ (x, w)) :
    parameterPartial A B Γ v =
      iteratedDeriv 2 (fun x => splitResidual A B Γ (x, v)) 0 / 2 := by
  exact EvenDescentChainRule.deriv_even_descent
    ((analyticAt_splitResidual A B Γ v hA hB hΓ).comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl)
    (fun x => splitResidual_even A B Γ hEven (x, v))

def explicitCoefficient (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (v : ℂ) : ℂ :=
  deriv (fun s => ExponentialModelTime.preparedModelTime (-U) (-H) e₁ (-e₂) s v) 0 +
    ∑' k : ℕ, explicitTerm A B Γ v k

/-- All compact uniform conclusions use the displayed explicit series,
whose spatial terms contain the actual inverse-orbit tangent recurrence. -/
def ExplicitCompactFirstOrder (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R₀ : ℝ) : Prop :=
  ∀ S : Set ℂ, IsCompact S → (∀ v ∈ S, R₀ + 1 ≤ (inverseCoordinate v).re) →
    ∃ C CD : ℝ, 0 ≤ C ∧ 0 ≤ CD ∧
      (∀ v ∈ S, ∀ k, ‖explicitTerm A B Γ v k‖ ≤ CD / ((k : ℝ) + 1) ^ 2) ∧
      (∀ v ∈ S, Summable (fun k => ‖explicitTerm A B Γ v k‖)) ∧
      (∀ v ∈ S, actualInversePreparedCoefficient U H e₁ e₂ A B Γ v =
        explicitCoefficient U H e₁ e₂ A B Γ v) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0, ∀ v ∈ S,
        ‖actualInversePreparedCoordinate U H e₁ e₂ A B Γ v s -
          actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0 -
          s • explicitCoefficient U H e₁ e₂ A B Γ v‖ ≤ C * s ^ (6 / 5 : ℝ)) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0, ∀ v ∈ S,
        ‖actualInversePreparedCoordinate U H e₁ e₂ A B Γ v s -
          actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0 -
          s • explicitCoefficient U H e₁ e₂ A B Γ v‖ ≤ C * s ^ (10 / 9 : ℝ)) ∧
      ∀ v ∈ S, HasDerivWithinAt (actualInversePreparedCoordinate U H e₁ e₂ A B Γ v)
        (explicitCoefficient U H e₁ e₂ A B Γ v) (Ici 0) 0

theorem explicit_compact_first_order_of_chain (U H e₁ e₂ A B : ℂ → ℂ)
    (Γ : ℂ × ℂ → ℂ) (R : ℝ)
    (hcompact : CompactFirstOrder U H e₁ e₂ A B Γ R)
    (hchain : ∀ v, R + 1 ≤ (inverseCoordinate v).re → ∀ k,
      deriv (fun s => shiftedTerm A B Γ 2 v s k) 0 = explicitTerm A B Γ v k) :
    ExplicitCompactFirstOrder U H e₁ e₂ A B Γ R := by
  intro S hS hpetal
  obtain ⟨C, CD, hC, hCD, hb, hsum, he, he', hd⟩ := hcompact S hS hpetal
  have hcoef : ∀ v ∈ S, actualInversePreparedCoefficient U H e₁ e₂ A B Γ v =
      explicitCoefficient U H e₁ e₂ A B Γ v := by
    intro v hv
    exact coefficient_eq_explicit_series U H e₁ e₂ A B Γ v (hchain v (hpetal v hv))
  refine ⟨C, CD, hC, hCD, ?_, ?_, hcoef, ?_, ?_, ?_⟩
  · intro v hv k
    rw [← hchain v (hpetal v hv) k]
    exact hb v hv k
  · intro v hv
    exact summable_norm_explicitTerm A B Γ v (hchain v (hpetal v hv)) (hsum v hv)
  · filter_upwards [he] with s hs v hv
    rw [← hcoef v hv]
    exact hs v hv
  · filter_upwards [he'] with s hs v hv
    rw [← hcoef v hv]
    exact hs v hv
  · intro v hv
    rw [← hcoef v hv]
    exact hd v hv

/-- Exact actual preparation identities retained by the explicit compact
certificate, including the nonzero root-branch derivative. -/
def ActualPreparationData (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ)
    (F Γ : ℂ × ℂ → ℂ) : Prop :=
  AnalyticAt ℂ U 0 ∧ U 0 = 0 ∧ deriv U 0 ≠ 0 ∧
  AnalyticAt ℂ H 0 ∧ H 0 ≠ 0 ∧
  (∀ x, Complex.log (ExponentialPreparedModel.rootMultiplier U x) = x * H x) ∧
  AnalyticAt ℂ A 0 ∧ AnalyticAt ℂ B 0 ∧ A 0 = 0 ∧ B 0 = 0 ∧
  AnalyticAt ℂ e₁ 0 ∧ AnalyticAt ℂ e₂ 0 ∧ AnalyticAt ℂ F 0 ∧ AnalyticAt ℂ Γ 0 ∧
  (∀ p : ℂ × ℂ, Γ (-p.1, p.2) = Γ p) ∧
  K 0 0 = 1 / 2 ∧ ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0 ∧
  (∀ x u, rootPolynomial A B (x ^ 2) u = (u - U x) * (u - U (-x))) ∧
  (∀ᶠ x in 𝓝 (0 : ℂ), unfolding (x ^ 2) (U x) = U x ∧
    unfolding (x ^ 2) (U (-x)) = U (-x)) ∧
  (∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
    unfolding s u - u = rootPolynomial A B s u * K s u) ∧
  (∀ᶠ p in 𝓝 (0 : ℂ × ℂ),
    F p + ExponentialPreparedModel.polynomialCorrection e₁ e₂ (p.1 ^ 2)
        (unfolding (p.1 ^ 2) p.2) -
      ExponentialPreparedModel.polynomialCorrection e₁ e₂ (p.1 ^ 2) p.2 =
        rootPolynomial A B (p.1 ^ 2) p.2 ^ 2 * Γ p) ∧
  (∀ᶠ p in 𝓝 (0 : ℂ × ℂ), p.1 ≠ 0 → F p =
    Complex.log (1 + (p.2 - U (-p.1)) * ExponentialMatrixDividedDifference.symmetricCofactor U p.1 p.2) /
      Complex.log (ExponentialPreparedModel.rootMultiplier U p.1) +
    Complex.log (1 + (p.2 - U p.1) * ExponentialMatrixDividedDifference.symmetricCofactor U p.1 p.2) /
      Complex.log (ExponentialPreparedModel.rootMultiplier U (-p.1)) - 1)

set_option maxHeartbeats 1000000 in
/-- The actual reflected coefficient is the absolutely convergent explicit
chain-rule series, with uniform first-order errors on every compact petal
set.  All actual preparation witnesses and identities are constructed. -/
theorem exists_actual_compact_repelling_explicit_coefficient :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      ActualPreparationData U H e₁ e₂ A B K F Γ ∧
      ∃ R₀ : ℝ, 0 < R₀ ∧ CompactFirstOrder U H e₁ e₂ A B Γ R₀ ∧
        (∀ v, R₀ + 1 ≤ (inverseCoordinate v).re → ∀ k,
          deriv (fun s => shiftedTerm A B Γ 2 v s k) 0 = explicitTerm A B Γ v k) ∧
        ExplicitCompactFirstOrder U H e₁ e₂ A B Γ R₀ := by
  obtain ⟨U, H, e₁, e₂, A, B, K, F, Γ, hU, hU0, hUd, hH, hHne, hHlog,
    hA, hB, hA0, hB0, he₁, he₂, hF, hΓ, hΓeven, hK0, hK, hq, hroots,
    hfactor, hprepared, hresidue, Rc, hRc, hcompact⟩ :=
    exists_actual_compact_repelling_first_order
  have hΓeven' : ∀ x v, Γ (-x, v) = Γ (x, v) := fun x v => hΓeven (x, v)
  obtain ⟨Rt, hRt, htangent⟩ := exists_deep_petal_chain_identity A B Γ hA hB hΓ hΓeven'
  let R₀ : ℝ := max Rc Rt
  have hR₀ : 0 < R₀ := hRc.trans_le (le_max_left _ _)
  have hcompact' : CompactFirstOrder U H e₁ e₂ A B Γ R₀ := by
    intro S hS hpetal
    apply hcompact S hS
    intro v hv
    have hle : Rc ≤ R₀ := le_max_left _ _
    linarith [hpetal v hv]
  have hchain : ∀ v, R₀ + 1 ≤ (inverseCoordinate v).re → ∀ k,
      deriv (fun s => shiftedTerm A B Γ 2 v s k) 0 = explicitTerm A B Γ v k := by
    intro v hv
    apply htangent v
    have hle : Rt ≤ R₀ := le_max_right _ _
    linarith
  refine ⟨U, H, e₁, e₂, A, B, K, F, Γ, ?_, R₀, hR₀, hcompact', hchain,
    explicit_compact_first_order_of_chain U H e₁ e₂ A B Γ R₀ hcompact' hchain⟩
  exact ⟨hU, hU0, hUd, hH, hHne, hHlog, hA, hB, hA0, hB0, he₁, he₂,
    hF, hΓ, hΓeven, hK0, hK, hq, hroots, hfactor, hprepared, hresidue⟩

end Kneser.ReflectedOrbitChainCoefficient

end
