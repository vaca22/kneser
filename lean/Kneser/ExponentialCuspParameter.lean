import Kneser.ExponentialUnfolding
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# A concrete cusp parameter for the exponential unfolding

The multiplier parameter `t = λ - 1` gives actual fixed points of the
unfolding.  Taylor factorization proves the analytic double zero of its
parameter map; this is a concrete input to an analytic Morse coordinate.
-/

noncomputable section

namespace Kneser.ExponentialCuspParameter

open Kneser.ExponentialUnfolding
open Filter
open scoped Topology

/-- The unfolding parameter expressed through the multiplier `1+t`. -/
def cuspParameter (t : ℂ) : ℂ := 1 - (1 + t) * Complex.exp (-t)

/-- The corresponding fixed point in the spatial coordinate. -/
def fixedPoint (t : ℂ) : ℂ := Complex.exp t - 1

@[simp] theorem cuspParameter_zero : cuspParameter 0 = 0 := by
  simp [cuspParameter]

@[simp] theorem fixedPoint_zero : fixedPoint 0 = 0 := by
  simp [fixedPoint]

theorem exponential_pair (t : ℂ) : Complex.exp (-t) * Complex.exp t = 1 := by
  rw [← Complex.exp_add]
  simp

/-- The exponent at the parametrized fixed point is exactly `t`. -/
theorem exponent_at_fixedPoint (t : ℂ) :
    -cuspParameter t + (1 - cuspParameter t) * fixedPoint t = t := by
  unfold cuspParameter fixedPoint
  calc
    -(1 - (1 + t) * Complex.exp (-t)) +
        (1 - (1 - (1 + t) * Complex.exp (-t))) * (Complex.exp t - 1) =
        (1 + t) * (Complex.exp (-t) * Complex.exp t) - 1 := by ring
    _ = t := by rw [exponential_pair]; ring

/-- These are actual fixed points, rather than an assumed root parametrization. -/
theorem unfolding_fixedPoint (t : ℂ) :
    unfolding (cuspParameter t) (fixedPoint t) = fixedPoint t := by
  unfold unfolding
  rw [exponent_at_fixedPoint]
  rfl

/-- The spatial multiplier at the parametrized fixed point is exactly `1+t`. -/
theorem multiplier_at_fixedPoint (t : ℂ) :
    Complex.exp (-cuspParameter t +
      (1 - cuspParameter t) * fixedPoint t) * (1 - cuspParameter t) = 1 + t := by
  rw [exponent_at_fixedPoint]
  unfold cuspParameter
  calc
    Complex.exp t * (1 - (1 - (1 + t) * Complex.exp (-t))) =
      (1 + t) * (Complex.exp (-t) * Complex.exp t) := by ring
    _ = 1 + t := by rw [exponential_pair]; ring

theorem hasDerivAt_unfolding_fixedPoint (t : ℂ) :
    HasDerivAt (unfolding (cuspParameter t)) (1 + t) (fixedPoint t) := by
  simpa only [multiplier_at_fixedPoint] using
    hasDerivAt_unfolding_spatial (cuspParameter t) (fixedPoint t)

/-- The multiplier parametrization is an entire analytic function. -/
theorem analyticAt_cuspParameter (t : ℂ) : AnalyticAt ℂ cuspParameter t := by
  unfold cuspParameter
  fun_prop

theorem hasDerivAt_cuspParameter (t : ℂ) :
    HasDerivAt cuspParameter (t * Complex.exp (-t)) t := by
  have h := (((hasDerivAt_id t).const_add 1).mul
    (hasDerivAt_id t).neg.cexp).const_sub 1
  convert h using 1 <;> first | rfl | ((try dsimp [cuspParameter]); ring)

theorem deriv_cuspParameter : deriv cuspParameter = fun t => t * Complex.exp (-t) := by
  funext t
  exact (hasDerivAt_cuspParameter t).deriv

@[simp] theorem deriv_cuspParameter_zero : deriv cuspParameter 0 = 0 := by
  rw [deriv_cuspParameter]
  simp

theorem hasDerivAt_deriv_cuspParameter (t : ℂ) :
    HasDerivAt (deriv cuspParameter) ((1 - t) * Complex.exp (-t)) t := by
  rw [deriv_cuspParameter]
  convert ((hasDerivAt_id t).mul (hasDerivAt_id t).neg.cexp) using 1 <;>
    first | rfl | (dsimp; ring)

@[simp] theorem second_deriv_cuspParameter_zero :
    iteratedDeriv 2 cuspParameter 0 = 1 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  simpa using (hasDerivAt_deriv_cuspParameter 0).deriv

/-- The actual cusp parameter has a double zero with analytic leading factor `1/2`.
The factor and equality are constructed using analytic Taylor's theorem. -/
theorem exists_analytic_quadratic_factor :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ H 0 = 1 / 2 ∧
      ∀ t : ℂ, cuspParameter t = t ^ 2 * H t := by
  obtain ⟨R, hRa, hR⟩ := (analyticAt_cuspParameter 0).exists_eq_sum_add_pow_mul 3
  refine ⟨fun t => (1 / 2 : ℂ) + t * R t, ?_, ?_, ?_⟩
  · fun_prop
  · simp
  · intro t
    have ht := hR t
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      iteratedDeriv_zero, iteratedDeriv_one, cuspParameter_zero,
      deriv_cuspParameter_zero, second_deriv_cuspParameter_zero] at ht
    norm_num at ht
    simpa only [smul_eq_mul] using ht.trans (by ring)

/-- An actual analytic Morse coordinate and its analytic local inverse.
It resolves the double zero into the square parameter without assuming
Weierstrass preparation or an already constructed root family. -/
theorem exists_analytic_morse_coordinate :
    ∃ X V : ℂ → ℂ, AnalyticAt ℂ X 0 ∧ AnalyticAt ℂ V 0 ∧
      X 0 = 0 ∧ V 0 = 0 ∧ deriv X 0 ≠ 0 ∧
      (∀ᶠ t in 𝓝 0, X t ^ 2 = cuspParameter t) ∧
      (∀ᶠ x in 𝓝 0, X (V x) = x) ∧
      (∀ᶠ t in 𝓝 0, V (X t) = t) ∧
      (∀ᶠ x in 𝓝 0, cuspParameter (V x) = x ^ 2) := by
  obtain ⟨H, hHa, hH0, hH⟩ := exists_analytic_quadratic_factor
  have hHslit : H 0 ∈ Complex.slitPlane := by
    rw [hH0, Complex.mem_slitPlane_iff]
    left
    norm_num
  let B : ℂ → ℂ := fun t => Complex.exp (Complex.log (H t) / 2)
  have hBa : AnalyticAt ℂ B 0 := by
    exact (hHa.clog hHslit).div_const.cexp
  let X : ℂ → ℂ := fun t => t * B t
  have hXa : AnalyticAt ℂ X 0 := analyticAt_id.mul hBa
  have hX0 : X 0 = 0 := by simp [X]
  have hXder : HasDerivAt X (B 0) 0 := by
    convert (hasDerivAt_id (0 : ℂ)).mul hBa.hasStrictDerivAt.hasDerivAt using 1 <;>
      first | rfl | simp
  have hXne : deriv X 0 ≠ 0 := by
    rw [hXder.deriv]
    exact Complex.exp_ne_zero _
  let V : ℂ → ℂ := hXa.hasStrictDerivAt.localInverse X (deriv X 0) 0 hXne
  have hVa : AnalyticAt ℂ V 0 := by
    simpa only [hX0] using hXa.analyticAt_localInverse hXne
  have hright : ∀ᶠ x in 𝓝 0, X (V x) = x := by
    simpa only [hX0] using hXa.hasStrictDerivAt.eventually_right_inverse hXne
  have hleft : ∀ᶠ t in 𝓝 0, V (X t) = t :=
    hXa.hasStrictDerivAt.eventually_left_inverse hXne
  have hV0 : V 0 = 0 := by
    simpa only [hX0] using hleft.self_of_nhds
  have hH0ne : H 0 ≠ 0 := by rw [hH0]; norm_num
  have hHne : ∀ᶠ t in 𝓝 0, H t ≠ 0 :=
    (hHa.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hH0ne
  have hsquare : ∀ᶠ t in 𝓝 0, X t ^ 2 = cuspParameter t := by
    filter_upwards [hHne] with t ht
    change (t * Complex.exp (Complex.log (H t) / 2)) ^ 2 = cuspParameter t
    rw [mul_pow, pow_two (Complex.exp _), ← Complex.exp_add]
    rw [show Complex.log (H t) / 2 + Complex.log (H t) / 2 =
      Complex.log (H t) by ring, Complex.exp_log ht, hH t]
  have hsquareV : ∀ᶠ x in 𝓝 0, X (V x) ^ 2 = cuspParameter (V x) :=
    (by simpa only [hV0] using hVa.continuousAt.tendsto :
      Tendsto V (𝓝 0) (𝓝 0)).eventually hsquare
  refine ⟨X, V, hXa, hVa, hX0, hV0, hXne, hsquare, hright, hleft, ?_⟩
  filter_upwards [hsquareV, hright] with x hx hx'
  rw [← hx, hx']

/-- The square parameter has a genuinely constructed analytic fixed-point branch.
Replacing `x` by `-x` gives the second branch at the same unfolding parameter. -/
theorem exists_analytic_fixedPoint_branch :
    ∃ U : ℂ → ℂ, AnalyticAt ℂ U 0 ∧ U 0 = 0 ∧
      (∀ᶠ x in 𝓝 0, unfolding (x ^ 2) (U x) = U x) := by
  obtain ⟨X, V, hXa, hVa, hX0, hV0, hXne, hsquare, hright, hleft, hsV⟩ :=
    exists_analytic_morse_coordinate
  refine ⟨fun x => fixedPoint (V x), ?_, ?_, ?_⟩
  · unfold fixedPoint
    exact hVa.cexp.sub analyticAt_const
  · change fixedPoint (V 0) = 0
    rw [hV0, fixedPoint_zero]
  · filter_upwards [hsV] with x hx
    rw [← hx]
    exact unfolding_fixedPoint (V x)

/-- The constructed fixed-point branch has a nonzero derivative and the two
branches at `x` and `-x` are locally distinct away from the cusp. -/
theorem exists_analytic_distinct_fixedPoint_branches :
    ∃ U : ℂ → ℂ, AnalyticAt ℂ U 0 ∧ U 0 = 0 ∧ deriv U 0 ≠ 0 ∧
      (∀ᶠ x in 𝓝 0, unfolding (x ^ 2) (U x) = U x) ∧
      (∀ᶠ x in 𝓝 0, U x = U (-x) ↔ x = 0) := by
  obtain ⟨X, V, hXa, hVa, hX0, hV0, hXne, hsquare, hright, hleft, hsV⟩ :=
    exists_analytic_morse_coordinate
  have hcomp : HasDerivAt (fun x => X (V x)) (deriv X 0 * deriv V 0) 0 := by
    have hx : HasDerivAt X (deriv X 0) (V 0) := by
      simpa only [hV0] using hXa.hasStrictDerivAt.hasDerivAt
    exact hx.comp 0 hVa.hasStrictDerivAt.hasDerivAt
  have hproduct : deriv X 0 * deriv V 0 = 1 := by
    have hrightEq : (fun x => X (V x)) =ᶠ[𝓝 0] id := hright
    rw [← hcomp.deriv, hrightEq.deriv_eq]
    exact (hasDerivAt_id (0 : ℂ)).deriv
  have hVne : deriv V 0 ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hproduct
    exact zero_ne_one hproduct
  let U : ℂ → ℂ := fun x => fixedPoint (V x)
  have hUa : AnalyticAt ℂ U 0 := hVa.cexp.sub analyticAt_const
  have hU0 : U 0 = 0 := by simp [U, hV0, fixedPoint]
  have hUder : HasDerivAt U (deriv V 0) 0 := by
    convert hVa.hasStrictDerivAt.hasDerivAt.cexp.sub_const 1 using 1 <;>
      first | rfl | (simp [hV0])
  have hUne : deriv U 0 ≠ 0 := by rwa [hUder.deriv]
  let W : ℂ → ℂ := hUa.hasStrictDerivAt.localInverse U (deriv U 0) 0 hUne
  have hWU : ∀ᶠ x in 𝓝 0, W (U x) = x :=
    hUa.hasStrictDerivAt.eventually_left_inverse hUne
  have hneg : Tendsto (fun x : ℂ => -x) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using continuous_neg.continuousAt.tendsto (x := (0 : ℂ))
  refine ⟨U, hUa, hU0, hUne, ?_, ?_⟩
  · filter_upwards [hsV] with x hx
    change unfolding (x ^ 2) (fixedPoint (V x)) = fixedPoint (V x)
    rw [← hx]
    exact unfolding_fixedPoint (V x)
  · filter_upwards [hWU, hneg.eventually hWU] with x hx hx'
    constructor
    · intro hu
      have heq : x = -x := calc
        x = W (U x) := hx.symm
        _ = W (U (-x)) := congrArg W hu
        _ = -x := hx'
      exact CharZero.eq_neg_self_iff.mp heq
    · intro hx0
      simp only [hx0, neg_zero]

end Kneser.ExponentialCuspParameter

end
