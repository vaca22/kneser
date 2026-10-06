import Kneser.ExponentialModelTime
import Kneser.ExponentialMultiplierSecondOrder

/-!
Actual fixed-point germs force the canonical logarithmic model at the
merging parameter.  The root velocity and multiplier-log coefficients are
derived from the genuine cusp equation, rather than normalization inputs.
-/

noncomputable section

namespace Kneser.PreparedModelAtZero

open Filter Kneser.ExponentialUnfolding Kneser.ExponentialPreparedModel
open Kneser.ExponentialModelTime Kneser.ExponentialCuspParameter
open Kneser.ExponentialMultiplierSecondOrder
open scoped Topology

def multiplierDisplacement (U : ℂ → ℂ) (x : ℂ) : ℂ := rootMultiplier U x - 1

theorem analyticAt_multiplierDisplacement {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) :
    AnalyticAt ℂ (multiplierDisplacement U) 0 := (analyticAt_rootMultiplier hU).sub analyticAt_const

theorem multiplierDisplacement_zero {U : ℂ → ℂ} (hU0 : U 0 = 0) :
    multiplierDisplacement U 0 = 0 := by simp [multiplierDisplacement, rootMultiplier, hU0]

/-- The multiplier displacement of any actual root branch solves the
actual cusp equation in the splitting parameter. -/
theorem eventually_cusp_multiplierDisplacement (U : ℂ → ℂ)
    (hroots : ∀ᶠ x in 𝓝 (0 : ℂ), unfolding (x ^ 2) (U x) = U x) :
    ∀ᶠ x in 𝓝 (0 : ℂ), cuspParameter (multiplierDisplacement U x) = x ^ 2 := by
  filter_upwards [hroots] with x hx
  have hV : multiplierDisplacement U x = -(x ^ 2) + (1 - x ^ 2) * U x := by
    dsimp [multiplierDisplacement, rootMultiplier]
    ring
  have hexp : Complex.exp (multiplierDisplacement U x) = 1 + U x := by
    rw [hV]
    change Complex.exp (-(x ^ 2) + (1 - x ^ 2) * U x) - 1 = U x at hx
    linear_combination hx
  have hmult : 1 + multiplierDisplacement U x = (1 - x ^ 2) * (1 + U x) := by
    dsimp [multiplierDisplacement, rootMultiplier]
    ring
  rw [cuspParameter, hmult]
  calc
    _ = 1 - (1 - x ^ 2) *
        (Complex.exp (-multiplierDisplacement U x) * Complex.exp (multiplierDisplacement U x)) := by
      rw [hexp]
      ring
    _ = x ^ 2 := by rw [exponential_pair]; ring

theorem log_factor_zero_eq_root_deriv (U H : ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0) (hH : AnalyticAt ℂ H 0)
    (hHlog : ∀ x, Complex.log (rootMultiplier U x) = x * H x) : H 0 = deriv U 0 := by
  have hm0 : rootMultiplier U 0 = 1 := by simp [rootMultiplier, hU0]
  have hlog := (hasDerivAt_rootMultiplier_zero hU hU0).clog
    (by simpa only [hm0] using Complex.one_mem_slitPlane)
  have heq : (fun x => Complex.log (rootMultiplier U x)) = (fun x => x * H x) := funext hHlog
  rw [heq] at hlog
  have hprod := (hasDerivAt_id (0 : ℂ)).mul hH.hasStrictDerivAt.hasDerivAt
  change HasDerivAt (fun x => x * H x) (1 * H 0 + 0 * deriv H 0) 0 at hprod
  have hp : HasDerivAt (fun x => x * H x) (H 0) 0 := by
    simpa only [one_mul, zero_mul, add_zero] using hprod
  have hl : HasDerivAt (fun x => x * H x) (deriv U 0) 0 := by simpa only [hm0, div_one] using hlog
  exact hp.unique hl

/-- Every actual root branch has the same squared root velocity and the
same derivative of the filled multiplier-log factor. -/
theorem actual_log_factor_coefficients (U H : ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hroots : ∀ᶠ x in 𝓝 (0 : ℂ), unfolding (x ^ 2) (U x) = U x)
    (hH : AnalyticAt ℂ H 0)
    (hHlog : ∀ x, Complex.log (rootMultiplier U x) = x * H x) :
    H 0 = deriv U 0 ∧ (H 0) ^ 2 = 2 ∧ deriv H 0 = -1 / 3 := by
  obtain ⟨α, γ, R, hR, hα, hαγ, hlog⟩ := exists_branch_log_cubic_coefficients
    (multiplierDisplacement U) (analyticAt_multiplierDisplacement hU)
    (multiplierDisplacement_zero hU0) (eventually_cusp_multiplierDisplacement U hroots)
  let P : ℂ → ℂ := fun x => α - x / 3 + γ * x ^ 2 + x ^ 3 * R x
  have hP : AnalyticAt ℂ P 0 := by dsimp [P]; fun_prop
  have hHP : H =ᶠ[𝓝 0] P := by
    apply cancel_power_eventually 1 H P hH.continuousAt hP.continuousAt
    exact Eventually.of_forall (fun x => by
      have hx := hlog x
      have heq : 1 + multiplierDisplacement U x = rootMultiplier U x := by
        dsimp [multiplierDisplacement]; ring
      rw [heq, hHlog] at hx
      dsimp [P]
      linear_combination hx)
  have hHα : H 0 = α := by
    simpa [P] using hHP.self_of_nhds
  have hPd : HasDerivAt P (-1 / 3) 0 := by
    have h := (((hasDerivAt_const 0 α).sub ((hasDerivAt_id (0 : ℂ)).div_const 3)).add
      (((hasDerivAt_id (0 : ℂ)).pow 2).const_mul γ)).add
        (((hasDerivAt_id (0 : ℂ)).pow 3).mul hR.hasStrictDerivAt.hasDerivAt)
    convert h using 1 <;> first | rfl | norm_num
  refine ⟨log_factor_zero_eq_root_deriv U H hU hU0 hH hHlog, ?_, ?_⟩
  · rw [hHα]
    exact hα
  · exact hHP.deriv_eq.trans hPd.deriv

/-- The filled paired numerator differentiates to the canonical
parabolic logarithmic model. -/
theorem deriv_modelNumerator_zero_eq_model (U H : ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0) (hUd : deriv U 0 ≠ 0)
    (hroots : ∀ᶠ x in 𝓝 (0 : ℂ), unfolding (x ^ 2) (U x) = U x)
    (hH : AnalyticAt ℂ H 0)
    (hHlog : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (u : ℂ) (hu : u.re < 0) :
    deriv (fun x => modelNumerator U H x u) 0 = ParabolicFatouCoordinate.model u := by
  obtain ⟨hH0, hHsq, hHd⟩ := actual_log_factor_coefficients U H hU hU0 hroots hH hHlog
  have hHne : H 0 ≠ 0 := hH0 ▸ hUd
  have hune : u ≠ 0 := by intro heq; simp [heq] at hu
  have hslit : U 0 - u ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simpa only [hU0, zero_sub, Complex.neg_re] using neg_pos.mpr hu
  have hA := ((hU.hasStrictDerivAt.hasDerivAt.sub_const u).clog hslit).div
    hH.hasStrictDerivAt.hasDerivAt hHne
  have hUn := hU.hasStrictDerivAt.hasDerivAt.comp_of_eq 0 (hasDerivAt_id (0 : ℂ)).neg (by simp)
  have hHn := hH.hasStrictDerivAt.hasDerivAt.comp_of_eq 0 (hasDerivAt_id (0 : ℂ)).neg (by simp)
  change HasDerivAt (fun x => U (-x)) (deriv U 0 * -1) 0 at hUn
  change HasDerivAt (fun x => H (-x)) (deriv H 0 * -1) 0 at hHn
  have hB := ((hUn.sub_const u).clog (by simpa only [neg_zero] using hslit)).div hHn
    (by simpa only [neg_zero] using hHne)
  have hd := (hA.sub hB).deriv
  change deriv (fun x => modelNumerator U H x u) 0 = _ at hd
  rw [hd]
  simp only [neg_zero, hU0, zero_sub, hHd, ← hH0, mul_neg, mul_one]
  dsimp [ParabolicFatouCoordinate.model]
  field_simp
  linear_combination -(Complex.log (-u) * u) * hHsq

/-- At the merger the actual logarithmic prepared model is exactly the
canonical parabolic model plus its constructed polynomial correction. -/
theorem preparedModelTime_zero_eq_model (U H e₁ e₂ : ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0) (hUd : deriv U 0 ≠ 0)
    (hroots : ∀ᶠ x in 𝓝 (0 : ℂ), unfolding (x ^ 2) (U x) = U x)
    (hH : AnalyticAt ℂ H 0)
    (hHlog : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (u : ℂ) (hu : u.re < 0) :
    preparedModelTime U H e₁ e₂ 0 u = ParabolicFatouCoordinate.model u +
      polynomialCorrection e₁ e₂ 0 u := by
  rw [preparedModelTime, logarithmicModel, Complex.sqrt_zero, dslope_same,
    deriv_modelNumerator_zero_eq_model U H hU hU0 hUd hroots hH hHlog u hu]

end Kneser.PreparedModelAtZero

end
