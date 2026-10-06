import Kneser.ParabolicExponentialOrbit
import Kneser.ParabolicOrbitSum
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
The finite model `-2/u + log(-u)/3` for the actual parabolic exponential.
Its defect is proved to have a double zero. This constructs its convergent
orbit correction on an actual attracting petal.
-/

noncomputable section

namespace Kneser.ParabolicFatouCoordinate

open Kneser.ParabolicExponentialOrbit Filter Set
open scoped Topology BigOperators

def model (u : ℂ) : ℂ := (-2 : ℂ) / u + Complex.log (-u) / 3

theorem exists_exponential_quotient :
    ∃ E L : ℂ → ℂ, AnalyticAt ℂ E 0 ∧ AnalyticAt ℂ L 0 ∧
      E 0 = 1 ∧ L 0 = 1 / 2 ∧ deriv E 0 = 1 / 2 ∧ deriv L 0 = 1 / 6 ∧
      (∀ u, parabolicMap u = u * E u) ∧ (∀ u, E u = 1 + u * L u) := by
  have ha : AnalyticAt ℂ Complex.exp 0 := by fun_prop
  obtain ⟨R, hRa, hR⟩ := ha.exists_eq_sum_add_pow_mul 4
  have ht : ∀ u : ℂ, Complex.exp u = 1 + u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 * R u := by
    intro u
    have h := hR u
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      iteratedDeriv_eq_iterate, Complex.iter_deriv_exp, Complex.exp_zero] at h
    norm_num [smul_eq_mul] at h
    exact h
  let L : ℂ → ℂ := fun u => 1 / 2 + u / 6 + u ^ 2 * R u
  let E : ℂ → ℂ := fun u => 1 + u * L u
  have hLa : AnalyticAt ℂ L 0 := by dsimp [L]; fun_prop
  have hEa : AnalyticAt ℂ E 0 := by dsimp [E]; fun_prop
  have hL0 : L 0 = 1 / 2 := by simp [L]
  have hE0 : E 0 = 1 := by simp [E]
  have hLd : HasDerivAt L (1 / 6) 0 := by
    have h := (((hasDerivAt_id (0 : ℂ)).div_const 6).add
      (((hasDerivAt_id (0 : ℂ)).pow 2).mul hRa.hasStrictDerivAt.hasDerivAt)).const_add (1 / 2)
    convert h using 1 <;> first | rfl | (simp; done) | (funext u; dsimp [L]; simp only [one_div]; ring)
  have hEd : HasDerivAt E (1 / 2) 0 := by
    convert ((hasDerivAt_id (0 : ℂ)).mul hLd).const_add 1 using 1 <;>
      first | rfl | simp [hL0]
  refine ⟨E, L, hEa, hLa, hE0, hL0, hEd.deriv, hLd.deriv, ?_, fun _ => rfl⟩
  intro u
  rw [parabolicMap, ht]
  dsimp [E, L]
  ring

theorem log_mul_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    Complex.log (x * y) = Complex.log x + Complex.log y := by
  have hxne : x ≠ 0 := by intro h; simp [h] at hx
  have hyne : y ≠ 0 := by intro h; simp [h] at hy
  apply Complex.log_mul hxne hyne
  have hax := (abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx)))
  have hay := (abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy)))
  constructor <;> linarith

theorem neg_re_pos_of_inverse_re_pos {u : ℂ} (hu : 0 < (inverseCoordinate u).re) :
    0 < (-u).re := by
  have h : 0 < (-2 * u.re) / Complex.normSq u := by
    simpa [inverseCoordinate, Complex.div_re] using hu
  have hn : 0 ≤ Complex.normSq u := Complex.normSq_nonneg u
  have hnum : 0 < -2 * u.re := by
    by_contra hc
    have hz : (-2 * u.re) / Complex.normSq u ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hc) hn
    linarith
  simp only [Complex.neg_re]
  linarith

theorem exists_analytic_defect_factor :
    ∃ D Q : ℂ → ℂ, AnalyticAt ℂ D 0 ∧ AnalyticAt ℂ Q 0 ∧
      (∀ u, D u = u ^ 2 * Q u) ∧
      (∀ᶠ u in 𝓝 0, 0 < (inverseCoordinate u).re →
        coordinateDefect parabolicMap model u = D u) := by
  obtain ⟨E, L, hEa, hLa, hE0, hL0, hEd, hLd, hf, hEL⟩ :=
    exists_exponential_quotient
  have hEne : E 0 ≠ 0 := by simp [hE0]
  have hEslit : E 0 ∈ Complex.slitPlane := by
    simp [hE0, Complex.mem_slitPlane_iff]
  let D : ℂ → ℂ := fun u => 2 * L u / E u - 1 + Complex.log (E u) / 3
  have hDa : AnalyticAt ℂ D 0 := by
    exact (((analyticAt_const.mul hLa) : AnalyticAt ℂ (fun u => 2 * L u) 0).div hEa hEne |>.sub analyticAt_const).add
      ((hEa.clog hEslit).div_const)
  have hD0 : D 0 = 0 := by norm_num [D, hE0, hL0]
  have hDd : HasDerivAt D 0 0 := by
    have hE := hEa.hasStrictDerivAt.hasDerivAt
    have hL := hLa.hasStrictDerivAt.hasDerivAt
    rw [hEd] at hE
    rw [hLd] at hL
    have h := (((hL.const_mul 2).div hE hEne).sub_const 1).add
      ((Complex.hasDerivAt_log hEslit).comp 0 hE |>.div_const 3)
    convert h using 1 <;> first | rfl | simp [hE0, hL0]; norm_num
  obtain ⟨Q, hQa, hQ⟩ := hDa.exists_eq_sum_add_pow_mul 2
  have hfactor : ∀ u, D u = u ^ 2 * Q u := by
    intro u
    simpa [Finset.sum_range_succ, hD0, hDd.deriv, smul_eq_mul] using hQ u
  have hEpos : ∀ᶠ u in 𝓝 0, 0 < (E u).re := by
    have hc : ContinuousAt (fun u => (E u).re) 0 := Complex.continuous_re.continuousAt.comp hEa.continuousAt
    exact hc.eventually (lt_mem_nhds (show (0 : ℝ) < (E 0).re by simp [hE0]))
  refine ⟨D, Q, hDa, hQa, hfactor, ?_⟩
  filter_upwards [hEpos] with u hu hpetal
  have hune : u ≠ 0 := by intro h; simp [h, inverseCoordinate] at hpetal
  have hEune : E u ≠ 0 := by intro h; simp [h] at hu
  have hlog := log_mul_of_re_pos (neg_re_pos_of_inverse_re_pos hpetal) hu
  have hneg : -parabolicMap u = (-u) * E u := by rw [hf]; ring
  rw [← hneg] at hlog
  change (-2 / parabolicMap u + Complex.log (-parabolicMap u) / 3) -
    (-2 / u + Complex.log (-u) / 3) - 1 = _
  rw [hlog, hf]
  dsimp [D]
  have hEform : E u - 1 = u * L u := by rw [hEL]; ring
  field_simp [hune, hEune]
  linear_combination 6 * hEform

theorem exists_local_defect_bound :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ u : ℂ, ‖u‖ < r →
      0 < (inverseCoordinate u).re →
      ‖coordinateDefect parabolicMap model u‖ ≤ C * ‖u‖ ^ 2 := by
  obtain ⟨D, Q, hDa, hQa, hfactor, hident⟩ := exists_analytic_defect_factor
  have hQbound : ∀ᶠ u in 𝓝 0, ‖Q u‖ < ‖Q 0‖ + 1 :=
    hQa.continuousAt.norm.eventually (gt_mem_nhds (by linarith : ‖Q 0‖ < ‖Q 0‖ + 1))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hQbound.and hident)
  refine ⟨r, ‖Q 0‖ + 1, hr, by positivity, ?_⟩
  intro u hu hp
  obtain ⟨hQ, hD⟩ := hball (by simpa using hu)
  rw [hD hp, hfactor, norm_mul, norm_pow]
  exact (mul_le_mul_of_nonneg_left hQ.le (by positivity)).trans_eq (by ring)

/-- The genuine finite model gives an actual attracting Fatou coordinate.
No defect, orbit decay, convergence, or Abel equation is assumed. -/
theorem exists_attracting_fatou_coordinate :
    ∃ R C : ℝ, 32 ≤ R ∧ 0 ≤ C ∧ ∀ u : ℂ, R ≤ (inverseCoordinate u).re →
      (∀ k : ℕ, ‖orbitTerm parabolicMap (coordinateDefect parabolicMap model) u k‖ ≤
        C / ((k : ℝ) + 1) ^ 2) ∧
      Summable (fun k => ‖orbitTerm parabolicMap (coordinateDefect parabolicMap model) u k‖) ∧
      correctedCoordinate parabolicMap model (coordinateDefect parabolicMap model) (parabolicMap u) =
        correctedCoordinate parabolicMap model (coordinateDefect parabolicMap model) u + 1 ∧
      Tendsto (fun n : ℕ => model ((parabolicMap^[n]) u) - (n : ℂ)) atTop
        (𝓝 (correctedCoordinate parabolicMap model (coordinateDefect parabolicMap model) u)) := by
  obtain ⟨r, M, hr, hM, hlocal⟩ := exists_local_defect_bound
  let R : ℝ := max 32 (4 / r)
  have hR : 32 ≤ R := le_max_left _ _
  have hRpos : 0 < R := by linarith
  have hRr : 4 / r ≤ R := le_max_right _ _
  have hsmall : 2 / R < r := by
    have hp := (div_le_iff₀ hr).mp hRr
    apply (div_lt_iff₀ hRpos).mpr
    nlinarith
  refine ⟨R, 16 * M, hR, by positivity, ?_⟩
  intro u hu
  have hbound : ∀ k : ℕ,
      ‖orbitTerm parabolicMap (coordinateDefect parabolicMap model) u k‖ ≤
        (16 * M) / ((k : ℝ) + 1) ^ 2 := by
    intro k
    have hkn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hdecay := iterate_norm_bound_of_threshold u R hR hu k
    have hden : 0 < R + (k : ℝ) / 2 := by linarith
    have hsize : ‖(parabolicMap^[k]) u‖ < r := by
      exact lt_of_le_of_lt (hdecay.trans (div_le_div_of_nonneg_left (by norm_num)
        hRpos (by linarith))) hsmall
    have hpetal : 0 < (inverseCoordinate ((parabolicMap^[k]) u)).re := by
      have hinc := iterate_inverse_re u (hR.trans hu) k
      linarith
    have hnorm : ‖(parabolicMap^[k]) u‖ ≤ 4 / ((k : ℝ) + 1) := by
      apply hdecay.trans
      apply (div_le_div_iff₀ hden (by positivity : 0 < (k : ℝ) + 1)).mpr
      linarith
    have hdefect := hlocal ((parabolicMap^[k]) u) hsize hpetal
    change ‖coordinateDefect parabolicMap model ((parabolicMap^[k]) u)‖ ≤ _
    apply hdefect.trans
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) hM
    convert hp using 1
    field_simp
    ring
  exact ⟨hbound, fatou_coordinate_of_defect_bound parabolicMap model u (16 * M)
    (by norm_num) hbound⟩

end Kneser.ParabolicFatouCoordinate

end
