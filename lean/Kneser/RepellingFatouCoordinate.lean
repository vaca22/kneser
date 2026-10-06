import Kneser.RepellingExponentialOrbit
import Kneser.ParabolicOrbitSum

/-!
# An unconditional parabolic repelling Fatou coordinate

The true reflected inverse `-log(1-v)` has model `-2/v-log(-v)/3`.
Its model defect is proved to vanish to order two; the true inverse orbit
then makes its correction series absolutely convergent.
-/

noncomputable section

namespace Kneser.RepellingFatouCoordinate

open Kneser.RepellingExponentialOrbit
open Kneser.ParabolicFatouCoordinate (log_mul_of_re_pos neg_re_pos_of_inverse_re_pos)
open Kneser.ParabolicExponentialOrbit (inverseCoordinate)
open Kneser.PerturbedExponentialOrbit (parameterRadius parameterRadius_pos)
open Filter Set
open scoped Topology BigOperators

def model (v : ℂ) : ℂ := (-2 : ℂ) / v - Complex.log (-v) / 3

theorem exists_logarithmic_quotient :
    ∃ E L : ℂ → ℂ, AnalyticAt ℂ E 0 ∧ AnalyticAt ℂ L 0 ∧
      E 0 = 1 ∧ L 0 = 1 / 2 ∧ deriv E 0 = 1 / 2 ∧ deriv L 0 = 1 / 3 ∧
      (∀ v, parabolicInverse v = v * E v) ∧ (∀ v, E v = 1 + v * L v) := by
  have ha : AnalyticAt ℂ parabolicInverse 0 := by
    unfold parabolicInverse
    exact ((analyticAt_const.sub analyticAt_id).clog (by simp)).neg
  obtain ⟨T, hTa, hT⟩ := ha.exists_eq_sum_add_pow_mul 4
  have hd0 : iteratedDeriv 0 parabolicInverse 0 = 0 := by simp [parabolicInverse]
  have hd1 : iteratedDeriv 1 parabolicInverse 0 = 1 := by
    rw [iteratedDeriv_one, (hasDerivAt_parabolicInverse 0 (by norm_num)).deriv]
    norm_num
  have hd2 : iteratedDeriv 2 parabolicInverse 0 = 1 := by
    change iteratedDeriv 2 (-(fun z : ℂ => Complex.log (1 - z))) 0 = 1
    rw [iteratedDeriv_neg, iteratedDeriv_comp_const_sub]
    norm_num [iteratedDeriv_succ_log Complex.one_mem_slitPlane]
  have hd3 : iteratedDeriv 3 parabolicInverse 0 = 2 := by
    change iteratedDeriv 3 (-(fun z : ℂ => Complex.log (1 - z))) 0 = 2
    rw [iteratedDeriv_neg, iteratedDeriv_comp_const_sub]
    norm_num [iteratedDeriv_succ_log Complex.one_mem_slitPlane]
  have ht : ∀ v : ℂ, parabolicInverse v = v + v ^ 2 / 2 + v ^ 3 / 3 + v ^ 4 * T v := by
    intro v
    have h := hT v
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, hd0, hd1, hd2, hd3] at h
    norm_num [smul_eq_mul] at h
    convert h using 1; ring
  let L : ℂ → ℂ := fun v => 1 / 2 + v / 3 + v ^ 2 * T v
  let E : ℂ → ℂ := fun v => 1 + v * L v
  have hLa : AnalyticAt ℂ L 0 := by dsimp [L]; fun_prop
  have hEa : AnalyticAt ℂ E 0 := by dsimp [E]; fun_prop
  have hL0 : L 0 = 1 / 2 := by simp [L]
  have hE0 : E 0 = 1 := by simp [E]
  have hLd : HasDerivAt L (1 / 3) 0 := by
    have h := (((hasDerivAt_id (0 : ℂ)).div_const 3).add
      (((hasDerivAt_id (0 : ℂ)).pow 2).mul hTa.hasStrictDerivAt.hasDerivAt)).const_add (1 / 2)
    convert h using 1 <;> first | rfl | (simp; done) | (funext v; dsimp [L]; simp only [one_div]; ring)
  have hEd : HasDerivAt E (1 / 2) 0 := by
    convert ((hasDerivAt_id (0 : ℂ)).mul hLd).const_add 1 using 1 <;>
      first | rfl | simp [hL0]
  refine ⟨E, L, hEa, hLa, hE0, hL0, hEd.deriv, hLd.deriv, ?_, fun _ => rfl⟩
  intro v
  rw [ht]
  dsimp [E, L]
  ring

theorem exists_analytic_defect_factor :
    ∃ D Q : ℂ → ℂ, AnalyticAt ℂ D 0 ∧ AnalyticAt ℂ Q 0 ∧
      (∀ u, D u = u ^ 2 * Q u) ∧
      (∀ᶠ u in 𝓝 0, 0 < (inverseCoordinate u).re →
        coordinateDefect parabolicInverse model u = D u) := by
  obtain ⟨E, L, hEa, hLa, hE0, hL0, hEd, hLd, hf, hEL⟩ :=
    exists_logarithmic_quotient
  have hEne : E 0 ≠ 0 := by simp [hE0]
  have hEslit : E 0 ∈ Complex.slitPlane := by
    simp [hE0, Complex.mem_slitPlane_iff]
  let D : ℂ → ℂ := fun u => 2 * L u / E u - 1 - Complex.log (E u) / 3
  have hDa : AnalyticAt ℂ D 0 := by
    exact (((analyticAt_const.mul hLa) : AnalyticAt ℂ (fun u => 2 * L u) 0).div hEa hEne |>.sub analyticAt_const).sub
      ((hEa.clog hEslit).div_const)
  have hD0 : D 0 = 0 := by norm_num [D, hE0, hL0]
  have hDd : HasDerivAt D 0 0 := by
    have hE := hEa.hasStrictDerivAt.hasDerivAt
    have hL := hLa.hasStrictDerivAt.hasDerivAt
    rw [hEd] at hE
    rw [hLd] at hL
    have h := (((hL.const_mul 2).div hE hEne).sub_const 1).sub
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
  have hneg : -parabolicInverse u = (-u) * E u := by rw [hf]; ring
  rw [← hneg] at hlog
  change (-2 / parabolicInverse u - Complex.log (-parabolicInverse u) / 3) -
    (-2 / u - Complex.log (-u) / 3) - 1 = _
  rw [hlog, hf]
  dsimp [D]
  have hEform : E u - 1 = u * L u := by rw [hEL]; ring
  field_simp [hune, hEune]
  linear_combination 6 * hEform

theorem exists_local_defect_bound :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ u : ℂ, ‖u‖ < r →
      0 < (inverseCoordinate u).re →
      ‖coordinateDefect parabolicInverse model u‖ ≤ C * ‖u‖ ^ 2 := by
  obtain ⟨D, Q, hDa, hQa, hfactor, hident⟩ := exists_analytic_defect_factor
  have hQbound : ∀ᶠ u in 𝓝 0, ‖Q u‖ < ‖Q 0‖ + 1 :=
    hQa.continuousAt.norm.eventually (gt_mem_nhds (by linarith : ‖Q 0‖ < ‖Q 0‖ + 1))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hQbound.and hident)
  refine ⟨r, ‖Q 0‖ + 1, hr, by positivity, ?_⟩
  intro u hu hp
  obtain ⟨hQ, hD⟩ := hball (by simpa using hu)
  rw [hD hp, hfactor, norm_mul, norm_pow]
  exact (mul_le_mul_of_nonneg_left hQ.le (by positivity)).trans_eq (by ring)


theorem inverseOrbit_zero_parameter (v : ℂ) (k : ℕ) :
    inverseOrbit v 0 k = (parabolicInverse^[k]) v := by
  have hf : reflectedInverse 0 = parabolicInverse := funext reflectedInverse_zero
  simp only [inverseOrbit, hf]

theorem inverse_iterate_re (v : ℂ) (R : ℝ) (hR : 64 ≤ R)
    (hv : R ≤ (inverseCoordinate v).re) (k : ℕ) :
    R + (k : ℝ) / 2 ≤ (inverseCoordinate ((parabolicInverse^[k]) v)).re := by
  have hr := parameterRadius_pos ‖inverseCoordinate v‖ (norm_nonneg _) k
  have h := (finite_inverseOrbit_inverse_bounds v 0 R hR hv k (by simpa using hr.le) k (le_refl k)).1
  simpa only [inverseOrbit_zero_parameter] using h

theorem inverse_iterate_norm_bound (v : ℂ) (R : ℝ) (hR : 64 ≤ R)
    (hv : R ≤ (inverseCoordinate v).re) (k : ℕ) :
    ‖(parabolicInverse^[k]) v‖ ≤ 2 / (R + (k : ℝ) / 2) := by
  have hr := parameterRadius_pos ‖inverseCoordinate v‖ (norm_nonneg _) k
  have h := finite_inverseOrbit_norm_bound v 0 R hR hv k (by simpa using hr.le) k (le_refl k)
  simpa only [inverseOrbit_zero_parameter] using h

/-- The genuine finite model gives an actual attracting Fatou coordinate.
No defect, orbit decay, convergence, or Abel equation is assumed. -/
theorem exists_repelling_fatou_coordinate :
    ∃ R C : ℝ, 64 ≤ R ∧ 0 ≤ C ∧ ∀ u : ℂ, R ≤ (inverseCoordinate u).re →
      (∀ k : ℕ, ‖orbitTerm parabolicInverse (coordinateDefect parabolicInverse model) u k‖ ≤
        C / ((k : ℝ) + 1) ^ 2) ∧
      Summable (fun k => ‖orbitTerm parabolicInverse (coordinateDefect parabolicInverse model) u k‖) ∧
      correctedCoordinate parabolicInverse model (coordinateDefect parabolicInverse model) (parabolicInverse u) =
        correctedCoordinate parabolicInverse model (coordinateDefect parabolicInverse model) u + 1 ∧
      Tendsto (fun n : ℕ => model ((parabolicInverse^[n]) u) - (n : ℂ)) atTop
        (𝓝 (correctedCoordinate parabolicInverse model (coordinateDefect parabolicInverse model) u)) := by
  obtain ⟨r, M, hr, hM, hlocal⟩ := exists_local_defect_bound
  let R : ℝ := max 64 (4 / r)
  have hR : 64 ≤ R := le_max_left _ _
  have hRpos : 0 < R := by linarith
  have hRr : 4 / r ≤ R := le_max_right _ _
  have hsmall : 2 / R < r := by
    have hp := (div_le_iff₀ hr).mp hRr
    apply (div_lt_iff₀ hRpos).mpr
    nlinarith
  refine ⟨R, 16 * M, hR, by positivity, ?_⟩
  intro u hu
  have hbound : ∀ k : ℕ,
      ‖orbitTerm parabolicInverse (coordinateDefect parabolicInverse model) u k‖ ≤
        (16 * M) / ((k : ℝ) + 1) ^ 2 := by
    intro k
    have hkn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hdecay := inverse_iterate_norm_bound u R hR hu k
    have hden : 0 < R + (k : ℝ) / 2 := by linarith
    have hsize : ‖(parabolicInverse^[k]) u‖ < r := by
      exact lt_of_le_of_lt (hdecay.trans (div_le_div_of_nonneg_left (by norm_num)
        hRpos (by linarith))) hsmall
    have hpetal : 0 < (inverseCoordinate ((parabolicInverse^[k]) u)).re := by
      have hinc := inverse_iterate_re u R hR hu k
      linarith
    have hnorm : ‖(parabolicInverse^[k]) u‖ ≤ 4 / ((k : ℝ) + 1) := by
      apply hdecay.trans
      apply (div_le_div_iff₀ hden (by positivity : 0 < (k : ℝ) + 1)).mpr
      linarith
    have hdefect := hlocal ((parabolicInverse^[k]) u) hsize hpetal
    change ‖coordinateDefect parabolicInverse model ((parabolicInverse^[k]) u)‖ ≤ _
    apply hdefect.trans
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) hM
    convert hp using 1
    field_simp
    ring
  exact ⟨hbound, fatou_coordinate_of_defect_bound parabolicInverse model u (16 * M)
    (by norm_num) hbound⟩

end Kneser.RepellingFatouCoordinate

end
