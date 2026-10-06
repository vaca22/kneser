import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Kneser.AnalyticContractionIntegral

/-!
Joint division by a coordinate which vanishes identically on a hyperplane.
The quotient is the actual integral of the first partial derivative, with
the factor identity proved by the fundamental theorem of calculus.
-/

noncomputable section

namespace Kneser.JointAnalyticDivision

open Filter Set MeasureTheory
open scoped Topology Interval

abbrev Pair := ℂ × ℂ

def firstProjection : Pair →L[ℂ] Pair :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).prod 0

def scaleFirst (t : ℝ) : Pair →L[ℂ] Pair :=
  ContinuousLinearMap.id ℂ Pair + ((t : ℂ) - 1) • firstProjection

@[simp] theorem scaleFirst_apply (t : ℝ) (p : Pair) :
    scaleFirst t p = ((t : ℂ) * p.1, p.2) := by
  ext <;> simp [scaleFirst, firstProjection]
  ring

theorem continuous_scaleFirst : Continuous scaleFirst := by
  exact continuous_const.add ((Complex.continuous_ofReal.sub continuous_const).smul continuous_const)

theorem norm_scaleFirst_le_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖scaleFirst t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro p
  rw [scaleFirst_apply, Prod.norm_def, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht.1, one_mul]
  have hfst := norm_fst_le p
  have hsnd := norm_snd_le p
  exact max_le (le_trans (mul_le_of_le_one_left (norm_nonneg p.1) ht.2) hfst) hsnd

theorem norm_scaleFirst_apply_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (p : Pair) :
    ‖scaleFirst t p‖ ≤ ‖p‖ := by
  exact (ContinuousLinearMap.le_opNorm _ p).trans
    (mul_le_of_le_one_left (norm_nonneg p) (norm_scaleFirst_le_one ht))

def partialFirst (B : Pair → ℂ) (p : Pair) : ℂ := (fderiv ℂ B p) (1, 0)

def quotient (B : Pair → ℂ) (p : Pair) : ℂ :=
  ∫ t in (0 : ℝ)..1, partialFirst B (scaleFirst t p)

theorem analyticAt_partialFirst {B : Pair → ℂ} (hB : AnalyticAt ℂ B 0) :
    AnalyticAt ℂ (partialFirst B) 0 := by
  exact ((ContinuousLinearMap.apply ℂ ℂ ((1 : ℂ), (0 : ℂ))).analyticAt _).comp hB.fderiv

theorem hasDerivAt_curve {B : Pair → ℂ} {p : Pair} {t : ℝ}
    (hB : DifferentiableAt ℂ B (scaleFirst t p)) :
    HasDerivAt (fun r : ℝ => B (scaleFirst r p))
      (p.1 * partialFirst B (scaleFirst t p)) t := by
  have hcurve : HasDerivAt (fun r : ℝ => scaleFirst r p) (p.1, 0) t := by
    have h := (((hasDerivAt_id (t : ℂ)).mul_const p.1).comp_ofReal).prodMk (hasDerivAt_const t p.2)
    convert h using 1 <;> first | rfl | simp [scaleFirst_apply]
  have h := (hB.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hcurve
  apply h.congr_deriv
  change (fderiv ℂ B (scaleFirst t p)) (p.1, 0) = _
  rw [show (p.1, (0 : ℂ)) = p.1 • ((1 : ℂ), (0 : ℂ)) by simp,
    map_smul]
  rfl

/-- Analyticity of the original function provides a single neighbourhood on
which the exact quotient identity holds, including points on the hyperplane. -/
theorem eventually_coordinate_factor {B : Pair → ℂ} (hB : AnalyticAt ℂ B 0) :
    ∀ᶠ p in 𝓝 (0 : Pair), B p - B (0, p.2) = p.1 * quotient B p := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hB.eventually_analyticAt
  have hpartial : ContinuousOn (partialFirst B) (Metric.ball (0 : Pair) r) := by
    intro p hp
    have hpa := hball (by simpa [Metric.mem_ball, dist_zero_right] using hp)
    exact (((ContinuousLinearMap.apply ℂ ℂ ((1 : ℂ), (0 : ℂ))).analyticAt _).comp hpa.fderiv).continuousAt.continuousWithinAt
  have hsmall : ∀ᶠ p in 𝓝 (0 : Pair), ‖p‖ < r := by
    have h : ∀ᶠ p in 𝓝 (0 : Pair), p ∈ Metric.ball (0 : Pair) r := Metric.ball_mem_nhds (0 : Pair) hr
    exact h.mono (fun p hp => by simpa [Metric.mem_ball, dist_zero_right] using hp)
  filter_upwards [hsmall] with p hp
  have hmaps : MapsTo (fun t : ℝ => scaleFirst t p) (Icc 0 1) (Metric.ball (0 : Pair) r) := by
    intro t ht
    simpa [Metric.mem_ball, dist_zero_right] using lt_of_le_of_lt (norm_scaleFirst_apply_le ht p) hp
  have hcurve : Continuous (fun t : ℝ => scaleFirst t p) := by
    simp only [scaleFirst_apply]
    fun_prop
  have hpc : ContinuousOn (fun t : ℝ => partialFirst B (scaleFirst t p)) (Icc 0 1) :=
    hpartial.comp hcurve.continuousOn hmaps
  have hint : IntervalIntegrable (fun t : ℝ => p.1 * partialFirst B (scaleFirst t p)) volume 0 1 :=
    (continuousOn_const.mul hpc).intervalIntegrable_of_Icc (by norm_num)
  have hder : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => B (scaleFirst t p))
      (p.1 * partialFirst B (scaleFirst t p)) t := by
    intro t ht
    exact hasDerivAt_curve (hball (by simpa [Metric.mem_ball, dist_zero_right] using hmaps ht)).differentiableAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hder t (by simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht)) hint
  rw [intervalIntegral.integral_const_mul] at h
  simpa only [scaleFirst_apply, Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul,
    quotient] using h.symm

theorem analyticAt_quotient {B : Pair → ℂ} (hB : AnalyticAt ℂ B 0) :
    AnalyticAt ℂ (quotient B) 0 :=
  AnalyticContractionIntegral.analyticAt_integral_contractions scaleFirst continuous_scaleFirst
    (fun _ ht => norm_scaleFirst_le_one ht) (partialFirst B) (analyticAt_partialFirst hB)

/-- Actual joint analytic division by the first coordinate. -/
theorem exists_coordinate_factor {B : Pair → ℂ} (hB : AnalyticAt ℂ B 0)
    (hzero : ∀ᶠ u : ℂ in 𝓝 0, B (0, u) = 0) :
    ∃ C : Pair → ℂ, AnalyticAt ℂ C 0 ∧
      ∀ᶠ p in 𝓝 (0 : Pair), B p = p.1 * C p := by
  have hsnd : Tendsto (fun p : Pair => p.2) (𝓝 0) (𝓝 (0 : ℂ)) := continuous_snd.tendsto 0
  refine ⟨quotient B, analyticAt_quotient hB, ?_⟩
  filter_upwards [eventually_coordinate_factor hB, hsnd.eventually hzero] with p hp hz
  simpa only [hz, sub_zero] using hp

/-- A root depending analytically on the first coordinate is divided out by
an actual analytic change of coordinates and the proved hyperplane division. -/
theorem exists_moving_root_factor {B : Pair → ℂ} {U : ℂ → ℂ}
    (hB : AnalyticAt ℂ B 0) (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hzero : ∀ᶠ x in 𝓝 0, B (x, U x) = 0) :
    ∃ C : Pair → ℂ, AnalyticAt ℂ C 0 ∧
      ∀ᶠ p in 𝓝 (0 : Pair), B p = (p.2 - U p.1) * C p := by
  let T : Pair → Pair := fun p => (p.2, U p.2 + p.1)
  let S : Pair → Pair := fun p => (p.2 - U p.1, p.1)
  have hUa : AnalyticAt ℂ (fun p : Pair => U p.2) 0 := hU.comp_of_eq analyticAt_snd rfl
  have hUa' : AnalyticAt ℂ (fun p : Pair => U p.1) 0 := hU.comp_of_eq analyticAt_fst rfl
  have hTa : AnalyticAt ℂ T 0 := analyticAt_snd.prod (hUa.add analyticAt_fst)
  have hSa : AnalyticAt ℂ S 0 := (analyticAt_snd.sub hUa').prod analyticAt_fst
  have hT0 : T 0 = 0 := by simp [T, hU0]
  have hS0 : S 0 = 0 := by simp [S, hU0]
  have hBTa : AnalyticAt ℂ (fun p => B (T p)) 0 := hB.comp_of_eq hTa hT0
  have hBTzero : ∀ᶠ u : ℂ in 𝓝 0, B (T (0, u)) = 0 := by
    simpa [T] using hzero
  obtain ⟨C, hCa, hC⟩ := exists_coordinate_factor hBTa hBTzero
  refine ⟨fun p => C (S p), hCa.comp_of_eq hSa hS0, ?_⟩
  have hSt : Tendsto S (𝓝 0) (𝓝 (0 : Pair)) := by
    simpa only [hS0] using hSa.continuousAt.tendsto
  filter_upwards [hSt.eventually hC] with p hp
  simpa [T, S] using hp

end Kneser.JointAnalyticDivision

end
