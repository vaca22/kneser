import Mathlib.Analysis.Analytic.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.NormNum

/-!
# Integrating an analytic germ along a continuous family of contractions

The coefficients of the integral are actual Bochner integrals of continuous
multilinear maps. A contraction preserves their norm majorant and convergence
radius; dominated convergence identifies their sum with the given integral.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Kneser.AnalyticContractionIntegral

open Filter MeasureTheory Metric Set
open scoped Topology BigOperators NNReal ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

/-- The continuous coefficient family induced by the contractions. -/
def contractionCoefficient (L : ℝ → E →L[ℂ] E)
    (p : FormalMultilinearSeries ℂ E F) (n : ℕ) (t : ℝ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => E) F :=
  (p n).compContinuousLinearMap (fun _ => L t)

/-- The coefficients of the actual integral, constructed in the Banach
space of continuous multilinear maps. -/
def integralSeries (L : ℝ → E →L[ℂ] E)
    (p : FormalMultilinearSeries ℂ E F) : FormalMultilinearSeries ℂ E F :=
  fun n => ∫ t in (0 : ℝ)..1, contractionCoefficient L p n t

omit [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
theorem continuous_contractionCoefficient (L : ℝ → E →L[ℂ] E) (hL : Continuous L)
    (p : FormalMultilinearSeries ℂ E F) (n : ℕ) :
    Continuous (contractionCoefficient L p n) := by
  exact (p n).compContinuousLinearMapLRight.cont.comp (continuous_pi (fun _ => hL))

omit [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
theorem norm_contractionCoefficient_le (L : ℝ → E →L[ℂ] E)
    (hLbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖L t‖ ≤ 1)
    (p : FormalMultilinearSeries ℂ E F) (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖contractionCoefficient L p n t‖ ≤ ‖p n‖ := by
  have hprod : (∏ _i : Fin n, ‖L t‖) ≤ 1 := by
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hLbound t ht)
  exact ((p n).norm_compContinuousLinearMap_le (fun _ => L t)).trans
    ((mul_le_mul_of_nonneg_left hprod (norm_nonneg _)).trans_eq (mul_one _))

omit [CompleteSpace F] in
theorem norm_integralSeries_le (L : ℝ → E →L[ℂ] E)
    (hLbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖L t‖ ≤ 1)
    (p : FormalMultilinearSeries ℂ E F) (n : ℕ) :
    ‖integralSeries L p n‖ ≤ ‖p n‖ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (f := contractionCoefficient L p n) (C := ‖p n‖) (by
      intro t ht
      apply norm_contractionCoefficient_le L hLbound p n t
      exact Ioc_subset_Icc_self (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht))
  simpa only [integralSeries, sub_zero, abs_one, mul_one] using h

theorem integralSeries_apply (L : ℝ → E →L[ℂ] E) (hL : Continuous L)
    (p : FormalMultilinearSeries ℂ E F) (n : ℕ) (z : E) :
    integralSeries L p n (fun _ => z) = ∫ t in (0 : ℝ)..1, p n (fun _ => L t z) := by
  have hi := (continuous_contractionCoefficient L hL p n).intervalIntegrable (μ := volume) 0 1
  exact ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => E) F (fun _ => z)).intervalIntegral_comp_comm hi).symm

theorem norm_apply_contraction_le (L : ℝ → E →L[ℂ] E)
    (hLbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖L t‖ ≤ 1)
    (z : E) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖L t z‖ ≤ ‖z‖ := by
  exact ((L t).le_opNorm z).trans
    ((mul_le_mul_of_nonneg_right (hLbound t ht) (norm_nonneg _)).trans_eq (one_mul _))

/-- Integration preserves the original analytic power-series ball and does
not decrease its convergence radius. -/
theorem hasFPowerSeriesOnBall_integral (L : ℝ → E →L[ℂ] E) (hL : Continuous L)
    (hLbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖L t‖ ≤ 1)
    (f : E → F) (p : FormalMultilinearSeries ℂ E F) (r : ℝ≥0∞)
    (hf : HasFPowerSeriesOnBall f p 0 r) :
    HasFPowerSeriesOnBall (fun z => ∫ t in (0 : ℝ)..1, f (L t z))
      (integralSeries L p) 0 r := by
  refine ⟨hf.r_le.trans (FormalMultilinearSeries.radius_le_of_le
    (norm_integralSeries_le L hLbound p)), hf.r_pos, ?_⟩
  intro z hz
  have hzrad : (‖z‖₊ : ℝ≥0∞) < p.radius :=
    (mem_eball_zero_iff.mp hz).trans_le hf.r_le
  have hsum : Summable (fun n => ‖p n‖ * ‖z‖ ^ n) :=
    p.summable_norm_mul_pow hzrad
  have hcont : ∀ n, Continuous (fun t : ℝ => p n (fun _ => L t z)) := by
    intro n
    exact (p n).cont.comp (continuous_pi (fun _ => hL.clm_apply continuous_const))
  have hsumint := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (F := fun n t => p n (fun _ => L t z)) (f := fun t => f (L t z))
    (fun n _t => ‖p n‖ * ‖z‖ ^ n)
    (fun n => (hcont n).aestronglyMeasurable)
    (fun n => Eventually.of_forall (fun t ht => by
      have ht' : t ∈ Icc (0 : ℝ) 1 :=
        Ioc_subset_Icc_self (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht)
      calc
        ‖p n (fun _ => L t z)‖ ≤ ‖p n‖ * ‖L t z‖ ^ n := by
          simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
            (p n).le_opNorm (fun _ => L t z)
        _ ≤ ‖p n‖ * ‖z‖ ^ n := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (norm_apply_contraction_le L hLbound z t ht') n)
          (norm_nonneg _)))
    (Eventually.of_forall (fun _ _ => hsum)) intervalIntegrable_const
    (Eventually.of_forall (fun t ht => by
      have ht' : t ∈ Icc (0 : ℝ) 1 :=
        Ioc_subset_Icc_self (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht)
      have hnorm := norm_apply_contraction_le L hLbound z t ht'
      have hmem : L t z ∈ eball (0 : E) r := by
        rw [mem_eball_zero_iff]
        exact (show (‖L t z‖₊ : ℝ≥0∞) ≤ ‖z‖₊ by exact_mod_cast hnorm).trans_lt
          (mem_eball_zero_iff.mp hz)
      simpa only [zero_add] using hf.hasSum hmem))
  simpa only [integralSeries_apply L hL p, zero_add] using hsumint

/-- An actual interval integral of an analytic germ along continuous complex
linear contractions is jointly analytic at the origin. -/
theorem analyticAt_integral_contractions (L : ℝ → E →L[ℂ] E) (hL : Continuous L)
    (hLbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖L t‖ ≤ 1)
    (f : E → F) (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℂ (fun z => ∫ t in (0 : ℝ)..1, f (L t z)) 0 := by
  obtain ⟨p, r, hp⟩ := hf
  exact (hasFPowerSeriesOnBall_integral L hL hLbound f p r hp).analyticAt

end Kneser.AnalyticContractionIntegral

end
