import Kneser.ParabolicFatouCoordinate
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
Uniform convergence and holomorphy of the actual attracting Fatou coordinate.
These follow from the proved exponential defect and genuine petal estimates.
-/

noncomputable section

namespace Kneser.ParabolicFatouHolomorphic

open Kneser.ParabolicExponentialOrbit Kneser.ParabolicFatouCoordinate Filter Set
open scoped Topology BigOperators

def petal (R : ℝ) : Set ℂ := {u | R < (inverseCoordinate u).re}

theorem petal_isOpen {R : ℝ} (hR : 0 < R) : IsOpen (petal R) := by
  rw [isOpen_iff_mem_nhds]
  intro u hu
  have hune : u ≠ 0 := by
    intro h
    simp [petal, h, inverseCoordinate] at hu
    linarith
  have hc : ContinuousAt (fun v : ℂ => (inverseCoordinate v).re) u :=
    Complex.continuous_re.continuousAt.comp
      (continuousAt_const.div continuousAt_id hune)
  exact hc.eventually (lt_mem_nhds hu)

theorem analyticAt_model {u : ℂ} (hu : 0 < (inverseCoordinate u).re) :
    AnalyticAt ℂ model u := by
  have hune : u ≠ 0 := by intro h; simp [h, inverseCoordinate] at hu
  have hslit : -u ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (neg_re_pos_of_inverse_re_pos hu))
  exact (analyticAt_const.div analyticAt_id hune).add
    (((analyticAt_id.neg).clog hslit).div_const)

theorem mapsTo_iterate_petal {R : ℝ} (hR : 32 ≤ R) (k : ℕ) :
    MapsTo (parabolicMap^[k]) (petal R) (petal R) := by
  intro u hu
  have hk := iterate_inverse_re u (hR.trans hu.le) k
  change R < (inverseCoordinate ((parabolicMap^[k]) u)).re
  change R < (inverseCoordinate u).re at hu
  linarith [Nat.cast_nonneg (α := ℝ) k]

theorem differentiable_parabolicMap : Differentiable ℂ parabolicMap := by
  unfold parabolicMap
  fun_prop

theorem differentiableOn_defect_petal {R : ℝ} (hR : 32 ≤ R) :
    DifferentiableOn ℂ (coordinateDefect parabolicMap model) (petal R) := by
  have hmodel : DifferentiableOn ℂ model (petal R) := by
    intro u hu
    exact (analyticAt_model (by change R < _ at hu; linarith)).differentiableAt.differentiableWithinAt
  have hmaps : MapsTo parabolicMap (petal R) (petal R) := by
    simpa using mapsTo_iterate_petal hR 1
  exact ((hmodel.comp differentiable_parabolicMap.differentiableOn hmaps).sub hmodel).sub_const 1

/-- The coordinate defined by the actual defect series is holomorphic on a
nonempty explicit attracting petal, and its finite partial sums converge
uniformly there. The dynamics and convergence hypotheses are all discharged. -/
theorem exists_holomorphic_attracting_coordinate :
    ∃ R C : ℝ, 32 ≤ R ∧ 0 ≤ C ∧
      DifferentiableOn ℂ
        (correctedCoordinate parabolicMap model (coordinateDefect parabolicMap model)) (petal R) ∧
      TendstoUniformlyOn
        (fun n : ℕ => fun u : ℂ =>
          ∑ k ∈ Finset.range n, orbitTerm parabolicMap (coordinateDefect parabolicMap model) u k)
        (fun u => ∑' k : ℕ, orbitTerm parabolicMap (coordinateDefect parabolicMap model) u k)
        atTop (petal R) ∧
      ∀ u ∈ petal R,
        Summable (fun k => ‖orbitTerm parabolicMap (coordinateDefect parabolicMap model) u k‖) ∧
        correctedCoordinate parabolicMap model (coordinateDefect parabolicMap model) (parabolicMap u) =
          correctedCoordinate parabolicMap model (coordinateDefect parabolicMap model) u + 1 := by
  obtain ⟨R, C, hR, hC, hresult⟩ := exists_attracting_fatou_coordinate
  have hbound : ∀ k : ℕ, ∀ u ∈ petal R,
      ‖orbitTerm parabolicMap (coordinateDefect parabolicMap model) u k‖ ≤
        C / ((k : ℝ) + 1) ^ 2 := by
    intro k u hu
    exact (hresult u hu.le).1 k
  have hterms : ∀ k : ℕ,
      DifferentiableOn ℂ (fun u => orbitTerm parabolicMap (coordinateDefect parabolicMap model) u k)
        (petal R) := by
    intro k
    exact (differentiableOn_defect_petal hR).comp
      (differentiable_parabolicMap.iterate k).differentiableOn (mapsTo_iterate_petal hR k)
  have hmodel : DifferentiableOn ℂ model (petal R) := by
    intro u hu
    exact (analyticAt_model (by change R < _ at hu; linarith)).differentiableAt.differentiableWithinAt
  have hsum := Complex.differentiableOn_tsum_of_summable_norm
    (summable_parabolic_majorant C (by norm_num : 2 ≤ (2 : ℕ))) hterms
    (petal_isOpen (by linarith)) (fun k u hu => hbound k u hu)
  have huni := tendstoUniformlyOn_tsum
    (summable_parabolic_majorant C (by norm_num : 2 ≤ (2 : ℕ))) (fun k u hu => hbound k u hu)
  refine ⟨R, C, hR, hC, hmodel.add hsum, ?_, ?_⟩
  · intro v hv
    exact (tendsto_finset_range : Tendsto Finset.range atTop atTop).eventually (huni v hv)
  · intro u hu
    exact ⟨(hresult u hu.le).2.1, (hresult u hu.le).2.2.1⟩

end Kneser.ParabolicFatouHolomorphic

end
