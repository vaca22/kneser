import Kneser.JointAnalyticDivision
import Kneser.ExponentialPreparedModel

/-!
# Joint analytic division at two coalescing moving roots

Both divisions use the actual contraction-integral quotient. The zero at
the second root after the first division is proved at the merger by
continuity from nonzero parameters.
-/

noncomputable section

namespace Kneser.PreparedTwoRootDivision

open Filter Kneser.JointAnalyticDivision
open scoped Topology

abbrev Pair := ℂ × ℂ

def reflectFirst (p : Pair) : Pair := (-p.1, p.2)

theorem analyticAt_reflectFirst : AnalyticAt ℂ reflectFirst (0 : Pair) :=
  analyticAt_fst.neg.prod analyticAt_snd

theorem reflectFirst_tendsto : Tendsto reflectFirst (𝓝 (0 : Pair)) (𝓝 (0 : Pair)) := by
  convert (by simpa [reflectFirst] using analyticAt_reflectFirst.continuousAt.tendsto) using 1 <;> rfl

/-- A continuous germ that vanishes for all nearby nonzero parameters also
vanishes at the merger, hence on a full neighbourhood. -/
theorem eventually_zero_of_punctured {f : ℂ → ℂ} (hf : ContinuousAt f 0)
    (hzero : ∀ᶠ x in 𝓝 0, x ≠ 0 → f x = 0) : ∀ᶠ x in 𝓝 0, f x = 0 := by
  have hpunct : f =ᶠ[𝓝[≠] 0] (fun _ => 0) := by
    filter_upwards [hzero.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with x hx hne
    exact hx hne
  have hf0 : f 0 = 0 := tendsto_nhds_unique_of_eventuallyEq
    (hf.tendsto.mono_left nhdsWithin_le_nhds) tendsto_const_nhds hpunct
  filter_upwards [hzero] with x hx
  by_cases hne : x = 0
  · simpa only [hne] using hf0
  · exact hx hne

/-- An odd numerator yields a globally even analytic coordinate quotient. -/
theorem exists_even_coordinate_factor {B : Pair → ℂ}
    (hB : AnalyticAt ℂ B (0 : Pair))
    (hzero : ∀ᶠ u : ℂ in 𝓝 0, B (0, u) = 0)
    (hodd : ∀ p, B (reflectFirst p) = -B p) :
    ∃ C : Pair → ℂ, AnalyticAt ℂ C (0 : Pair) ∧
      (∀ p, C (reflectFirst p) = C p) ∧
      (∀ᶠ p in 𝓝 (0 : Pair), B p = p.1 * C p) := by
  obtain ⟨D, hDa, hD⟩ := exists_coordinate_factor hB hzero
  let C : Pair → ℂ := fun p => (D p + D (reflectFirst p)) / 2
  have hCa : AnalyticAt ℂ C 0 :=
    (hDa.add (hDa.comp_of_eq analyticAt_reflectFirst (by simp [reflectFirst]))).div_const
  refine ⟨C, hCa, ?_, ?_⟩
  · intro p
    simp only [C, reflectFirst, neg_neg, add_comm]
  · filter_upwards [hD, reflectFirst_tendsto.eventually hD] with p hp hnp
    rw [hodd] at hnp
    change -B p = -p.1 * D (reflectFirst p) at hnp
    dsimp [C]
    linear_combination (hp - hnp) / 2

/-- Divide by the genuine product of two coalescing analytic roots. -/
theorem exists_two_root_factor {B : Pair → ℂ} {U : ℂ → ℂ}
    (hB : AnalyticAt ℂ B (0 : Pair)) (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hdistinct : ∀ᶠ x in 𝓝 0, U x = U (-x) ↔ x = 0)
    (hzero : ∀ᶠ x in 𝓝 0, B (x, U x) = 0 ∧ B (x, U (-x)) = 0) :
    ∃ C : Pair → ℂ, AnalyticAt ℂ C (0 : Pair) ∧
      (∀ᶠ p in 𝓝 (0 : Pair),
        B p = (p.2 - U p.1) * (p.2 - U (-p.1)) * C p) := by
  obtain ⟨D, hDa, hD⟩ := exists_moving_root_factor hB hU hU0 (hzero.mono (fun _ h => h.1))
  have hUn : AnalyticAt ℂ (fun x => U (-x)) 0 :=
    hU.comp_of_eq (f := fun x : ℂ => -x) analyticAt_id.neg (by simp)
  have hcurve : AnalyticAt ℂ (fun x => (x, U (-x))) 0 := analyticAt_id.prod hUn
  have hcurve0 : ((0 : ℂ), U (-(0 : ℂ))) = (0 : Pair) := by simp [hU0]
  have hDt : ContinuousAt (fun x => D (x, U (-x))) 0 :=
    (hDa.comp_of_eq hcurve hcurve0).continuousAt
  have hct : Tendsto (fun x => (x, U (-x))) (𝓝 0) (𝓝 (0 : Pair)) := by
    simpa only [hcurve0] using hcurve.continuousAt.tendsto
  have hDzero : ∀ᶠ x in 𝓝 0, D (x, U (-x)) = 0 := by
    apply eventually_zero_of_punctured hDt
    filter_upwards [hzero, hdistinct, hct.eventually hD] with x hx hd hdx hne
    rw [hx.2] at hdx
    have hgap : U (-x) - U x ≠ 0 :=
      sub_ne_zero.mpr (fun he => hne (hd.mp he.symm))
    exact (mul_eq_zero.mp hdx.symm).resolve_left hgap
  obtain ⟨C, hCa, hC⟩ := exists_moving_root_factor hDa hUn (by simpa [hU0]) hDzero
  refine ⟨C, hCa, ?_⟩
  filter_upwards [hD, hC] with p hp hc
  rw [hp, hc, mul_assoc]

end Kneser.PreparedTwoRootDivision

end
