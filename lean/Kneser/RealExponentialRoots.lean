import Kneser.ExponentialUnfolding
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-!
# Actual ordered real fixed points for small positive parameters

The roots are obtained by the intermediate value theorem applied directly to
the real exponential map. Reality and ordering are conclusions; they are not
assumed properties of a complex analytic square-root branch.
-/

namespace Kneser.RealExponentialRoots

open Filter Metric Set Kneser.ExponentialUnfolding
open scoped Topology

noncomputable def realDefect (s u : ℝ) : ℝ := Real.exp (-s + (1 - s) * u) - 1 - u

theorem actual_root_of_realDefect_zero (s u : ℝ) (h : realDefect s u = 0) :
    unfolding (s : ℂ) (u : ℂ) = (u : ℂ) := by
  have hr : Real.exp (-s + (1 - s) * u) - 1 = u := by
    dsimp [realDefect] at h
    linarith
  simpa [unfolding, Complex.ofReal_exp] using congrArg Complex.ofReal hr

/-- For every prescribed spatial neighbourhood, all sufficiently small
positive real parameters have one negative and one positive actual fixed point. -/
theorem exists_ordered_small_real_roots (δ : ℝ) (hδ : 0 < δ) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 / 2 ∧
      ∀ s : ℝ, 0 < s → s < s₀ →
        ∃ a b : ℝ, -δ < a ∧ a < 0 ∧ 0 < b ∧ b < δ ∧
          unfolding (s : ℂ) (a : ℂ) = (a : ℂ) ∧
          unfolding (s : ℂ) (b : ℂ) = (b : ℂ) := by
  have hminus : 0 < realDefect 0 (-δ) := by
    have he := Real.add_one_lt_exp (show -δ ≠ 0 by linarith)
    dsimp [realDefect]
    simp only [neg_zero, sub_zero, one_mul, zero_add]
    linarith
  have hplus : 0 < realDefect 0 δ := by
    have he := Real.add_one_lt_exp (ne_of_gt hδ)
    dsimp [realDefect]
    simp only [neg_zero, sub_zero, one_mul, zero_add]
    linarith
  have hcminus : Continuous (fun s : ℝ => realDefect s (-δ)) := by
    unfold realDefect
    fun_prop
  have hcplus : Continuous (fun s : ℝ => realDefect s δ) := by
    unfold realDefect
    fun_prop
  have hevent : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < realDefect s (-δ) ∧ 0 < realDefect s δ :=
    (hcminus.continuousAt.eventually (Ioi_mem_nhds hminus)).and
      (hcplus.continuousAt.eventually (Ioi_mem_nhds hplus))
  obtain ⟨r, hr, hsign⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨min r (1 / 2), lt_min hr (by norm_num), min_le_right _ _, ?_⟩
  intro s hs hs₀
  have hsr : s < r := lt_of_lt_of_le hs₀ (min_le_left _ _)
  have hdist : dist s 0 < r := by simpa [dist_zero_right, Real.norm_eq_abs, abs_of_pos hs] using hsr
  obtain ⟨hsm, hsp⟩ := hsign hdist
  have hzero : realDefect s 0 < 0 := by
    dsimp [realDefect]
    simp only [mul_zero, add_zero, sub_zero]
    exact sub_neg.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hcont : Continuous (realDefect s) := by
    unfold realDefect
    fun_prop
  obtain ⟨a, hai, haroot⟩ := intermediate_value_Icc' (by linarith : -δ ≤ 0)
    hcont.continuousOn (show (0 : ℝ) ∈ Icc (realDefect s 0) (realDefect s (-δ)) from ⟨hzero.le, hsm.le⟩)
  obtain ⟨b, hbi, hbroot⟩ := intermediate_value_Icc (by linarith : 0 ≤ δ)
    hcont.continuousOn (show (0 : ℝ) ∈ Icc (realDefect s 0) (realDefect s δ) from ⟨hzero.le, hsp.le⟩)
  have ha_lower : -δ < a := by
    rcases lt_or_eq_of_le hai.1 with ha | ha
    · exact ha
    · rw [ha, haroot] at hsm
      linarith
  have ha_upper : a < 0 := by
    rcases lt_or_eq_of_le hai.2 with ha | ha
    · exact ha
    · rw [← ha, haroot] at hzero
      linarith
  have hb_lower : 0 < b := by
    rcases lt_or_eq_of_le hbi.1 with hb | hb
    · exact hb
    · rw [hb, hbroot] at hzero
      linarith
  have hb_upper : b < δ := by
    rcases lt_or_eq_of_le hbi.2 with hb | hb
    · exact hb
    · rw [← hb, hbroot] at hsp
      linarith
  exact ⟨a, b, ha_lower, ha_upper, hb_lower, hb_upper,
    actual_root_of_realDefect_zero s a haroot, actual_root_of_realDefect_zero s b hbroot⟩

end Kneser.RealExponentialRoots
