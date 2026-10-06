import Kneser.PreparedTwoRootDivision

/-!
# Actual analytic paired logarithmic defect

The reciprocal logarithmic multipliers are combined before taking the
merging-parameter limit. Joint analyticity and divisibility by the actual
root polynomial are consequences of the proved analytic divisions.
-/

noncomputable section

namespace Kneser.ExponentialLogDefect

open Kneser.PreparedTwoRootDivision Kneser.ExponentialPreparedModel
open Kneser.ExponentialMatrixDividedDifference Kneser.ExponentialUnfolding
open Filter
open scoped Topology

def symmetrizeFirst (F : Pair → ℂ) (p : Pair) : ℂ :=
  (F p + F (reflectFirst p)) / 2

theorem symmetrizeFirst_even (F : Pair → ℂ) (p : Pair) :
    symmetrizeFirst F (reflectFirst p) = symmetrizeFirst F p := by
  simp only [symmetrizeFirst, reflectFirst, neg_neg, add_comm]

theorem analyticAt_symmetrizeFirst {F : Pair → ℂ} (hF : AnalyticAt ℂ F 0) :
    AnalyticAt ℂ (symmetrizeFirst F) 0 :=
  (hF.add (hF.comp_of_eq analyticAt_reflectFirst (by simp [reflectFirst]))).div_const

/-- An even joint germ is analytic in the original parameter along any
analytic spatial curve lying at its point of analyticity. -/
theorem analyticAt_even_pair_descent_curve {G : Pair → ℂ} {v : ℂ → ℂ}
    (hG : AnalyticAt ℂ G (0, v 0)) (heven : ∀ p, G (reflectFirst p) = G p)
    (hv : AnalyticAt ℂ v 0) :
    AnalyticAt ℂ (fun s => G (Complex.sqrt s, v s)) 0 := by
  let F : ℂ → ℂ := fun x => G (x, v (x ^ 2))
  have hvs : AnalyticAt ℂ (fun x : ℂ => v (x ^ 2)) 0 :=
    hv.comp_of_eq (f := fun x : ℂ => x ^ 2) (analyticAt_id.pow 2) (by simp)
  have hcurve : AnalyticAt ℂ (fun x : ℂ => (x, v (x ^ 2))) 0 := analyticAt_id.prod hvs
  have hFa : AnalyticAt ℂ F 0 := hG.comp_of_eq hcurve (by simp)
  have hFeven : ∀ x, F (-x) = F x := by
    intro x
    dsimp [F]
    rw [neg_sq]
    exact heven (x, v (x ^ 2))
  have hd := Kneser.AnalyticEvenDescent.analyticAt_even_sqrt hFeven hFa
  convert hd using 1
  funext s
  simp only [F, Kneser.AnalyticEvenDescent.square_sqrt]

theorem continuousAt_even_pair_descent {G : Pair → ℂ} {u : ℂ}
    (hG : ContinuousAt G (0, u)) :
    ContinuousAt (fun p : Pair => G (Complex.sqrt p.1, p.2)) (0, u) := by
  exact continuousAt_sqrt_substitution (fun x u => G (x, u)) u hG

/-- The actual logarithmic defect has a jointly analytic extension and its
first root-polynomial factor is constructed at the merger. -/
theorem exists_analytic_log_defect {U : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0) (hUd : deriv U 0 ≠ 0)
    (hroots : ∀ᶠ x in 𝓝 0, unfolding (x ^ 2) (U x) = U x ∧
      unfolding (x ^ 2) (U (-x)) = U (-x))
    (hdistinct : ∀ᶠ x in 𝓝 0, U x = U (-x) ↔ x = 0) :
    ∃ F φ : Pair → ℂ, AnalyticAt ℂ F 0 ∧ AnalyticAt ℂ φ 0 ∧
      (∀ p, F (reflectFirst p) = F p) ∧
      (∀ p, φ (reflectFirst p) = φ p) ∧
      (∀ᶠ p in 𝓝 (0 : Pair), F p =
        (p.2 - U p.1) * (p.2 - U (-p.1)) * φ p) ∧
      (∀ᶠ p in 𝓝 (0 : Pair), p.1 ≠ 0 → F p =
        Complex.log (1 + (p.2 - U (-p.1)) * symmetricCofactor U p.1 p.2) /
          Complex.log (rootMultiplier U p.1) +
        Complex.log (1 + (p.2 - U p.1) * symmetricCofactor U p.1 p.2) /
          Complex.log (rootMultiplier U (-p.1)) - 1) := by
  obtain ⟨H, hHa, hH0, hH⟩ := exists_log_multiplier_factor hU hU0
  have hHne : H 0 ≠ 0 := by simpa only [hH0] using hUd
  let N : Pair → ℂ := fun p => logDefectNumerator U H p.1 p.2
  have hNa : AnalyticAt ℂ N 0 := analyticAt_logDefectNumerator hU hU0 hHa hHne
  obtain ⟨C, hCa, hCeven, hC⟩ := exists_even_coordinate_factor hNa
    (Filter.Eventually.of_forall (fun u => logDefectNumerator_zero U H u))
    (fun p => logDefectNumerator_odd U H p.1 p.2)
  let F : Pair → ℂ := fun p => C p - 1
  have hFa : AnalyticAt ℂ F 0 := hCa.sub analyticAt_const
  have hFeven : ∀ p, F (reflectFirst p) = F p := by intro p; simp [F, hCeven]
  have hHnear : ∀ᶠ x in 𝓝 0, H x ≠ 0 := hHa.continuousAt.eventually_ne hHne
  have hneg : Tendsto (fun x : ℂ => -x) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using continuous_neg.continuousAt.tendsto (x := (0 : ℂ))
  have hUn : AnalyticAt ℂ (fun x => U (-x)) 0 :=
    hU.comp_of_eq (f := fun x : ℂ => -x) analyticAt_id.neg (by simp)
  have hcp : AnalyticAt ℂ (fun x => (x, U x)) 0 := analyticAt_id.prod hU
  have hcn : AnalyticAt ℂ (fun x => (x, U (-x))) 0 := analyticAt_id.prod hUn
  have hcp0 : ((0 : ℂ), U 0) = (0 : Pair) := by simp [hU0]
  have hcn0 : ((0 : ℂ), U (-(0 : ℂ))) = (0 : Pair) := by simp [hU0]
  have hcpt : Tendsto (fun x => (x, U x)) (𝓝 0) (𝓝 (0 : Pair)) := by
    simpa only [hcp0] using hcp.continuousAt.tendsto
  have hcnt : Tendsto (fun x => (x, U (-x))) (𝓝 0) (𝓝 (0 : Pair)) := by
    simpa only [hcn0] using hcn.continuousAt.tendsto
  have hfactor := eventually_symmetricCofactor_factor hU hroots hdistinct
  have hFzero : ∀ᶠ x in 𝓝 0, F (x, U x) = 0 ∧ F (x, U (-x)) = 0 := by
    have hz : ∀ᶠ x in 𝓝 0, x ≠ 0 → F (x, U x) = 0 ∧ F (x, U (-x)) = 0 := by
      filter_upwards [hroots, hneg.eventually hroots, hfactor, hneg.eventually hfactor,
        hHnear, hneg.eventually hHnear, hcpt.eventually hC, hcnt.eventually hC]
        with x hr hnr hf hnf hh hnh hcx hcnx hx
      have hNp := logDefectNumerator_at_root U H hH x hh hr.1 hf
      have hNn := logDefectNumerator_at_root U H hH (-x) hnh hnr.1 hnf
      have hNn' : logDefectNumerator U H x (U (-x)) = x := by
        rw [logDefectNumerator_odd] at hNn
        linear_combination -hNn
      have hCpos : C (x, U x) = 1 := by
        apply mul_left_cancel₀ hx
        simpa only [N, mul_one] using hcx.symm.trans hNp
      have hCneg : C (x, U (-x)) = 1 := by
        apply mul_left_cancel₀ hx
        simpa only [N, mul_one] using hcnx.symm.trans hNn'
      exact ⟨by simp [F, hCpos], by simp [F, hCneg]⟩
    have hzp : ∀ᶠ x in 𝓝 0, F (x, U x) = 0 := eventually_zero_of_punctured
      (hFa.comp_of_eq hcp hcp0).continuousAt (hz.mono (fun _ h hx => (h hx).1))
    have hzn : ∀ᶠ x in 𝓝 0, F (x, U (-x)) = 0 := eventually_zero_of_punctured
      (hFa.comp_of_eq hcn hcn0).continuousAt (hz.mono (fun _ h hx => (h hx).2))
    exact hzp.and hzn
  obtain ⟨D, hDa, hD⟩ := exists_two_root_factor hFa hU hU0 hdistinct hFzero
  refine ⟨F, symmetrizeFirst D, hFa, analyticAt_symmetrizeFirst hDa,
    hFeven, symmetrizeFirst_even D, ?_, ?_⟩
  · filter_upwards [hD, reflectFirst_tendsto.eventually hD] with p hp hnp
    rw [hFeven] at hnp
    simp only [reflectFirst, neg_neg] at hnp
    dsimp [symmetrizeFirst, reflectFirst]
    linear_combination (hp + hnp) / 2
  · have hfst : Tendsto (fun p : Pair => p.1) (𝓝 0) (𝓝 (0 : ℂ)) :=
      continuous_fst.tendsto 0
    filter_upwards [hC, hfst.eventually hHnear, hfst.eventually (hneg.eventually hHnear)]
      with p hp hh hnh hx
    have hcv : C p = N p / p.1 := by
      apply (eq_div_iff hx).mpr
      linear_combination -hp
    dsimp [F]
    rw [hcv]
    exact congrArg (fun z : ℂ => z - 1)
      (logDefectNumerator_residue_pair U H hH p.1 p.2 hx hh hnh)

end Kneser.ExponentialLogDefect

end
