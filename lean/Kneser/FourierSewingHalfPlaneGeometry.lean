import Kneser.WeightedFourierUnivalent
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Quantitative half-plane coverage is constructed by contraction from the
actual Fourier corrections.  Together with univalence it supplies the
geometric sewing maps on both sides of the seam.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.FourierSewing

open Set Filter Metric
open scoped Topology Classical
open Kneser.WeightedFourier

theorem halfPlaneLipschitz_at_unit_gap_lt_one (H : ℝ) (a : Space) (ha : ‖a‖ ≤ 1 / 4) :
    halfPlaneLipschitz H (1 - H) a < 1 := by
  have hq : 0 < Real.exp (-2 * Real.pi) := Real.exp_pos _
  have hlarge : (7 : ℝ) ≤ Real.exp (2 * Real.pi) := by
    linarith [Real.add_one_le_exp (2 * Real.pi), Real.pi_gt_three]
  have hqsmall : Real.exp (-2 * Real.pi) ≤ 1 / 7 := by
    rw [show -2 * Real.pi = -(2 * Real.pi) by ring, Real.exp_neg]
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 7) hlarge
  have hqone : Real.exp (-2 * Real.pi) < 1 := hqsmall.trans_lt (by norm_num)
  rw [halfPlaneLipschitz, show H + (1 - H) = 1 by ring, mul_one]
  apply (div_lt_one (sq_pos_of_pos (by linarith : 0 < 1 - Real.exp (-2 * Real.pi)))).mpr
  have hcoeff : 4 * Real.pi * ‖a‖ ≤ 4 := by
    have h := mul_le_mul_of_nonneg_left ha (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
    nlinarith [Real.pi_lt_four]
  have hn := mul_le_mul_of_nonneg_right hcoeff hq.le
  nlinarith [sq_nonneg (Real.exp (-2 * Real.pi))]

theorem exists_upper_preimage (H : ℝ) (P : Space)
    (hP : ∀ n : ℤ, n < 0 → P n = 0) (v ρ : ℝ) (hρ : 0 ≤ ρ)
    (hgap : 0 < H + v) (hPnorm : ‖P‖ ≤ ρ)
    (hsmall : halfPlaneLipschitz H v P < 1) (t₀ y : ℂ)
    (hy : v + ρ ≤ (y - t₀).im) :
    ∃ z : ℂ, ‖z - (y - t₀)‖ ≤ ρ ∧ v ≤ z.im ∧ z + t₀ + evaluate H P z = y := by
  let c := y - t₀
  let f : ℂ → ℂ := fun z => c - evaluate H P z
  have hpoint (z : ℂ) (hz : z ∈ closedBall c ρ) : v ≤ z.im := by
    have hh := im_lower_on_closedBall c z ρ hz
    dsimp [c] at hh
    have hy' : v + ρ ≤ y.im - t₀.im := by simpa only [Complex.sub_im] using hy
    linarith
  have hm : MapsTo f (closedBall c ρ) (closedBall c ρ) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    change ‖c - evaluate H P z - c‖ ≤ ρ
    rw [show c - evaluate H P z - c = -evaluate H P z by abel, norm_neg]
    exact (norm_evaluate_positive_le H P hP z (by have hh := hpoint z hz; linarith)).trans hPnorm
  let K : NNReal := ⟨halfPlaneLipschitz H v P, by unfold halfPlaneLipschitz; positivity⟩
  have hc : ContractingWith K (hm.restrict f _ _) := by
    refine ⟨hsmall, LipschitzWith.of_dist_le_mul ?_⟩
    intro z w
    change dist (f z.val) (f w.val) ≤ _ * dist z.val w.val
    rw [dist_eq_norm, dist_eq_norm]
    have he : f z.val - f w.val = -(evaluate H P z.val - evaluate H P w.val) := by dsimp [f]; abel
    rw [he, norm_neg]
    exact norm_evaluate_positive_sub_le_on_halfPlane H P hP v hgap _ _
      (hpoint _ z.property) (hpoint _ w.property)
  obtain ⟨z, hz, hfixed, _, _⟩ := ContractingWith.exists_fixedPoint'
    isClosed_closedBall.isComplete hm hc (by simpa [mem_closedBall] using hρ : c ∈ closedBall c ρ)
    (edist_ne_top c (f c))
  refine ⟨z, by simpa [mem_closedBall, dist_eq_norm] using hz, hpoint z hz, ?_⟩
  have he : (y - t₀) - evaluate H P z = z := hfixed
  linear_combination -he

theorem evaluate_neg (H : ℝ) (a : Space) (z : ℂ) :
    evaluate H (-a) z = -evaluate H a z := by
  simp only [evaluate, coefficient, lp.coeFn_neg, Pi.neg_apply, neg_div, neg_mul, tsum_neg]

theorem exists_lower_preimage (H : ℝ) (Q : Space) (hQ : Q ∈ Negative)
    (v ρ : ℝ) (hρ : 0 ≤ ρ) (hgap : 0 < H - v) (hQnorm : ‖Q‖ ≤ ρ)
    (hsmall : halfPlaneLipschitz H (-v) (reflection Q) < 1) (y : ℂ)
    (hy : y.im ≤ v - ρ) :
    ∃ z : ℂ, ‖z - y‖ ≤ ρ ∧ z.im ≤ v ∧ z + evaluate H Q z = y := by
  have hpos : ∀ n : ℤ, n < 0 → (-reflection Q) n = 0 := by
    intro n hn
    simp only [lp.coeFn_neg, Pi.neg_apply, reflection_negative_is_positive Q hQ n hn, neg_zero]
  have hnorm : ‖-reflection Q‖ ≤ ρ := by simpa only [norm_neg, norm_reflection] using hQnorm
  have hsmall' : halfPlaneLipschitz H (-v) (-reflection Q) < 1 := by
    simpa only [halfPlaneLipschitz, norm_neg] using hsmall
  obtain ⟨z, hz, hzim, he⟩ := exists_upper_preimage H (-reflection Q) hpos (-v) ρ hρ
    (by linarith) hnorm hsmall' 0 (-y) (by simp only [sub_zero, Complex.neg_im]; linarith)
  refine ⟨-z, ?_, ?_, ?_⟩
  · rw [show -z - y = -(z + y) by abel, norm_neg]
    simpa only [sub_zero, sub_neg_eq_add] using hz
  · simpa only [Complex.neg_im, neg_neg] using neg_le_neg hzim
  · simp only [add_zero, evaluate_neg, evaluate_reflection] at he
    linear_combination -he

/-- The constructed lower sewing map bijects its actual sublevel domain
onto every sufficiently low physical half-plane; no coverage assumption
is needed. -/
theorem bijOn_lower_sublevel (H : ℝ) (Q : Space) (hQ : Q ∈ Negative)
    (v ρ a : ℝ) (hρ : 0 ≤ ρ) (hgap : 0 < H - v) (hQnorm : ‖Q‖ ≤ ρ)
    (hsmall : halfPlaneLipschitz H (-v) (reflection Q) < 1) (ha : a ≤ v - ρ) :
    Set.BijOn (fun z : ℂ => z + evaluate H Q z)
      {z : ℂ | z.im ≤ v ∧ (z + evaluate H Q z).im ≤ a} {y : ℂ | y.im ≤ a} := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact hz.2
  · exact (injOn_negative_sewing H Q hQ v hgap hsmall).mono (fun z hz => hz.1)
  · intro y hy
    obtain ⟨z, _, hz, he⟩ := exists_lower_preimage H Q hQ v ρ hρ hgap hQnorm hsmall y (hy.trans ha)
    refine ⟨z, ⟨hz, ?_⟩, he⟩
    rw [he]
    exact hy

theorem bijOn_upper_superlevel (H : ℝ) (P : Space)
    (hP : ∀ n : ℤ, n < 0 → P n = 0)
    (v ρ a : ℝ) (hρ : 0 ≤ ρ) (hgap : 0 < H + v) (hPnorm : ‖P‖ ≤ ρ)
    (hsmall : halfPlaneLipschitz H v P < 1) (ha : v + ρ ≤ a) (t₀ : ℂ) :
    Set.BijOn (fun z : ℂ => z + t₀ + evaluate H P z)
      {z : ℂ | v ≤ z.im ∧ a ≤ ((z + t₀ + evaluate H P z) - t₀).im}
      {y : ℂ | a ≤ (y - t₀).im} := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact hz.2
  · exact (injOn_positive_sewing H P hP v hgap hsmall t₀).mono (fun z hz => hz.1)
  · intro y hy
    obtain ⟨z, _, hz, he⟩ := exists_upper_preimage H P hP v ρ hρ hgap hPnorm hsmall t₀ y (ha.trans hy)
    refine ⟨z, ⟨hz, ?_⟩, he⟩
    rw [he]
    exact hy

end Kneser.FourierSewing

end
