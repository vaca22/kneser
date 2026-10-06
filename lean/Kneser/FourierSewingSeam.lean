import Kneser.FourierSewingHalfPlaneGeometry

/-!
The actual sewing seam is the unique inverse image of the real line under
the constructed negative Fourier map.  Its boundedness, continuity,
injectivity and translation law are proved rather than assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.FourierSewing

open Set Filter Metric
open scoped Topology Classical
open Kneser.WeightedFourier

def lowerMap (H : ℝ) (Q : Space) (z : ℂ) : ℂ := z + evaluate H Q z

theorem norm_evaluate_negative_sub_le (H : ℝ) (Q : Space) (hQ : Q ∈ Negative)
    (v : ℝ) (hgap : 0 < H - v) (z w : ℂ) (hz : z.im ≤ v) (hw : w.im ≤ v) :
    ‖evaluate H Q z - evaluate H Q w‖ ≤
      halfPlaneLipschitz H (-v) (reflection Q) * ‖z - w‖ := by
  have hl := norm_evaluate_positive_sub_le_on_halfPlane H (reflection Q)
    (reflection_negative_is_positive Q hQ) (-v) (by linarith) (-z) (-w)
    (by simp only [Complex.neg_im]; linarith) (by simp only [Complex.neg_im]; linarith)
  simpa only [evaluate_reflection, neg_neg, neg_sub_neg, norm_sub_rev] using hl

theorem lowerMap_translation (H : ℝ) (Q : Space) (z : ℂ) :
    lowerMap H Q (z + 1) = lowerMap H Q z + 1 := by
  unfold lowerMap
  rw [evaluate_periodic]
  ring

theorem exists_periodic_seam (H : ℝ) (Q : Space) (hQ : Q ∈ Negative)
    (v ρ : ℝ) (hρ : 0 ≤ ρ) (hmargin : ρ ≤ v) (hgap : 0 < H - v)
    (hQnorm : ‖Q‖ ≤ ρ) (hsmall : halfPlaneLipschitz H (-v) (reflection Q) < 1) :
    ∃ γ : ℝ → ℂ, Continuous γ ∧ Function.Injective γ ∧
      (∀ x : ℝ, ‖γ x - (x : ℂ)‖ ≤ ρ ∧ (γ x).im ≤ v ∧ lowerMap H Q (γ x) = (x : ℂ)) ∧
      (∀ x : ℝ, γ (x + 1) = γ x + 1) ∧
      (∀ x : ℝ, |(γ x).im| ≤ ρ) ∧
      Set.range γ = {z : ℂ | z.im ≤ v ∧ (lowerMap H Q z).im = 0} := by
  have hpre (x : ℝ) : ∃ z : ℂ, ‖z - (x : ℂ)‖ ≤ ρ ∧ z.im ≤ v ∧ lowerMap H Q z = (x : ℂ) := by
    exact exists_lower_preimage H Q hQ v ρ hρ hgap hQnorm hsmall (x : ℂ)
      (by simp only [Complex.ofReal_im]; linarith)
  choose γ hγ using hpre
  have hnear (x : ℝ) := (hγ x).1
  have him (x : ℝ) := (hγ x).2.1
  have hid (x : ℝ) := (hγ x).2.2
  let K := halfPlaneLipschitz H (-v) (reflection Q)
  have hK : K < 1 := hsmall
  have hKpos : 0 ≤ K := by unfold K halfPlaneLipschitz; positivity
  have hdenom : 0 < 1 - K := by linarith
  have hbound (x y : ℝ) : ‖γ x - γ y‖ ≤ (1 - K)⁻¹ * dist x y := by
    have he : γ x - γ y = (x : ℂ) - y - (evaluate H Q (γ x) - evaluate H Q (γ y)) := by
      have hx := hid x
      have hy := hid y
      unfold lowerMap at hx hy
      linear_combination hx - hy
    have hnorm := norm_sub_le ((x : ℂ) - y) (evaluate H Q (γ x) - evaluate H Q (γ y))
    have hcoef := norm_evaluate_negative_sub_le H Q hQ v hgap (γ x) (γ y) (him x) (him y)
    have hineq : ‖γ x - γ y‖ ≤ ‖(x : ℂ) - y‖ + K * ‖γ x - γ y‖ := by
      conv_lhs => rw [he]
      exact hnorm.trans (add_le_add le_rfl hcoef)
    have hreal : ‖(x : ℂ) - y‖ = dist x y := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Real.dist_eq]
    rw [hreal] at hineq
    have hh : (1 - K) * ‖γ x - γ y‖ ≤ dist x y := by nlinarith
    calc
      ‖γ x - γ y‖ = (1 - K)⁻¹ * ((1 - K) * ‖γ x - γ y‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hdenom), one_mul]
      _ ≤ (1 - K)⁻¹ * dist x y := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hdenom.le)
  let C : NNReal := ⟨(1 - K)⁻¹, inv_nonneg.mpr hdenom.le⟩
  have hC : (C : ℝ) = (1 - K)⁻¹ := rfl
  have hlip : LipschitzWith C γ := LipschitzWith.of_dist_le_mul (fun x y => by
    rw [hC, dist_eq_norm]
    exact hbound x y)
  have hinj : Function.Injective γ := by
    intro x y hxy
    have hh := congrArg (lowerMap H Q) hxy
    rw [hid x, hid y] at hh
    exact Complex.ofReal_injective hh
  have hmapinj := injOn_negative_sewing H Q hQ v hgap hsmall
  refine ⟨γ, hlip.continuous, hinj, hγ, ?_, ?_, ?_⟩
  · intro x
    apply hmapinj (him (x + 1)) (by
      change (γ x + 1).im ≤ v
      simpa only [Complex.add_im, Complex.one_im, add_zero] using him x)
    change lowerMap H Q (γ (x + 1)) = lowerMap H Q (γ x + 1)
    rw [hid (x + 1), lowerMap_translation, hid x]
    push_cast
    rfl
  · intro x
    have hh := Complex.abs_im_le_norm (γ x - (x : ℂ))
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using hh.trans (hnear x)
  · apply Set.Subset.antisymm
    · rintro z ⟨x, rfl⟩
      refine ⟨him x, ?_⟩
      rw [hid x, Complex.ofReal_im]
    · intro z hz
      let x : ℝ := (lowerMap H Q z).re
      have he : lowerMap H Q z = (x : ℂ) := by
        apply Complex.ext
        · rfl
        · simpa only [Complex.ofReal_im] using hz.2
      refine ⟨x, ?_⟩
      apply hmapinj (him x) hz.1
      change lowerMap H Q (γ x) = lowerMap H Q z
      rw [hid x, he]

end Kneser.FourierSewing

end
