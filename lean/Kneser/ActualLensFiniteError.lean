import Kneser.ActualLensBounds
import Kneser.FiniteSeparatedKernelBounds

/-! The phase defect of a true finite orbit is bounded independently of its
length, using the actual chart product and separated real-time kernels. -/

noncomputable section
namespace Kneser.ActualLensFiniteError

open Kneser.ActualLensGeometry Kneser.ActualLensBounds Kneser.GrowingBandGeometry
open Kneser.GrowingBandKernel Kneser.FiniteSeparatedKernelBounds
open Kneser.ExponentialUnfolding Kneser.EvenPreparedOrbitDiscs
open scoped BigOperators

def errorBound (M Y θ : ℝ) : ℝ :=
  2 * M * smallConstant ^ 2 * (2 + Real.pi / (3 / 4)) / Y ^ 3 +
    2 * M * largeConstant ^ 2 * (Real.exp (2 * (3 / 4)) / (3 / 4)) * θ ^ 3

theorem true_lens_residual_kernel (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (s a b θ Y M : ℝ) (u : ℂ) (hab : a < b) (hθ : 0 < θ) (hY : 0 < Y)
    (hYθ : θ * Y ≤ Real.pi) (hratio : (b - a) / θ ≤ 5)
    (hua : u ≠ (a : ℂ)) (hub : u ≠ (b : ℂ))
    (hband : bandTime a b θ u ∈ strip θ Y)
    (hres : ‖descendedTerm A B Γ 2 u s 0‖ ≤ M * (‖u - (a : ℂ)‖ * ‖u - (b : ℂ)‖) ^ 2)
    (hM : 0 ≤ M) :
    ‖descendedTerm A B Γ 2 u s 0‖ ≤
      2 * M * smallConstant ^ 2 * (((bandTime a b θ u).re ^ 2 + Y ^ 2) ^ 2)⁻¹ +
      2 * M * largeConstant ^ 2 * θ ^ 4 * Real.exp (-2 * θ * |(bandTime a b θ u).re|) := by
  have hchart := bandChart_bandTime a b θ u (ne_of_lt hab) (ne_of_gt hθ) hua hub
  have hp := bandChart_product_bound a b θ Y (bandTime a b θ u) hab hθ hY hYθ hband hratio
  rw [hchart] at hp
  let X := (bandTime a b θ u).re
  have hD : 0 < X ^ 2 + Y ^ 2 := by nlinarith [sq_nonneg X]
  have hsmall : 0 ≤ smallConstant / (X ^ 2 + Y ^ 2) := by dsimp [smallConstant]; positivity
  have hlarge : 0 ≤ largeConstant * θ ^ 2 * Real.exp (-θ * |X|) := by dsimp [largeConstant]; positivity
  have hsquare : (‖u - (a : ℂ)‖ * ‖u - (b : ℂ)‖) ^ 2 ≤
      2 * (smallConstant / (X ^ 2 + Y ^ 2)) ^ 2 +
        2 * (largeConstant * θ ^ 2 * Real.exp (-θ * |X|)) ^ 2 := by
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ ‖u - (a : ℂ)‖ * ‖u - (b : ℂ)‖) hp 2
    nlinarith [sq_nonneg (smallConstant / (X ^ 2 + Y ^ 2) - largeConstant * θ ^ 2 * Real.exp (-θ * |X|))]
  have he : Real.exp (-θ * |X|) ^ 2 = Real.exp (-2 * θ * |X|) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  apply hres.trans
  apply (mul_le_mul_of_nonneg_left hsquare hM).trans_eq
  dsimp [X] at he ⊢
  rw [div_pow, mul_pow, mul_pow, he]
  ring

/-- The finite bounds refer to the actual orbit and need no assumptions
about subsequent iterates. -/
theorem finite_true_lens_residual_sum (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (u : ℂ) (s a b θ Y M : ℝ) (N : ℕ) (hab : a < b) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hY : 1 ≤ Y) (hYθ : θ * Y ≤ Real.pi)
    (hratio : (b - a) / θ ≤ 5) (hM : 0 ≤ M)
    (hroots : ∀ k < N, orbit u s k ≠ (a : ℂ) ∧ orbit u s k ≠ (b : ℂ))
    (hband : ∀ k < N, bandTime a b θ (orbit u s k) ∈ strip θ Y)
    (hres : ∀ k < N, ‖descendedTerm A B Γ 2 (orbit u s k) s 0‖ ≤
      M * (‖orbit u s k - (a : ℂ)‖ * ‖orbit u s k - (b : ℂ)‖) ^ 2)
    (hstep : ∀ k < N, (bandTime a b θ (orbit u s k)).re + 3 / 4 ≤
      (bandTime a b θ (orbit u s (k + 1))).re) :
    (∑ k ∈ Finset.range N, ‖descendedTerm A B Γ 2 (orbit u s k) s 0‖) ≤
      errorBound M Y θ := by
  let x : ℕ → ℝ := fun k => (bandTime a b θ (orbit u s k)).re
  have h₁ := finite_rational_kernel_bound x N (3 / 4) Y (by norm_num) hY hstep
  have h₂ := finite_exponential_cubic_bound x N (3 / 4) θ (by norm_num) hθ hθ1 hstep
  have hsum : (∑ k ∈ Finset.range N, ‖descendedTerm A B Γ 2 (orbit u s k) s 0‖) ≤
      ∑ k ∈ Finset.range N,
        (2 * M * smallConstant ^ 2 * ((x k ^ 2 + Y ^ 2) ^ 2)⁻¹ +
          2 * M * largeConstant ^ 2 * θ ^ 4 * Real.exp (-2 * θ * |x k|)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hkN := Finset.mem_range.mp hk
    exact true_lens_residual_kernel A B Γ s a b θ Y M (orbit u s k) hab hθ
      (by linarith) hYθ hratio (hroots k hkN).1 (hroots k hkN).2
      (hband k hkN) (hres k hkN) hM
  apply hsum.trans
  rw [Finset.sum_add_distrib]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  change 2 * (M * (smallConstant ^ 2 * _)) + 2 * (M * (largeConstant ^ 2 * _)) ≤ _
  have h₁' := mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 2 * M * smallConstant ^ 2 by positivity)
  have h₂' := mul_le_mul_of_nonneg_left h₂ (show 0 ≤ 2 * M * largeConstant ^ 2 by positivity)
  simp_rw [mul_assoc, ← Finset.mul_sum] at h₂'
  dsimp [errorBound]
  convert add_le_add h₁' h₂' using 1
  all_goals first | rfl | ring

end Kneser.ActualLensFiniteError
end
