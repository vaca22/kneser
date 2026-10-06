import Kneser.GrowingLensEntry
import Kneser.ParabolicOrbitSum

/-! A summable local uniform majorant follows from genuine real-time drift.
It combines a fourth-power majorant with a geometric one. -/
noncomputable section
namespace Kneser.GrowingLensUniformMajorant

open Kneser.GrowingBandKernel Kneser.ActualLensFiniteError
open Kneser.GrowingBandGeometry Kneser.EvenPreparedOrbitDiscs

def majorant (M L θ : ℝ) (k : ℕ) : ℝ :=
  128 * M * smallConstant ^ 2 * (L + 1) ^ 4 / ((k : ℝ) + 1) ^ 4 +
    2 * M * largeConstant ^ 2 * θ ^ 4 * Real.exp (2 * θ * L) *
      Real.exp (-(3 / 2) * θ) ^ k

theorem rational_kernel_le_parabolic (x L Y : ℝ) (k : ℕ)
    (hL : 0 ≤ L) (hY : 1 ≤ Y) (hx : -L + (3 / 4) * k ≤ x) :
    ((x ^ 2 + Y ^ 2) ^ 2)⁻¹ ≤ 64 * (L + 1) ^ 4 / ((k : ℝ) + 1) ^ 4 := by
  have hn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk : (k : ℝ) + 1 ≤ 2 * (|x| + L + 1) := by linarith [le_abs_self x]
  have hsq : ((k : ℝ) + 1) ^ 2 ≤ 8 * (x ^ 2 + (L + 1) ^ 2) := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (k : ℝ) + 1) hk 2
    nlinarith [sq_nonneg (|x| - (L + 1)), sq_abs x]
  have hLsq : 1 ≤ (L + 1) ^ 2 := by nlinarith
  have hYsq : 1 ≤ Y ^ 2 := by nlinarith
  have hfac : x ^ 2 + (L + 1) ^ 2 ≤ (L + 1) ^ 2 * (x ^ 2 + Y ^ 2) := by
    nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ (L + 1) ^ 2 - 1 by linarith),
      mul_nonneg (sq_nonneg (L + 1)) (show 0 ≤ Y ^ 2 - 1 by linarith)]
  have hsq' : ((k : ℝ) + 1) ^ 2 ≤ 8 * (L + 1) ^ 2 * (x ^ 2 + Y ^ 2) := by linarith
  have hfour := pow_le_pow_left₀ (sq_nonneg ((k : ℝ) + 1)) hsq' 2
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (by nlinarith [sq_nonneg x] : 0 < (x ^ 2 + Y ^ 2) ^ 2)
    (by positivity : 0 < ((k : ℝ) + 1) ^ 4)).mpr
  nlinarith

theorem exponential_kernel_le_geometric (x L θ : ℝ) (k : ℕ)
    (hθ : 0 < θ) (hx : -L + (3 / 4) * k ≤ x) :
    Real.exp (-2 * θ * |x|) ≤ Real.exp (2 * θ * L) * Real.exp (-(3 / 2) * θ) ^ k := by
  have he : Real.exp (2 * θ * L) * Real.exp (-(3 / 2) * θ) ^ k =
      Real.exp (2 * θ * L - (3 / 2) * θ * k) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  apply Real.exp_le_exp.mpr
  nlinarith [le_abs_self x]

theorem summable_majorant (M L θ : ℝ) (hθ : 0 < θ) : Summable (majorant M L θ) := by
  have hp := Kneser.summable_parabolic_majorant (128 * M * smallConstant ^ 2 * (L + 1) ^ 4)
    (by norm_num : 2 ≤ (4 : ℕ))
  have hg := summable_geometric_of_lt_one (Real.exp_pos (-(3 / 2) * θ)).le
    (Real.exp_lt_one_iff.mpr (by nlinarith : -(3 / 2) * θ < 0))
  change Summable (fun k : ℕ => 128 * M * smallConstant ^ 2 * (L + 1) ^ 4 / ((k : ℝ) + 1) ^ 4 +
    2 * M * largeConstant ^ 2 * θ ^ 4 * Real.exp (2 * θ * L) * Real.exp (-(3 / 2) * θ) ^ k)
  exact hp.add (hg.mul_left (2 * M * largeConstant ^ 2 * θ ^ 4 * Real.exp (2 * θ * L)))

theorem residual_le_majorant (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (s a b θ Y M L : ℝ) (u : ℂ) (k : ℕ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hab : a < b) (hθ : 0 < θ) (hY : 1 ≤ Y) (hYθ : θ * Y ≤ Real.pi)
    (hratio : (b - a) / θ ≤ 5) (hua : u ≠ (a : ℂ)) (hub : u ≠ (b : ℂ))
    (hband : bandTime a b θ u ∈ strip θ Y)
    (hres : ‖descendedTerm A B Γ 2 u s 0‖ ≤ M * (‖u - (a : ℂ)‖ * ‖u - (b : ℂ)‖) ^ 2)
    (hx : -L + (3 / 4) * k ≤ (bandTime a b θ u).re) :
    ‖descendedTerm A B Γ 2 u s 0‖ ≤ majorant M L θ k := by
  have hp := true_lens_residual_kernel A B Γ s a b θ Y M u hab hθ (by linarith) hYθ hratio hua hub hband hres hM
  have hr := rational_kernel_le_parabolic (bandTime a b θ u).re L Y k hL hY hx
  have hg := exponential_kernel_le_geometric (bandTime a b θ u).re L θ k hθ hx
  apply hp.trans
  have hh := add_le_add
    (mul_le_mul_of_nonneg_left hr (show 0 ≤ 2 * M * smallConstant ^ 2 by positivity))
    (mul_le_mul_of_nonneg_left hg (show 0 ≤ 2 * M * largeConstant ^ 2 * θ ^ 4 by positivity))
  dsimp [majorant]
  convert hh using 1
  all_goals first | rfl | ring

theorem residual_le_majorant_left (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (s a b θ Y M L : ℝ) (u : ℂ) (k : ℕ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hab : a < b) (hθ : 0 < θ) (hY : 1 ≤ Y) (hYθ : θ * Y ≤ Real.pi)
    (hratio : (b - a) / θ ≤ 5) (hua : u ≠ (a : ℂ)) (hub : u ≠ (b : ℂ))
    (hband : bandTime a b θ u ∈ strip θ Y)
    (hres : ‖descendedTerm A B Γ 2 u s 0‖ ≤ M * (‖u - (a : ℂ)‖ * ‖u - (b : ℂ)‖) ^ 2)
    (hx : -L + (3 / 4) * k ≤ -(bandTime a b θ u).re) :
    ‖descendedTerm A B Γ 2 u s 0‖ ≤ majorant M L θ k := by
  have hp := true_lens_residual_kernel A B Γ s a b θ Y M u hab hθ (by linarith) hYθ hratio hua hub hband hres hM
  have hr := rational_kernel_le_parabolic (-(bandTime a b θ u).re) L Y k hL hY hx
  have hg := exponential_kernel_le_geometric (-(bandTime a b θ u).re) L θ k hθ hx
  simp only [neg_sq, abs_neg] at hr hg
  apply hp.trans
  have hh := add_le_add
    (mul_le_mul_of_nonneg_left hr (show 0 ≤ 2 * M * smallConstant ^ 2 by positivity))
    (mul_le_mul_of_nonneg_left hg (show 0 ≤ 2 * M * largeConstant ^ 2 * θ ^ 4 by positivity))
  dsimp [majorant]
  convert hh using 1
  all_goals first | rfl | ring

end Kneser.GrowingLensUniformMajorant
end
