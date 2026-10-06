import Kneser.ParabolicOverlapGate

/-!
High-imaginary finite parabolic orbits have a reciprocal height bound.
The bound retains the gate height, rather than replacing it by a fixed
small radius, and therefore controls finite defect sums as height grows.
-/

set_option autoImplicit false
noncomputable section
namespace Kneser.HighImaginaryOrbit

open Complex Kneser.ParabolicExponentialOrbit Kneser.ParabolicOverlapGate
open scoped BigOperators

theorem finite_orbit_inverse_norm_lower (f : ℂ → ℂ)
    (hstep : ∀ u : ℂ, ‖u‖ ≤ 1 / 2 → u ≠ 0 →
      ‖inverseCoordinate (f u) - inverseCoordinate u - 1‖ ≤ 8 * ‖u‖)
    (u : ℂ) (N : ℕ) (hgate : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate u).im|)
    (k : ℕ) (hk : k ≤ N) :
    |(inverseCoordinate u).im| / 2 ≤ ‖inverseCoordinate ((f^[k]) u)‖ := by
  have hb := finite_orbit_gate_bound f hstep u N hgate k hk
  have hi := (abs_im_le_norm
    (inverseCoordinate ((f^[k]) u) - (inverseCoordinate u + (k : ℂ)))).trans hb
  simp only [sub_im, add_im, natCast_im, add_zero] at hi
  have ht := norm_sub_norm_le (inverseCoordinate u).im
    (inverseCoordinate ((f^[k]) u)).im
  simp only [Real.norm_eq_abs] at ht
  rw [abs_sub_comm] at ht
  have hn := abs_im_le_norm (inverseCoordinate ((f^[k]) u))
  have hk' : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
  linarith [Nat.cast_nonneg (α := ℝ) N]

theorem finite_orbit_height_norm (f : ℂ → ℂ)
    (hstep : ∀ u : ℂ, ‖u‖ ≤ 1 / 2 → u ≠ 0 →
      ‖inverseCoordinate (f u) - inverseCoordinate u - 1‖ ≤ 8 * ‖u‖)
    (u : ℂ) (N : ℕ) (hgate : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate u).im|)
    (k : ℕ) (hk : k ≤ N) : ‖(f^[k]) u‖ ≤ 4 / |(inverseCoordinate u).im| := by
  have hY : 0 < |(inverseCoordinate u).im| := by
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hn := finite_orbit_inverse_norm_lower f hstep u N hgate k hk
  have he : ‖(f^[k]) u‖ = 2 / ‖inverseCoordinate ((f^[k]) u)‖ := by
    conv_lhs => rw [← inverseCoordinate_involutive ((f^[k]) u)]
    exact inverseCoordinate_norm _
  rw [he]
  have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
    (half_pos hY) hn
  have hd : (2 : ℝ) / (|(inverseCoordinate u).im| / 2) = 4 / |(inverseCoordinate u).im| := by
    field_simp
    norm_num
  exact hh.trans_eq hd

theorem finite_defect_sum_bound (f D : ℂ → ℂ)
    (hstep : ∀ u : ℂ, ‖u‖ ≤ 1 / 2 → u ≠ 0 →
      ‖inverseCoordinate (f u) - inverseCoordinate u - 1‖ ≤ 8 * ‖u‖)
    (r C : ℝ) (hC : 0 ≤ C)
    (hD : ∀ v : ℂ, ‖v‖ < r → ‖D v‖ ≤ C * ‖v‖ ^ 2)
    (u : ℂ) (N : ℕ) (hgate : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate u).im|)
    (hr : 4 / |(inverseCoordinate u).im| < r) :
    ‖∑ k ∈ Finset.range N, D ((f^[k]) u)‖ ≤
      (N : ℝ) * C * (4 / |(inverseCoordinate u).im|) ^ 2 := by
  have hY : 0 < |(inverseCoordinate u).im| := by
    linarith [Nat.cast_nonneg (α := ℝ) N]
  calc
    _ ≤ ∑ k ∈ Finset.range N, ‖D ((f^[k]) u)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range N, C * (4 / |(inverseCoordinate u).im|) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hn := finite_orbit_height_norm f hstep u N hgate k
        (Nat.le_of_lt (Finset.mem_range.mp hk))
      exact (hD _ (hn.trans_lt hr)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) hC)
    _ = _ := by simp; ring

end Kneser.HighImaginaryOrbit
end
