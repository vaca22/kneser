import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Kneser.ExponentialUnfolding

/-!
# An explicit attracting petal for the parabolic exponential

All map estimates in this file are proved for the actual map `exp u - 1`.
The inverse coordinate is `ζ = -2/u`. A numerical Taylor estimate gives the
step error and consequently the growth of `Re ζ` on every forward iterate.
-/

namespace Kneser.ParabolicExponentialOrbit

open scoped BigOperators

noncomputable def parabolicMap (u : ℂ) : ℂ := Complex.exp u - 1

noncomputable def inverseCoordinate (u : ℂ) : ℂ := (-2 : ℂ) / u

/-- The genuine exponential Taylor remainder, with a convenient numerical bound. -/
theorem cubic_remainder_bound (u : ℂ) (hu : ‖u‖ ≤ 1) :
    ‖parabolicMap u - u - u ^ 2 / 2‖ ≤ ‖u‖ ^ 3 := by
  have h := Complex.exp_bound hu (n := 3) (by norm_num)
  have hs : (∑ m ∈ Finset.range 3, u ^ m / (m.factorial : ℂ)) =
      1 + u + u ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hs] at h
  calc
    ‖parabolicMap u - u - u ^ 2 / 2‖ = ‖Complex.exp u - (1 + u + u ^ 2 / 2)‖ := by
      congr 1
      dsimp [parabolicMap]
      ring
    _ ≤ ‖u‖ ^ 3 * ((3 + 1 : ℝ) * ((Nat.factorial 3 : ℝ) * 3)⁻¹) := by
      norm_num [Nat.factorial] at h ⊢
      exact h
    _ ≤ ‖u‖ ^ 3 := by
      norm_num [Nat.factorial]
      nlinarith [pow_nonneg (norm_nonneg u) 3]

/-- On the half-unit disc the actual map has no additional zero. -/
theorem map_norm_lower (u : ℂ) (hu : ‖u‖ ≤ 1 / 2) :
    ‖u‖ / 2 ≤ ‖parabolicMap u‖ := by
  have hnorm : ‖u‖ ≤ 1 := by linarith
  have h := Complex.norm_exp_sub_one_sub_id_le hnorm
  change ‖parabolicMap u - u‖ ≤ ‖u‖ ^ 2 at h
  have hn := norm_sub_norm_le u (parabolicMap u)
  rw [norm_sub_rev] at hn
  have hp := mul_nonneg (norm_nonneg u) (sub_nonneg.mpr hu)
  nlinarith

theorem map_ne_zero (u : ℂ) (hu : ‖u‖ ≤ 1 / 2) (hne : u ≠ 0) :
    parabolicMap u ≠ 0 := by
  have h := map_norm_lower u hu
  have hp := norm_pos_iff.mpr hne
  exact norm_pos_iff.mp (by linarith)

/-- A bound on the numerator in the inverse-coordinate step error. -/
theorem step_numerator_bound (u : ℂ) (hu : ‖u‖ ≤ 1 / 2) :
    ‖(2 - u) * parabolicMap u - 2 * u‖ ≤ 4 * ‖u‖ ^ 3 := by
  have ht : ‖u‖ ≤ 1 := by linarith
  have hr := cubic_remainder_bound u ht
  have heq : (2 - u) * parabolicMap u - 2 * u =
      -u ^ 3 / 2 + (2 - u) * (parabolicMap u - u - u ^ 2 / 2) := by ring
  rw [heq]
  have h2 : ‖(2 : ℂ) - u‖ ≤ 3 := by
    have hn := norm_sub_le (2 : ℂ) u
    norm_num at hn
    linarith
  calc
    ‖-u ^ 3 / 2 + (2 - u) * (parabolicMap u - u - u ^ 2 / 2)‖ ≤
        ‖-u ^ 3 / 2‖ + ‖(2 - u) * (parabolicMap u - u - u ^ 2 / 2)‖ := norm_add_le _ _
    _ = ‖u‖ ^ 3 / 2 + ‖(2 : ℂ) - u‖ * ‖parabolicMap u - u - u ^ 2 / 2‖ := by
      rw [Complex.norm_div, norm_neg, Complex.norm_pow, Complex.norm_mul]
      norm_num
    _ ≤ ‖u‖ ^ 3 / 2 + 3 * ‖u‖ ^ 3 := by
      have hm := mul_le_mul h2 hr (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
      linarith
    _ ≤ 4 * ‖u‖ ^ 3 := by nlinarith [pow_nonneg (norm_nonneg u) 3]

/-- An unconditional estimate for the true inverse-coordinate step. -/
theorem inverse_step_error_bound (u : ℂ) (hu : ‖u‖ ≤ 1 / 2) (hne : u ≠ 0) :
    ‖inverseCoordinate (parabolicMap u) - inverseCoordinate u - 1‖ ≤ 8 * ‖u‖ := by
  have hfne := map_ne_zero u hu hne
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hne
  have hfpos : 0 < ‖parabolicMap u‖ := norm_pos_iff.mpr hfne
  have heq : inverseCoordinate (parabolicMap u) - inverseCoordinate u - 1 =
      ((2 - u) * parabolicMap u - 2 * u) / (u * parabolicMap u) := by
    dsimp [inverseCoordinate]
    field_simp
    ring
  rw [heq, Complex.norm_div, Complex.norm_mul]
  apply (div_le_iff₀ (mul_pos hupos hfpos)).mpr
  have hnum := step_numerator_bound u hu
  have hlow := map_norm_lower u hu
  have hm := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 8 * ‖u‖ * ‖u‖ by positivity)
  nlinarith

@[simp] theorem inverseCoordinate_norm (u : ℂ) :
    ‖inverseCoordinate u‖ = 2 / ‖u‖ := by
  simp [inverseCoordinate]

/-- The inverse right-half-plane controls the size of the original coordinate. -/
theorem norm_le_two_div_re (u : ℂ) (hpos : 0 < (inverseCoordinate u).re) :
    ‖u‖ ≤ 2 / (inverseCoordinate u).re := by
  have hne : u ≠ 0 := by
    intro hu
    simp [hu, inverseCoordinate] at hpos
  have hunorm : 0 < ‖u‖ := norm_pos_iff.mpr hne
  apply (le_div_iff₀ hpos).mpr
  have hre := Complex.re_le_norm (inverseCoordinate u)
  have hm := mul_le_mul_of_nonneg_left hre (norm_nonneg u)
  rw [inverseCoordinate_norm] at hm
  have hc : ‖u‖ * (2 / ‖u‖) = 2 := by field_simp
  rwa [hc] at hm

/-- The numerical half-plane `Re ζ ≥ 32` is mapped strictly into itself.
The lower increment `1/2` follows from the actual exponential Taylor bound. -/
theorem inverse_step_re (u : ℂ) (hpetal : 32 ≤ (inverseCoordinate u).re) :
    (inverseCoordinate u).re + 1 / 2 ≤ (inverseCoordinate (parabolicMap u)).re := by
  have hpos : 0 < (inverseCoordinate u).re := by linarith
  have hn := norm_le_two_div_re u hpos
  have hsmall : ‖u‖ ≤ 1 / 16 := by
    have hd : (2 : ℝ) / (inverseCoordinate u).re ≤ 1 / 16 :=
      (div_le_iff₀ hpos).mpr (by linarith)
    exact hn.trans hd
  have hne : u ≠ 0 := by
    intro hu
    simp [hu, inverseCoordinate] at hpos
  have he := inverse_step_error_bound u (by linarith) hne
  have habs := Complex.abs_re_le_norm
    (inverseCoordinate (parabolicMap u) - inverseCoordinate u - 1)
  have hbound : |(inverseCoordinate (parabolicMap u) - inverseCoordinate u - 1).re| ≤ 1 / 2 := by
    exact habs.trans (he.trans (by linarith))
  have hl := (abs_le.mp hbound).1
  simp only [Complex.sub_re, Complex.one_re] at hl
  linarith

/-- Every genuine forward iterate stays in the explicit petal, with linear
growth of the real part of the inverse coordinate. -/
theorem iterate_inverse_re (u : ℂ) (hpetal : 32 ≤ (inverseCoordinate u).re) (k : ℕ) :
    (inverseCoordinate u).re + (k : ℝ) / 2 ≤
      (inverseCoordinate ((parabolicMap^[k]) u)).re := by
  induction k with
  | zero => simp
  | succ k hk =>
    have hp : 32 ≤ (inverseCoordinate ((parabolicMap^[k]) u)).re := by
      have hkn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hs := inverse_step_re ((parabolicMap^[k]) u) hp
    rw [Function.iterate_succ_apply']
    push_cast
    linarith

/-- The actual exponential orbit obeys the required reciprocal decay estimate.
No recurrence or orbit estimate is supplied as an assumption. -/
theorem iterate_norm_bound (u : ℂ) (hpetal : 32 ≤ (inverseCoordinate u).re) (k : ℕ) :
    ‖(parabolicMap^[k]) u‖ ≤ 2 / ((inverseCoordinate u).re + (k : ℝ) / 2) := by
  have hre := iterate_inverse_re u hpetal k
  have hden : 0 < (inverseCoordinate u).re + (k : ℝ) / 2 := by
    have hkn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hpos : 0 < (inverseCoordinate ((parabolicMap^[k]) u)).re := lt_of_lt_of_le hden hre
  exact (norm_le_two_div_re _ hpos).trans (div_le_div_of_nonneg_left (by norm_num) hden hre)

/-- A petal threshold `R ≥ 32` gives the usual manuscript bound. -/
theorem iterate_norm_bound_of_threshold (u : ℂ) (R : ℝ) (hR : 32 ≤ R)
    (hu : R ≤ (inverseCoordinate u).re) (k : ℕ) :
    ‖(parabolicMap^[k]) u‖ ≤ 2 / (R + (k : ℝ) / 2) := by
  have hden : 0 < R + (k : ℝ) / 2 := by
    have hkn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  exact (iterate_norm_bound u (hR.trans hu) k).trans
    (div_le_div_of_nonneg_left (by norm_num) hden (by linarith))

/-- The recursive orbit used for parameter differentiation is exactly the
forward iterate of the parabolic exponential at parameter zero. -/
theorem unfolding_orbit_zero_eq_iterate (u : ℂ) (k : ℕ) :
    ExponentialUnfolding.orbit u 0 k = (parabolicMap^[k]) u := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [ExponentialUnfolding.orbit_succ, hk, Function.iterate_succ_apply']
    simp [parabolicMap]

theorem unfolding_orbit_zero_norm_bound (u : ℂ) (R : ℝ) (hR : 32 ≤ R)
    (hu : R ≤ (inverseCoordinate u).re) (k : ℕ) :
    ‖ExponentialUnfolding.orbit u 0 k‖ ≤ 2 / (R + (k : ℝ) / 2) := by
  rw [unfolding_orbit_zero_eq_iterate]
  exact iterate_norm_bound_of_threshold u R hR hu k

end Kneser.ParabolicExponentialOrbit
