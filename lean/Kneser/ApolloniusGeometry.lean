import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Quantitative geometry of an Apollonius petal

The estimates are unconditional geometric identities and real exponential
inequalities. Instantiating them for an infinite exponential orbit additionally
requires the actual map's cross-ratio contraction; that dynamical statement is
not assumed silently in these geometric theorems.
-/

namespace Kneser.ApolloniusGeometry

/-- The exponential denominator estimate in the manuscript's petal argument. -/
theorem exponential_kernel_bound (σ : ℝ) (hσ : 0 < σ) :
    Real.exp (-σ) / (1 - Real.exp (-σ)) ^ 2 ≤ 4 / σ ^ 2 := by
  have hepos : 0 < Real.exp (-σ) := Real.exp_pos _
  have helt : Real.exp (-σ) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hB : 0 < 1 + σ := by linarith
  have hunit : Real.exp σ * Real.exp (-σ) = 1 := by
    rw [← Real.exp_add]
    simp
  have hadd := Real.add_one_le_exp σ
  have hmul := mul_le_mul_of_nonneg_right hadd hepos.le
  rw [hunit] at hmul
  have hden : σ ≤ (1 + σ) * (1 - Real.exp (-σ)) := by nlinarith
  have hquad := Real.quadratic_le_exp_of_nonneg hσ.le
  have hqm := mul_le_mul_of_nonneg_right hquad hepos.le
  rw [hunit] at hqm
  have hk : (1 + σ) ^ 2 * Real.exp (-σ) ≤ 2 := by nlinarith
  have hsq : σ ^ 2 ≤ ((1 + σ) * (1 - Real.exp (-σ))) ^ 2 :=
    pow_le_pow_left₀ hσ.le hden 2
  have hm1 := mul_le_mul_of_nonneg_left hsq hepos.le
  have hm2 := mul_le_mul_of_nonneg_right hk
    (sq_nonneg (1 - Real.exp (-σ)))
  apply (div_le_div_iff₀ (sq_pos_of_pos (by linarith)) (sq_pos_of_pos hσ)).mpr
  nlinarith [sq_nonneg (1 - Real.exp (-σ))]

noncomputable def crossRatio (a b u : ℂ) : ℂ := (u - a) / (u - b)

/-- A cross-ratio modulus bound gives the explicit product estimate required
for the vanishing factor `q_s = (u-u₁)(u-u₂)`. -/
theorem root_product_bound (a b u : ℂ) (σ : ℝ) (hσ : 0 < σ)
    (hub : u ≠ b) (hq : ‖crossRatio a b u‖ ≤ Real.exp (-σ)) :
    ‖u - a‖ * ‖u - b‖ ≤ 4 * ‖b - a‖ ^ 2 / σ ^ 2 := by
  have hepos : 0 < Real.exp (-σ) := Real.exp_pos _
  have helt : Real.exp (-σ) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hden : 0 < 1 - Real.exp (-σ) := by linarith
  have hubne : u - b ≠ 0 := sub_ne_zero.mpr hub
  have hmul : crossRatio a b u * (u - b) = u - a := by
    dsimp [crossRatio]
    exact div_mul_cancel₀ _ hubne
  have hgap : (crossRatio a b u - 1) * (u - b) = b - a := by
    rw [sub_mul, hmul]
    ring
  have hgapnorm : ‖1 - crossRatio a b u‖ * ‖u - b‖ = ‖b - a‖ := by
    rw [norm_sub_rev]
    rw [← Complex.norm_mul, hgap]
  have hlower : 1 - Real.exp (-σ) ≤ ‖1 - crossRatio a b u‖ := by
    have ht := norm_sub_norm_le (1 : ℂ) (crossRatio a b u)
    have hone : ‖(1 : ℂ)‖ = 1 := by norm_num [Complex.norm_def]
    rw [hone] at ht
    linarith
  have hnormb : ‖u - b‖ ≤ ‖b - a‖ / (1 - Real.exp (-σ)) := by
    apply (le_div_iff₀ hden).mpr
    have hm := mul_le_mul_of_nonneg_right hlower (norm_nonneg (u - b))
    rw [hgapnorm] at hm
    nlinarith
  have hnorma : ‖u - a‖ = ‖crossRatio a b u‖ * ‖u - b‖ := by
    rw [← Complex.norm_mul, hmul]
  have hk := exponential_kernel_bound σ hσ
  have hbpow := pow_le_pow_left₀ (norm_nonneg (u - b)) hnormb 2
  calc
    ‖u - a‖ * ‖u - b‖ = ‖crossRatio a b u‖ * ‖u - b‖ ^ 2 := by rw [hnorma]; ring
    _ ≤ Real.exp (-σ) * (‖b - a‖ / (1 - Real.exp (-σ))) ^ 2 :=
      mul_le_mul hq hbpow (sq_nonneg _) hepos.le
    _ = ‖b - a‖ ^ 2 * (Real.exp (-σ) / (1 - Real.exp (-σ)) ^ 2) := by
      rw [div_pow]
      ring
    _ ≤ ‖b - a‖ ^ 2 * (4 / σ ^ 2) :=
      mul_le_mul_of_nonneg_left hk (sq_nonneg _)
    _ = 4 * ‖b - a‖ ^ 2 / σ ^ 2 := by ring

/-- Express the product bound in the normalized model-time variable. -/
theorem root_product_bound_model_time (a b u : ℂ) (θ x : ℝ)
    (hθ : 0 < θ) (hx : 0 < x) (hub : u ≠ b)
    (hq : ‖crossRatio a b u‖ ≤ Real.exp (-(θ * x))) :
    ‖u - a‖ * ‖u - b‖ ≤ 4 * (‖b - a‖ / θ) ^ 2 / x ^ 2 := by
  have h := root_product_bound a b u (θ * x) (mul_pos hθ hx) hub hq
  convert h using 1
  ring

/-- The same Apollonius condition bounds the distance to the attracting root.
This ensures that a whole infinite orbit remains inside the local analytic disc. -/
theorem attracting_root_distance_bound (a b u : ℂ) (σ : ℝ) (hσ : 0 < σ)
    (hub : u ≠ b) (hq : ‖crossRatio a b u‖ ≤ Real.exp (-σ)) :
    ‖u - a‖ ≤ ‖b - a‖ / σ := by
  have hepos : 0 < Real.exp (-σ) := Real.exp_pos _
  have helt : Real.exp (-σ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hden : 0 < 1 - Real.exp (-σ) := by linarith
  have hun : u - b ≠ 0 := sub_ne_zero.mpr hub
  have hmul : crossRatio a b u * (u - b) = u - a := by
    dsimp [crossRatio]
    exact div_mul_cancel₀ _ hun
  have hgap : (1 - crossRatio a b u) * (u - b) = a - b := by rw [sub_mul, hmul]; ring
  have hlower : 1 - Real.exp (-σ) ≤ ‖1 - crossRatio a b u‖ := by
    have ht := norm_sub_norm_le (1 : ℂ) (crossRatio a b u)
    have hone : ‖(1 : ℂ)‖ = 1 := by norm_num [Complex.norm_def]
    rw [hone] at ht
    linarith
  have hnormb : ‖u - b‖ ≤ ‖b - a‖ / (1 - Real.exp (-σ)) := by
    apply (le_div_iff₀ hden).mpr
    have hm := mul_le_mul_of_nonneg_right hlower (norm_nonneg (u - b))
    have hgn : ‖1 - crossRatio a b u‖ * ‖u - b‖ = ‖b - a‖ := by
      rw [← Complex.norm_mul, hgap, norm_sub_rev]
    rw [hgn] at hm
    nlinarith
  have hnorma : ‖u - a‖ = ‖crossRatio a b u‖ * ‖u - b‖ := by
    rw [← Complex.norm_mul, hmul]
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp σ) hepos.le
  have hunit : Real.exp σ * Real.exp (-σ) = 1 := by rw [← Real.exp_add]; simp
  rw [hunit] at he
  have hk : Real.exp (-σ) / (1 - Real.exp (-σ)) ≤ 1 / σ := by
    apply (div_le_div_iff₀ hden hσ).mpr
    nlinarith
  calc
    ‖u - a‖ ≤ Real.exp (-σ) * (‖b - a‖ / (1 - Real.exp (-σ))) := by
      rw [hnorma]
      exact mul_le_mul hq hnormb (norm_nonneg _) hepos.le
    _ = ‖b - a‖ * (Real.exp (-σ) / (1 - Real.exp (-σ))) := by ring
    _ ≤ ‖b - a‖ * (1 / σ) := mul_le_mul_of_nonneg_left hk (norm_nonneg _)
    _ = ‖b - a‖ / σ := by ring

end Kneser.ApolloniusGeometry
