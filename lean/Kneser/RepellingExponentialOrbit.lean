import Kneser.ParabolicInitialPetal
import Kneser.PerturbedExponentialOrbit
import Mathlib.Analysis.Complex.Liouville

/-!
# Actual reflected inverse dynamics of the exponential unfolding

The inverse branch is the principal logarithm near zero, reflected to put its
repelling petal in the same coordinate `-2/v` as the attracting petal.
-/

namespace Kneser.RepellingExponentialOrbit

open Kneser.ParabolicExponentialOrbit hiding cubic_remainder_bound map_norm_lower map_ne_zero
  step_numerator_bound inverse_step_error_bound inverseCoordinate_norm norm_le_two_div_re
open scoped Topology

open Kneser.PerturbedExponentialOrbit (parameterRadius parameterRadius_pos
  parameterRadius_le_quarter parameterRadius_antitone local_parameter_bound coordinate_increment_bounds)

noncomputable def parabolicInverse (v : ℂ) : ℂ := -Complex.log (1 - v)

noncomputable def reflectedInverse (s v : ℂ) : ℂ := -(Complex.log (1 - v) + s) / (1 - s)

noncomputable def inverseOrbit (v s : ℂ) (k : ℕ) : ℂ := (reflectedInverse s)^[k] v

@[simp] theorem inverseOrbit_zero (v s : ℂ) : inverseOrbit v s 0 = v := rfl

theorem inverseOrbit_succ (v s : ℂ) (k : ℕ) :
    inverseOrbit v s (k + 1) = reflectedInverse s (inverseOrbit v s k) :=
  Function.iterate_succ_apply' ..

@[simp] theorem reflectedInverse_zero (v : ℂ) : reflectedInverse 0 v = parabolicInverse v := by
  simp [reflectedInverse, parabolicInverse]

/-- The genuine exponential Taylor remainder, with a convenient numerical bound. -/
theorem cubic_remainder_bound (u : ℂ) (hu : ‖u‖ ≤ 1 / 2) :
    ‖parabolicInverse u - u - u ^ 2 / 2‖ ≤ ‖u‖ ^ 3 := by
  have h := Complex.norm_log_sub_logTaylor_le 2
    (z := -u) (by simpa using (show ‖u‖ < 1 by linarith))
  have hp : Complex.logTaylor 3 (-u) = -u - u ^ 2 / 2 := by
    norm_num [Complex.logTaylor_succ, Complex.logTaylor_zero]
    ring
  rw [hp] at h
  have heq : parabolicInverse u - u - u ^ 2 / 2 =
      -(Complex.log (1 + -u) - (-u - u ^ 2 / 2)) := by
    dsimp [parabolicInverse]
    simp only [sub_eq_add_neg]
    ring
  rw [heq, norm_neg]
  simp only [norm_neg] at h
  have hden : 0 < 1 - ‖u‖ := by linarith
  have hi : (1 - ‖u‖)⁻¹ ≤ 2 := by
    rw [← one_div, div_le_iff₀ hden]
    linarith
  calc
    _ ≤ ‖u‖ ^ 3 * (1 - ‖u‖)⁻¹ / 3 := by convert h using 1; norm_num
    _ ≤ ‖u‖ ^ 3 * 2 / 3 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hi (pow_nonneg (norm_nonneg u) 3)) (by norm_num)
    _ ≤ ‖u‖ ^ 3 := by nlinarith [pow_nonneg (norm_nonneg u) 3]

/-- On the half-unit disc the actual map has no additional zero. -/
theorem map_norm_lower (u : ℂ) (hu : ‖u‖ ≤ 1 / 2) :
    ‖u‖ / 2 ≤ ‖parabolicInverse u‖ := by
  have h := Kneser.ParabolicInitialPetal.norm_log_one_sub_remainder hu
  have heq : parabolicInverse u - u = -(Complex.log (1 - u) + u) := by
    dsimp [parabolicInverse]
    ring
  rw [← norm_neg, ← heq] at h
  have hn := norm_sub_norm_le u (parabolicInverse u)
  rw [norm_sub_rev] at hn
  have hp := mul_nonneg (norm_nonneg u) (sub_nonneg.mpr hu)
  nlinarith

theorem map_ne_zero (u : ℂ) (hu : ‖u‖ ≤ 1 / 2) (hne : u ≠ 0) :
    parabolicInverse u ≠ 0 := by
  have h := map_norm_lower u hu
  have hp := norm_pos_iff.mpr hne
  exact norm_pos_iff.mp (by linarith)

/-- A bound on the numerator in the inverse-coordinate step error. -/
theorem step_numerator_bound (u : ℂ) (hu : ‖u‖ ≤ 1 / 2) :
    ‖(2 - u) * parabolicInverse u - 2 * u‖ ≤ 4 * ‖u‖ ^ 3 := by
  have hr := cubic_remainder_bound u hu
  have heq : (2 - u) * parabolicInverse u - 2 * u =
      -u ^ 3 / 2 + (2 - u) * (parabolicInverse u - u - u ^ 2 / 2) := by ring
  rw [heq]
  have h2 : ‖(2 : ℂ) - u‖ ≤ 3 := by
    have hn := norm_sub_le (2 : ℂ) u
    norm_num at hn
    linarith
  calc
    ‖-u ^ 3 / 2 + (2 - u) * (parabolicInverse u - u - u ^ 2 / 2)‖ ≤
        ‖-u ^ 3 / 2‖ + ‖(2 - u) * (parabolicInverse u - u - u ^ 2 / 2)‖ := norm_add_le _ _
    _ = ‖u‖ ^ 3 / 2 + ‖(2 : ℂ) - u‖ * ‖parabolicInverse u - u - u ^ 2 / 2‖ := by
      rw [Complex.norm_div, norm_neg, Complex.norm_pow, Complex.norm_mul]
      norm_num
    _ ≤ ‖u‖ ^ 3 / 2 + 3 * ‖u‖ ^ 3 := by
      have hm := mul_le_mul h2 hr (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
      linarith
    _ ≤ 4 * ‖u‖ ^ 3 := by nlinarith [pow_nonneg (norm_nonneg u) 3]

/-- An unconditional estimate for the true inverse-coordinate step. -/
theorem inverse_step_error_bound (u : ℂ) (hu : ‖u‖ ≤ 1 / 2) (hne : u ≠ 0) :
    ‖inverseCoordinate (parabolicInverse u) - inverseCoordinate u - 1‖ ≤ 8 * ‖u‖ := by
  have hfne := map_ne_zero u hu hne
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hne
  have hfpos : 0 < ‖parabolicInverse u‖ := norm_pos_iff.mpr hfne
  have heq : inverseCoordinate (parabolicInverse u) - inverseCoordinate u - 1 =
      ((2 - u) * parabolicInverse u - 2 * u) / (u * parabolicInverse u) := by
    dsimp [inverseCoordinate]
    field_simp
    ring
  rw [heq, Complex.norm_div, Complex.norm_mul]
  apply (div_le_iff₀ (mul_pos hupos hfpos)).mpr
  have hnum := step_numerator_bound u hu
  have hlow := map_norm_lower u hu
  have hm := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 8 * ‖u‖ * ‖u‖ by positivity)
  nlinarith

theorem inverseCoordinate_norm (u : ℂ) :
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


/-- The actual reflected logarithmic family has a uniform absolute perturbation bound. -/
theorem map_perturbation_bound (s u : ℂ) (hu : ‖u‖ ≤ 1 / 2) (hs : ‖s‖ ≤ 1 / 4) :
    ‖reflectedInverse s u - parabolicInverse u‖ ≤ 6 * ‖s‖ := by
  have hn : ‖parabolicInverse u - u‖ ≤ ‖u‖ ^ 2 := by
    have h := Kneser.ParabolicInitialPetal.norm_log_one_sub_remainder hu
    have heq : parabolicInverse u - u = -(Complex.log (1 - u) + u) := by
      dsimp [parabolicInverse]
      ring
    rw [← norm_neg, ← heq] at h
    exact h
  have hgn : ‖parabolicInverse u‖ ≤ 1 := by
    have h := norm_sub_norm_le (parabolicInverse u) u
    nlinarith [norm_nonneg u]
  have ht := norm_sub_le (parabolicInverse u) (1 : ℂ)
  norm_num at ht
  have hp : ‖parabolicInverse u - 1‖ ≤ 2 := by linarith
  have hden : 3 / 4 ≤ ‖1 - s‖ := by
    have h := norm_sub_norm_le (1 : ℂ) s
    norm_num at h
    linarith
  have hdenpos : 0 < ‖1 - s‖ := by linarith
  have hsn : 1 - s ≠ 0 := norm_pos_iff.mp hdenpos
  have heq : reflectedInverse s u - parabolicInverse u = s * (parabolicInverse u - 1) / (1 - s) := by
    dsimp [reflectedInverse, parabolicInverse]
    field_simp
    ring
  rw [heq, norm_div, norm_mul]
  apply (div_le_iff₀ hdenpos).mpr
  have hmul := mul_le_mul_of_nonneg_left hp (norm_nonneg s)
  have hmulden := mul_le_mul_of_nonneg_left hden (show 0 ≤ 6 * ‖s‖ by positivity)
  nlinarith [norm_nonneg s]

/-- The actual perturbed map remains bounded below if its absolute perturbation
is at most a quarter of the original coordinate. -/
theorem perturbed_map_norm_lower (s u : ℂ) (hu : ‖u‖ ≤ 1 / 2)
    (hs : ‖s‖ ≤ 1 / 4) (hsmall : 6 * ‖s‖ ≤ ‖u‖ / 4) :
    ‖u‖ / 4 ≤ ‖reflectedInverse s u‖ := by
  have hp := map_perturbation_bound s u hu hs
  have hf := map_norm_lower u hu
  have ht := norm_sub_norm_le (parabolicInverse u) (reflectedInverse s u)
  rw [norm_sub_rev] at ht
  linarith

/-- The inverse coordinates of the true perturbed and unperturbed maps differ
by at most `24 |s| |ζ|²`. -/
theorem inverse_perturbation_bound (s u : ℂ) (hu : ‖u‖ ≤ 1 / 2)
    (hs : ‖s‖ ≤ 1 / 4) (hne : u ≠ 0) (hsmall : 6 * ‖s‖ ≤ ‖u‖ / 4) :
    ‖inverseCoordinate (reflectedInverse s u) - inverseCoordinate (parabolicInverse u)‖ ≤
      24 * ‖s‖ * ‖inverseCoordinate u‖ ^ 2 := by
  have hfne := map_ne_zero u hu hne
  have hupr := norm_pos_iff.mpr hne
  have hlow := perturbed_map_norm_lower s u hu hs hsmall
  have hspos : 0 < ‖reflectedInverse s u‖ := by linarith
  have hsne := norm_pos_iff.mp hspos
  have hfpos := norm_pos_iff.mpr hfne
  have hformula : inverseCoordinate (reflectedInverse s u) - inverseCoordinate (parabolicInverse u) =
      2 * (reflectedInverse s u - parabolicInverse u) / (reflectedInverse s u * parabolicInverse u) := by
    dsimp [inverseCoordinate]
    field_simp
    ring
  rw [hformula, Complex.norm_div, Complex.norm_mul, Complex.norm_mul]
  norm_num
  apply (div_le_iff₀ (mul_pos hspos hfpos)).mpr
  have hpert := map_perturbation_bound s u hu hs
  have hf := map_norm_lower u hu
  have hden : ‖u‖ ^ 2 / 8 ≤ ‖reflectedInverse s u‖ * ‖parabolicInverse u‖ := by
    have hm := mul_le_mul hlow hf (by positivity : (0 : ℝ) ≤ ‖u‖ / 2)
      (norm_nonneg _)
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hden
    (show 0 ≤ 24 * ‖s‖ * ‖inverseCoordinate u‖ ^ 2 by positivity)
  have hc : (24 * ‖s‖ * ‖inverseCoordinate u‖ ^ 2) * (‖u‖ ^ 2 / 8) = 12 * ‖s‖ := by
    rw [inverseCoordinate_norm]
    field_simp
    ring
  rw [hc] at hm
  rw [inverseCoordinate_norm] at hm
  nlinarith

/-- A fully numerical local perturbation criterion for an inverse-coordinate
step, derived for the actual exponential maps. -/
theorem inverse_step_bound (s u : ℂ) (hpetal : 64 ≤ (inverseCoordinate u).re)
    (hs : ‖s‖ ≤ 1 / 4)
    (hparam : 24 * ‖s‖ * ‖inverseCoordinate u‖ ^ 2 ≤ 1 / 4) :
    ‖inverseCoordinate (reflectedInverse s u) - inverseCoordinate u - 1‖ ≤ 1 / 2 := by
  have hpos : 0 < (inverseCoordinate u).re := by linarith
  have hn := norm_le_two_div_re u hpos
  have hu : ‖u‖ ≤ 1 / 32 := by
    exact hn.trans ((div_le_iff₀ hpos).mpr (by linarith))
  have hne : u ≠ 0 := by
    intro hz
    simp [hz, inverseCoordinate] at hpos
  have hunorm := norm_pos_iff.mpr hne
  have hζ : 64 ≤ ‖inverseCoordinate u‖ := hpetal.trans (Complex.re_le_norm _)
  have hζpos : 0 < ‖inverseCoordinate u‖ := by linarith
  have hζsquare : ‖inverseCoordinate u‖ ≤ ‖inverseCoordinate u‖ ^ 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hζsquare (norm_nonneg s)
  have hrel : 6 * ‖s‖ * ‖inverseCoordinate u‖ ≤ 1 / 2 := by nlinarith
  have hsmall : 6 * ‖s‖ ≤ ‖u‖ / 4 := by
    rw [inverseCoordinate_norm] at hrel
    have hm := mul_le_mul_of_nonneg_right hrel (le_of_lt hunorm)
    have hc : 6 * ‖s‖ * (2 / ‖u‖) * ‖u‖ = 12 * ‖s‖ := by
      field_simp
      ring
    rw [hc] at hm
    linarith
  have hp := inverse_perturbation_bound s u (by linarith) hs hne hsmall
  have hbase := inverse_step_error_bound u (by linarith) hne
  have heq : inverseCoordinate (reflectedInverse s u) - inverseCoordinate u - 1 =
      (inverseCoordinate (reflectedInverse s u) - inverseCoordinate (parabolicInverse u)) +
      (inverseCoordinate (parabolicInverse u) - inverseCoordinate u - 1) := by ring
  rw [heq]
  have ht := norm_add_le
    (inverseCoordinate (reflectedInverse s u) - inverseCoordinate (parabolicInverse u))
    (inverseCoordinate (parabolicInverse u) - inverseCoordinate u - 1)
  linarith

/-- Genuine perturbed finite inverseOrbits remain in the petal for complex parameters
inside an explicitly computed disc. Both real-part growth and norm growth are
proved by induction on the actual exponential inverseOrbit. -/
theorem finite_inverseOrbit_inverse_bounds (u s : ℂ) (R : ℝ) (hR : 64 ≤ R)
    (hu : R ≤ (inverseCoordinate u).re) (J : ℕ)
    (hs : ‖s‖ ≤ parameterRadius ‖inverseCoordinate u‖ J)
    (k : ℕ) (hk : k ≤ J) :
    R + (k : ℝ) / 2 ≤ (inverseCoordinate (inverseOrbit u s k)).re ∧
      ‖inverseCoordinate (inverseOrbit u s k)‖ ≤ ‖inverseCoordinate u‖ + 2 * (k : ℝ) := by
  induction k with
  | zero => simpa using And.intro hu (le_refl ‖inverseCoordinate u‖)
  | succ k ih =>
    have hkj : k ≤ J := Nat.le_trans (Nat.le_succ k) hk
    obtain ⟨hre, hnorm⟩ := ih hkj
    have hkn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hJn : 0 ≤ (J : ℝ) := Nat.cast_nonneg J
    have hkcast : (k : ℝ) ≤ (J : ℝ) := by exact_mod_cast hkj
    have hp : 64 ≤ (inverseCoordinate (inverseOrbit u s k)).re := by linarith
    have hlocal : ‖inverseCoordinate (inverseOrbit u s k)‖ ≤
        (‖inverseCoordinate u‖ + 2) * ((J : ℝ) + 1) := by
      nlinarith [mul_nonneg (norm_nonneg (inverseCoordinate u)) hJn]
    have hpar := local_parameter_bound ‖inverseCoordinate u‖
      (norm_nonneg _) J s (inverseCoordinate (inverseOrbit u s k)) hs hlocal
    have hsquarter := hs.trans (parameterRadius_le_quarter _ (norm_nonneg _) J)
    have hstep := inverse_step_bound s (inverseOrbit u s k) hp hsquarter hpar
    have hinc := coordinate_increment_bounds (inverseCoordinate (inverseOrbit u s k))
      (inverseCoordinate (reflectedInverse s (inverseOrbit u s k))) hstep
    rw [← inverseOrbit_succ] at hinc
    constructor
    · have hh := hinc.1
      push_cast
      linarith
    · have hh := hinc.2
      push_cast
      linarith

/-- The actual finite perturbed inverseOrbit has the reciprocal decay needed for
Cauchy estimates, uniformly throughout the explicit parameter disc. -/
theorem finite_inverseOrbit_norm_bound (u s : ℂ) (R : ℝ) (hR : 64 ≤ R)
    (hu : R ≤ (inverseCoordinate u).re) (J : ℕ)
    (hs : ‖s‖ ≤ parameterRadius ‖inverseCoordinate u‖ J)
    (k : ℕ) (hk : k ≤ J) :
    ‖inverseOrbit u s k‖ ≤ 2 / (R + (k : ℝ) / 2) := by
  have hre := (finite_inverseOrbit_inverse_bounds u s R hR hu J hs k hk).1
  have hden : 0 < R + (k : ℝ) / 2 := by
    have hkn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  exact (norm_le_two_div_re _ (lt_of_lt_of_le hden hre)).trans
    (div_le_div_of_nonneg_left (by norm_num) hden hre)

/-- A common inverse-coordinate upper bound yields a common parameter disc,
as required when the initial point ranges over a compact petal subset. -/
theorem finite_inverseOrbit_norm_bound_of_upper_bound (u s : ℂ) (R Z : ℝ)
    (hR : 64 ≤ R) (hu : R ≤ (inverseCoordinate u).re)
    (hZ : ‖inverseCoordinate u‖ ≤ Z) (J : ℕ)
    (hs : ‖s‖ ≤ parameterRadius Z J) (k : ℕ) (hk : k ≤ J) :
    ‖inverseOrbit u s k‖ ≤ 2 / (R + (k : ℝ) / 2) := by
  exact finite_inverseOrbit_norm_bound u s R hR hu J
    (hs.trans (parameterRadius_antitone _ Z (norm_nonneg _) hZ J)) k hk

theorem finite_inverseOrbit_ne_zero (u s : ℂ) (R : ℝ) (hR : 64 ≤ R)
    (hu : R ≤ (inverseCoordinate u).re) (J : ℕ)
    (hs : ‖s‖ ≤ parameterRadius ‖inverseCoordinate u‖ J)
    (k : ℕ) (hk : k ≤ J) : inverseOrbit u s k ≠ 0 := by
  have hre := (finite_inverseOrbit_inverse_bounds u s R hR hu J hs k hk).1
  have hp : 0 < R + (k : ℝ) / 2 := by
    have hkn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  intro hz
  simp only [hz, inverseCoordinate, div_zero, Complex.zero_re] at hre
  linarith

/-- The chosen logarithm is a genuine inverse of the actual unfolding. -/
theorem unfolding_reflectedInverse (s v : ℂ) (hs : s ≠ 1) (hv : ‖v‖ < 1) :
    Kneser.ExponentialUnfolding.unfolding s (-reflectedInverse s v) = -v := by
  have hsn : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have hn : 1 - v ≠ 0 := by
    intro h
    have hnorm : ‖v‖ = 1 := by rw [← sub_eq_zero.mp h]; norm_num
    linarith
  have harg : -s + (1 - s) * -reflectedInverse s v = Complex.log (1 - v) := by
    dsimp [reflectedInverse]
    field_simp
    ring
  rw [Kneser.ExponentialUnfolding.unfolding, harg, Complex.exp_log hn]
  ring

theorem hasDerivAt_parabolicInverse (v : ℂ) (hv : ‖v‖ < 1) :
    HasDerivAt parabolicInverse (1 / (1 - v)) v := by
  have hslit : 1 - v ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Complex.sub_re, Complex.one_re]
    linarith [Complex.re_le_norm v]
  have h := (((hasDerivAt_const v (1 : ℂ)).sub (hasDerivAt_id v)).clog hslit).neg
  change HasDerivAt parabolicInverse (-((0 - 1) / (1 - v))) v at h
  convert h using 1
  ring

theorem parabolicInverse_lipschitz (u v : ℂ) (hu : ‖u‖ < 1 / 2) (hv : ‖v‖ < 1 / 2) :
    ‖parabolicInverse u - parabolicInverse v‖ ≤ 2 * ‖u - v‖ := by
  have hder : ∀ z ∈ Metric.ball (0 : ℂ) (1 / 2),
      ‖deriv parabolicInverse z‖ ≤ 2 := by
    intro z hz
    have hn : ‖z‖ < 1 / 2 := by simpa [Metric.mem_ball, dist_zero_right] using hz
    rw [(hasDerivAt_parabolicInverse z (by linarith)).deriv, norm_div, norm_one]
    have ht := norm_sub_norm_le (1 : ℂ) z
    norm_num at ht
    have hp : 0 < ‖1 - z‖ := by linarith
    exact (div_le_iff₀ hp).mpr (by linarith)
  exact (convex_ball (0 : ℂ) (1 / 2)).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hasDerivAt_parabolicInverse z (by
      have hn : ‖z‖ < 1 / 2 := by simpa [Metric.mem_ball, dist_zero_right] using hz
      linarith)).differentiableAt) hder
    (by simpa [Metric.mem_ball, dist_zero_right] using hv)
    (by simpa [Metric.mem_ball, dist_zero_right] using hu)

theorem reflectedInverse_lipschitz (s : ℝ) (hs : 0 < s) (hs' : s < 1 / 2)
    (u v : ℂ) (hu : ‖u‖ < 1 / 2) (hv : ‖v‖ < 1 / 2) :
    ‖reflectedInverse s u - reflectedInverse s v‖ ≤ 4 * ‖u - v‖ := by
  have hden : ‖1 - (s : ℂ)‖ = 1 - s := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_of_nonneg (by linarith)]
  have heq : reflectedInverse s u - reflectedInverse s v =
      (parabolicInverse u - parabolicInverse v) / (1 - (s : ℂ)) := by
    dsimp [reflectedInverse, parabolicInverse]
    ring
  rw [heq, norm_div, hden]
  apply (div_le_iff₀ (by linarith : 0 < 1 - s)).mpr
  have h := parabolicInverse_lipschitz u v hu hv
  have hm := mul_le_mul_of_nonneg_left (show (1 / 2 : ℝ) ≤ 1 - s by linarith)
    (show 0 ≤ 4 * ‖u - v‖ by positivity)
  linarith

theorem reflectedInverse_fixedPoint (s a : ℝ) (hs : s < 1)
    (ha : Kneser.ExponentialUnfolding.unfolding s a = (a : ℂ)) :
    reflectedInverse s (-(a : ℂ)) = -(a : ℂ) := by
  have hsne : 1 - (s : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have hexp : Complex.exp (-(s : ℂ) + (1 - s) * a) = 1 + a := by
    change Complex.exp (-(s : ℂ) + (1 - s) * a) - 1 = a at ha
    simpa only [add_comm] using sub_eq_iff_eq_add.mp ha
  have hlog : Complex.log (1 - -(a : ℂ)) = -(s : ℂ) + (1 - s) * a := by
    rw [sub_neg_eq_add, ← hexp]
    apply Complex.log_exp <;> simp [Real.pi_pos.le, Real.pi_pos]
  rw [reflectedInverse, hlog]
  field_simp
  ring

theorem differentiableAt_inverseOrbit_parameter (v s : ℂ) (R Z : ℝ)
    (hR : 64 ≤ R) (hv : R ≤ (inverseCoordinate v).re)
    (hZ : ‖inverseCoordinate v‖ ≤ Z) (J : ℕ) (hs : ‖s‖ ≤ parameterRadius Z J)
    (k : ℕ) (hk : k ≤ J) : DifferentiableAt ℂ (fun t => inverseOrbit v t k) s := by
  have hZpos : 0 ≤ Z := (norm_nonneg _).trans hZ
  have hsquarter := hs.trans (parameterRadius_le_quarter Z hZpos J)
  induction k with
  | zero => exact differentiableAt_const _
  | succ k ih =>
    have hkj : k ≤ J := (Nat.le_succ k).trans hk
    have hd := ih hkj
    have hn := finite_inverseOrbit_norm_bound_of_upper_bound v s R Z hR hv hZ J hs k hkj
    have hden : 0 < R + (k : ℝ) / 2 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hnorm : ‖inverseOrbit v s k‖ ≤ 1 / 32 :=
      hn.trans ((div_le_iff₀ hden).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k]))
    have hre := Complex.re_le_norm (inverseOrbit v s k)
    have hslit : 1 - inverseOrbit v s k ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hsn : 1 - s ≠ 0 := by
      intro h
      have hn : ‖s‖ = 1 := by rw [← sub_eq_zero.mp h]; norm_num
      linarith
    have heq : (fun t => inverseOrbit v t (k + 1)) =
        (fun t => -(Complex.log (1 - inverseOrbit v t k) + t) / (1 - t)) := by
      funext t
      rw [inverseOrbit_succ]
      rfl
    rw [heq]
    exact (((differentiableAt_const (1 : ℂ)).sub hd).clog hslit |>.add
      differentiableAt_id).neg.div ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id) hsn

theorem inverseOrbit_diffContOnCl (v : ℂ) (R Z : ℝ)
    (hR : 64 ≤ R) (hv : R ≤ (inverseCoordinate v).re)
    (hZ : ‖inverseCoordinate v‖ ≤ Z) (J k : ℕ) (hk : k ≤ J) :
    DiffContOnCl ℂ (fun s => inverseOrbit v s k) (Metric.ball 0 (parameterRadius Z J)) := by
  have hr := parameterRadius_pos Z ((norm_nonneg _).trans hZ) J
  constructor
  · intro s hs
    exact (differentiableAt_inverseOrbit_parameter v s R Z hR hv hZ J
      (le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hs)) k hk).differentiableWithinAt
  · rw [closure_ball _ hr.ne']
    intro s hs
    exact (differentiableAt_inverseOrbit_parameter v s R Z hR hv hZ J
      (by simpa [Metric.mem_closedBall, dist_zero_right] using hs) k hk).continuousAt.continuousWithinAt

theorem analyticAt_inverseOrbit_parameter (v s : ℂ) (R Z : ℝ)
    (hR : 64 ≤ R) (hv : R ≤ (inverseCoordinate v).re)
    (hZ : ‖inverseCoordinate v‖ ≤ Z) (J : ℕ) (hs : ‖s‖ < parameterRadius Z J)
    (k : ℕ) (hk : k ≤ J) : AnalyticAt ℂ (fun t => inverseOrbit v t k) s := by
  exact (inverseOrbit_diffContOnCl v R Z hR hv hZ J k hk).differentiableOn.analyticAt
    (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_zero_right] using hs))

/-- Cauchy's estimate gives the true parameter velocity of the reflected
inverse iterates, with the same linear growth constant as for the forward map. -/
theorem inverseOrbit_parameter_derivative_bound (v : ℂ) (R Z : ℝ)
    (hR : 64 ≤ R) (hv : R ≤ (inverseCoordinate v).re)
    (hZ : ‖inverseCoordinate v‖ ≤ Z) (k : ℕ) :
    ‖deriv (fun s => inverseOrbit v s k) 0‖ ≤ 384 * (Z + 2) ^ 2 * ((k : ℝ) + 1) := by
  have hr := parameterRadius_pos Z ((norm_nonneg _).trans hZ) k
  have hZpos : 0 ≤ Z := (norm_nonneg _).trans hZ
  have hZne : Z + 2 ≠ 0 := by linarith
  have hden : 0 < R + (k : ℝ) / 2 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    (inverseOrbit_diffContOnCl v R Z hR hv hZ k k (le_refl k))
    (fun s hs => by
      have hn : ‖s‖ = parameterRadius Z k := by simpa [Metric.mem_sphere, dist_zero_right] using hs
      exact finite_inverseOrbit_norm_bound_of_upper_bound v s R Z hR hv hZ k hn.le k (le_refl k))
  apply hc.trans
  apply (div_le_iff₀ hr).mpr
  have heq : (384 * (Z + 2) ^ 2 * ((k : ℝ) + 1)) * parameterRadius Z k =
      4 / ((k : ℝ) + 1) := by
    dsimp [parameterRadius]
    field_simp
    ring
  rw [heq]
  apply (div_le_div_iff₀ hden (by positivity : 0 < (k : ℝ) + 1)).mpr
  linarith

end Kneser.RepellingExponentialOrbit
