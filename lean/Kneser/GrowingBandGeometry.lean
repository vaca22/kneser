import Kneser.PositiveKoenigsPetal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
An explicit two-root chart on the genuine growing strip. Its period and
midline are calculated from the actual attracting multiplier. This file
proves chart geometry; it does not assume invariant band dynamics.
-/

noncomputable section

namespace Kneser.GrowingBandGeometry

open Set Kneser.ApolloniusGeometry Kneser.RealExponentialPetal
open Kneser.ExponentialUnfolding Kneser.PositiveKoenigsOrbit

def height (θ : ℝ) : ℝ := 2 * Real.pi / θ

def rootChart (a b : ℝ) (q : ℂ) : ℂ := ((a : ℂ) - (b : ℂ) * q) / (1 - q)

def bandChart (a b θ : ℝ) (Z : ℂ) : ℂ := rootChart a b (Complex.exp (-(θ : ℂ) * Z))

def bandTime (a b θ : ℝ) (u : ℂ) : ℂ :=
  -(Complex.log (-crossRatio a b u) - (Real.pi : ℂ) * Complex.I) / (θ : ℂ)

def strip (θ Y : ℝ) : Set ℂ := {Z | Y < Z.im ∧ Z.im < height θ - Y}

theorem rootChart_sub_roots (a b : ℝ) (q : ℂ) (hq : q ≠ 1) :
    rootChart a b q - (b : ℂ) = ((a : ℂ) - (b : ℂ)) / (1 - q) ∧
    rootChart a b q - (a : ℂ) = q * (((a : ℂ) - (b : ℂ)) / (1 - q)) := by
  have hden : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  constructor <;> dsimp [rootChart] <;> field_simp <;> ring

theorem crossRatio_rootChart (a b : ℝ) (q : ℂ) (hab : a ≠ b) (hq : q ≠ 1) :
    crossRatio a b (rootChart a b q) = q := by
  have hgap : (a : ℂ) - (b : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hab)
  rw [crossRatio, (rootChart_sub_roots a b q hq).1, (rootChart_sub_roots a b q hq).2]
  exact mul_div_cancel_right₀ _ (div_ne_zero hgap (sub_ne_zero.mpr (Ne.symm hq)))

theorem sine_band_lower_bound (η y : ℝ) (hη : 0 < η) (_hηπ : η ≤ Real.pi)
    (hy : η ≤ y) (hy' : y ≤ 2 * Real.pi - η) :
    η / Real.pi ≤ Real.sin (y / 2) := by
  by_cases hyp : y ≤ Real.pi
  · have hs := Real.mul_le_sin (show 0 ≤ y / 2 by linarith) (by linarith : y / 2 ≤ Real.pi / 2)
    have hh : η / Real.pi ≤ 2 / Real.pi * (y / 2) := by
      apply (div_le_div_of_nonneg_right hy Real.pi_pos.le).trans_eq
      ring
    exact hh.trans hs
  · have hs := Real.mul_le_sin (show 0 ≤ Real.pi - y / 2 by linarith)
      (by linarith : Real.pi - y / 2 ≤ Real.pi / 2)
    rw [Real.sin_pi_sub] at hs
    have hh : η / Real.pi ≤ 2 / Real.pi * (Real.pi - y / 2) := by
      apply (div_le_iff₀ Real.pi_pos).mpr
      field_simp
      linarith
    exact hh.trans hs

theorem norm_exp_sub_one_half_angle (z : ℂ) :
    |Real.sin (z.im / 2)| * (1 + ‖Complex.exp z‖) ≤ ‖1 - Complex.exp z‖ := by
  let r := Real.exp z.re
  have hr : 0 < r := Real.exp_pos _
  have hc : Real.cos z.im = 1 - 2 * Real.sin (z.im / 2) ^ 2 := by
    have hc := Real.cos_two_mul' (z.im / 2)
    rw [show 2 * (z.im / 2) = z.im by ring] at hc
    nlinarith [Real.sin_sq_add_cos_sq (z.im / 2)]
  have hnorm : ‖1 - Complex.exp z‖ ^ 2 =
      (1 - r) ^ 2 + 4 * r * Real.sin (z.im / 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      Complex.exp_re, Complex.exp_im]
    have hs := Real.sin_sq_add_cos_sq z.im
    dsimp [r]
    nlinarith
  have hsin : Real.sin (z.im / 2) ^ 2 ≤ 1 := Real.sin_sq_le_one _
  have hnormr : ‖Complex.exp z‖ = r := Complex.norm_exp z
  rw [hnormr]
  have hsq : (|Real.sin (z.im / 2)| * (1 + r)) ^ 2 ≤ ‖1 - Complex.exp z‖ ^ 2 := by
    rw [mul_pow, sq_abs, hnorm]
    nlinarith [mul_nonneg (show 0 ≤ 1 - Real.sin (z.im / 2) ^ 2 by linarith) (sq_nonneg (1 - r))]
  exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hsq

theorem band_exponential_denominator (θ Y : ℝ) (Z : ℂ)
    (hθ : 0 < θ) (hY : 0 < Y) (hYθ : θ * Y ≤ Real.pi)
    (hZ : Z ∈ strip θ Y) :
    θ * Y / Real.pi * (1 + ‖Complex.exp (-(θ : ℂ) * Z)‖) ≤
      ‖1 - Complex.exp (-(θ : ℂ) * Z)‖ := by
  have hupper : θ * Z.im < 2 * Real.pi - θ * Y := by
    have hh := mul_lt_mul_of_pos_left hZ.2 hθ
    dsimp [height] at hh
    have hθne := ne_of_gt hθ
    field_simp [hθne] at hh
    nlinarith
  have hsin := sine_band_lower_bound (θ * Y) (θ * Z.im) (mul_pos hθ hY) hYθ
    (mul_le_mul_of_nonneg_left hZ.1.le hθ.le) hupper.le
  have hspos : 0 ≤ Real.sin (θ * Z.im / 2) :=
    (by positivity : 0 ≤ θ * Y / Real.pi).trans hsin
  have him : (-(θ : ℂ) * Z).im / 2 = -(θ * Z.im / 2) := by simp; ring
  have he := norm_exp_sub_one_half_angle (-(θ : ℂ) * Z)
  rw [him, Real.sin_neg, abs_neg, abs_of_nonneg hspos] at he
  exact (mul_le_mul_of_nonneg_right hsin (by positivity)).trans he

theorem bandChart_ne_roots (a b θ Y : ℝ) (Z : ℂ)
    (hab : a < b) (hθ : 0 < θ) (hY : 0 < Y) (hYθ : θ * Y ≤ Real.pi)
    (hZ : Z ∈ strip θ Y) : bandChart a b θ Z ≠ (a : ℂ) ∧ bandChart a b θ Z ≠ (b : ℂ) := by
  have hden := band_exponential_denominator θ Y Z hθ hY hYθ hZ
  have hdenpos : 0 < ‖1 - Complex.exp (-(θ : ℂ) * Z)‖ :=
    (by positivity : 0 < θ * Y / Real.pi * (1 + ‖Complex.exp (-(θ : ℂ) * Z)‖)).trans_le hden
  have hq : Complex.exp (-(θ : ℂ) * Z) ≠ 1 := by
    intro he
    simp only [he, sub_self, norm_zero] at hdenpos
    linarith
  have hgap : (a : ℂ) - (b : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ne_of_lt hab)
  obtain ⟨hb, ha⟩ := rootChart_sub_roots a b _ hq
  constructor
  · apply sub_ne_zero.mp
    change rootChart a b _ - (a : ℂ) ≠ 0
    rw [ha]
    exact mul_ne_zero (Complex.exp_ne_zero _) (div_ne_zero hgap (sub_ne_zero.mpr (Ne.symm hq)))
  · apply sub_ne_zero.mp
    change rootChart a b _ - (b : ℂ) ≠ 0
    rw [hb]
    exact div_ne_zero hgap (sub_ne_zero.mpr (Ne.symm hq))

theorem bandChart_root_distance_bound (a b θ Y : ℝ) (Z : ℂ)
    (hab : a < b) (hθ : 0 < θ) (hY : 0 < Y) (hYθ : θ * Y ≤ Real.pi)
    (hZ : Z ∈ strip θ Y) :
    ‖bandChart a b θ Z - (a : ℂ)‖ ≤ (b - a) * Real.pi / (θ * Y) ∧
    ‖bandChart a b θ Z - (b : ℂ)‖ ≤ (b - a) * Real.pi / (θ * Y) := by
  let q := Complex.exp (-(θ : ℂ) * Z)
  have hden := band_exponential_denominator θ Y Z hθ hY hYθ hZ
  have hp : 0 < θ * Y / Real.pi := by positivity
  have hdn : 0 < ‖1 - q‖ := (by positivity : 0 < θ * Y / Real.pi * (1 + ‖q‖)).trans_le hden
  have hq : q ≠ 1 := by intro he; simp only [he, sub_self, norm_zero] at hdn; linarith
  have hgap : ‖(a : ℂ) - (b : ℂ)‖ = b - a := by
    rw [norm_sub_rev, ← Complex.ofReal_sub, Complex.norm_of_nonneg (sub_pos.mpr hab).le]
  have hroots := rootChart_sub_roots a b q hq
  have ha : ‖bandChart a b θ Z - (a : ℂ)‖ = ‖q‖ * ((b - a) / ‖1 - q‖) := by
    change ‖rootChart a b q - (a : ℂ)‖ = _
    rw [hroots.2, norm_mul, norm_div, hgap]
  have hb : ‖bandChart a b θ Z - (b : ℂ)‖ = (b - a) / ‖1 - q‖ := by
    change ‖rootChart a b q - (b : ℂ)‖ = _
    rw [hroots.1, norm_div, hgap]
  constructor
  · rw [ha]
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hdn (mul_pos hθ hY)).mpr
    have hh : θ * Y / Real.pi * ‖q‖ ≤ ‖1 - q‖ := by nlinarith [norm_nonneg q]
    have hh' : θ * Y * ‖q‖ ≤ ‖1 - q‖ * Real.pi := by
      apply (div_le_iff₀ Real.pi_pos).mp
      simpa only [div_mul_eq_mul_div] using hh
    nlinarith [mul_le_mul_of_nonneg_left hh' (sub_pos.mpr hab).le]
  · rw [hb]
    apply (div_le_div_iff₀ hdn (mul_pos hθ hY)).mpr
    have hh : θ * Y / Real.pi ≤ ‖1 - q‖ := by nlinarith [norm_nonneg q]
    have hh' := (div_le_iff₀ Real.pi_pos).mp hh
    nlinarith [mul_le_mul_of_nonneg_left hh' (sub_pos.mpr hab).le]

theorem bandTime_bandChart (a b θ Y : ℝ) (Z : ℂ)
    (hab : a < b) (hθ : 0 < θ) (hY : 0 < Y) (hYθ : θ * Y ≤ Real.pi)
    (hZ : Z ∈ strip θ Y) : bandTime a b θ (bandChart a b θ Z) = Z := by
  have hden := band_exponential_denominator θ Y Z hθ hY hYθ hZ
  have hq : Complex.exp (-(θ : ℂ) * Z) ≠ 1 := by
    intro he
    simp only [he, sub_self, norm_zero, norm_one] at hden
    have hh : 0 < θ * Y / Real.pi := by positivity
    linarith
  have hupper : θ * Z.im < 2 * Real.pi := by
    have hh := mul_lt_mul_of_pos_left hZ.2 hθ
    dsimp [height] at hh
    rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hθ)] at hh
    nlinarith
  have hlower : 0 < θ * Z.im := mul_pos hθ (lt_trans hY hZ.1)
  have hex : -Complex.exp (-(θ : ℂ) * Z) =
      Complex.exp (-(θ : ℂ) * Z + (Real.pi : ℂ) * Complex.I) := by
    rw [Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  unfold bandTime bandChart
  rw [crossRatio_rootChart a b _ (ne_of_lt hab) hq, hex,
    Complex.log_exp (by simp; linarith : -Real.pi < (-(θ : ℂ) * Z + (Real.pi : ℂ) * Complex.I).im)
      (by simp; linarith : (-(θ : ℂ) * Z + (Real.pi : ℂ) * Complex.I).im ≤ Real.pi)]
  have hθc : (θ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hθ
  field_simp
  ring

theorem analyticOnNhd_bandChart (a b θ Y : ℝ)
    (_hab : a < b) (hθ : 0 < θ) (hY : 0 < Y) (hYθ : θ * Y ≤ Real.pi) :
    AnalyticOnNhd ℂ (bandChart a b θ) (strip θ Y) := by
  intro Z hZ
  have he : AnalyticAt ℂ (fun W : ℂ => Complex.exp (-(θ : ℂ) * W)) Z :=
    (analyticAt_const.mul analyticAt_id).cexp
  have hden := band_exponential_denominator θ Y Z hθ hY hYθ hZ
  have hne : 1 - Complex.exp (-(θ : ℂ) * Z) ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hden
    have hh : 0 < θ * Y / Real.pi * (1 + ‖Complex.exp (-(θ : ℂ) * Z)‖) := by positivity
    linarith
  exact (analyticAt_const.sub (analyticAt_const.mul he)).div (analyticAt_const.sub he) hne

theorem injOn_bandChart (a b θ Y : ℝ)
    (hab : a < b) (hθ : 0 < θ) (hY : 0 < Y) (hYθ : θ * Y ≤ Real.pi) :
    InjOn (bandChart a b θ) (strip θ Y) := by
  intro Z hZ W hW heq
  rw [← bandTime_bandChart a b θ Y Z hab hθ hY hYθ hZ,
    ← bandTime_bandChart a b θ Y W hab hθ hY hYθ hW, heq]

/-- The real segment between the actual roots is exactly the central
line of the constructed chart. -/
theorem bandChart_midline (a b θ x : ℝ) (hθ : 0 < θ) :
    bandChart a b θ ((x : ℂ) + ((Real.pi / θ : ℝ) : ℂ) * Complex.I) =
      (((a + b * Real.exp (-θ * x)) / (1 + Real.exp (-θ * x)) : ℝ) : ℂ) := by
  have hθc : (θ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hθ
  have hi : -(θ : ℂ) * ((x : ℂ) + ((Real.pi / θ : ℝ) : ℂ) * Complex.I) =
      ((-θ * x : ℝ) : ℂ) - (Real.pi : ℂ) * Complex.I := by
    push_cast
    field_simp
    ring
  unfold bandChart
  rw [hi, Complex.exp_sub, ← Complex.ofReal_exp, Complex.exp_pi_mul_I]
  simp only [div_neg, div_one]
  unfold rootChart
  push_cast
  ring

theorem bandChart_midline_between (a b θ x : ℝ) (hab : a < b) (hθ : 0 < θ) :
    a < (bandChart a b θ ((x : ℂ) + ((Real.pi / θ : ℝ) : ℂ) * Complex.I)).re ∧
    (bandChart a b θ ((x : ℂ) + ((Real.pi / θ : ℝ) : ℂ) * Complex.I)).re < b := by
  rw [bandChart_midline a b θ x hθ, Complex.ofReal_re]
  have hr : 0 < Real.exp (-θ * x) := Real.exp_pos _
  have hd : 0 < 1 + Real.exp (-θ * x) := by positivity
  constructor
  · apply (lt_div_iff₀ hd).mpr
    nlinarith [mul_pos (sub_pos.mpr hab) hr]
  · apply (div_lt_iff₀ hd).mpr
    nlinarith

theorem bandTime_midline_height (a b θ Y x : ℝ)
    (hab : a < b) (hθ : 0 < θ) (hY : 0 < Y) (hYθ : θ * Y < Real.pi) :
    (bandTime a b θ (bandChart a b θ
      ((x : ℂ) + ((Real.pi / θ : ℝ) : ℂ) * Complex.I))).im = height θ / 2 := by
  have hmid : (x : ℂ) + ((Real.pi / θ : ℝ) : ℂ) * Complex.I ∈ strip θ Y := by
    constructor
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
        Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
      exact (lt_div_iff₀ hθ).mpr (by simpa only [mul_comm] using hYθ)
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
        Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
      dsimp [height]
      apply (lt_sub_iff_add_lt).mpr
      apply (lt_div_iff₀ hθ).mpr
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hθ)]
      linarith
  rw [bandTime_bandChart a b θ Y _ hab hθ hY hYθ.le hmid]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im, Complex.I_im,
    Complex.I_re, mul_one, mul_zero, add_zero, zero_add, height]
  ring

/-- Substituting the genuine multiplier time scale into the chart bound
gives a spatial constant independent of the unfolding parameter. -/
theorem actual_bandChart_distance_bound (Q : QuotientControl) (s a b Y : ℝ) (Z : ℂ)
    (hs : 0 < s) (hs1 : s < 1 / 2) (hab : a < b)
    (hκr : (1 - s) * (b - a) < Q.radius)
    (hY : 0 < Y) (hYθ : timeScale Q ((1 - s) * (b - a)) * Y ≤ Real.pi)
    (hZ : Z ∈ strip (timeScale Q ((1 - s) * (b - a))) Y) :
    ‖bandChart a b (timeScale Q ((1 - s) * (b - a))) Z - (a : ℂ)‖ ≤ 5 * Real.pi / Y ∧
    ‖bandChart a b (timeScale Q ((1 - s) * (b - a))) Z - (b : ℂ)‖ ≤ 5 * Real.pi / Y := by
  obtain ⟨hθ, hratio⟩ := timeScale_pos_and_gap_bound Q s a b hs hs1 hab hκr
  obtain ⟨ha, hb⟩ := bandChart_root_distance_bound a b _ Y Z hab hθ hY hYθ hZ
  have hc : (b - a) * Real.pi / (timeScale Q ((1 - s) * (b - a)) * Y) ≤ 5 * Real.pi / Y := by
    calc
      _ = ((b - a) / timeScale Q ((1 - s) * (b - a))) * (Real.pi / Y) := by ring
      _ ≤ _ := by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right hratio (show 0 ≤ Real.pi / Y by positivity)
  exact ⟨ha.trans hc, hb.trans hc⟩

end Kneser.GrowingBandGeometry

end
