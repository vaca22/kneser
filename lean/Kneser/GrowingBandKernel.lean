import Kneser.GrowingBandGeometry

/-! Sharp two-root product bounds on the genuine exponential chart.
The real and imaginary chart variables enter the denominator together.
-/

noncomputable section

namespace Kneser.GrowingBandKernel

open Kneser.GrowingBandGeometry Kneser.RealExponentialPetal

theorem exp_sub_one_abs_lower (x : ℝ) :
    Real.exp (-|x|) * |x| ≤ |Real.exp x - 1| := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, abs_of_nonneg (by linarith [Real.add_one_le_exp x])]
    have he : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith [Real.add_one_le_exp x]
  · have hx' : x < 0 := lt_of_not_ge hx
    rw [abs_of_neg hx', abs_of_neg (by linarith [Real.exp_lt_one_iff.mpr hx'])]
    have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
    rw [show Real.exp (-x) * Real.exp x = 1 by rw [← Real.exp_add]; simp] at hh
    simp only [neg_neg]
    nlinarith

theorem norm_exp_denominator_sq (z : ℂ) :
    ‖1 - Complex.exp z‖ ^ 2 = (1 - Real.exp z.re) ^ 2 +
      4 * Real.exp z.re * Real.sin (z.im / 2) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
    Complex.exp_re, Complex.exp_im]
  have hc : Real.cos z.im = 1 - 2 * Real.sin (z.im / 2) ^ 2 := by
    have hh := Real.cos_two_mul' (z.im / 2)
    rw [show 2 * (z.im / 2) = z.im by ring] at hh
    nlinarith [Real.sin_sq_add_cos_sq (z.im / 2)]
  have hs := Real.sin_sq_add_cos_sq z.im
  linear_combination (Real.exp z.re) ^ 2 * hs - 2 * Real.exp z.re * hc

theorem rootChart_product_norm (a b : ℝ) (q : ℂ) (hab : a < b) (hq : q ≠ 1) :
    ‖rootChart a b q - (a : ℂ)‖ * ‖rootChart a b q - (b : ℂ)‖ =
      (b - a) ^ 2 * ‖q‖ / ‖1 - q‖ ^ 2 := by
  obtain ⟨hb, ha⟩ := rootChart_sub_roots a b q hq
  rw [ha, hb, norm_mul, norm_div]
  have hg : ‖(a : ℂ) - (b : ℂ)‖ = b - a := by
    rw [norm_sub_rev, ← Complex.ofReal_sub, Complex.norm_of_nonneg (sub_pos.mpr hab).le]
  rw [hg]
  ring

theorem small_real_denominator_lower (θ Y : ℝ) (Z : ℂ)
    (hθ : 0 < θ) (hY : 0 < Y) (hYθ : θ * Y ≤ Real.pi)
    (hZ : Z ∈ strip θ Y) (hx : |θ * Z.re| ≤ 1) :
    Real.exp (-2) / Real.pi ^ 2 * θ ^ 2 * (Z.re ^ 2 + Y ^ 2) ≤
      ‖1 - Complex.exp (-(θ : ℂ) * Z)‖ ^ 2 := by
  let x := -θ * Z.re
  have hxp : |x| ≤ 1 := by simpa only [x, neg_mul, abs_neg] using hx
  have hxe : Real.exp (-1) ≤ Real.exp (-|x|) := Real.exp_le_exp.mpr (by linarith)
  have hxl : Real.exp (-1) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith [(abs_le.mp hxp).1])
  have hex := exp_sub_one_abs_lower x
  have hlower : Real.exp (-1) * |x| ≤ |Real.exp x - 1| :=
    (mul_le_mul_of_nonneg_right hxe (abs_nonneg x)).trans hex
  have hsq := pow_le_pow_left₀ (by positivity) hlower 2
  rw [mul_pow, sq_abs, sq_abs, ← Real.exp_nat_mul] at hsq
  have hupper : θ * Z.im ≤ 2 * Real.pi - θ * Y := by
    have hh := mul_lt_mul_of_pos_left hZ.2 hθ
    dsimp [height] at hh
    rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hθ)] at hh
    linarith
  have hs := sine_band_lower_bound (θ * Y) (θ * Z.im) (mul_pos hθ hY) hYθ
    (mul_le_mul_of_nonneg_left hZ.1.le hθ.le) hupper
  have hss := pow_le_pow_left₀ (by positivity) hs 2
  have him : (-(θ : ℂ) * Z).im / 2 = -(θ * Z.im / 2) := by simp; ring
  rw [norm_exp_denominator_sq, him, Real.sin_neg, neg_sq]
  have hre : (-(θ : ℂ) * Z).re = x := by simp [x]
  rw [hre]
  have he2 : Real.exp (-2) = Real.exp (-1) ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; ring
  have heone : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
  have hx2 : x ^ 2 = θ ^ 2 * Z.re ^ 2 := by dsimp [x]; ring
  rw [hx2] at hsq
  norm_num at hsq
  have hm : θ ^ 2 * Y ^ 2 ≤ Real.pi ^ 2 * Real.sin (θ * Z.im / 2) ^ 2 := by
    have hh := (div_le_iff₀ (by positivity : 0 < Real.pi ^ 2)).mp
      (show θ ^ 2 * Y ^ 2 / Real.pi ^ 2 ≤ Real.sin (θ * Z.im / 2) ^ 2 by
        simpa only [div_pow, mul_pow] using hss)
    simpa only [mul_comm] using hh
  have hfirst : Real.exp (-2) * θ ^ 2 * Z.re ^ 2 ≤ Real.pi ^ 2 * (1 - Real.exp x) ^ 2 := by
    have hsq' : Real.exp (-2) * θ ^ 2 * Z.re ^ 2 ≤ (1 - Real.exp x) ^ 2 := by nlinarith [hsq]
    exact hsq'.trans (le_mul_of_one_le_left (sq_nonneg _) hpi)
  have hefour : Real.exp (-2) ≤ 4 * Real.exp x := by
    rw [he2]
    nlinarith [Real.exp_pos (-1)]
  have hsecond : Real.exp (-2) * θ ^ 2 * Y ^ 2 ≤
      4 * Real.pi ^ 2 * Real.sin (θ * Z.im / 2) ^ 2 * Real.exp x := by
    have hh := mul_le_mul_of_nonneg_left hm (Real.exp_pos (-2)).le
    have hh' := mul_le_mul_of_nonneg_left hefour
      (show 0 ≤ Real.pi ^ 2 * Real.sin (θ * Z.im / 2) ^ 2 by positivity)
    nlinarith
  have hπne := ne_of_gt Real.pi_pos
  field_simp [hπne]
  nlinarith [hfirst, hsecond]

theorem large_real_exp_ratio (z : ℂ) (hz : 1 ≤ |z.re|) :
    ‖Complex.exp z‖ / ‖1 - Complex.exp z‖ ^ 2 ≤
      (1 - Real.exp (-1))⁻¹ ^ 2 * Real.exp (-|z.re|) := by
  let c : ℝ := 1 - Real.exp (-1)
  have hc : 0 < c := by dsimp [c]; linarith [Real.exp_lt_one_iff.mpr (show (-1 : ℝ) < 0 by norm_num)]
  have hn := abs_norm_sub_norm_le (1 : ℂ) (Complex.exp z)
  rw [norm_one, Complex.norm_exp] at hn
  rw [Complex.norm_exp]
  by_cases hzr : 0 ≤ z.re
  · have hx : 1 ≤ z.re := by simpa only [abs_of_nonneg hzr] using hz
    have hr1 : 1 ≤ Real.exp z.re := Real.one_le_exp_iff.mpr hzr
    rw [abs_of_nonpos (by linarith : 1 - Real.exp z.re ≤ 0)] at hn
    have hm : 1 ≤ Real.exp (-1) * Real.exp z.re := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by linarith)
    have hl : c * Real.exp z.re ≤ ‖1 - Complex.exp z‖ := by dsimp [c]; nlinarith
    calc
      _ ≤ Real.exp z.re / (c * Real.exp z.re) ^ 2 :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
          (pow_le_pow_left₀ (by positivity) hl 2)
      _ = _ := by
        rw [abs_of_nonneg hzr, Real.exp_neg z.re]
        change Real.exp z.re / (c * Real.exp z.re) ^ 2 = c⁻¹ ^ 2 * (Real.exp z.re)⁻¹
        field_simp
  · have hx : z.re ≤ -1 := by rw [abs_of_neg (lt_of_not_ge hzr)] at hz; linarith
    have hr : Real.exp z.re ≤ Real.exp (-1) := Real.exp_le_exp.mpr hx
    have hre : Real.exp z.re ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [abs_of_nonneg (by linarith : 0 ≤ 1 - Real.exp z.re)] at hn
    have hl : c ≤ ‖1 - Complex.exp z‖ := by dsimp [c]; linarith
    calc
      _ ≤ Real.exp z.re / c ^ 2 := div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
        (pow_le_pow_left₀ hc.le hl 2)
      _ = _ := by
        rw [abs_of_neg (lt_of_not_ge hzr), neg_neg]
        change Real.exp z.re / c ^ 2 = c⁻¹ ^ 2 * Real.exp z.re
        field_simp

def smallConstant : ℝ := 25 * Real.exp 1 * Real.pi ^ 2 / Real.exp (-2)
def largeConstant : ℝ := 25 * (1 - Real.exp (-1))⁻¹ ^ 2

theorem small_bandChart_product (a b θ Y : ℝ) (Z : ℂ)
    (hab : a < b) (hθ : 0 < θ) (hY : 0 < Y) (hYθ : θ * Y ≤ Real.pi)
    (hZ : Z ∈ strip θ Y) (hratio : (b - a) / θ ≤ 5) (hx : |θ * Z.re| ≤ 1) :
    ‖bandChart a b θ Z - (a : ℂ)‖ * ‖bandChart a b θ Z - (b : ℂ)‖ ≤
      smallConstant / (Z.re ^ 2 + Y ^ 2) := by
  let q := Complex.exp (-(θ : ℂ) * Z)
  have hd := small_real_denominator_lower θ Y Z hθ hY hYθ hZ hx
  have hD : 0 < Z.re ^ 2 + Y ^ 2 := by positivity
  have hdl : 0 < Real.exp (-2) / Real.pi ^ 2 * θ ^ 2 * (Z.re ^ 2 + Y ^ 2) := by positivity
  have hden : 0 < ‖1 - q‖ ^ 2 := hdl.trans_le hd
  have hq : q ≠ 1 := by intro he; simp only [he, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hden; linarith
  have hqnorm : ‖q‖ ≤ Real.exp 1 := by
    dsimp [q]
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      neg_zero, zero_mul, sub_zero]
    linarith [(abs_le.mp hx).1]
  have hratio2 : ((b - a) / θ) ^ 2 ≤ 25 := by
    nlinarith [pow_le_pow_left₀ (by positivity : 0 ≤ (b - a) / θ) hratio 2]
  change ‖rootChart a b q - (a : ℂ)‖ * ‖rootChart a b q - (b : ℂ)‖ ≤ _
  rw [rootChart_product_norm a b q hab hq]
  calc
    _ ≤ (b - a) ^ 2 * Real.exp 1 / ‖1 - q‖ ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hqnorm (sq_nonneg _)) (sq_nonneg _)
    _ ≤ (b - a) ^ 2 * Real.exp 1 / (Real.exp (-2) / Real.pi ^ 2 * θ ^ 2 * (Z.re ^ 2 + Y ^ 2)) :=
      div_le_div_of_nonneg_left (by positivity) hdl hd
    _ = ((b - a) / θ) ^ 2 * (Real.exp 1 * Real.pi ^ 2 / Real.exp (-2)) /
        (Z.re ^ 2 + Y ^ 2) := by field_simp
    _ ≤ _ := by
      unfold smallConstant
      simpa only [mul_div_assoc, mul_assoc] using div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hratio2 (show 0 ≤ Real.exp 1 * Real.pi ^ 2 / Real.exp (-2) by positivity)) hD.le

theorem large_bandChart_product (a b θ Y : ℝ) (Z : ℂ)
    (hab : a < b) (hθ : 0 < θ) (hY : 0 < Y) (hYθ : θ * Y ≤ Real.pi)
    (hZ : Z ∈ strip θ Y) (hratio : (b - a) / θ ≤ 5) (hx : 1 ≤ |θ * Z.re|) :
    ‖bandChart a b θ Z - (a : ℂ)‖ * ‖bandChart a b θ Z - (b : ℂ)‖ ≤
      largeConstant * θ ^ 2 * Real.exp (-θ * |Z.re|) := by
  let q := Complex.exp (-(θ : ℂ) * Z)
  have hden := band_exponential_denominator θ Y Z hθ hY hYθ hZ
  have hdenpos : 0 < ‖1 - q‖ :=
    (by positivity : 0 < θ * Y / Real.pi * (1 + ‖q‖)).trans_le hden
  have hq : q ≠ 1 := by intro he; simp only [he, sub_self, norm_zero] at hdenpos; linarith
  have hre : |(-(θ : ℂ) * Z).re| = θ * |Z.re| := by simp [abs_mul, abs_of_pos hθ]
  have hx' : 1 ≤ |(-(θ : ℂ) * Z).re| := by
    simpa only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      neg_zero, zero_mul, sub_zero, neg_mul, abs_neg] using hx
  have hlarge := large_real_exp_ratio (-(θ : ℂ) * Z) hx'
  rw [hre] at hlarge
  rw [show -(θ * |Z.re|) = -θ * |Z.re| by ring] at hlarge
  have hgap : b - a ≤ 5 * θ := (div_le_iff₀ hθ).mp hratio
  have hgap2 : (b - a) ^ 2 ≤ 25 * θ ^ 2 := by
    nlinarith [pow_le_pow_left₀ (sub_pos.mpr hab).le hgap 2]
  change ‖rootChart a b q - (a : ℂ)‖ * ‖rootChart a b q - (b : ℂ)‖ ≤ _
  rw [rootChart_product_norm a b q hab hq, mul_div_assoc]
  have hh := mul_le_mul_of_nonneg_left hlarge (sq_nonneg (b - a))
  have hh' := mul_le_mul_of_nonneg_right hgap2
    (show 0 ≤ (1 - Real.exp (-1))⁻¹ ^ 2 * Real.exp (-θ * |Z.re|) by positivity)
  exact hh.trans (by simpa only [largeConstant, mul_assoc, mul_left_comm, mul_comm] using hh')

theorem bandChart_product_bound (a b θ Y : ℝ) (Z : ℂ)
    (hab : a < b) (hθ : 0 < θ) (hY : 0 < Y) (hYθ : θ * Y ≤ Real.pi)
    (hZ : Z ∈ strip θ Y) (hratio : (b - a) / θ ≤ 5) :
    ‖bandChart a b θ Z - (a : ℂ)‖ * ‖bandChart a b θ Z - (b : ℂ)‖ ≤
      smallConstant / (Z.re ^ 2 + Y ^ 2) + largeConstant * θ ^ 2 * Real.exp (-θ * |Z.re|) := by
  by_cases hx : |θ * Z.re| ≤ 1
  · exact (small_bandChart_product a b θ Y Z hab hθ hY hYθ hZ hratio hx).trans
      (le_add_of_nonneg_right (by unfold largeConstant; positivity))
  · exact (large_bandChart_product a b θ Y Z hab hθ hY hYθ hZ hratio (le_of_not_ge hx)).trans
      (le_add_of_nonneg_left (by unfold smallConstant; positivity))

end Kneser.GrowingBandKernel

end
