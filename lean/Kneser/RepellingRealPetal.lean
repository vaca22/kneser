import Kneser.RepellingExponentialOrbit

/-!
# Actual infinite repelling petals of the exponential unfolding

The reflected principal-logarithm inverse has a contracting cross-ratio.
Its step is obtained from the exact forward exponential factorization at the
output point, so it uses the same constructed divided difference.
-/

namespace Kneser.RepellingRealPetal

open Kneser.RepellingExponentialOrbit
open Kneser.ParabolicExponentialOrbit (inverseCoordinate)
open Kneser.RealExponentialPetal Kneser.ExponentialDividedDifference
open Kneser.ParabolicInitialPetal Kneser.ApolloniusGeometry
open Kneser.ExponentialUnfolding Kneser.RealExponentialRoots
open Metric Set

noncomputable section

def inverseTimeScale (Q : QuotientControl) (κ : ℝ) : ℝ := κ - timeScale Q κ

theorem inverseTimeScale_bounds (Q : QuotientControl) (κ : ℝ)
    (hκ : 0 < κ) (hκr : κ < Q.radius) :
    (7 / 16) * κ ≤ inverseTimeScale Q κ ∧ inverseTimeScale Q κ ≤ (9 / 16) * κ := by
  have hh := timeScale_bounds Q κ hκ hκr
  dsimp [inverseTimeScale]
  constructor <;> linarith

theorem inverseTimeScale_pos_and_gap_bound (Q : QuotientControl) (s a b : ℝ)
    (hs : 0 < s) (hs' : s < 1 / 2) (hab : a < b)
    (hκr : (1 - s) * (b - a) < Q.radius) :
    0 < inverseTimeScale Q ((1 - s) * (b - a)) ∧
      (b - a) / inverseTimeScale Q ((1 - s) * (b - a)) ≤ 5 := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have hκ : 0 < (1 - s) * (b - a) := mul_pos (by linarith) hd
  have hl := (inverseTimeScale_bounds Q _ hκ hκr).1
  have hp : 0 < inverseTimeScale Q ((1 - s) * (b - a)) := lt_of_lt_of_le (by positivity) hl
  refine ⟨hp, (div_le_iff₀ hp).mpr ?_⟩
  have hm := mul_le_mul_of_nonneg_right (show (1 / 2 : ℝ) ≤ 1 - s by linarith) hd.le
  linarith

/-- The exact inverse cross-ratio identity, derived from the actual exponential
at the inverse image. -/
theorem inverse_crossRatio_step (Q : QuotientControl) (s a b : ℂ) (v : ℂ)
    (hroota : unfolding s a = a) (hrootb : unfolding s b = b)
    (hs : s ≠ 1) (hane : a ≠ -1) (hv : ‖v‖ < 1) (hva : v ≠ -a)
    (_hEa : Q.E ((1 - s) * (-reflectedInverse s v - a)) ≠ 0)
    (hEb : Q.E ((1 - s) * (-reflectedInverse s v - b)) ≠ 0) :
    reflectedInverse s v ≠ -a ∧
      crossRatio (-b) (-a) (reflectedInverse s v) =
        crossRatio (-b) (-a) v * Complex.exp (-((1 - s) * (b - a))) *
          (Q.E ((1 - s) * (-reflectedInverse s v - a)) /
            Q.E ((1 - s) * (-reflectedInverse s v - b))) := by
  let w := reflectedInverse s v
  have hinv : unfolding s (-w) = -v := unfolding_reflectedInverse s v hs hv
  have hwa : w ≠ -a := by
    intro h
    have hneg : -w = a := by rw [h]; simp
    rw [hneg, hroota] at hinv
    apply hva
    linear_combination hinv
  have hfa := unfolding_fixedPoint_factor Q.E Q.factor s a (-w) hroota
  have hfb := unfolding_fixedPoint_factor Q.E Q.factor s b (-w) hrootb
  rw [hinv] at hfa hfb
  have hratio := fixedPoint_multiplier_ratio s a b hroota hrootb
  have hsa : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have han : 1 + a ≠ 0 := by intro h; apply hane; linear_combination h
  have hcore : 1 + b = (1 + a) * Complex.exp ((1 - s) * (b - a)) := by
    apply mul_left_cancel₀ hsa
    simpa only [mul_assoc] using hratio
  have hden : v + a ≠ 0 := by intro h; apply hva; linear_combination h
  have hwden : w + a ≠ 0 := by intro h; apply hwa; linear_combination h
  have he : Complex.exp ((1 - s) * (b - a)) ≠ 0 := Complex.exp_ne_zero _
  have hh : Complex.exp (-((1 - s) * (b - a))) =
      (Complex.exp ((1 - s) * (b - a)))⁻¹ := Complex.exp_neg _
  refine ⟨hwa, ?_⟩
  change (w - -b) / (w - -a) = _
  rw [crossRatio, hh]
  simp only [sub_neg_eq_add]
  field_simp
  have hfacA : v + a = (1 - s) * (1 + a) * (w + a) * Q.E ((1 - s) * (-w - a)) := by
    linear_combination -hfa
  have hfacB : v + b = (1 - s) * (1 + b) * (w + b) * Q.E ((1 - s) * (-w - b)) := by
    linear_combination -hfb
  rw [hfacA, hfacB, hcore]
  ring

theorem inverse_petal_output_arguments_mem (Q : QuotientControl) (s a b x : ℝ) (v : ℂ)
    (hs : 0 < s) (hs' : s < 1 / 2) (ha : a < 0) (hb : 0 < b) (hbsmall : b < 1 / 4)
    (hrootb : unfolding s b = (b : ℂ)) (hgap : b - a < Q.radius / 8)
    (hx : 80 / Q.radius ≤ x) (hx80 : 80 ≤ x) (hva : v ≠ -(a : ℂ))
    (hq : ‖crossRatio (-b) (-a) v‖ ≤
      Real.exp (-(inverseTimeScale Q ((1 - s) * (b - a)) * x))) :
    ‖v‖ < 1 / 2 ∧
      (1 - (s : ℂ)) * (-reflectedInverse s v - (a : ℂ)) ∈ ball 0 Q.radius ∧
      (1 - (s : ℂ)) * (-reflectedInverse s v - (b : ℂ)) ∈ ball 0 Q.radius := by
  have hab : a < b := by linarith
  have hd : 0 < b - a := sub_pos.mpr hab
  have hκr : (1 - s) * (b - a) < Q.radius := by
    have hm := mul_le_mul_of_nonneg_right (show 1 - s ≤ 1 by linarith) hd.le
    linarith [Q.radius_pos]
  obtain ⟨hθ, hratio⟩ := inverseTimeScale_pos_and_gap_bound Q s a b hs hs' hab hκr
  have hxpos : 0 < x := by linarith
  have hgapnorm : ‖(-(a : ℂ)) - (-(b : ℂ))‖ = b - a := by
    have hh : -(a : ℂ) - -(b : ℂ) = ((b - a : ℝ) : ℂ) := by push_cast; ring
    rw [hh, Complex.norm_of_nonneg hd.le]
  have hn := attracting_root_distance_bound (-(b : ℂ)) (-(a : ℂ)) v
    (inverseTimeScale Q ((1 - s) * (b - a)) * x) (mul_pos hθ hxpos) hva hq
  rw [hgapnorm] at hn
  have hfrac : (b - a) / (inverseTimeScale Q ((1 - s) * (b - a)) * x) =
      ((b - a) / inverseTimeScale Q ((1 - s) * (b - a))) / x := by ring
  rw [hfrac] at hn
  have hdist : ‖v + (b : ℂ)‖ ≤ 5 / x := by
    simpa only [sub_neg_eq_add] using
      hn.trans (div_le_div_of_nonneg_right hratio hxpos.le)
  have hfrac80 : (5 : ℝ) / x ≤ 1 / 16 := (div_le_iff₀ hxpos).mpr (by linarith)
  have hnormv : ‖v‖ < 1 / 2 := by
    have ht := norm_sub_le (v + (b : ℂ)) (b : ℂ)
    have heq : v + (b : ℂ) - b = v := by ring
    rw [heq, Complex.norm_of_nonneg hb.le] at ht
    linarith
  have hnormb : ‖-(b : ℂ)‖ < 1 / 2 := by
    rw [norm_neg, Complex.norm_of_nonneg hb.le]
    linarith
  have hw := reflectedInverse_lipschitz s hs hs' v (-(b : ℂ)) hnormv hnormb
  rw [reflectedInverse_fixedPoint s b (by linarith) hrootb] at hw
  simp only [sub_neg_eq_add] at hw
  have hwclose : ‖reflectedInverse s v + (b : ℂ)‖ ≤ 20 / x := by
    calc
      _ ≤ 4 * (5 / x) := hw.trans (mul_le_mul_of_nonneg_left hdist (by norm_num))
      _ = _ := by ring
  have hfracQ : (20 : ℝ) / x ≤ Q.radius / 4 := by
    apply (div_le_iff₀ hxpos).mpr
    have hm := (div_le_iff₀ Q.radius_pos).mp hx
    linarith
  have hwb : ‖-reflectedInverse s v - (b : ℂ)‖ ≤ Q.radius / 4 := by
    have heq : -reflectedInverse s v - (b : ℂ) = -(reflectedInverse s v + (b : ℂ)) := by ring
    rw [heq, norm_neg]
    exact hwclose.trans hfracQ
  have hwa : ‖-reflectedInverse s v - (a : ℂ)‖ ≤ Q.radius / 4 + (b - a) := by
    have heq : -reflectedInverse s v - (a : ℂ) =
        (-reflectedInverse s v - (b : ℂ)) + ((b : ℂ) - (a : ℂ)) := by ring
    rw [heq]
    have hh : ‖(b : ℂ) - (a : ℂ)‖ = b - a := by
      rw [← Complex.ofReal_sub, Complex.norm_of_nonneg hd.le]
    exact (norm_add_le _ _).trans (by rw [hh]; linarith)
  have hh : ‖1 - (s : ℂ)‖ = 1 - s := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_of_nonneg (by linarith)]
  refine ⟨hnormv, ?_, ?_⟩
  · simp only [mem_ball, dist_zero_right, norm_mul, hh]
    have hm := mul_le_mul_of_nonneg_right (show 1 - s ≤ 1 by linarith)
      (norm_nonneg (-reflectedInverse s v - (a : ℂ)))
    linarith [Q.radius_pos]
  · simp only [mem_ball, dist_zero_right, norm_mul, hh]
    have hm := mul_le_mul_of_nonneg_right (show 1 - s ≤ 1 by linarith)
      (norm_nonneg (-reflectedInverse s v - (b : ℂ)))
    linarith [Q.radius_pos]

theorem actual_inverse_crossRatio_contraction (Q : QuotientControl) (s a b x : ℝ) (v : ℂ)
    (hs : 0 < s) (hs' : s < 1 / 2) (ha : a < 0) (hasmall : -1 / 4 < a)
    (hb : 0 < b) (hbsmall : b < 1 / 4)
    (hroota : unfolding s a = (a : ℂ)) (hrootb : unfolding s b = (b : ℂ))
    (hgap : b - a < Q.radius / 8) (hx : 80 / Q.radius ≤ x) (hx80 : 80 ≤ x)
    (hva : v ≠ -(a : ℂ))
    (hq : ‖crossRatio (-b) (-a) v‖ ≤
      Real.exp (-(inverseTimeScale Q ((1 - s) * (b - a)) * x))) :
    reflectedInverse s v ≠ -(a : ℂ) ∧
      ‖crossRatio (-b) (-a) (reflectedInverse s v)‖ ≤
        ‖crossRatio (-b) (-a) v‖ *
          Real.exp (-(3 / 4) * inverseTimeScale Q ((1 - s) * (b - a))) := by
  obtain ⟨hvnorm, hma, hmb⟩ := inverse_petal_output_arguments_mem Q s a b x v
    hs hs' ha hb hbsmall hrootb hgap hx hx80 hva hq
  let κ : ℝ := (1 - s) * (b - a)
  have hκ : 0 < κ := mul_pos (by linarith) (by linarith)
  have hκr : κ < Q.radius := by
    have hm := mul_le_mul_of_nonneg_right (show 1 - s ≤ 1 by linarith)
      (show 0 ≤ b - a by linarith)
    dsimp [κ]
    linarith [Q.radius_pos]
  have hsne : (s : ℂ) ≠ 1 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith
  have hane : (a : ℂ) ≠ -1 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith
  obtain ⟨hne, hstep⟩ := inverse_crossRatio_step Q s a b v hroota hrootb hsne hane
    (by linarith) hva (Q.ne_zero _ hma) (Q.ne_zero _ hmb)
  have hκeq : (1 - (s : ℂ)) * ((b : ℂ) - (a : ℂ)) = (κ : ℂ) := by simp [κ]
  rw [hκeq] at hstep
  have hdiff : (1 - (s : ℂ)) * (-reflectedInverse s v - (a : ℂ)) -
      (1 - (s : ℂ)) * (-reflectedInverse s v - (b : ℂ)) = (κ : ℂ) := by rw [← hκeq]; ring
  have hl := Q.increment _ hmb _ hma
  rw [hdiff] at hl
  have hab : |(Complex.log (Q.E ((1 - (s : ℂ)) * (-reflectedInverse s v - (a : ℂ)))) -
      Complex.log (Q.E ((1 - (s : ℂ)) * (-reflectedInverse s v - (b : ℂ)))) - (κ : ℂ) / 2).re| ≤ κ / 16 := by
    have hh := (Complex.abs_re_le_norm _).trans hl
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ,
      div_eq_mul_inv, mul_comm] using hh
  have hlogupper := (abs_le.mp hab).2
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.ofReal_re] at hlogupper
  have hθ := (inverseTimeScale_bounds Q κ hκ hκr).2
  have hnorma := Complex.norm_exp (Complex.log (Q.E ((1 - (s : ℂ)) * (-reflectedInverse s v - (a : ℂ)))))
  have hnormb := Complex.norm_exp (Complex.log (Q.E ((1 - (s : ℂ)) * (-reflectedInverse s v - (b : ℂ)))))
  rw [Complex.exp_log (Q.ne_zero _ hma)] at hnorma
  rw [Complex.exp_log (Q.ne_zero _ hmb)] at hnormb
  refine ⟨hne, ?_⟩
  rw [hstep, norm_mul, norm_mul, norm_div, Complex.norm_exp, hnorma, hnormb]
  simp only [Complex.neg_re, Complex.ofReal_re]
  have heq : ‖crossRatio (-(b : ℂ)) (-(a : ℂ)) v‖ * Real.exp (-κ) *
      (Real.exp (Complex.log (Q.E ((1 - (s : ℂ)) * (-reflectedInverse s v - (a : ℂ))))).re /
       Real.exp (Complex.log (Q.E ((1 - (s : ℂ)) * (-reflectedInverse s v - (b : ℂ))))).re) =
      ‖crossRatio (-(b : ℂ)) (-(a : ℂ)) v‖ * Real.exp (-κ +
        (Complex.log (Q.E ((1 - (s : ℂ)) * (-reflectedInverse s v - (a : ℂ))))).re -
        (Complex.log (Q.E ((1 - (s : ℂ)) * (-reflectedInverse s v - (b : ℂ))))).re) := by
    rw [← Real.exp_sub, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [heq]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (norm_nonneg _)

theorem infinite_inverseOrbit_crossRatio_bound (Q : QuotientControl) (s a b R : ℝ) (v : ℂ)
    (hs : 0 < s) (hs' : s < 1 / 2) (ha : a < 0) (hasmall : -1 / 4 < a)
    (hb : 0 < b) (hbsmall : b < 1 / 4)
    (hroota : unfolding s a = (a : ℂ)) (hrootb : unfolding s b = (b : ℂ))
    (hgap : b - a < Q.radius / 8) (hR : 80 / Q.radius ≤ R) (hR80 : 80 ≤ R)
    (hva : v ≠ -(a : ℂ))
    (hq : ‖crossRatio (-b) (-a) v‖ ≤
      Real.exp (-(inverseTimeScale Q ((1 - s) * (b - a)) * R))) (k : ℕ) :
    inverseOrbit v s k ≠ -(a : ℂ) ∧
      ‖crossRatio (-b) (-a) (inverseOrbit v s k)‖ ≤
        Real.exp (-(inverseTimeScale Q ((1 - s) * (b - a)) * (R + (3 / 4) * (k : ℝ)))) := by
  induction k with
  | zero => simpa using And.intro hva hq
  | succ k ih =>
    obtain ⟨hne, hn⟩ := ih
    have hkn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    obtain ⟨hnew, hc⟩ := actual_inverse_crossRatio_contraction Q s a b
      (R + (3 / 4) * (k : ℝ)) (inverseOrbit v s k) hs hs' ha hasmall hb hbsmall
      hroota hrootb hgap (by linarith) (by linarith) hne hn
    rw [← inverseOrbit_succ] at hnew hc
    refine ⟨hnew, hc.trans ?_⟩
    calc
      _ ≤ Real.exp (-(inverseTimeScale Q ((1 - s) * (b - a)) * (R + (3 / 4) * (k : ℝ)))) *
          Real.exp (-(3 / 4) * inverseTimeScale Q ((1 - s) * (b - a))) :=
        mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

theorem infinite_inverseOrbit_root_product_bound (Q : QuotientControl) (s a b R : ℝ) (v : ℂ)
    (hs : 0 < s) (hs' : s < 1 / 2) (ha : a < 0) (hasmall : -1 / 4 < a)
    (hb : 0 < b) (hbsmall : b < 1 / 4)
    (hroota : unfolding s a = (a : ℂ)) (hrootb : unfolding s b = (b : ℂ))
    (hgap : b - a < Q.radius / 8) (hR : 80 / Q.radius ≤ R) (hR80 : 80 ≤ R)
    (hva : v ≠ -(a : ℂ))
    (hq : ‖crossRatio (-b) (-a) v‖ ≤
      Real.exp (-(inverseTimeScale Q ((1 - s) * (b - a)) * R))) (k : ℕ) :
    ‖inverseOrbit v s k + (b : ℂ)‖ * ‖inverseOrbit v s k + (a : ℂ)‖ ≤
      100 / (R + (3 / 4) * (k : ℝ)) ^ 2 := by
  have hab : a < b := by linarith
  have hd : 0 < b - a := sub_pos.mpr hab
  have hκr : (1 - s) * (b - a) < Q.radius := by
    have hm := mul_le_mul_of_nonneg_right (show 1 - s ≤ 1 by linarith) hd.le
    linarith [Q.radius_pos]
  obtain ⟨hθ, hratio⟩ := inverseTimeScale_pos_and_gap_bound Q s a b hs hs' hab hκr
  obtain ⟨hne, hn⟩ := infinite_inverseOrbit_crossRatio_bound Q s a b R v
    hs hs' ha hasmall hb hbsmall hroota hrootb hgap hR hR80 hva hq k
  have hx : 0 < R + (3 / 4) * (k : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hprod := root_product_bound_model_time (-(b : ℂ)) (-(a : ℂ)) (inverseOrbit v s k)
    (inverseTimeScale Q ((1 - s) * (b - a))) (R + (3 / 4) * (k : ℝ)) hθ hx hne hn
  have hgapnorm : ‖(-(a : ℂ)) - (-(b : ℂ))‖ = b - a := by
    have heq : -(a : ℂ) - -(b : ℂ) = ((b - a : ℝ) : ℂ) := by push_cast; ring
    rw [heq, Complex.norm_of_nonneg hd.le]
  rw [hgapnorm] at hprod
  simp only [sub_neg_eq_add] at hprod
  apply hprod.trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have hrnonneg : 0 ≤ (b - a) / inverseTimeScale Q ((1 - s) * (b - a)) := by positivity
  nlinarith

theorem inverseTimeScale_eq_log_multiplier (Q : QuotientControl) (s a b : ℝ)
    (hs : s < 1) (ha : -1 < a) (hab : a < b)
    (hroota : unfolding s a = (a : ℂ)) (hrootb : unfolding s b = (b : ℂ)) :
    inverseTimeScale Q ((1 - s) * (b - a)) = Real.log ((1 - s) * (1 + b)) := by
  have hθ := timeScale_eq_neg_log_multiplier Q s a b hs ha hab hroota hrootb
  have hratio := fixedPoint_multiplier_ratio (s : ℂ) a b hroota hrootb
  have hκ : (1 - (s : ℂ)) * ((b : ℂ) - a) = (((1 - s) * (b - a) : ℝ) : ℂ) := by push_cast; ring
  rw [hκ] at hratio
  rw [← Complex.ofReal_exp] at hratio
  have hreal : (1 - s) * (1 + b) = (1 - s) * (1 + a) * Real.exp ((1 - s) * (b - a)) := by
    have h := congrArg Complex.re hratio
    simpa only [Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.one_re,
      Complex.ofReal_re, Complex.one_im, Complex.sub_im, Complex.add_im, Complex.ofReal_im,
      mul_zero, sub_zero, add_zero, zero_mul] using h
  have hμ : 0 < (1 - s) * (1 + a) := mul_pos (by linarith) (by linarith)
  dsimp [inverseTimeScale]
  rw [hθ, hreal, Real.log_mul hμ.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

theorem inverseTimeScale_quadratic_upper (Q : QuotientControl) (r C s a b : ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (hs' : s < 1 / 2) (hab : a < b)
    (hκr : (1 - s) * (b - a) < r)
    (hquad : ∀ z : ℂ, ‖z‖ < r → ‖Complex.log (Q.E z) - z / 2‖ ≤ C * ‖z‖ ^ 2) :
    inverseTimeScale Q ((1 - s) * (b - a)) ≤ (b - a) / 2 + C * (b - a) ^ 2 := by
  let d := b - a
  have hd : 0 < d := sub_pos.mpr hab
  have hκ : 0 < (1 - s) * d := mul_pos (by linarith) hd
  have hκd : (1 - s) * d ≤ d := by nlinarith
  have hmem : ‖(((1 - s) * d : ℝ) : ℂ)‖ < r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]
    exact hκr
  have hh := (Complex.abs_re_le_norm _).trans (hquad (((1 - s) * d : ℝ) : ℂ) hmem)
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.ofReal_re,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ] at hh
  have hl := (abs_le.mp hh).1
  have hsq : ((1 - s) * d) ^ 2 ≤ d ^ 2 := (sq_le_sq₀ hκ.le hd.le).mpr hκd
  have hmul := mul_le_mul_of_nonneg_left hsq hC
  dsimp [inverseTimeScale, timeScale, d] at *
  linarith

/-- Every bounded set in a buffered parabolic inverse petal is contained in
the true positive-parameter repelling petal for all sufficiently small
parameters. The infinite estimate is proved for the actual logarithmic branch. -/
theorem exists_uniform_initial_repelling_petals :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ Z : ℝ, 0 ≤ Z →
      ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 / 2 ∧ ∀ s : ℝ, 0 < s → s < s₀ →
        ∃ a b θ : ℝ, a < 0 ∧ 0 < b ∧ |a| < 1 / (4 * (Z + 1)) ∧
          |b| < 1 / (4 * (Z + 1)) ∧ 0 < θ ∧
          unfolding s a = (a : ℂ) ∧ unfolding s b = (b : ℂ) ∧
          θ = Real.log ((1 - s) * (1 + b)) ∧
          ∀ v : ℂ, R + 1 ≤ (inverseCoordinate v).re → ‖inverseCoordinate v‖ ≤ Z →
            ‖crossRatio (-b) (-a) v‖ ≤ Real.exp (-(θ * R)) ∧
            ∀ k : ℕ, ‖inverseOrbit v s k + (b : ℂ)‖ * ‖inverseOrbit v s k + (a : ℂ)‖ ≤
              100 / (R + (3 / 4) * (k : ℝ)) ^ 2 := by
  obtain ⟨Q⟩ := exists_quotientControl
  have hQr : 0 < Q.radius := Q.radius_pos
  obtain ⟨r, C, hr, hC, hquad⟩ := quotient_log_quadratic_bound Q
  refine ⟨max (80 / Q.radius) 80, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro R hR Z hZ
  have hRbase : 80 / Q.radius ≤ R := (le_max_left _ _).trans hR
  have hR80 : 80 ≤ R := (le_max_right _ _).trans hR
  have hRpos : 0 < R := by linarith
  let B : ℝ := Z ^ 2 / 2 + C * R
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let δ : ℝ := min (Q.radius / 16)
    (min (r / 4) (min (1 / 4) (min (1 / (4 * (Z + 1))) (1 / (16 * (B + 1))))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδQ : δ ≤ Q.radius / 16 := min_le_left _ _
  have hδr : δ ≤ r / 4 := (min_le_left _ _).trans' (min_le_right _ _)
  have hδsmall : δ ≤ 1 / 4 :=
    (min_le_left _ _).trans' ((min_le_right _ _).trans (min_le_right _ _))
  have hδZ : δ ≤ 1 / (4 * (Z + 1)) :=
    (min_le_left _ _).trans' ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hδB : δ ≤ 1 / (16 * (B + 1)) :=
    (min_le_right _ _).trans' ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨s₀, hs₀, hs₀half, hroots⟩ := exists_ordered_small_real_roots δ hδ
  refine ⟨s₀, hs₀, hs₀half, ?_⟩
  intro s hs hss
  have hshalf : s < 1 / 2 := hss.trans_le hs₀half
  obtain ⟨a, b, haδ, ha, hb, hbδ, hroota, hrootb⟩ := hroots s hs hss
  have hab : a < b := by linarith
  have hd : 0 < b - a := sub_pos.mpr hab
  have hgap : b - a < Q.radius / 8 := by linarith
  have hκQ : (1 - s) * (b - a) < Q.radius := by
    have hm := mul_le_mul_of_nonneg_right (show 1 - s ≤ 1 by linarith) hd.le
    linarith [Q.radius_pos]
  have hκr : (1 - s) * (b - a) < r := by
    have hm := mul_le_mul_of_nonneg_right (show 1 - s ≤ 1 by linarith) hd.le
    linarith
  have hmulZ : δ * (4 * (Z + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 4 * (Z + 1))).mp hδZ
  have hdZ : (b - a) * Z ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right (show b - a ≤ 2 * δ by linarith) hZ
    nlinarith
  have hmulB : δ * (16 * (B + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 16 * (B + 1))).mp hδB
  have hdsmall : (b - a) * (Z ^ 2 / 2 + C * R) ≤ 1 / 4 := by
    have hm := mul_le_mul_of_nonneg_right (show b - a ≤ 2 * δ by linarith) hB
    change (b - a) * B ≤ _
    nlinarith
  have haZ : |a| < 1 / (4 * (Z + 1)) := by rw [abs_of_neg ha]; linarith
  have hbZ : |b| < 1 / (4 * (Z + 1)) := by rw [abs_of_pos hb]; linarith
  refine ⟨a, b, inverseTimeScale Q ((1 - s) * (b - a)), ha, hb, haZ, hbZ,
    (inverseTimeScale_pos_and_gap_bound Q s a b hs hshalf hab hκQ).1, hroota, hrootb,
    inverseTimeScale_eq_log_multiplier Q s a b (by linarith) (by linarith)
      hab hroota hrootb, ?_⟩
  intro v hζre hζnorm
  have hθ := inverseTimeScale_quadratic_upper Q r C s a b hC.le hs hshalf hab hκr hquad
  obtain ⟨hva, hq⟩ := initial_crossRatio_bound_of_time_upper C R Z s (-b) (-a)
    (inverseTimeScale Q ((1 - s) * (b - a))) v hC.le hRpos.le hZ hs hshalf
    (by linarith) (by linarith) hζre hζnorm (by convert hdZ using 1; ring)
    (by convert hdsmall using 1; ring) (by convert hθ using 1; ring)
  have hq' : ‖crossRatio (-(b : ℂ)) (-(a : ℂ)) v‖ ≤
      Real.exp (-(inverseTimeScale Q ((1 - s) * (b - a)) * R)) := by simpa using hq
  have hva' : v ≠ -(a : ℂ) := by simpa using hva
  refine ⟨hq', ?_⟩
  intro k
  exact infinite_inverseOrbit_root_product_bound Q s a b R v hs hshalf ha (by linarith)
    hb (by linarith) hroota hrootb hgap hRbase hR80 hva' hq' k

end

end Kneser.RepellingRealPetal
