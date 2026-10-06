import Kneser.FourierSewingIntegralCoefficient

/-!
Actual holomorphic upper/lower sewing maps are univalent whenever their
explicit derivative budget is below one.  The conclusion follows from a
proved Fourier-series Lipschitz bound on a convex half-plane.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.WeightedFourier

open Set Filter Metric
open scoped Topology Classical
open Kneser.FourierSewing

theorem convex_im_ge (v : ℝ) : Convex ℝ {z : ℂ | v ≤ z.im} :=
  (convex_Ici v).linear_preimage Complex.imCLM.toLinearMap

theorem norm_mode_sub_le_on_halfPlane (n : ℤ) (hn : 0 ≤ n) (v : ℝ)
    (z w : ℂ) (hz : v ≤ z.im) (hw : v ≤ w.im) :
    ‖mode n z - mode n w‖ ≤
      (‖Kneser.fourierFrequency n‖ * Real.exp (-2 * Real.pi * (n : ℝ) * v)) * ‖z - w‖ := by
  apply (convex_im_ge v).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hasDerivAt_mode n x).hasDerivWithinAt) _ hw hz
  intro x hx
  rw [norm_mul, norm_mode_nonnegative n hn x, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hnreal : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * (n : ℝ)) (sub_nonneg.mpr hx)]

def halfPlaneLipschitz (H v : ℝ) (a : Space) : ℝ :=
  4 * Real.pi * ‖a‖ * Real.exp (-2 * Real.pi * (H + v)) /
    (1 - Real.exp (-2 * Real.pi * (H + v))) ^ 2

theorem norm_evaluate_positive_sub_le_on_halfPlane (H : ℝ) (P : Space)
    (hP : ∀ n : ℤ, n < 0 → P n = 0) (v : ℝ) (hgap : 0 < H + v)
    (z w : ℂ) (hz : v ≤ z.im) (hw : v ≤ w.im) :
    ‖evaluate H P z - evaluate H P w‖ ≤ halfPlaneLipschitz H v P * ‖z - w‖ := by
  let q := Real.exp (-2 * Real.pi * (H + v))
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hqlt : q < 1 := by
    change Real.exp (-2 * Real.pi * (H + v)) < 1
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have hb (n : ℤ) : ‖coefficient H P n * mode n z - coefficient H P n * mode n w‖ ≤
      ((2 * Real.pi * ‖P‖) * firstGeometric q n) * ‖z - w‖ := by
    by_cases hn : 0 < n
    · rw [← mul_sub, norm_mul]
      calc
        _ ≤ (‖P‖ / weight H n) *
            ((‖Kneser.fourierFrequency n‖ * Real.exp (-2 * Real.pi * (n : ℝ) * v)) * ‖z - w‖) :=
          mul_le_mul (norm_coefficient_le H P n)
            (norm_mode_sub_le_on_halfPlane n hn.le v z w hz hw) (norm_nonneg _)
            (by have hh := weight_pos H n; positivity)
        _ = _ := by
          rw [norm_fourierFrequency, firstGeometric, nonzeroGeometric,
            ite_eq_right (ne_of_gt hn), abs_of_nonneg (by exact_mod_cast hn.le : (0 : ℝ) ≤ (n : ℝ))]
          have hr := positive_mode_ratio H v n hn.le
          dsimp [q]
          rw [← hr]
          ring
    · by_cases hnzero : n = 0
      · subst n
        simp [mode, Kneser.fourierFrequency, firstGeometric, nonzeroGeometric]
      · simp [coefficient, hP n (by omega), firstGeometric, nonzeroGeometric, hnzero]
        positivity
  have hsum := ((summable_firstGeometric q hq hqlt).mul_left (2 * Real.pi * ‖P‖)).mul_right ‖z - w‖
  have hnorm := hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  have hzs := summable_evaluate_positive H P hP z (by linarith)
  have hws := summable_evaluate_positive H P hP w (by linarith)
  rw [evaluate, evaluate, ← hzs.tsum_sub hws]
  exact (norm_tsum_le_tsum_norm hnorm).trans
    ((hnorm.tsum_le_tsum hb hsum).trans_eq (by
      rw [tsum_mul_right, tsum_mul_left, tsum_firstGeometric q hq hqlt]
      dsimp [q, halfPlaneLipschitz]
      ring))

theorem injOn_positive_sewing (H : ℝ) (P : Space)
    (hP : ∀ n : ℤ, n < 0 → P n = 0) (v : ℝ) (hgap : 0 < H + v)
    (hsmall : halfPlaneLipschitz H v P < 1) (t₀ : ℂ) :
    Set.InjOn (fun z : ℂ => z + t₀ + evaluate H P z) {z : ℂ | v ≤ z.im} := by
  intro z hz w hw he
  have hd : z - w = evaluate H P w - evaluate H P z := by linear_combination he
  have hl := norm_evaluate_positive_sub_le_on_halfPlane H P hP v hgap z w hz hw
  have hdle : ‖z - w‖ ≤ halfPlaneLipschitz H v P * ‖z - w‖ := by
    conv_lhs => rw [hd, norm_sub_rev]
    exact hl
  have hnzero : ‖z - w‖ = 0 := by nlinarith [norm_nonneg (z - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnzero)

def reflection (a : Space) : Space :=
  ⟨fun n => a (-n), by
    apply memℓp_gen
    simpa only [ENNReal.toReal_one, Real.rpow_one, Function.comp_def] using
      ((summable_norm a).comp_injective (i := fun n : ℤ => -n) neg_injective)⟩

@[simp] theorem reflection_apply (a : Space) (n : ℤ) : reflection a n = a (-n) := rfl

@[simp] theorem weight_neg (H : ℝ) (n : ℤ) : weight H (-n) = weight H n := by
  simp [weight]

theorem norm_reflection (a : Space) : ‖reflection a‖ = ‖a‖ := by
  rw [norm_eq_tsum (reflection a), norm_eq_tsum a]
  simpa only [reflection_apply, Equiv.neg_apply] using
    (Equiv.neg ℤ).tsum_eq (fun n : ℤ => ‖a n‖)

theorem coefficient_reflection (H : ℝ) (a : Space) (n : ℤ) :
    coefficient H (reflection a) n = coefficient H a (-n) := by
  simp only [coefficient, reflection_apply, weight_neg]

theorem evaluate_reflection (H : ℝ) (a : Space) (z : ℂ) :
    evaluate H (reflection a) z = evaluate H a (-z) := by
  simp only [evaluate, coefficient_reflection]
  have hr := (Equiv.neg ℤ).tsum_eq (fun n : ℤ => coefficient H a n * mode (-n) z)
  simp only [Equiv.neg_apply, neg_neg] at hr
  rw [hr]
  apply tsum_congr
  intro n
  congr 1
  rw [mode, mode]
  congr 1
  simp [Kneser.fourierFrequency]

theorem reflection_negative_is_positive (Q : Space) (hQ : Q ∈ Negative) :
    ∀ n : ℤ, n < 0 → reflection Q n = 0 := by
  intro n hn
  rw [reflection_apply]
  exact hQ (-n) (by omega)

theorem norm_evaluate_negative_le (H : ℝ) (Q : Space) (hQ : Q ∈ Negative)
    (z : ℂ) (hz : z.im ≤ H) : ‖evaluate H Q z‖ ≤ ‖Q‖ := by
  have he := norm_evaluate_positive_le H (reflection Q) (reflection_negative_is_positive Q hQ)
    (-z) (by simp only [Complex.neg_im]; linarith)
  simpa only [evaluate_reflection, neg_neg, norm_reflection] using he

theorem differentiableOn_evaluate_negative (H : ℝ) (Q : Space) (hQ : Q ∈ Negative) :
    DifferentiableOn ℂ (evaluate H Q) {z : ℂ | z.im < H} := by
  have hpos := differentiableOn_evaluate_positive H (reflection Q)
    (reflection_negative_is_positive Q hQ)
  have hsopen : IsOpen {z : ℂ | 0 < H + z.im} :=
    isOpen_lt continuous_const (continuous_const.add Complex.continuous_im)
  intro z hz
  change z.im < H at hz
  have hpoint : -z ∈ {z : ℂ | 0 < H + z.im} := by
    simp only [Set.mem_setOf_eq, Complex.neg_im]
    linarith
  have hd := (hpos.differentiableAt (hsopen.mem_nhds hpoint)).comp z
    ((hasDerivAt_id z).neg.differentiableAt)
  have heq : (fun w : ℂ => evaluate H (reflection Q) (-w)) = evaluate H Q := by
    funext w
    rw [evaluate_reflection, neg_neg]
  change DifferentiableWithinAt ℂ (evaluate H Q) {z : ℂ | z.im < H} z
  change DifferentiableAt ℂ (fun w => evaluate H (reflection Q) (-w)) z at hd
  rw [heq] at hd
  exact hd.differentiableWithinAt

theorem injOn_negative_sewing (H : ℝ) (Q : Space) (hQ : Q ∈ Negative)
    (v : ℝ) (hgap : 0 < H - v) (hsmall : halfPlaneLipschitz H (-v) (reflection Q) < 1) :
    Set.InjOn (fun z : ℂ => z + evaluate H Q z) {z : ℂ | z.im ≤ v} := by
  intro z hz w hw he
  change z.im ≤ v at hz
  change w.im ≤ v at hw
  have hd : z - w = evaluate H Q w - evaluate H Q z := by linear_combination he
  have hl := norm_evaluate_positive_sub_le_on_halfPlane H (reflection Q)
    (reflection_negative_is_positive Q hQ) (-v) (by linarith) (-z) (-w)
    (by simp only [Complex.neg_im]; linarith) (by simp only [Complex.neg_im]; linarith)
  simp only [evaluate_reflection, neg_neg, neg_sub_neg, norm_sub_rev] at hl
  have hdle : ‖z - w‖ ≤ halfPlaneLipschitz H (-v) (reflection Q) * ‖z - w‖ := by
    conv_lhs => rw [hd, norm_sub_rev]
    exact hl
  have hnzero : ‖z - w‖ = 0 := by nlinarith [norm_nonneg (z - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnzero)

end Kneser.WeightedFourier

end
