import Kneser.WeightedFourierSpace

/-!
Actual multiplication of weighted Fourier coefficients, as an absolutely
convergent convolution in the complete coefficient space.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Kneser.WeightedFourier

open Set Filter Metric
open scoped Topology Classical

def ofCoefficients (H : ℝ) (t : ℤ → ℂ)
    (ht : Summable (fun n : ℤ => ‖t n‖ * weight H n)) : Space :=
  ⟨fun n => (weight H n : ℂ) * t n, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_one, Real.rpow_one, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (weight_pos H _), mul_comm] using ht⟩

@[simp] theorem coefficient_ofCoefficients (H : ℝ) (t : ℤ → ℂ)
    (ht : Summable (fun n : ℤ => ‖t n‖ * weight H n)) (n : ℤ) :
    coefficient H (ofCoefficients H t ht) n = t n := by
  dsimp [coefficient, ofCoefficients]
  field_simp [Complex.ofReal_ne_zero.mpr (weight_pos H n).ne']

theorem shift_coordinate_bound (H : ℝ) (hH : 0 ≤ H) (m n : ℤ) (a : Space) :
    ‖((weight H n / weight H (n - m) : ℝ) : ℂ) * a (n - m)‖ ≤
      weight H m * ‖a (n - m)‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos (weight_pos H n) (weight_pos H (n - m)))]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (div_le_iff₀ (weight_pos H (n - m))).mpr
  simpa only [add_sub_cancel] using weight_submultiplicative H hH m (n - m)

def shift (H : ℝ) (hH : 0 ≤ H) (m : ℤ) (a : Space) : Space :=
  ⟨fun n => ((weight H n / weight H (n - m) : ℝ) : ℂ) * a (n - m), by
    have hs : Summable (fun n : ℤ => ‖a (n - m)‖) :=
      (summable_norm a).comp_injective (i := fun n : ℤ => n - m)
        (sub_left_injective (b := m))
    have hb := (hs.mul_left (weight H m)).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun n => shift_coordinate_bound H hH m n a)
    apply memℓp_gen
    simpa only [ENNReal.toReal_one, Real.rpow_one] using hb⟩

@[simp] theorem shift_apply (H : ℝ) (hH : 0 ≤ H) (m n : ℤ) (a : Space) :
    shift H hH m a n = ((weight H n / weight H (n - m) : ℝ) : ℂ) * a (n - m) := rfl

theorem norm_shift_le (H : ℝ) (hH : 0 ≤ H) (m : ℤ) (a : Space) :
    ‖shift H hH m a‖ ≤ weight H m * ‖a‖ := by
  rw [norm_eq_tsum (shift H hH m a), norm_eq_tsum a]
  have hs : Summable (fun n : ℤ => ‖a (n - m)‖) :=
    (summable_norm a).comp_injective (i := fun n : ℤ => n - m)
      (sub_left_injective (b := m))
  have hreindex : (∑' n : ℤ, ‖a (n - m)‖) = ∑' n : ℤ, ‖a n‖ := by
    simpa only [Equiv.coe_addRight, sub_eq_add_neg] using
      (Equiv.addRight (-m)).tsum_eq (fun n : ℤ => ‖a n‖)
  calc
    _ ≤ ∑' n : ℤ, weight H m * ‖a (n - m)‖ :=
      (summable_norm (shift H hH m a)).tsum_le_tsum
        (fun n => by simpa only [shift_apply] using shift_coordinate_bound H hH m n a)
        (hs.mul_left _)
    _ = weight H m * ∑' n : ℤ, ‖a n‖ := by rw [tsum_mul_left, hreindex]

def shiftCLM (H : ℝ) (hH : 0 ≤ H) (m : ℤ) : Space →L[ℂ] Space :=
  LinearMap.mkContinuous
    { toFun := shift H hH m
      map_add' := by
        intro a b
        apply lp.ext
        funext n
        simp only [shift_apply, lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := by
        intro c a
        apply lp.ext
        funext n
        simp only [shift_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
    (weight H m) (norm_shift_le H hH m)

@[simp] theorem shiftCLM_apply (H : ℝ) (hH : 0 ≤ H) (m : ℤ) (a : Space) :
    shiftCLM H hH m a = shift H hH m a := rfl

@[simp] theorem coefficient_shift (H : ℝ) (hH : 0 ≤ H) (m n : ℤ) (a : Space) :
    coefficient H (shift H hH m a) n = coefficient H a (n - m) := by
  dsimp only [coefficient]
  rw [shift_apply, Complex.ofReal_div]
  field_simp [Complex.ofReal_ne_zero.mpr (weight_pos H n).ne',
    Complex.ofReal_ne_zero.mpr (weight_pos H (n - m)).ne']

theorem evaluate_shift (H : ℝ) (hH : 0 ≤ H) (m : ℤ) (a : Space) (z : ℂ) :
    evaluate H (shift H hH m a) z = mode m z * evaluate H a z := by
  simp only [evaluate, coefficient_shift]
  have hr := (Equiv.addRight m).tsum_eq
    (fun n : ℤ => coefficient H a (n - m) * mode n z)
  rw [← hr]
  simp only [Equiv.coe_addRight, add_sub_cancel_right, mode_mul]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

def product (H : ℝ) (hH : 0 ≤ H) (a b : Space) : Space :=
  ∑' m : ℤ, coefficient H a m • shift H hH m b

theorem summable_product (H : ℝ) (hH : 0 ≤ H) (a b : Space) :
    Summable (fun m : ℤ => coefficient H a m • shift H hH m b) := by
  apply Summable.of_norm_bounded ((summable_norm a).mul_right ‖b‖)
  intro m
  rw [norm_smul]
  calc
    _ ≤ ‖coefficient H a m‖ * (weight H m * ‖b‖) :=
      mul_le_mul_of_nonneg_left (norm_shift_le H hH m b) (norm_nonneg _)
    _ = ‖a m‖ * ‖b‖ := by rw [← mul_assoc, norm_coefficient_mul_weight]

theorem norm_product_le (H : ℝ) (hH : 0 ≤ H) (a b : Space) :
    ‖product H hH a b‖ ≤ ‖a‖ * ‖b‖ := by
  have hb (m : ℤ) : ‖coefficient H a m • shift H hH m b‖ ≤ ‖a m‖ * ‖b‖ := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left (norm_shift_le H hH m b) (norm_nonneg _)).trans_eq
      (by rw [← mul_assoc, norm_coefficient_mul_weight])
  have hs := ((summable_norm a).mul_right ‖b‖).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  calc
    _ ≤ ∑' m : ℤ, ‖coefficient H a m • shift H hH m b‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' m : ℤ, ‖a m‖ * ‖b‖ := hs.tsum_le_tsum hb ((summable_norm a).mul_right _)
    _ = ‖a‖ * ‖b‖ := by rw [tsum_mul_right, ← norm_eq_tsum]

theorem coefficient_product (H : ℝ) (hH : 0 ≤ H) (a b : Space) (n : ℤ) :
    coefficient H (product H hH a b) n =
      ∑' m : ℤ, coefficient H a m * coefficient H b (n - m) := by
  rw [← coefficientCLM_apply]
  dsimp only [product]
  rw [(coefficientCLM H n).map_tsum (summable_product H hH a b)]
  simp only [map_smul, coefficientCLM_apply, coefficient_shift, smul_eq_mul]

theorem evaluate_product (H : ℝ) (hH : 0 ≤ H) (a b : Space) (z : ℂ) (hz : |z.im| ≤ H) :
    evaluate H (product H hH a b) z = evaluate H a z * evaluate H b z := by
  change evaluateCLM H z hz (∑' m : ℤ, coefficient H a m • shift H hH m b) = _
  rw [(evaluateCLM H z hz).map_tsum (summable_product H hH a b)]
  simp only [map_smul, evaluateCLM_apply, evaluate_shift, smul_eq_mul]
  simp only [evaluate, ← mul_assoc, tsum_mul_right]

theorem product_add_left (H : ℝ) (hH : 0 ≤ H) (a b c : Space) :
    product H hH (a + b) c = product H hH a c + product H hH b c := by
  simp only [product, coefficient, lp.coeFn_add, Pi.add_apply, add_div, add_smul]
  exact (summable_product H hH a c).tsum_add (summable_product H hH b c)

theorem product_add_right (H : ℝ) (hH : 0 ≤ H) (a b c : Space) :
    product H hH a (b + c) = product H hH a b + product H hH a c := by
  have he (m : ℤ) : shift H hH m (b + c) = shift H hH m b + shift H hH m c :=
    (shiftCLM H hH m).map_add b c
  simp only [product, he, smul_add]
  exact (summable_product H hH a b).tsum_add (summable_product H hH a c)

theorem product_smul_left (H : ℝ) (hH : 0 ≤ H) (r : ℂ) (a b : Space) :
    product H hH (r • a) b = r • product H hH a b := by
  simp only [product, coefficient, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    mul_div_assoc, mul_smul, tsum_const_smul'']

theorem product_smul_right (H : ℝ) (hH : 0 ≤ H) (r : ℂ) (a b : Space) :
    product H hH a (r • b) = r • product H hH a b := by
  have he (m : ℤ) : shift H hH m (r • b) = r • shift H hH m b :=
    (shiftCLM H hH m).map_smul r b
  simp only [product, he]
  calc
    _ = ∑' m : ℤ, r • (coefficient H a m • shift H hH m b) := by
      apply tsum_congr
      intro m
      rw [smul_smul, smul_smul, mul_comm]
    _ = r • ∑' m : ℤ, coefficient H a m • shift H hH m b := tsum_const_smul'' r

end Kneser.WeightedFourier

end
