import Kneser.WeightedFourierConvolution

/-!
The exponential is constructed by its absolutely convergent convolution
power series.  Evaluation is the genuine complex exponential, and its
Lipschitz bound is proved from the convolution power recurrence.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.WeightedFourier

open Set Filter Metric
open scoped Topology Classical

def leftProductLM (H : ℝ) (hH : 0 ≤ H) (b : Space) : Space →ₗ[ℂ] Space where
  toFun a := product H hH a b
  map_add' a c := product_add_left H hH a c b
  map_smul' r a := by simpa only [RingHom.id_apply] using product_smul_left H hH r a b

def rightProductLM (H : ℝ) (hH : 0 ≤ H) (a : Space) : Space →ₗ[ℂ] Space where
  toFun b := product H hH a b
  map_add' b c := product_add_right H hH a b c
  map_smul' r b := by simpa only [RingHom.id_apply] using product_smul_right H hH r a b

theorem product_sub_left (H : ℝ) (hH : 0 ≤ H) (a b c : Space) :
    product H hH (a - b) c = product H hH a c - product H hH b c :=
  (leftProductLM H hH c).map_sub a b

theorem product_sub_right (H : ℝ) (hH : 0 ≤ H) (a b c : Space) :
    product H hH a (b - c) = product H hH a b - product H hH a c :=
  (rightProductLM H hH a).map_sub b c

def power (H : ℝ) (hH : 0 ≤ H) (a : Space) : ℕ → Space
  | 0 => atom H 0
  | n + 1 => product H hH a (power H hH a n)

@[simp] theorem power_zero (H : ℝ) (hH : 0 ≤ H) (a : Space) : power H hH a 0 = atom H 0 := rfl
@[simp] theorem power_succ (H : ℝ) (hH : 0 ≤ H) (a : Space) (n : ℕ) :
    power H hH a (n + 1) = product H hH a (power H hH a n) := rfl

theorem norm_power_le (H : ℝ) (hH : 0 ≤ H) (a : Space) (n : ℕ) :
    ‖power H hH a n‖ ≤ ‖a‖ ^ n := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [power_succ, pow_succ']
    exact (norm_product_le H hH _ _).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg _))

theorem evaluate_power (H : ℝ) (hH : 0 ≤ H) (a : Space) (n : ℕ) (z : ℂ) (hz : |z.im| ≤ H) :
    evaluate H (power H hH a n) z = evaluate H a z ^ n := by
  induction n with
  | zero => simp [mode, Kneser.fourierFrequency]
  | succ n hn => rw [power_succ, evaluate_product H hH _ _ z hz, hn, pow_succ']

theorem norm_power_sub_succ_le (H : ℝ) (hH : 0 ≤ H) (a b : Space)
    (R : ℝ) (hR : 0 ≤ R) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) (n : ℕ) :
    ‖power H hH a (n + 1) - power H hH b (n + 1)‖ ≤
      (n + 1 : ℝ) * R ^ n * ‖a - b‖ := by
  induction n with
  | zero =>
    simp only [power_succ, power_zero, ← product_sub_left]
    simpa using norm_product_le H hH (a - b) (atom H 0)
  | succ n hn =>
    have he : power H hH a (n + 1 + 1) - power H hH b (n + 1 + 1) =
        product H hH (a - b) (power H hH a (n + 1)) +
        product H hH b (power H hH a (n + 1) - power H hH b (n + 1)) := by
      rw [power_succ, power_succ, product_sub_left, product_sub_right]
      abel
    have hpa : ‖power H hH a (n + 1)‖ ≤ R ^ (n + 1) :=
      (norm_power_le H hH a _).trans (pow_le_pow_left₀ (norm_nonneg _) ha _)
    rw [he]
    calc
      _ ≤ ‖product H hH (a - b) (power H hH a (n + 1))‖ +
          ‖product H hH b (power H hH a (n + 1) - power H hH b (n + 1))‖ := norm_add_le _ _
      _ ≤ ‖a - b‖ * R ^ (n + 1) + R * ((n + 1 : ℝ) * R ^ n * ‖a - b‖) := by
        exact add_le_add
          ((norm_product_le H hH _ _).trans (mul_le_mul_of_nonneg_left hpa (norm_nonneg _)))
          ((norm_product_le H hH _ _).trans
            (mul_le_mul hb hn (norm_nonneg _) hR))
      _ = ((n + 1 : ℕ) + 1 : ℝ) * R ^ (n + 1) * ‖a - b‖ := by
        rw [pow_succ]
        push_cast
        ring

def exponentialTerm (H : ℝ) (hH : 0 ≤ H) (a : Space) (n : ℕ) : Space :=
  ((n.factorial : ℂ)⁻¹) • power H hH a n

theorem norm_exponentialTerm_le (H : ℝ) (hH : 0 ≤ H) (a : Space) (n : ℕ) :
    ‖exponentialTerm H hH a n‖ ≤ ‖a‖ ^ n / (n.factorial : ℝ) := by
  rw [exponentialTerm, norm_smul, norm_inv]
  simp only [Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left (norm_power_le H hH a n) (inv_nonneg.mpr (Nat.cast_nonneg _))).trans_eq
    (by ring)

theorem summable_exponential_norm (H : ℝ) (hH : 0 ≤ H) (a : Space) :
    Summable (fun n : ℕ => ‖exponentialTerm H hH a n‖) :=
  (NormedSpace.expSeries_div_summable ‖a‖).of_nonneg_of_le
    (fun _ => norm_nonneg _) (norm_exponentialTerm_le H hH a)

def exponential (H : ℝ) (hH : 0 ≤ H) (a : Space) : Space :=
  ∑' n : ℕ, exponentialTerm H hH a n

theorem norm_exponential_le (H : ℝ) (hH : 0 ≤ H) (a : Space) :
    ‖exponential H hH a‖ ≤ Real.exp ‖a‖ := by
  calc
    _ ≤ ∑' n : ℕ, ‖exponentialTerm H hH a n‖ := norm_tsum_le_tsum_norm (summable_exponential_norm H hH a)
    _ ≤ ∑' n : ℕ, ‖a‖ ^ n / (n.factorial : ℝ) :=
      (summable_exponential_norm H hH a).tsum_le_tsum (norm_exponentialTerm_le H hH a)
        (NormedSpace.expSeries_div_summable ‖a‖)
    _ = Real.exp ‖a‖ := by
      rw [(NormedSpace.expSeries_div_hasSum_exp ‖a‖).tsum_eq, ← Real.exp_eq_exp_ℝ]

theorem evaluate_exponential (H : ℝ) (hH : 0 ≤ H) (a : Space) (z : ℂ) (hz : |z.im| ≤ H) :
    evaluate H (exponential H hH a) z = Complex.exp (evaluate H a z) := by
  change evaluateCLM H z hz (∑' n : ℕ, exponentialTerm H hH a n) = _
  rw [(evaluateCLM H z hz).map_tsum (summable_exponential_norm H hH a).of_norm]
  simp only [exponentialTerm, map_smul, evaluateCLM_apply, evaluate_power H hH a _ z hz, smul_eq_mul]
  have he (n : ℕ) : (n.factorial : ℂ)⁻¹ * evaluate H a z ^ n =
      evaluate H a z ^ n / (n.factorial : ℂ) := by ring
  simp only [he]
  rw [(NormedSpace.expSeries_div_hasSum_exp (evaluate H a z)).tsum_eq, ← Complex.exp_eq_exp_ℂ]

theorem norm_exponentialTerm_sub_succ_le (H : ℝ) (hH : 0 ≤ H) (a b : Space)
    (R : ℝ) (hR : 0 ≤ R) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) (n : ℕ) :
    ‖exponentialTerm H hH a (n + 1) - exponentialTerm H hH b (n + 1)‖ ≤
      ‖a - b‖ * (R ^ n / (n.factorial : ℝ)) := by
  rw [exponentialTerm, exponentialTerm, ← smul_sub, norm_smul, norm_inv, Complex.norm_natCast]
  have h := mul_le_mul_of_nonneg_left (norm_power_sub_succ_le H hH a b R hR ha hb n)
    (inv_nonneg.mpr (Nat.cast_nonneg (n + 1).factorial : (0 : ℝ) ≤ _))
  refine h.trans_eq ?_
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  field_simp

/-- The sharp exponential Lipschitz estimate on each norm ball follows
from the actual convolution recurrence, rather than being a certificate. -/
theorem norm_exponential_sub_le (H : ℝ) (hH : 0 ≤ H) (a b : Space)
    (R : ℝ) (hR : 0 ≤ R) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖exponential H hH a - exponential H hH b‖ ≤ ‖a - b‖ * Real.exp R := by
  have hs := (summable_exponential_norm H hH a).of_norm.sub
    (summable_exponential_norm H hH b).of_norm
  have he : exponential H hH a - exponential H hH b =
      ∑' n : ℕ, (exponentialTerm H hH a (n + 1) - exponentialTerm H hH b (n + 1)) := by
    rw [exponential, exponential, ← (summable_exponential_norm H hH a).of_norm.tsum_sub
      (summable_exponential_norm H hH b).of_norm, hs.tsum_eq_zero_add]
    simp [exponentialTerm]
  have hd (n : ℕ) := norm_exponentialTerm_sub_succ_le H hH a b R hR ha hb n
  have hsn := ((NormedSpace.expSeries_div_summable R).mul_left ‖a - b‖).of_nonneg_of_le
    (fun _ => norm_nonneg _) hd
  rw [he]
  calc
    _ ≤ ∑' n : ℕ, ‖exponentialTerm H hH a (n + 1) - exponentialTerm H hH b (n + 1)‖ :=
      norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' n : ℕ, ‖a - b‖ * (R ^ n / (n.factorial : ℝ)) :=
      hsn.tsum_le_tsum hd ((NormedSpace.expSeries_div_summable R).mul_left _)
    _ = ‖a - b‖ * Real.exp R := by
      rw [tsum_mul_left, (NormedSpace.expSeries_div_hasSum_exp R).tsum_eq, ← Real.exp_eq_exp_ℝ]

end Kneser.WeightedFourier

end
