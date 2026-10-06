import Kneser.HornCoefficient
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.MetricSpace.Contracting

/-!
The weighted Fourier space is an actual complete ℓ¹ space.  Its stored
coordinates are the Fourier coefficients multiplied by the strip weight,
so completeness uses the existing ℓ¹ theorem, without an assumed Banach
space or an assumed Fourier projection.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.WeightedFourier

open Set Filter Metric
open scoped Topology Classical

abbrev Space := lp (fun _ : ℤ => ℂ) 1

def weight (H : ℝ) (n : ℤ) : ℝ := Real.exp (2 * Real.pi * |(n : ℝ)| * H)

theorem weight_pos (H : ℝ) (n : ℤ) : 0 < weight H n := Real.exp_pos _

@[simp] theorem weight_zero (H : ℝ) : weight H 0 = 1 := by simp [weight]

theorem weight_submultiplicative (H : ℝ) (hH : 0 ≤ H) (m n : ℤ) :
    weight H (m + n) ≤ weight H m * weight H n := by
  rw [weight, weight, weight, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  push_cast
  have h := abs_add_le (m : ℝ) (n : ℝ)
  have hc : 0 ≤ 2 * Real.pi * H := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h hc]

def coefficient (H : ℝ) (a : Space) (n : ℤ) : ℂ := a n / (weight H n : ℂ)

def atom (H : ℝ) (n : ℤ) : Space := lp.single 1 n (weight H n : ℂ)

theorem norm_eq_tsum (a : Space) : ‖a‖ = ∑' n : ℤ, ‖a n‖ := by
  simpa using lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal) a

theorem summable_norm (a : Space) : Summable (fun n : ℤ => ‖a n‖) := by
  simpa using (lp.memℓp a).summable (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal)

theorem norm_coefficient_mul_weight (H : ℝ) (a : Space) (n : ℤ) :
    ‖coefficient H a n‖ * weight H n = ‖a n‖ := by
  rw [coefficient, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (weight_pos H n), div_mul_cancel₀ _ (weight_pos H n).ne']

theorem weighted_norm_eq (H : ℝ) (a : Space) :
    ∑' n : ℤ, ‖coefficient H a n‖ * weight H n = ‖a‖ := by
  simp only [norm_coefficient_mul_weight, ← norm_eq_tsum]

theorem norm_coefficient_le (H : ℝ) (a : Space) (n : ℤ) :
    ‖coefficient H a n‖ ≤ ‖a‖ / weight H n := by
  apply (le_div_iff₀ (weight_pos H n)).mpr
  rw [norm_coefficient_mul_weight]
  exact lp.norm_apply_le_norm (by norm_num) a n

@[simp] theorem coefficient_atom (H : ℝ) (m n : ℤ) :
    coefficient H (atom H m) n = if n = m then 1 else 0 := by
  simp only [coefficient, atom, lp.coeFn_single, Pi.single_apply]
  split_ifs with h
  · subst n; exact div_self (Complex.ofReal_ne_zero.mpr (weight_pos H m).ne')
  · simp

@[simp] theorem norm_atom (H : ℝ) (n : ℤ) : ‖atom H n‖ = weight H n := by
  rw [atom, lp.norm_single (by norm_num), Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (weight_pos H n)]

def coefficientCLM (H : ℝ) (n : ℤ) : Space →L[ℂ] ℂ :=
  ((weight H n : ℂ)⁻¹) • lp.evalCLM ℂ (fun _ : ℤ => ℂ) 1 n

@[simp] theorem coefficientCLM_apply (H : ℝ) (n : ℤ) (a : Space) :
    coefficientCLM H n a = coefficient H a n := by
  simp [coefficientCLM, coefficient, lp.evalCLM, lp.evalₗ, div_eq_mul_inv, mul_comm]
  exact Or.inl rfl

def mask (P : ℤ → Prop) (a : Space) : Space := by
  classical
  exact ⟨fun n => if P n then a n else 0,
    (lp.memℓp a).mono' fun n => by split_ifs <;> simp⟩

theorem mask_apply (P : ℤ → Prop) (a : Space) (n : ℤ) :
    mask P a n = if P n then a n else 0 := by rfl

theorem norm_mask_le (P : ℤ → Prop) (a : Space) : ‖mask P a‖ ≤ ‖a‖ := by
  apply lp.norm_mono (by norm_num)
  intro n
  classical
  rw [mask_apply]
  split_ifs <;> simp

def maskLM (P : ℤ → Prop) : Space →ₗ[ℂ] Space := by
  classical
  refine { toFun := mask P, map_add' := ?_, map_smul' := ?_ }
  · intro a b
    apply lp.ext
    funext n
    simp only [mask_apply, lp.coeFn_add, Pi.add_apply]
    split_ifs <;> simp

  · intro c a
    apply lp.ext
    funext n
    simp only [mask_apply, lp.coeFn_smul, Pi.smul_apply]
    split_ifs <;> simp

def maskCLM (P : ℤ → Prop) : Space →L[ℂ] Space :=
  (maskLM P).mkContinuous 1 (fun a => by
    change ‖mask P a‖ ≤ 1 * ‖a‖
    simpa using norm_mask_le P a)

def negativeProjection : Space →L[ℂ] Space := maskCLM (fun n => n < 0)
def positiveProjection : Space →L[ℂ] Space := maskCLM (fun n => 0 ≤ n)

@[simp] theorem negativeProjection_apply (a : Space) (n : ℤ) :
    negativeProjection a n = if n < 0 then a n else 0 := by
  simp only [negativeProjection, maskCLM, LinearMap.mkContinuous_apply]
  change mask (fun n => n < 0) a n = _
  by_cases hn : n < 0 <;> simp [mask_apply, hn]

@[simp] theorem positiveProjection_apply (a : Space) (n : ℤ) :
    positiveProjection a n = if 0 ≤ n then a n else 0 := by
  simp only [positiveProjection, maskCLM, LinearMap.mkContinuous_apply]
  change mask (fun n => 0 ≤ n) a n = _
  by_cases hn : 0 ≤ n <;> simp [mask_apply, hn]

theorem projection_split (a : Space) : negativeProjection a + positiveProjection a = a := by
  apply lp.ext
  funext n
  simp only [lp.coeFn_add, Pi.add_apply, negativeProjection_apply, positiveProjection_apply]
  by_cases hn : n < 0 <;> simp [hn, not_lt.mp, not_le.mpr]

theorem norm_negativeProjection_le (a : Space) : ‖negativeProjection a‖ ≤ ‖a‖ := norm_mask_le _ a
theorem norm_positiveProjection_le (a : Space) : ‖positiveProjection a‖ ≤ ‖a‖ := norm_mask_le _ a

def Negative : Set Space := {a | ∀ n : ℤ, 0 ≤ n → a n = 0}

theorem isClosed_negative : IsClosed Negative := by
  rw [show Negative = ⋂ n : ℤ, ⋂ (_hn : 0 ≤ n), {a : Space | a n = 0} by
    ext a; simp [Negative]]
  exact isClosed_iInter fun n => isClosed_iInter fun _ =>
    isClosed_singleton.preimage (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 1 n).continuous

theorem negativeProjection_mem (a : Space) : negativeProjection a ∈ Negative := by
  intro n hn
  simp [not_lt.mpr hn]

theorem negativeProjection_eq_self (a : Space) (ha : a ∈ Negative) : negativeProjection a = a := by
  apply lp.ext
  funext n
  rw [negativeProjection_apply]
  by_cases hn : n < 0
  · simp [hn]
  · simp [hn, ha n (not_lt.mp hn)]

def negativeBall (ρ : ℝ) : Set Space := Negative ∩ closedBall 0 ρ

theorem isComplete_negativeBall (ρ : ℝ) : IsComplete (negativeBall ρ) :=
  (isClosed_negative.inter isClosed_closedBall).isComplete

theorem zero_mem_negativeBall (ρ : ℝ) (hρ : 0 ≤ ρ) : (0 : Space) ∈ negativeBall ρ := by
  refine ⟨?_, ?_⟩
  · intro n _; rfl
  · simpa using hρ

def mode (n : ℤ) (z : ℂ) : ℂ := Complex.exp (Kneser.fourierFrequency n * z)

theorem norm_mode_le_weight (H : ℝ) (n : ℤ) (z : ℂ) (hz : |z.im| ≤ H) :
    ‖mode n z‖ ≤ weight H n := by
  rw [mode, Complex.norm_exp, weight]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hz (abs_nonneg (n : ℝ))
  have hab := neg_le_abs ((n : ℝ) * z.im)
  rw [abs_mul] at hab
  simp only [Kneser.fourierFrequency, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.intCast_re, Complex.intCast_im] at ⊢
  norm_num
  nlinarith [mul_le_mul_of_nonneg_left (hab.trans hmul) (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]

def evaluate (H : ℝ) (a : Space) (z : ℂ) : ℂ := ∑' n : ℤ, coefficient H a n * mode n z

theorem summable_evaluate (H : ℝ) (a : Space) (z : ℂ) (hz : |z.im| ≤ H) :
    Summable (fun n : ℤ => coefficient H a n * mode n z) := by
  apply Summable.of_norm_bounded (summable_norm a)
  intro n
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (norm_mode_le_weight H n z hz) (norm_nonneg _)).trans_eq
    (norm_coefficient_mul_weight H a n)

theorem norm_evaluate_le (H : ℝ) (a : Space) (z : ℂ) (hz : |z.im| ≤ H) :
    ‖evaluate H a z‖ ≤ ‖a‖ := by
  rw [evaluate, norm_eq_tsum]
  have hb (n : ℤ) : ‖coefficient H a n * mode n z‖ ≤ ‖a n‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (norm_mode_le_weight H n z hz) (norm_nonneg _)).trans_eq
      (norm_coefficient_mul_weight H a n)
  have hs := (summable_norm a).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hb (summable_norm a))

def evaluateCLM (H : ℝ) (z : ℂ) (hz : |z.im| ≤ H) : Space →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun a => evaluate H a z
      map_add' := by
        intro a b
        simp only [evaluate, coefficient, lp.coeFn_add, Pi.add_apply, add_div, add_mul]
        exact (summable_evaluate H a z hz).tsum_add (summable_evaluate H b z hz)
      map_smul' := by
        intro c a
        simp only [evaluate, coefficient, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
          mul_div_assoc, mul_assoc]
        exact tsum_mul_left }
    1 (fun a => by simpa using norm_evaluate_le H a z hz)

@[simp] theorem evaluateCLM_apply (H : ℝ) (z : ℂ) (hz : |z.im| ≤ H) (a : Space) :
    evaluateCLM H z hz a = evaluate H a z := rfl

@[simp] theorem evaluate_atom (H : ℝ) (n : ℤ) (z : ℂ) : evaluate H (atom H n) z = mode n z := by
  simp [evaluate, coefficient_atom, tsum_eq_single n]

theorem mode_mul (m n : ℤ) (z : ℂ) : mode (m + n) z = mode m z * mode n z := by
  rw [mode, mode, mode, ← Complex.exp_add]
  congr 1
  simp only [Kneser.fourierFrequency, Int.cast_add]
  ring

theorem mode_periodic (n : ℤ) (z : ℂ) : mode n (z + 1) = mode n z := by
  have he : Complex.exp (Kneser.fourierFrequency n) = 1 := by
    have hf : Kneser.fourierFrequency n = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      dsimp [Kneser.fourierFrequency]; ring
    rw [hf]
    exact Complex.exp_int_mul_two_pi_mul_I n
  simp only [mode, mul_add, mul_one, Complex.exp_add, he, mul_one]

theorem evaluate_periodic (H : ℝ) (a : Space) (z : ℂ) : evaluate H a (z + 1) = evaluate H a z := by
  simp only [evaluate, mode_periodic]

end Kneser.WeightedFourier

end
