import Kneser.FourierSewingDecayCoefficient
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! Actual positive Fourier evaluation and quantitative half-plane bounds. -/

set_option autoImplicit false
noncomputable section

namespace Kneser.WeightedFourier

open Set Filter Metric
open scoped Topology Classical
open Kneser.FourierSewing

theorem norm_mode_nonnegative (n : ℤ) (hn : 0 ≤ n) (z : ℂ) :
    ‖mode n z‖ = Real.exp (-2 * Real.pi * (n : ℝ) * z.im) := by
  rw [mode, Complex.norm_exp]
  congr 1
  simp only [Kneser.fourierFrequency, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.intCast_re, Complex.intCast_im]
  norm_num

theorem positive_mode_ratio (H v : ℝ) (n : ℤ) (hn : 0 ≤ n) :
    Real.exp (-2 * Real.pi * (n : ℝ) * v) / weight H n =
      Real.exp (-2 * Real.pi * (H + v)) ^ n.natAbs := by
  have hnr : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcast : (n.natAbs : ℝ) = (n : ℝ) := by
    have hh := congrArg (fun m : ℤ => (m : ℝ)) (Int.natCast_natAbs n)
    simpa only [Int.cast_natCast, abs_of_nonneg hn] using hh
  rw [weight, abs_of_nonneg hnr, ← Real.exp_sub, ← Real.exp_nat_mul, hcast]
  congr 1
  ring

theorem norm_positive_term_le (H : ℝ) (P : Space)
    (hP : ∀ n : ℤ, n < 0 → P n = 0) (z : ℂ) (hz : 0 ≤ H + z.im) (n : ℤ) :
    ‖coefficient H P n * mode n z‖ ≤ ‖P n‖ := by
  by_cases hn : 0 ≤ n
  · rw [norm_mul, norm_mode_nonnegative n hn z, coefficient, norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (weight_pos H n)]
    have hratio : Real.exp (-2 * Real.pi * (n : ℝ) * z.im) / weight H n ≤ 1 := by
      rw [positive_mode_ratio H z.im n hn]
      apply pow_le_one₀ (Real.exp_pos _).le
      rw [Real.exp_le_one_iff]
      have hnreal : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith [Real.pi_pos]
    calc
      _ = ‖P n‖ * (Real.exp (-2 * Real.pi * (n : ℝ) * z.im) / weight H n) := by ring
      _ ≤ ‖P n‖ * 1 := mul_le_mul_of_nonneg_left hratio (norm_nonneg _)
      _ = _ := mul_one _
  · simp [coefficient, hP n (not_le.mp hn)]

theorem summable_evaluate_positive (H : ℝ) (P : Space)
    (hP : ∀ n : ℤ, n < 0 → P n = 0) (z : ℂ) (hz : 0 ≤ H + z.im) :
    Summable (fun n : ℤ => coefficient H P n * mode n z) :=
  Summable.of_norm_bounded (summable_norm P) (norm_positive_term_le H P hP z hz)

theorem norm_evaluate_positive_le (H : ℝ) (P : Space)
    (hP : ∀ n : ℤ, n < 0 → P n = 0) (z : ℂ) (hz : 0 ≤ H + z.im) :
    ‖evaluate H P z‖ ≤ ‖P‖ := by
  have hb := norm_positive_term_le H P hP z hz
  have hs := (summable_norm P).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  exact (norm_tsum_le_tsum_norm hs).trans
    ((hs.tsum_le_tsum hb (summable_norm P)).trans_eq (norm_eq_tsum P).symm)

theorem hasDerivAt_mode (n : ℤ) (z : ℂ) :
    HasDerivAt (mode n) (mode n z * Kneser.fourierFrequency n) z := by
  unfold mode
  simpa only [mode, mul_one, id_eq] using
    ((hasDerivAt_id z).const_mul (Kneser.fourierFrequency n)).cexp

/-- Positive Fourier coefficients define a genuine holomorphic function
on their entire upper half-plane of convergence. -/
theorem differentiableOn_evaluate_positive (H : ℝ) (P : Space)
    (hP : ∀ n : ℤ, n < 0 → P n = 0) :
    DifferentiableOn ℂ (evaluate H P) {z : ℂ | 0 < H + z.im} := by
  have hsopen : IsOpen {z : ℂ | 0 < H + z.im} :=
    isOpen_lt continuous_const (continuous_const.add Complex.continuous_im)
  have hterms (n : ℤ) : DifferentiableOn ℂ
      (fun z => coefficient H P n * mode n z) {z : ℂ | 0 < H + z.im} := by
    intro z hz
    exact ((hasDerivAt_mode n z).const_mul (coefficient H P n)).differentiableAt.differentiableWithinAt
  exact Complex.differentiableOn_tsum_of_summable_norm (summable_norm P) hterms hsopen
    (fun n z hz => norm_positive_term_le H P hP z hz.le n)

theorem norm_evaluate_positive_sub_constant_le (H v : ℝ) (hgap : 0 < H + v)
    (P : Space) (hP : ∀ n : ℤ, n < 0 → P n = 0) (z : ℂ) (hz : v ≤ z.im) :
    ‖evaluate H P z - coefficient H P 0‖ ≤
      ‖P‖ * Real.exp (-2 * Real.pi * (H + v)) /
        (1 - Real.exp (-2 * Real.pi * (H + v))) := by
  let q := Real.exp (-2 * Real.pi * (H + v))
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hqlt : q < 1 := by
    change Real.exp (-2 * Real.pi * (H + v)) < 1
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have hs := summable_evaluate_positive H P hP z (by linarith)
  have he : evaluate H P z - coefficient H P 0 =
      ∑' n : ℤ, if n = 0 then 0 else coefficient H P n * mode n z := by
    rw [evaluate, hs.tsum_eq_add_tsum_ite 0]
    simp [mode, Kneser.fourierFrequency]
  have hb (n : ℤ) : ‖if n = 0 then 0 else coefficient H P n * mode n z‖ ≤
      ‖P‖ * upperGeometric q n := by
    by_cases hn : 0 < n
    · have hnzero : n ≠ 0 := ne_of_gt hn
      simp only [ite_eq_right hnzero, upperGeometric, ite_eq_left hn, norm_mul]
      calc
        _ ≤ (‖P‖ / weight H n) * Real.exp (-2 * Real.pi * (n : ℝ) * v) :=
          mul_le_mul (norm_coefficient_le H P n)
            (by rw [norm_mode_nonnegative n hn.le z]; apply Real.exp_le_exp.mpr
                have hnr : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.le
                nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * (n : ℝ)) (sub_nonneg.mpr hz)])
            (norm_nonneg _) (by have hw := weight_pos H n; positivity)
        _ = ‖P‖ * q ^ n.toNat := by
          rw [div_mul_eq_mul_div, mul_div_assoc, positive_mode_ratio H v n hn.le]
          have ht : n.toNat = n.natAbs := by
            cases n with
            | ofNat k => rfl
            | negSucc k => omega
          rw [ht]
    · by_cases hnzero : n = 0
      · simp [hnzero, upperGeometric]
      · simp [hnzero, coefficient, hP n (by omega), upperGeometric, hn]
  have hu := (summable_upperGeometric q hq hqlt).mul_left ‖P‖
  have hnorm := hu.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  rw [he]
  exact (norm_tsum_le_tsum_norm hnorm).trans
    ((hnorm.tsum_le_tsum hb hu).trans_eq (by
      rw [tsum_mul_left, tsum_upperGeometric q hq hqlt]
      dsimp [q]
      ring))


theorem im_lower_on_closedBall (c z : ℂ) (r : ℝ) (hz : z ∈ closedBall c r) :
    c.im - r ≤ z.im := by
  have h := Complex.abs_im_le_norm (z - c)
  rw [mem_closedBall, dist_eq_norm] at hz
  simp only [Complex.sub_im] at h
  linarith [neg_le_abs (z.im - c.im)]

theorem norm_mode_sub_le_on_disc (n : ℤ) (hn : 0 ≤ n) (c : ℂ) (r : ℝ)
    (z w : ℂ) (hz : z ∈ closedBall c r) (hw : w ∈ closedBall c r) :
    ‖mode n z - mode n w‖ ≤
      (‖Kneser.fourierFrequency n‖ * Real.exp (-2 * Real.pi * (n : ℝ) * (c.im - r))) * ‖z - w‖ := by
  apply (convex_closedBall c r).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hasDerivAt_mode n x).hasDerivWithinAt) _ hw hz
  intro x hx
  rw [norm_mul, norm_mode_nonnegative n hn x, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hxl := im_lower_on_closedBall c x r hx
  have hnreal : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * (n : ℝ)) (sub_nonneg.mpr hxl)]

/-- The actual positive Fourier evaluation is Lipschitz on every closed
disc contained in its half-plane of convergence. -/
theorem norm_evaluate_positive_sub_le_on_disc (H : ℝ) (P : Space)
    (hP : ∀ n : ℤ, n < 0 → P n = 0) (c : ℂ) (r : ℝ) (hgap : 0 < H + c.im - r)
    (z w : ℂ) (hz : z ∈ closedBall c r) (hw : w ∈ closedBall c r) :
    ‖evaluate H P z - evaluate H P w‖ ≤
      (4 * Real.pi * ‖P‖ * Real.exp (-2 * Real.pi * (H + c.im - r)) /
        (1 - Real.exp (-2 * Real.pi * (H + c.im - r))) ^ 2) * ‖z - w‖ := by
  let q := Real.exp (-2 * Real.pi * (H + c.im - r))
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hqlt : q < 1 := by
    change Real.exp (-2 * Real.pi * (H + c.im - r)) < 1
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have hb (n : ℤ) : ‖coefficient H P n * mode n z - coefficient H P n * mode n w‖ ≤
      ((2 * Real.pi * ‖P‖) * firstGeometric q n) * ‖z - w‖ := by
    by_cases hn : 0 < n
    · rw [← mul_sub, norm_mul]
      calc
        _ ≤ (‖P‖ / weight H n) *
            ((‖Kneser.fourierFrequency n‖ * Real.exp (-2 * Real.pi * (n : ℝ) * (c.im - r))) * ‖z - w‖) :=
          mul_le_mul (norm_coefficient_le H P n)
            (norm_mode_sub_le_on_disc n hn.le c r z w hz hw) (norm_nonneg _)
            (by have hh := weight_pos H n; positivity)
        _ = _ := by
          rw [norm_fourierFrequency, firstGeometric, nonzeroGeometric,
            ite_eq_right (ne_of_gt hn), abs_of_nonneg (by exact_mod_cast hn.le : (0 : ℝ) ≤ (n : ℝ))]
          have hr := positive_mode_ratio H (c.im - r) n hn.le
          have he : H + (c.im - r) = H + c.im - r := by ring
          rw [he] at hr
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
  have hzs := summable_evaluate_positive H P hP z (by have hh := im_lower_on_closedBall c z r hz; linarith)
  have hws := summable_evaluate_positive H P hP w (by have hh := im_lower_on_closedBall c w r hw; linarith)
  rw [evaluate, evaluate, ← hzs.tsum_sub hws]
  exact (norm_tsum_le_tsum_norm hnorm).trans
    ((hnorm.tsum_le_tsum hb hsum).trans_eq (by
      rw [tsum_mul_right, tsum_mul_left, tsum_firstGeometric q hq hqlt]
      dsimp [q]
      ring))

end Kneser.WeightedFourier

end
