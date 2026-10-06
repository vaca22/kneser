import Kneser.LocalPeriodicStrip
import Kneser.StripFourierReconstruction
import Kneser.WeightedFourierDecay

/-!
The actual analytic gate germ gives exponential decay of all its integral
Fourier coefficients. The bound is derived by moving the integration height
inside the constructed strip; no Fourier decay hypothesis is needed.
-/

set_option autoImplicit false
noncomputable section
namespace Kneser.LocalStripFourierDecay

open Filter Set Metric Complex MeasureTheory Kneser.LocalPeriodicStrip
open Kneser.GateFourierDerivative Kneser.StripFourierReconstruction
open scoped Topology Interval

theorem exists_uniform_displacement_bound (T : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ T (ball (0 : ℂ) 4)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ strip, ‖lift T z - z‖ ≤ M := by
  have hc : ContinuousOn (fun w : ℂ => T w - w) (closedBall (0 : ℂ) 2) := by
    intro w hw
    have hh : w ∈ ball (0 : ℂ) 4 := by
      simp only [mem_closedBall, mem_ball, dist_zero_right] at *
      linarith
    exact ((ha w hh).continuousAt.sub continuousAt_id).continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : ℂ) 2).exists_bound_of_continuousOn hc
  refine ⟨max M₀ 0, le_max_right _ _, ?_⟩
  intro z hz
  have hr := reduced_mem_ball z hz
  have he : lift T z - z = T (reduced z) - reduced z := by
    dsimp [Kneser.LocalPeriodicStrip.lift, reduced]
    ring
  rw [he]
  exact (hM₀ _ (ball_subset_closedBall hr)).trans (le_max_left _ _)

theorem gate_coefficient_bound (n : ℤ) (T : ℂ → ℂ) (Y M : ℝ)
    (hM : ∀ x ∈ Icc (0 : ℝ) 1, ‖T (gatePoint Y x) - gatePoint Y x‖ ≤ M) :
    ‖gateFourierCoefficient n Y T‖ ≤ M * Real.exp (2 * Real.pi * (n : ℝ) * Y) := by
  unfold gateFourierCoefficient
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := M * Real.exp (2 * Real.pi * (n : ℝ) * Y))
    (f := fun x => (T (gatePoint Y x) - gatePoint Y x) * gateWeight n Y x) (by
      intro x hx
      rw [norm_mul, norm_gateWeight]
      apply mul_le_mul_of_nonneg_right (hM x ?_) (Real.exp_pos _).le
      exact Ioc_subset_Icc_self (by simpa using hx))
  simpa using hh

theorem exists_gate_mode_decay (T : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ T (ball (0 : ℂ) 4))
    (hp : ∀ z ∈ ball (0 : ℂ) 2, T (z + 1) = T z + 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℤ,
      ‖gateFourierCoefficient n 0 T‖ ≤ M * Real.exp (-Real.pi * |(n : ℝ)|) := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_displacement_bound T ha
  refine ⟨M, hM, ?_⟩
  intro n
  let Y : ℝ := if 0 ≤ (n : ℝ) then -1 / 2 else 1 / 2
  have hY : |Y| < 1 := by dsimp [Y]; split_ifs <;> norm_num
  have hh := gate_coefficient_bound n (lift T) Y M (by
    intro x _
    apply hbound
    change |(gatePoint Y x).im| < 1
    simpa [gatePoint] using hY)
  rw [gateFourier_height_eq_zero n T ha hp Y hY] at hh
  have he : 2 * Real.pi * (n : ℝ) * Y = -Real.pi * |(n : ℝ)| := by
    dsimp [Y]
    split_ifs with hn
    · rw [abs_of_nonneg hn]; ring
    · rw [abs_of_neg (lt_of_not_ge hn)]; ring
  rwa [he] at hh

theorem summable_integer_geometric (q : ℝ) (hq : 0 ≤ q) (hqlt : q < 1) :
    Summable (fun n : ℤ => q ^ n.natAbs) := by
  have hs := summable_geometric_of_lt_one hq hqlt
  have hp : Summable (fun n : ℕ => q ^ (Int.natAbs (n : ℤ))) := by simpa using hs
  have hn : Summable (fun n : ℕ => q ^ (Int.natAbs (-(n + 1 : ℤ)))) := by
    have he : (fun n : ℕ => q ^ (Int.natAbs (-(n + 1 : ℤ)))) = (fun n : ℕ => q ^ (n + 1)) := by
      funext n
      congr 1
    rw [he]
    exact hs.comp_injective (i := fun n : ℕ => n + 1)
      (by intro i j hij; exact Nat.add_right_cancel hij)
  exact hp.of_nat_of_neg_add_one hn

theorem summable_height_coefficients (T : ℂ → ℂ) (Y M : ℝ) (hM : 0 ≤ M)
    (hY : |Y| < 1 / 2)
    (hdecay : ∀ n : ℤ, ‖gateFourierCoefficient n 0 T‖ ≤
      M * Real.exp (-Real.pi * |(n : ℝ)|)) :
    Summable (fun n : ℤ => exp (Kneser.fourierFrequency n * (I * (Y : ℂ))) *
      gateFourierCoefficient n 0 T) := by
  let d : ℝ := 1 / 2 - |Y|
  let q : ℝ := Real.exp (-2 * Real.pi * d)
  have hd : 0 < d := by dsimp [d]; linarith
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hqlt : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  apply Summable.of_norm_bounded ((summable_integer_geometric q hq hqlt).mul_left M)
  intro n
  have he : ‖exp (Kneser.fourierFrequency n * (I * (Y : ℂ)))‖ =
      Real.exp (-2 * Real.pi * (n : ℝ) * Y) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Kneser.fourierFrequency]
  have hab : -(n : ℝ) * Y ≤ |(n : ℝ)| * |Y| := by
    exact (le_abs_self (-(n : ℝ) * Y)).trans_eq (by simp [abs_mul])
  have hcast : (n.natAbs : ℝ) = |(n : ℝ)| := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs n)
    simpa only [Int.cast_natCast, Int.cast_abs] using h
  rw [norm_mul, he]
  calc
    _ ≤ Real.exp (-2 * Real.pi * (n : ℝ) * Y) *
        (M * Real.exp (-Real.pi * |(n : ℝ)|)) :=
      mul_le_mul_of_nonneg_left (hdecay n) (Real.exp_pos _).le
    _ = M * Real.exp (-2 * Real.pi * (n : ℝ) * Y - Real.pi * |(n : ℝ)|) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring_nf
    _ ≤ M * Real.exp (-2 * Real.pi * d * |(n : ℝ)|) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM
      dsimp [d]
      nlinarith [Real.pi_pos]
    _ = M * q ^ n.natAbs := by
      dsimp [q]
      rw [← Real.exp_nat_mul, hcast]
      congr 2
      ring

theorem exists_actual_germ_fourier_representation (T : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ T (ball (0 : ℂ) 4))
    (hp : ∀ z ∈ ball (0 : ℂ) 2, T (z + 1) = T z + 1) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ n : ℤ, ‖gateFourierCoefficient n 0 T‖ ≤ M * Real.exp (-Real.pi * |(n : ℝ)|)) ∧
      ∀ z : ℂ, |z.im| < 1 / 2 →
        HasSum (fun n : ℤ => gateFourierCoefficient n 0 T *
          exp (Kneser.fourierFrequency n * z)) (lift T z - z) := by
  obtain ⟨M, hM, hdecay⟩ := exists_gate_mode_decay T ha hp
  refine ⟨M, hM, hdecay, ?_⟩
  intro z hz
  have hcz : Continuous (displacement (lift T) z.im) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hg : gatePoint z.im x ∈ strip := by
      change |(gatePoint z.im x).im| < 1
      simp only [gatePoint, add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re,
        zero_mul, one_mul, zero_add]
      linarith
    exact (((lift_analytic T ha hp) _ hg).continuousAt.comp
      (Complex.continuous_ofReal.continuousAt.add
        continuousAt_const)).sub (Complex.continuous_ofReal.continuousAt.add continuousAt_const)
  have hhe : ∀ n : ℤ, gateFourierCoefficient n z.im (lift T) = gateFourierCoefficient n 0 T :=
    fun n => gateFourier_height_eq_zero n T ha hp z.im (by linarith)
  have hs : Summable (fun n : ℤ => exp (Kneser.fourierFrequency n * (I * (z.im : ℂ))) *
      gateFourierCoefficient n z.im (lift T)) := by
    simpa only [hhe] using summable_height_coefficients T z.im M hM hz hdecay
  have hh := hasSum_gate_fourier (lift T) z.im z.re (lift_translation T) hcz hs
  have he : gatePoint z.im z.re = z := by apply Complex.ext <;> simp [gatePoint]
  simpa only [hhe, he, displacement] using hh

end Kneser.LocalStripFourierDecay
end
