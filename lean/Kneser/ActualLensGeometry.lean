import Kneser.ActualLensModel
import Kneser.GrowingBandKernel

/-! True chart inversion and real-time drift for the exponential family. -/

noncomputable section

namespace Kneser.ActualLensGeometry

open Kneser.GrowingBandGeometry Kneser.ActualLensModel
open Kneser.RealExponentialPetal Kneser.ApolloniusGeometry
open Kneser.ExponentialUnfolding Kneser.ExponentialDividedDifference

theorem rootChart_crossRatio (a b : ℝ) (u : ℂ) (hab : a ≠ b) (hub : u ≠ (b : ℂ)) :
    rootChart a b (crossRatio a b u) = u := by
  have hden : u - (b : ℂ) ≠ 0 := sub_ne_zero.mpr hub
  have hgap : (a : ℂ) - (b : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hab)
  unfold rootChart crossRatio
  field_simp
  field_simp [hgap]
  ring

theorem bandChart_bandTime (a b θ : ℝ) (u : ℂ) (hab : a ≠ b) (hθ : θ ≠ 0)
    (hua : u ≠ (a : ℂ)) (hub : u ≠ (b : ℂ)) :
    bandChart a b θ (bandTime a b θ u) = u := by
  have hθc : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ
  have hq : -crossRatio a b u ≠ 0 := neg_ne_zero.mpr
    (div_ne_zero (sub_ne_zero.mpr hua) (sub_ne_zero.mpr hub))
  have he : Complex.exp (-(θ : ℂ) * bandTime a b θ u) = crossRatio a b u := by
    unfold bandTime
    have hc : -(θ : ℂ) * (-(Complex.log (-crossRatio a b u) - (Real.pi : ℂ) * Complex.I) / (θ : ℂ)) =
        Complex.log (-crossRatio a b u) - (Real.pi : ℂ) * Complex.I := by field_simp
    rw [hc, Complex.exp_sub, Complex.exp_log hq, Complex.exp_pi_mul_I]
    simp
  unfold bandChart
  rw [he]
  exact rootChart_crossRatio a b u hab hub

theorem bandTime_re (a b θ : ℝ) (u : ℂ) :
    (bandTime a b θ u).re = -Real.log ‖crossRatio a b u‖ / θ := by
  simp [bandTime, Complex.div_ofReal_re, Complex.log_re]

theorem actual_bandTime_re_drift (Q : QuotientControl) (s a b : ℝ) (u : ℂ)
    (hs : 0 < s) (hs1 : s < 1 / 2) (ha : -1 < a) (hab : a < b) (hb : 0 < b)
    (hfa : unfolding s a = (a : ℂ)) (hfb : unfolding s b = (b : ℂ))
    (hua : u ≠ (a : ℂ)) (hub : u ≠ (b : ℂ))
    (hκr : (1 - s) * (b - a) < Q.radius)
    (hma : (1 - (s : ℂ)) * (u - (a : ℂ)) ∈ Metric.ball 0 Q.radius)
    (hmb : (1 - (s : ℂ)) * (u - (b : ℂ)) ∈ Metric.ball 0 Q.radius) :
    unfolding s u ≠ (a : ℂ) ∧ unfolding s u ≠ (b : ℂ) ∧
      (bandTime a b (timeScale Q ((1 - s) * (b - a))) u).re + 3 / 4 ≤
        (bandTime a b (timeScale Q ((1 - s) * (b - a))) (unfolding s u)).re := by
  obtain ⟨hnewb, hcross⟩ := actual_crossRatio_contraction Q s a b u hs hs1 hab hb hfa hfb hub hκr hma hmb
  obtain ⟨hθ, _hratio⟩ := timeScale_pos_and_gap_bound Q s a b hs hs1 hab hκr
  have hnewa : unfolding s u ≠ (a : ℂ) := by
    apply sub_ne_zero.mp
    rw [unfolding_fixedPoint_factor Q.E Q.factor s a u hfa]
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
          exact_mod_cast (by linarith : 1 - s ≠ 0)
        · rw [← Complex.ofReal_one, ← Complex.ofReal_add]
          exact_mod_cast (by linarith : 1 + a ≠ 0)
      · exact sub_ne_zero.mpr hua
    · exact Q.ne_zero _ hma
  have hqn : 0 < ‖crossRatio a b u‖ := norm_pos_iff.mpr
    (div_ne_zero (sub_ne_zero.mpr hua) (sub_ne_zero.mpr hub))
  have hqfn : 0 < ‖crossRatio a b (unfolding s u)‖ := norm_pos_iff.mpr
    (div_ne_zero (sub_ne_zero.mpr hnewa) (sub_ne_zero.mpr hnewb))
  have hl := Real.log_le_log hqfn hcross
  rw [Real.log_mul (ne_of_gt hqn) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at hl
  refine ⟨hnewa, hnewb, ?_⟩
  rw [bandTime_re, bandTime_re]
  apply (le_div_iff₀ hθ).mpr
  rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hθ)]
  linarith

end Kneser.ActualLensGeometry

end
