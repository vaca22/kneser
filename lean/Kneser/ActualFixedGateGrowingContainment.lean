import Kneser.ActualBandTimeConfluence
import Kneser.ActualLocalGrowingTransitionBridge
import Kneser.UpperCanonicalInjectivity

/-! Compact uniform confluence embeds the genuine fixed reciprocal gate
into the same global growing lens. The only temporary height condition
is an explicit bound on the actual multiplier height. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace Kneser.ActualFixedGateGrowingContainment

open Set Metric Filter Complex
open Kneser.ActualBandTimeConfluence Kneser.GrowingBandGeometry
open Kneser.ActualQuantitativeGateTransition Kneser.ExponentialUnfolding
open Kneser.ParabolicExponentialOrbit Kneser.ReflectedOrbitChainCoefficient
open scoped Topology

theorem chartPoint_upper (Yg : ℝ) (hYg : 64 ≤ Yg) (z : ℂ)
    (hz : z ∈ closedBall (0 : ℂ) 12) : 0 < (chartPoint Yg z).im := by
  have hn : ‖z‖ ≤ 12 := by simpa only [mem_closedBall,dist_zero_right] using hz
  apply Kneser.UpperCanonicalInjectivity.inverseCoordinate_upper
  have hi := (abs_le.mp ((Complex.abs_im_le_norm z).trans hn)).1
  simp only [chartCenter,Complex.add_im,Complex.mul_im,Complex.I_re,
    Complex.ofReal_im,zero_mul,Complex.I_im,Complex.ofReal_re,one_mul,zero_add]
  linarith

theorem fixed_gate_time_uniform (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ)
    (F Γ : ℂ × ℂ → ℂ) (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ)
    (N : ℕ) (Yg : ℝ) (hYg : 64 * ((N : ℝ) + 1) + 64 ≤ Yg) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ a b : ℝ, a < 0 → 0 < b →
      unfolding (s : ℂ) (a : ℂ) = (a : ℂ) → unfolding (s : ℂ) (b : ℂ) = (b : ℂ) →
      ∀ z ∈ closedBall (0 : ℂ) 12,
        ‖bandTime a b (-Real.log (Kneser.PositiveKoenigsOrbit.multiplier s a)) (chartPoint Yg z) -
          (chartCenter Yg + z)‖ < 1 ∧
        bandChart a b (-Real.log (Kneser.PositiveKoenigsOrbit.multiplier s a))
          (bandTime a b (-Real.log (Kneser.PositiveKoenigsOrbit.multiplier s a)) (chartPoint Yg z)) =
          chartPoint Yg z := by
  let S : Set ℂ := chartPoint Yg '' closedBall (0 : ℂ) 12
  have hS : IsCompact S := (isCompact_closedBall (0 : ℂ) 12).image_of_continuousOn
    (fun z hz => (chartPoint_analytic N Yg hYg z
      (closedBall_subset_closedBall (by norm_num) hz)).continuousAt.continuousWithinAt)
  have h64 : 64 ≤ Yg := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hu : ∀ u ∈ S, 0 < u.im := by
    rintro _ ⟨z,hz,rfl⟩
    exact chartPoint_upper Yg h64 z hz
  filter_upwards [actual_bandTime_uniform_upper_compact U H e₁ e₂ A B K F Γ hdata
    S hS hu 1 (by norm_num)] with s hs
  intro a b ha hb hfa hfb z hz
  have hh := hs a b ha hb hfa hfb _ (mem_image_of_mem (chartPoint Yg) hz)
  simpa only [chartPoint,Kneser.ParabolicOverlapGate.inverseCoordinate_involutive] using hh

theorem fixed_gate_points_in_growing_lens
    (a b θ Yg D : ℝ) (hdeep : D + 14 ≤ Yg) (hheight : Yg + 13 + D < height θ)
    (htime : ∀ z ∈ closedBall (0 : ℂ) 12,
      ‖bandTime a b θ (chartPoint Yg z) - (chartCenter Yg + z)‖ < 1 ∧
      bandChart a b θ (bandTime a b θ (chartPoint Yg z)) = chartPoint Yg z)
    (hYg : 64 ≤ Yg) :
    ∀ z ∈ closedBall (0 : ℂ) 12, ∃ Z : ℂ,
      Z ∈ strip θ D ∧ 0 < (bandChart a b θ Z).im ∧ bandChart a b θ Z = chartPoint Yg z := by
  intro z hz
  refine ⟨bandTime a b θ (chartPoint Yg z),?_,?_,(htime z hz).2⟩
  · have hn : ‖z‖ ≤ 12 := by simpa only [mem_closedBall,dist_zero_right] using hz
    have hi := abs_le.mp ((Complex.abs_im_le_norm z).trans hn)
    have hb := (Complex.abs_im_le_norm
      (bandTime a b θ (chartPoint Yg z) - (chartCenter Yg + z))).trans_lt (htime z hz).1
    have hh := abs_lt.mp hb
    simp only [Complex.sub_im,chartCenter,Complex.add_im,Complex.mul_im,Complex.I_re,
      Complex.ofReal_im,zero_mul,Complex.I_im,Complex.ofReal_re,one_mul,zero_add] at hh
    exact ⟨by linarith [hi.1,hh.1],by linarith [hi.2,hh.2]⟩
  · rw [(htime z hz).2]
    exact chartPoint_upper Yg hYg z hz

end Kneser.ActualFixedGateGrowingContainment
end
