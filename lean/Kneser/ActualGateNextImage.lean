import Kneser.ActualGateAbel
import Kneser.FullCanonicalImageGate

/-!
The genuine exponential sends the small inverse-image chart back into the
same large zeta chart.  Uniform positive-parameter containment follows from
joint analyticity on the actual compact chart, not an image hypothesis.
-/

noncomputable section

namespace Kneser.ActualGateNextImage

open Filter Set Metric Kneser.ParabolicExponentialOrbit Kneser.ExponentialUnfolding
open Kneser.ParabolicCoordinateJacobian Kneser.ActualBilateralGate
open scoped Topology

def chartCenter (Y : ℝ) : ℂ := Complex.I * (Y : ℂ)

def chartPoint (Y : ℝ) (z : ℂ) : ℂ := inverseCoordinate (chartCenter Y + z)

def translatedStep (Y : ℝ) (s z : ℂ) : ℂ :=
  inverseCoordinate (unfolding s (chartPoint Y z)) - chartCenter Y

theorem inverseCoordinate_chartPoint (Y : ℝ) (z : ℂ) :
    inverseCoordinate (chartPoint Y z) = chartCenter Y + z :=
  inverseCoordinate_involutive _

theorem chartPoint_ne_zero {Y : ℝ} {z : ℂ} (hz : ‖z‖ < Y) : chartPoint Y z ≠ 0 := by
  have hY : 0 < Y := lt_of_le_of_lt (norm_nonneg _) hz
  have hc : ‖chartCenter Y‖ = Y := by
    simp [chartCenter, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY]
  have hne : chartCenter Y + z ≠ 0 := by
    intro he
    have h := norm_sub_le (chartCenter Y + z) z
    rw [add_sub_cancel_right, he, norm_zero, zero_add, hc] at h
    linarith
  exact div_ne_zero (by norm_num) hne

theorem chartPoint_gate (N : ℕ) (H Y : ℝ)
    (hH : 64 * ((N : ℝ) + 1) ≤ H) (hY : H + 64 ≤ Y)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 8) : chartPoint Y z ∈ gate 64 N := by
  have hH0 : 0 ≤ H := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hn : ‖z‖ ≤ 8 := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hzc : chartCenter Y + z ∈ closedBall (chartCenter Y) 8 := by
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left] using hn
  have hi := FiniteZetaGateProjection.height_on_closedBall Y 8 H (by linarith) hH0
    (chartCenter Y + z) hzc
  refine ⟨?_, ?_⟩
  · rw [inverseCoordinate_chartPoint]
    have hr := (Complex.abs_re_le_norm z).trans hn
    simpa only [Complex.add_re, chartCenter, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_self, zero_add] using
      (hr.trans (by norm_num : (8 : ℝ) ≤ 64))
  · rw [inverseCoordinate_chartPoint]
    exact hH.trans hi

theorem translatedStep_chart_identity (Y : ℝ) (s z : ℂ) :
    unfolding s (chartPoint Y z) = chartPoint Y (translatedStep Y s z) := by
  dsimp only [chartPoint, translatedStep]
  have he : chartCenter Y +
      (inverseCoordinate (unfolding s (inverseCoordinate (chartCenter Y + z))) - chartCenter Y) =
      inverseCoordinate (unfolding s (inverseCoordinate (chartCenter Y + z))) := by ring
  rw [he, inverseCoordinate_involutive]

theorem translatedStep_zero_error (N : ℕ) (H Y : ℝ)
    (hH : 64 * ((N : ℝ) + 1) ≤ H) (hY : H + 64 ≤ Y)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 8) :
    ‖translatedStep Y 0 z - z - 1‖ ≤ 1 / 4 := by
  have hg := chartPoint_gate N H Y hH hY z hz
  have hn := ActualGateAbel.gate_norm_small _ N hg
  have hne : chartPoint Y z ≠ 0 := by
    apply chartPoint_ne_zero
    have hzn : ‖z‖ ≤ 8 := by simpa only [mem_closedBall, dist_zero_right] using hz
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have he := Kneser.ParabolicExponentialOrbit.inverse_step_error_bound
    (chartPoint Y z) (by linarith) hne
  have heq : translatedStep Y 0 z - z - 1 =
      inverseCoordinate (parabolicMap (chartPoint Y z)) - inverseCoordinate (chartPoint Y z) - 1 := by
    rw [inverseCoordinate_chartPoint]
    dsimp [translatedStep, parabolicMap]
    simp only [unfolding_zero]
    ring
  rw [heq]
  exact he.trans (by linarith)

theorem translatedStep_zero_mem_ball (N : ℕ) (H Y : ℝ)
    (hH : 64 * ((N : ℝ) + 1) ≤ H) (hY : H + 64 ≤ Y)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 8) : translatedStep Y 0 z ∈ ball (0 : ℂ) 10 := by
  have hb := translatedStep_zero_error N H Y hH hY z hz
  have hn : ‖z‖ ≤ 8 := by simpa only [mem_closedBall, dist_zero_right] using hz
  have ht := norm_add_le (translatedStep Y 0 z - z - 1) (z + 1)
  have he : translatedStep Y 0 z - z - 1 + (z + 1) = translatedStep Y 0 z := by ring
  rw [he] at ht
  have hu := norm_add_le z (1 : ℂ)
  rw [norm_one] at hu
  rw [mem_ball, dist_zero_right]
  linarith

theorem analyticAt_translatedStep_zero (N : ℕ) (H Y : ℝ)
    (hH : 64 * ((N : ℝ) + 1) ≤ H) (hY : H + 64 ≤ Y)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 8) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => translatedStep Y p.1 p.2) (0, z) := by
  have hg := chartPoint_gate N H Y hH hY z hz
  have hn := ActualGateAbel.gate_norm_small _ N hg
  have hpointne : chartPoint Y z ≠ 0 := by
    apply chartPoint_ne_zero
    have hzn : ‖z‖ ≤ 8 := by simpa only [mem_closedBall, dist_zero_right] using hz
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hwne : chartCenter Y + z ≠ 0 := by
    intro he
    simp [chartPoint, he, inverseCoordinate] at hpointne
  have hfne : unfolding 0 (chartPoint Y z) ≠ 0 := by
    simpa only [unfolding_zero, parabolicMap] using
      map_ne_zero (chartPoint Y z) (by linarith) hpointne
  have hpoint : AnalyticAt ℂ (fun p : ℂ × ℂ => chartPoint Y p.2) (0, z) :=
    analyticAt_const.div (analyticAt_const.add analyticAt_snd) hwne
  have hmap : AnalyticAt ℂ (fun p : ℂ × ℂ => unfolding p.1 (chartPoint Y p.2)) (0, z) :=
    ((analyticAt_fst.neg.add ((analyticAt_const.sub analyticAt_fst).mul hpoint)).cexp).sub analyticAt_const
  exact (analyticAt_const.div hmap hfne).sub analyticAt_const

theorem translatedStep_zero_containment (N : ℕ) (H Y : ℝ)
    (hH : 64 * ((N : ℝ) + 1) ≤ H) (hY : H + 64 ≤ Y)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 8) :
    translatedStep Y 0 z ∈ ball (0 : ℂ) 10 ∧
      unfolding 0 (chartPoint Y z) = chartPoint Y (translatedStep Y 0 z) ∧
      unfolding 0 (chartPoint Y z) ≠ 0 := by
  have hm := translatedStep_zero_mem_ball N H Y hH hY z hz
  refine ⟨hm, translatedStep_chart_identity Y 0 z, ?_⟩
  rw [translatedStep_chart_identity]
  apply chartPoint_ne_zero
  have hn : ‖translatedStep Y 0 z‖ < 10 := by simpa only [mem_ball, dist_zero_right] using hm
  linarith [Nat.cast_nonneg (α := ℝ) N]

/-- Uniform containment is derived from true joint analytic germs over
the compact small chart. The actual next image lies in the radius-12
chart and is exactly represented by its reciprocal coordinate. -/
theorem eventually_translatedStep_mem_ball (N : ℕ) (H Y : ℝ)
    (hH : 64 * ((N : ℝ) + 1) ≤ H) (hY : H + 64 ≤ Y) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ closedBall (0 : ℂ) 8,
      translatedStep Y s z ∈ ball (0 : ℂ) 12 ∧
      unfolding s (chartPoint Y z) = chartPoint Y (translatedStep Y s z) ∧
      unfolding s (chartPoint Y z) ≠ 0 := by
  have hnear : ∀ᶠ s : ℂ in 𝓝 0, ∀ z ∈ closedBall (0 : ℂ) 8,
      translatedStep Y s z ∈ ball (0 : ℂ) 12 := by
    apply (isCompact_closedBall (0 : ℂ) 8).eventually_forall_of_forall_eventually
    intro z hz
    have hzero := translatedStep_zero_mem_ball N H Y hH hY z hz
    have hmem : translatedStep Y 0 z ∈ ball (0 : ℂ) 12 :=
      ball_subset_ball (by norm_num : (10 : ℝ) ≤ 12) hzero
    exact (analyticAt_translatedStep_zero N H Y hH hY z hz).continuousAt.eventually
      (isOpen_ball.mem_nhds hmem)
  have hreal : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ closedBall (0 : ℂ) 8,
      translatedStep Y s z ∈ ball (0 : ℂ) 12 :=
    (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually hnear
  filter_upwards [hreal] with s hs z hz
  refine ⟨hs z hz, translatedStep_chart_identity Y s z, ?_⟩
  rw [translatedStep_chart_identity]
  apply chartPoint_ne_zero
  have hn : ‖translatedStep Y s z‖ < 12 := by simpa only [mem_ball, dist_zero_right] using hs z hz
  linarith [Nat.cast_nonneg (α := ℝ) N]

/-- The physical chart belongs to the genuine overlap gate for every
source radius at most 64. -/
theorem chartPoint_gate_of_radius (N : ℕ) (H Y ρ : ℝ)
    (hH : 64 * ((N : ℝ) + 1) ≤ H) (hY : H + 64 ≤ Y) (hρ : ρ ≤ 64)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) ρ) : chartPoint Y z ∈ gate 64 N := by
  have hH0 : 0 ≤ H := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hn : ‖z‖ ≤ ρ := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hzc : chartCenter Y + z ∈ closedBall (chartCenter Y) ρ := by
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left] using hn
  have hi := FiniteZetaGateProjection.height_on_closedBall Y ρ H (by linarith) hH0
    (chartCenter Y + z) hzc
  refine ⟨?_, ?_⟩
  · rw [inverseCoordinate_chartPoint]
    have hr := (Complex.abs_re_le_norm z).trans (hn.trans hρ)
    simpa only [Complex.add_re, chartCenter, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_self, zero_add] using hr
  · rw [inverseCoordinate_chartPoint]
    exact hH.trans hi

theorem translatedStep_zero_error_of_radius (N : ℕ) (H Y ρ : ℝ)
    (hH : 64 * ((N : ℝ) + 1) ≤ H) (hY : H + 64 ≤ Y) (hρ : ρ ≤ 64)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) ρ) :
    ‖translatedStep Y 0 z - z - 1‖ ≤ 1 / 4 := by
  have hg := chartPoint_gate_of_radius N H Y ρ hH hY hρ z hz
  have hn := ActualGateAbel.gate_norm_small _ N hg
  have hne : chartPoint Y z ≠ 0 := by
    apply chartPoint_ne_zero
    have hzn : ‖z‖ ≤ ρ := by simpa only [mem_closedBall, dist_zero_right] using hz
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have he := inverse_step_error_bound (chartPoint Y z) (by linarith) hne
  have heq : translatedStep Y 0 z - z - 1 =
      inverseCoordinate (parabolicMap (chartPoint Y z)) - inverseCoordinate (chartPoint Y z) - 1 := by
    rw [inverseCoordinate_chartPoint]
    dsimp [translatedStep, parabolicMap]
    simp only [unfolding_zero]
    ring
  rw [heq]
  exact he.trans (by linarith)

theorem analyticAt_translatedStep_zero_of_radius (N : ℕ) (H Y ρ : ℝ)
    (hH : 64 * ((N : ℝ) + 1) ≤ H) (hY : H + 64 ≤ Y) (hρ : ρ ≤ 64)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) ρ) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => translatedStep Y p.1 p.2) (0, z) := by
  have hg := chartPoint_gate_of_radius N H Y ρ hH hY hρ z hz
  have hn := ActualGateAbel.gate_norm_small _ N hg
  have hpointne : chartPoint Y z ≠ 0 := by
    apply chartPoint_ne_zero
    have hzn : ‖z‖ ≤ ρ := by simpa only [mem_closedBall, dist_zero_right] using hz
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hwne : chartCenter Y + z ≠ 0 := by
    intro he
    simp [chartPoint, he, inverseCoordinate] at hpointne
  have hfne : unfolding 0 (chartPoint Y z) ≠ 0 := by
    simpa only [unfolding_zero, parabolicMap] using
      map_ne_zero (chartPoint Y z) (by linarith) hpointne
  have hpoint : AnalyticAt ℂ (fun p : ℂ × ℂ => chartPoint Y p.2) (0, z) :=
    analyticAt_const.div (analyticAt_const.add analyticAt_snd) hwne
  have hmap : AnalyticAt ℂ (fun p : ℂ × ℂ => unfolding p.1 (chartPoint Y p.2)) (0, z) :=
    ((analyticAt_fst.neg.add ((analyticAt_const.sub analyticAt_fst).mul hpoint)).cexp).sub analyticAt_const
  exact (analyticAt_const.div hmap hfne).sub analyticAt_const

theorem translatedStep_zero_mem_ball_eighteen (N : ℕ) (H Y : ℝ)
    (hH : 64 * ((N : ℝ) + 1) ≤ H) (hY : H + 64 ≤ Y)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 16) : translatedStep Y 0 z ∈ ball (0 : ℂ) 18 := by
  have hb := translatedStep_zero_error_of_radius N H Y 16 hH hY (by norm_num) z hz
  have hn : ‖z‖ ≤ 16 := by simpa only [mem_closedBall, dist_zero_right] using hz
  have ht := norm_add_le (translatedStep Y 0 z - z - 1) (z + 1)
  have he : translatedStep Y 0 z - z - 1 + (z + 1) = translatedStep Y 0 z := by ring
  rw [he] at ht
  have hu := norm_add_le z (1 : ℂ)
  rw [norm_one] at hu
  rw [mem_ball, dist_zero_right]
  linarith

/-- The full radius-16 inverse image used by the actual transition has
its next image inside radius 24, uniformly for small positive parameters. -/
theorem eventually_translatedStep_mem_ball_twentyFour (N : ℕ) (H Y : ℝ)
    (hH : 64 * ((N : ℝ) + 1) ≤ H) (hY : H + 64 ≤ Y) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ closedBall (0 : ℂ) 16,
      translatedStep Y s z ∈ ball (0 : ℂ) 24 ∧
      unfolding s (chartPoint Y z) = chartPoint Y (translatedStep Y s z) ∧
      unfolding s (chartPoint Y z) ≠ 0 := by
  have hnear : ∀ᶠ s : ℂ in 𝓝 0, ∀ z ∈ closedBall (0 : ℂ) 16,
      translatedStep Y s z ∈ ball (0 : ℂ) 24 := by
    apply (isCompact_closedBall (0 : ℂ) 16).eventually_forall_of_forall_eventually
    intro z hz
    have hzero := translatedStep_zero_mem_ball_eighteen N H Y hH hY z hz
    have hmem : translatedStep Y 0 z ∈ ball (0 : ℂ) 24 :=
      ball_subset_ball (by norm_num : (18 : ℝ) ≤ 24) hzero
    exact (analyticAt_translatedStep_zero_of_radius N H Y 16 hH hY (by norm_num) z hz).continuousAt.eventually
      (isOpen_ball.mem_nhds hmem)
  have hreal : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ closedBall (0 : ℂ) 16,
      translatedStep Y s z ∈ ball (0 : ℂ) 24 :=
    (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually hnear
  filter_upwards [hreal] with s hs z hz
  refine ⟨hs z hz, translatedStep_chart_identity Y s z, ?_⟩
  rw [translatedStep_chart_identity]
  apply chartPoint_ne_zero
  have hn : ‖translatedStep Y s z‖ < 24 := by simpa only [mem_ball, dist_zero_right] using hs z hz
  linarith [Nat.cast_nonneg (α := ℝ) N]

end Kneser.ActualGateNextImage

end
