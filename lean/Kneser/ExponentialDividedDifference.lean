import Kneser.ParabolicFatouCoordinate
import Mathlib.Analysis.Calculus.MeanValue
import Kneser.ApolloniusGeometry

/-!
# The true exponential divided difference in a two-root petal step

The analytic quotient is constructed from the exponential Taylor expansion.
Its logarithm has derivative `1/2` at zero; continuity of its derivative and
the complex mean value estimate yield a quantitative two-point increment.
-/

namespace Kneser.ExponentialDividedDifference

open Filter Metric Set Kneser.ParabolicExponentialOrbit
open Kneser.ExponentialUnfolding Kneser.ParabolicFatouCoordinate
open scoped Topology

/-- Construct the actual exponential divided difference and its logarithmic
increment estimate, with any requested positive error constant. -/
theorem exists_quotient_log_increment (ε : ℝ) (hε : 0 < ε) :
    ∃ E : ℂ → ℂ, ∃ r : ℝ, 0 < r ∧ AnalyticAt ℂ E 0 ∧ E 0 = 1 ∧ deriv E 0 = 1 / 2 ∧
      (∀ z, parabolicMap z = z * E z) ∧
      (∀ z ∈ ball (0 : ℂ) r, E z ≠ 0) ∧
      (∀ z₁ ∈ ball (0 : ℂ) r, ∀ z₂ ∈ ball (0 : ℂ) r,
        ‖Complex.log (E z₂) - Complex.log (E z₁) - (z₂ - z₁) / 2‖ ≤ ε * ‖z₂ - z₁‖) := by
  obtain ⟨E, L, hEa, hLa, hE0, hL0, hEd, hLd, hE, hEL⟩ := exists_exponential_quotient
  have hslit : E 0 ∈ Complex.slitPlane := by simp [hE0, Complex.mem_slitPlane_iff]
  let F : ℂ → ℂ := fun z => Complex.log (E z) - z / 2
  have hFa : AnalyticAt ℂ F 0 := (hEa.clog hslit).sub (analyticAt_id.div_const)
  have hEder : HasDerivAt E (1 / 2) 0 := by
    simpa only [hEd] using hEa.hasStrictDerivAt.hasDerivAt
  have hFder : HasDerivAt F 0 0 := by
    have hd := (hEder.clog hslit).sub ((hasDerivAt_id (0 : ℂ)).div_const 2)
    change HasDerivAt (fun z => Complex.log (E z) - z / 2) ((1 / 2) / E 0 - 1 / 2) 0 at hd
    simpa [F, hE0] using hd
  have hder0 : deriv F 0 = 0 := hFder.deriv
  have hn : ContinuousAt (fun z => ‖deriv F z‖) 0 := hFa.deriv.continuousAt.norm
  have hbound : ∀ᶠ z in 𝓝 (0 : ℂ), ‖deriv F z‖ ≤ ε := by
    have hlt : ‖deriv F 0‖ < ε := by simpa [hder0] using hε
    exact (hn.eventually (Iio_mem_nhds hlt)).mono (fun _ h => h.le)
  have hne : ∀ᶠ z in 𝓝 (0 : ℂ), E z ≠ 0 :=
    (hEa.continuousAt.ne_iff_eventually_ne continuousAt_const).mp (by simp [hE0])
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hFa.eventually_analyticAt.and (hbound.and hne))
  refine ⟨E, r, hr, hEa, hE0, hEd, hE, ?_, ?_⟩
  · intro z hz
    exact (hball z hz).2.2
  · intro z₁ hz₁ z₂ hz₂
    have hm := (convex_ball (0 : ℂ) r).norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hball z hz).1.differentiableAt)
      (fun z hz => (hball z hz).2.1) hz₁ hz₂
    have heq : F z₂ - F z₁ = Complex.log (E z₂) - Complex.log (E z₁) - (z₂ - z₁) / 2 := by
      dsimp [F]
      ring
    rwa [heq] at hm

/-- The exponential divided difference factors the genuine unfolding about
each of its actual fixed points. -/
theorem unfolding_fixedPoint_factor (E : ℂ → ℂ)
    (hE : ∀ z, parabolicMap z = z * E z) (s a u : ℂ)
    (ha : unfolding s a = a) :
    unfolding s u - a = (1 - s) * (1 + a) * (u - a) * E ((1 - s) * (u - a)) := by
  have hexp : Complex.exp (-s + (1 - s) * a) = 1 + a := by
    change Complex.exp (-s + (1 - s) * a) - 1 = a at ha
    simpa only [add_comm] using sub_eq_iff_eq_add.mp ha
  have harg : -s + (1 - s) * u =
      (-s + (1 - s) * a) + (1 - s) * (u - a) := by ring
  have hquot : Complex.exp ((1 - s) * (u - a)) =
      1 + ((1 - s) * (u - a)) * E ((1 - s) * (u - a)) := by
    have h := hE ((1 - s) * (u - a))
    change Complex.exp ((1 - s) * (u - a)) - 1 = _ at h
    simpa only [add_comm] using sub_eq_iff_eq_add.mp h
  rw [unfolding, harg, Complex.exp_add, hexp, hquot]
  ring

/-- For two actual fixed points, the multiplier ratio is the exponential of
their scaled gap. This identity removes the need for a residue asymptotic in
the petal step estimate. -/
theorem fixedPoint_multiplier_ratio (s a b : ℂ)
    (ha : unfolding s a = a) (hb : unfolding s b = b) :
    (1 - s) * (1 + b) = ((1 - s) * (1 + a)) * Complex.exp ((1 - s) * (b - a)) := by
  have hexpa : Complex.exp (-s + (1 - s) * a) = 1 + a := by
    change Complex.exp (-s + (1 - s) * a) - 1 = a at ha
    simpa only [add_comm] using sub_eq_iff_eq_add.mp ha
  have hexpb : Complex.exp (-s + (1 - s) * b) = 1 + b := by
    change Complex.exp (-s + (1 - s) * b) - 1 = b at hb
    simpa only [add_comm] using sub_eq_iff_eq_add.mp hb
  have harg : -s + (1 - s) * b =
      (-s + (1 - s) * a) + (1 - s) * (b - a) := by ring
  rw [harg, Complex.exp_add, hexpa] at hexpb
  rw [← hexpb]
  ring

/-- The exact cross-ratio step for the genuine unfolding, written using its
constructed exponential divided difference. -/
theorem crossRatio_step (E : ℂ → ℂ)
    (hE : ∀ z, parabolicMap z = z * E z) (s a b u : ℂ)
    (ha : unfolding s a = a) (hb : unfolding s b = b)
    (hs : s ≠ 1) (hbne : b ≠ -1) (hub : u ≠ b)
    (hEb : E ((1 - s) * (u - b)) ≠ 0) :
    ApolloniusGeometry.crossRatio a b (unfolding s u) =
      ApolloniusGeometry.crossRatio a b u * Complex.exp (-((1 - s) * (b - a))) *
      (E ((1 - s) * (u - a)) / E ((1 - s) * (u - b))) := by
  have hsa : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have hbn : 1 + b ≠ 0 := by
    intro h
    apply hbne
    linear_combination h
  have hun : u - b ≠ 0 := sub_ne_zero.mpr hub
  have hfa := unfolding_fixedPoint_factor E hE s a u ha
  have hfb := unfolding_fixedPoint_factor E hE s b u hb
  have hratio := fixedPoint_multiplier_ratio s a b ha hb
  have hcore : 1 + b = (1 + a) * Complex.exp ((1 - s) * (b - a)) := by
    apply mul_left_cancel₀ hsa
    simpa only [mul_assoc] using hratio
  have hexp := Complex.exp_ne_zero ((1 - s) * (b - a))
  have hinv : Complex.exp (-((1 - s) * (b - a))) =
      (Complex.exp ((1 - s) * (b - a)))⁻¹ := Complex.exp_neg _
  unfold ApolloniusGeometry.crossRatio
  rw [hfa, hfb, hinv]
  field_simp
  linear_combination - E ((1 - s) * (u - a)) * (u - a) * hcore

end Kneser.ExponentialDividedDifference
