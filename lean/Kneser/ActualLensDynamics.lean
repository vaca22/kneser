import Kneser.ActualLensBootstrap
import Kneser.RealLensMidline

/-! True full-lens dynamics and absolute residual convergence, including
the real midline. -/

noncomputable section
namespace Kneser.ActualLensDynamics

open Kneser.ActualLensGeometry Kneser.ActualLensBounds Kneser.ActualLensModel
open Kneser.ActualLensFiniteError Kneser.ActualLensBootstrap
open Kneser.GrowingBandGeometry Kneser.GrowingBandKernel
open Kneser.ExponentialUnfolding Kneser.EvenPreparedOrbitDiscs
open Kneser.RealExponentialPetal Kneser.ExponentialDividedDifference
open Kneser.PositiveKoenigsOrbit
open scoped BigOperators

theorem true_lens_invariant (Q : QuotientControl)
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (e₁ e₂ : ℂ)
    (s a b η Y M P : ℝ) (u : ℂ)
    (hη : 0 < η) (hηq : η ≤ 1 / 4) (hηr : η ≤ Q.radius / 4)
    (hs : 0 < s) (hs1 : s < 1 / 2) (hsη : s ≤ η / 8)
    (ha : |a| ≤ η / 8) (hb : |b| ≤ η / 8) (ha0 : a < 0) (hb0 : 0 < b)
    (hfa : unfolding s a = (a : ℂ)) (hfb : unfolding s b = (b : ℂ))
    (hM : 0 ≤ M) (_hP : 0 ≤ P) (hY : 2 ≤ Y)
    (hYlarge : 5 * Real.pi / (Y / 2) ≤ η / 8)
    (hmargin : 2 * (Real.pi + 2 * P) + 1 < Y / 2)
    (hθ1 : timeScale Q ((1 - s) * (b - a)) ≤ 1)
    (hYθ : timeScale Q ((1 - s) * (b - a)) * Y ≤ Real.pi)
    (hE : errorBound M (Y / 2) (timeScale Q ((1 - s) * (b - a))) ≤ 1)
    (hlocalres : ∀ v : ℂ, ‖v‖ < η → ‖descendedTerm A B Γ 2 v s 0‖ ≤
      M * (‖v - (a : ℂ)‖ * ‖v - (b : ℂ)‖) ^ 2)
    (hlocalphase : ∀ v : ℂ, ‖v‖ < η →
      |(lensModel s a b (-Real.log (multiplier s a)) e₁ e₂ v -
        bandTime a b (-Real.log (multiplier s a)) v).im| ≤ Real.pi + 2 * P)
    (hlocalstep : ∀ v : ℂ, ‖v‖ < η → v.im ≠ 0 →
      lensModel s a b (-Real.log (multiplier s a)) e₁ e₂ (unfolding s v) -
        lensModel s a b (-Real.log (multiplier s a)) e₁ e₂ v - 1 =
          descendedTerm A B Γ 2 v s 0)
    (hua : u ≠ (a : ℂ)) (hub : u ≠ (b : ℂ))
    (hsource : bandTime a b (timeScale Q ((1 - s) * (b - a))) u ∈
      strip (timeScale Q ((1 - s) * (b - a))) Y) :
    ∀ k : ℕ, orbit u s k ≠ (a : ℂ) ∧ orbit u s k ≠ (b : ℂ) ∧
      ‖orbit u s k‖ ≤ η / 4 ∧
      bandTime a b (timeScale Q ((1 - s) * (b - a))) (orbit u s k) ∈
        strip (timeScale Q ((1 - s) * (b - a))) (Y / 2) := by
  by_cases hui : u.im = 0
  · have hlens := Kneser.RealLensMidline.real_midline_invariant s a b
      (timeScale Q ((1 - s) * (b - a))) Y u (by linarith) (by linarith)
      (timeScale_pos_and_gap_bound Q s a b hs hs1 (by linarith)
        (by
          have hm : (1 - s) * (b - a) ≤ b - a := by nlinarith
          have ha' := (abs_le.mp ha).1
          have hb' := (abs_le.mp hb).2
          linarith [Q.radius_pos])).1 (by linarith) hfa hfb hua hub hui hsource
    have hu : u = (u.re : ℂ) := by apply Complex.ext <;> simp [hui]
    have hi := Kneser.RealLensMidline.real_bandTime_between a b
      (timeScale Q ((1 - s) * (b - a))) u.re (by linarith)
      (timeScale_pos_and_gap_bound Q s a b hs hs1 (by linarith)
        (by
          have hm : (1 - s) * (b - a) ≤ b - a := by nlinarith
          have ha' := (abs_le.mp ha).1
          have hb' := (abs_le.mp hb).2
          linarith [Q.radius_pos])).1
      (by intro he; apply hua; rw [hu, he]) (by intro he; apply hub; rw [hu, he])
      (by rw [← hu]; linarith [hsource.1])
    intro k
    have hk := Kneser.RealLensMidline.real_between_orbit s a b u.re (by linarith) hfa hfb hi.1 hi.2 k
    have horbit : orbit u s k = orbit (u.re : ℂ) s k := congrArg (fun w => orbit w s k) hu
    have hk' : (orbit u s k).im = 0 ∧ a < (orbit u s k).re ∧ (orbit u s k).re < b := by
      rw [horbit]
      exact hk
    have he : orbit u s k = ((orbit u s k).re : ℂ) := by
      apply Complex.ext <;> simp [hk'.1]
    have hn : ‖orbit u s k‖ ≤ η / 4 := by
      rw [he, Complex.norm_real, Real.norm_eq_abs]
      apply abs_le.mpr
      have ha' := (abs_le.mp ha).1
      have hb' := (abs_le.mp hb).2
      constructor <;> linarith [hk'.2.1, hk'.2.2]
    exact ⟨(hlens k).1, (hlens k).2.1, hn, (hlens k).2.2⟩
  · intro k
    have hh := nonreal_true_lens_invariant Q A B Γ e₁ e₂ s a b η Y M P u
      hη hηq hηr hs hs1 hsη ha hb ha0 hb0 hfa hfb hM _hP hY hYlarge hmargin
      hθ1 hYθ hE hlocalres hlocalphase hlocalstep hua hub hui hsource k
    exact ⟨hh.1, hh.2.1, hh.2.2.2.1, hh.2.2.2.2⟩

theorem quotient_arguments_of_local_norm (Q : QuotientControl) (s a b η : ℝ) (v : ℂ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hη : 0 < η) (hηr : η ≤ Q.radius / 4)
    (ha : |a| ≤ η / 8) (hb : |b| ≤ η / 8) (hv : ‖v‖ ≤ η / 4) :
    (1 - (s : ℂ)) * (v - (a : ℂ)) ∈ Metric.ball 0 Q.radius ∧
      (1 - (s : ℂ)) * (v - (b : ℂ)) ∈ Metric.ball 0 Q.radius := by
  have hm : ‖1 - (s : ℂ)‖ ≤ 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - s)]
    linarith
  have he (r : ℝ) (hr : |r| ≤ η / 8) :
      (1 - (s : ℂ)) * (v - (r : ℂ)) ∈ Metric.ball 0 Q.radius := by
    rw [Metric.mem_ball, dist_zero_right, norm_mul]
    have ht := norm_sub_le v (r : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at ht
    have hh := mul_le_mul_of_nonneg_right hm (norm_nonneg (v - (r : ℂ)))
    linarith [Q.radius_pos]
  exact ⟨he a ha, he b hb⟩

theorem descendedTerm_at_orbit (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (u s : ℂ) (k : ℕ) :
    descendedTerm A B Γ 2 (orbit u s k) s 0 = descendedTerm A B Γ 2 u s k := by
  simp [descendedTerm, splitTerm]

/-- An actual infinite residual series is absolutely convergent when the
proved finite-lens control holds along the true orbit. -/
theorem true_lens_absolute_residual (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (u : ℂ) (s a b θ Y M : ℝ) (hab : a < b) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hY : 1 ≤ Y) (hYθ : θ * Y ≤ Real.pi)
    (hratio : (b - a) / θ ≤ 5) (hM : 0 ≤ M)
    (hroots : ∀ k, orbit u s k ≠ (a : ℂ) ∧ orbit u s k ≠ (b : ℂ))
    (hband : ∀ k, bandTime a b θ (orbit u s k) ∈ strip θ Y)
    (hres : ∀ k, ‖descendedTerm A B Γ 2 (orbit u s k) s 0‖ ≤
      M * (‖orbit u s k - (a : ℂ)‖ * ‖orbit u s k - (b : ℂ)‖) ^ 2)
    (hstep : ∀ k, (bandTime a b θ (orbit u s k)).re + 3 / 4 ≤
      (bandTime a b θ (orbit u s (k + 1))).re) :
    Summable (fun k => ‖descendedTerm A B Γ 2 u s k‖) ∧
      (∑' k, ‖descendedTerm A B Γ 2 u s k‖) ≤ errorBound M Y θ := by
  have hfinite : ∀ N : ℕ, (∑ k ∈ Finset.range N, ‖descendedTerm A B Γ 2 u s k‖) ≤ errorBound M Y θ := by
    intro N
    have hh := finite_true_lens_residual_sum A B Γ u s a b θ Y M N hab hθ hθ1 hY hYθ
      hratio hM (fun k _ => hroots k) (fun k _ => hband k) (fun k _ => hres k) (fun k _ => hstep k)
    simpa only [descendedTerm_at_orbit] using hh
  have hs := summable_of_sum_range_le (fun k => norm_nonneg _) hfinite
  exact ⟨hs, hs.tsum_le_of_sum_range_le hfinite⟩

end Kneser.ActualLensDynamics
end
