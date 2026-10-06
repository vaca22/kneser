import Kneser.ActualInverseLensBootstrap
import Kneser.ActualReflectedLensMidline

/-! Actual full inverse-lens control and absolute shifted residual sums. -/
noncomputable section
namespace Kneser.ActualInverseLensDynamics

open Kneser.ActualReflectedLensModel Kneser.ActualLensGeometry Kneser.ActualLensBounds
open Kneser.ActualLensModel Kneser.ActualLensFiniteError Kneser.GrowingBandGeometry
open Kneser.GrowingBandKernel Kneser.ActualInverseLensBootstrap
open Kneser.EvenPreparedOrbitDiscs Kneser.ExponentialUnfolding
open Kneser.RealExponentialPetal Kneser.PositiveKoenigsOrbit
open scoped BigOperators

theorem inverseOrbit_eq_iterate (s : ℝ) (u : ℂ) (k : ℕ) :
    inverseOrbit s u k = (inverseStep s)^[k] u := by
  induction k with
  | zero => rfl
  | succ k ih => rw [inverseOrbit_succ, Function.iterate_succ_apply', ih]

theorem inverseOrbit_eq_reflected (s : ℝ) (u : ℂ) (k : ℕ) :
    inverseOrbit s u k = -Kneser.RepellingExponentialOrbit.inverseOrbit (-u) (s : ℂ) k := by
  rw [inverseOrbit_eq_iterate]
  exact Kneser.ActualReflectedLensMidline.physical_inverse_iterate_reflected s u k

theorem true_inverse_lens_invariant (Q : QuotientControl)
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (e₁ e₂ : ℂ)
    (s a b η Y M P : ℝ) (u : ℂ)
    (hη : 0 < η) (hηq : η ≤ 1 / 4) (hηr : 2 * η ≤ Q.radius)
    (hs : 0 < s) (hsη : s ≤ η / 8)
    (ha : |a| ≤ η / 8) (hb : |b| ≤ η / 8) (ha0 : a < 0) (hb0 : 0 < b)
    (hfa : unfolding s a = (a : ℂ)) (hfb : unfolding s b = (b : ℂ))
    (hM : 0 ≤ M) (hMη : M * η ^ 4 ≤ 1) (hY : 2 ≤ Y)
    (hYlarge : 5 * Real.pi / (Y / 2) ≤ η / 8)
    (hmargin : 2 * (Real.pi + 2 * P) + 2 < Y / 2)
    (hθ1 : -Real.log (multiplier s a) ≤ 1)
    (hYθ : -Real.log (multiplier s a) * Y ≤ Real.pi)
    (hE : errorBound M (Y / 2) (-Real.log (multiplier s a)) ≤ 1)
    (hlocalres : ∀ v : ℂ, ‖v‖ < η → ‖descendedTerm A B Γ 2 v s 0‖ ≤
      M * (‖v - (a : ℂ)‖ * ‖v - (b : ℂ)‖) ^ 2)
    (hlocalphase : ∀ v : ℂ, ‖v‖ < η →
      |(lensModel s a b (-Real.log (multiplier s a)) e₁ e₂ v -
        bandTime a b (-Real.log (multiplier s a)) v).im| ≤ Real.pi + 2 * P)
    (hlocalstep : ∀ v : ℂ, ‖v‖ ≤ η / 4 → v.im ≠ 0 →
      lensModel s a b (-Real.log (multiplier s a)) e₁ e₂ (inverseStep s v) -
        lensModel s a b (-Real.log (multiplier s a)) e₁ e₂ v + 1 =
          -descendedTerm A B Γ 2 (inverseStep s v) s 0)
    (hua : u ≠ (a : ℂ)) (hub : u ≠ (b : ℂ))
    (hsource : bandTime a b (-Real.log (multiplier s a)) u ∈
      strip (-Real.log (multiplier s a)) Y) :
    ∀ k : ℕ, inverseOrbit s u k ≠ (a : ℂ) ∧ inverseOrbit s u k ≠ (b : ℂ) ∧
      ‖inverseOrbit s u k‖ ≤ η / 4 ∧
      bandTime a b (-Real.log (multiplier s a)) (inverseOrbit s u k) ∈
        strip (-Real.log (multiplier s a)) (Y / 2) := by
  by_cases hui : u.im = 0
  · have haa : -1 < a := by have hh := (abs_le.mp ha).1; linarith
    have hab : a < b := by linarith
    have hs1 : s < 1 / 2 := by linarith
    have hκr : (1 - s) * (b - a) < Q.radius := by
      have hm : (1 - s) * (b - a) ≤ b - a := by nlinarith
      linarith [(abs_le.mp ha).1, (abs_le.mp hb).2]
    have hθeq := timeScale_eq_neg_log_multiplier Q s a b (by linarith) haa hab hfa hfb
    obtain ⟨hθ, hratio⟩ := timeScale_pos_and_gap_bound Q s a b hs hs1 hab hκr
    change timeScale Q ((1 - s) * (b - a)) = -Real.log (multiplier s a) at hθeq
    rw [hθeq] at hθ hratio
    have hhalf : -Real.log (multiplier s a) * (Y / 2) ≤ Real.pi := by
      linarith [mul_pos hθ (show 0 < Y by linarith)]
    have hlens := Kneser.ActualReflectedLensMidline.inverse_real_midline_invariant s a b
      (-Real.log (multiplier s a)) Y u (by linarith) haa hab hθ (by linarith)
      hfa hfb hua hub hui hsource
    intro k
    have hk := hlens k
    rw [← inverseOrbit_eq_iterate] at hk
    exact ⟨hk.1, hk.2.1,
      norm_of_lens_time a b (-Real.log (multiplier s a)) (Y / 2) η (inverseOrbit s u k)
        hab hθ (by linarith) hhalf hratio hη ha hYlarge hk.1 hk.2.1 hk.2.2.2,
      hk.2.2.2⟩
  · intro k
    have hh := nonreal_true_inverse_lens_invariant Q A B Γ e₁ e₂ s a b η Y M P u
      hη hηq hηr hs hsη ha hb ha0 hb0 hfa hfb hM hMη hY hYlarge hmargin
      hθ1 hYθ hE hlocalres hlocalphase hlocalstep hua hub hui hsource k
    exact ⟨hh.1, hh.2.1, hh.2.2.2.1, hh.2.2.2.2⟩

theorem true_inverse_lens_absolute_residual (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (u : ℂ) (s a b θ Y M : ℝ) (hab : a < b) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hY : 1 ≤ Y) (hYθ : θ * Y ≤ Real.pi)
    (hratio : (b - a) / θ ≤ 5) (hM : 0 ≤ M)
    (hroots : ∀ k, inverseOrbit s u k ≠ (a : ℂ) ∧ inverseOrbit s u k ≠ (b : ℂ))
    (hband : ∀ k, bandTime a b θ (inverseOrbit s u k) ∈ strip θ Y)
    (hres : ∀ k, ‖descendedTerm A B Γ 2 (inverseOrbit s u k) s 0‖ ≤
      M * (‖inverseOrbit s u k - (a : ℂ)‖ * ‖inverseOrbit s u k - (b : ℂ)‖) ^ 2)
    (hstep : ∀ k, (bandTime a b θ (inverseOrbit s u (k + 1))).re + 3 / 4 ≤
      (bandTime a b θ (inverseOrbit s u k)).re) :
    Summable (fun k => ‖descendedTerm A B Γ 2 (inverseOrbit s u (k + 1)) s 0‖) ∧
      (∑' k, ‖descendedTerm A B Γ 2 (inverseOrbit s u (k + 1)) s 0‖) ≤ errorBound M Y θ := by
  have hfinite : ∀ N : ℕ, (∑ k ∈ Finset.range N,
      ‖descendedTerm A B Γ 2 (inverseOrbit s u (k + 1)) s 0‖) ≤ errorBound M Y θ := by
    intro N
    have hh := finite_inverse_residual_sum A B Γ u s a b θ Y M (N + 1) hab hθ hθ1 hY hYθ
      hratio hM (fun k _ => hroots k) (fun k _ => hband k) (fun k _ => hres k) (fun k _ => hstep k)
    have he := sum_range_shift (fun k => ‖descendedTerm A B Γ 2 (inverseOrbit s u k) s 0‖) N
    rw [Finset.sum_range_succ] at hh
    linarith only [he, hh, norm_nonneg (descendedTerm A B Γ 2 (inverseOrbit s u 0) s 0)]
  have hs := summable_of_sum_range_le (fun k => norm_nonneg _) hfinite
  exact ⟨hs, hs.tsum_le_of_sum_range_le hfinite⟩

end Kneser.ActualInverseLensDynamics
end
