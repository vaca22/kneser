import Kneser.ActualLensFiniteError

/-! A genuine finite bootstrap for the exponential unfolding on the
nonreal part of the two-root lens. Local preparation identities are used
only inside their proved neighborhood. -/

noncomputable section
set_option maxHeartbeats 1000000
namespace Kneser.ActualLensBootstrap

open Kneser.ActualLensGeometry Kneser.ActualLensBounds Kneser.ActualLensModel
open Kneser.ActualLensFiniteError Kneser.GrowingBandGeometry Kneser.GrowingBandKernel
open Kneser.ExponentialUnfolding Kneser.EvenPreparedOrbitDiscs
open Kneser.RealExponentialPetal Kneser.ExponentialDividedDifference
open Kneser.PositiveKoenigsOrbit
open scoped BigOperators

theorem finite_model_telescope (ψ : ℂ → ℂ) (f : ℂ → ℂ)
    (u s : ℂ) (N : ℕ)
    (hstep : ∀ k < N, ψ (unfolding s (orbit u s k)) - ψ (orbit u s k) - 1 = f (orbit u s k)) :
    ψ (orbit u s N) - ψ u - N = ∑ k ∈ Finset.range N, f (orbit u s k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hi := ih (fun k hk => hstep k (by omega))
    have hn := hstep N (by omega)
    rw [Finset.sum_range_succ, ← hi]
    rw [orbit_succ, Nat.cast_add, Nat.cast_one]
    linear_combination hn

theorem finite_phase_bound (ψ : ℂ → ℂ) (f : ℂ → ℂ) (τ : ℂ → ℂ)
    (u s : ℂ) (N : ℕ) (B E : ℝ)
    (hstep : ∀ k < N, ψ (unfolding s (orbit u s k)) - ψ (orbit u s k) - 1 = f (orbit u s k))
    (herror : (∑ k ∈ Finset.range N, ‖f (orbit u s k)‖) ≤ E)
    (hstart : |(ψ u - τ u).im| ≤ B)
    (hend : |(ψ (orbit u s N) - τ (orbit u s N)).im| ≤ B) :
    |(τ (orbit u s N)).im - (τ u).im| ≤ 2 * B + E := by
  have ht := finite_model_telescope ψ f u s N hstep
  have hh : |(ψ (orbit u s N)).im - (ψ u).im| ≤ E := by
    have hn := (norm_sum_le (Finset.range N) (fun k => f (orbit u s k))).trans herror
    have him := Complex.abs_im_le_norm (∑ k ∈ Finset.range N, f (orbit u s k))
    have he := congrArg Complex.im ht
    simp only [Complex.sub_im, Complex.natCast_im, sub_zero] at he
    rw [← he] at him
    exact him.trans hn
  have he : (τ (orbit u s N)).im - (τ u).im =
      ((ψ (orbit u s N)).im - (ψ u).im) + (ψ u - τ u).im -
        (ψ (orbit u s N) - τ (orbit u s N)).im := by simp
  rw [he]
  calc
    _ ≤ |(ψ (orbit u s N)).im - (ψ u).im + (ψ u - τ u).im| +
      |(ψ (orbit u s N) - τ (orbit u s N)).im| := abs_sub _ _
    _ ≤ (|(ψ (orbit u s N)).im - (ψ u).im| + |(ψ u - τ u).im|) +
      |(ψ (orbit u s N) - τ (orbit u s N)).im| := by gcongr; exact abs_add_le _ _
    _ ≤ 2 * B + E := by linarith

/-- From the actual local preparation bounds, the actual nonreal orbit
remains in the growing strip. The strip conclusion is proved by a finite
phase bootstrap, rather than used as a hypothesis for all iterates. -/
theorem nonreal_true_lens_invariant (Q : QuotientControl)
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
    (hua : u ≠ (a : ℂ)) (hub : u ≠ (b : ℂ)) (hui : u.im ≠ 0)
    (hsource : bandTime a b (timeScale Q ((1 - s) * (b - a))) u ∈
      strip (timeScale Q ((1 - s) * (b - a))) Y) :
    ∀ k : ℕ, orbit u s k ≠ (a : ℂ) ∧ orbit u s k ≠ (b : ℂ) ∧
      (orbit u s k).im ≠ 0 ∧ ‖orbit u s k‖ ≤ η / 4 ∧
      bandTime a b (timeScale Q ((1 - s) * (b - a))) (orbit u s k) ∈
        strip (timeScale Q ((1 - s) * (b - a))) (Y / 2) := by
  let θ := timeScale Q ((1 - s) * (b - a))
  have hab : a < b := by linarith
  have haa : -1 < a := by have hh := (abs_le.mp ha).1; linarith
  have hκr : (1 - s) * (b - a) < Q.radius := by
    have hai := (abs_le.mp ha).1
    have hbi := (abs_le.mp hb).2
    have hh : b - a ≤ η / 4 := by linarith
    have hm : (1 - s) * (b - a) ≤ b - a := by nlinarith
    linarith [Q.radius_pos]
  obtain ⟨hθ, hratio⟩ := timeScale_pos_and_gap_bound Q s a b hs hs1 hab hκr
  have hθeq : θ = -Real.log (multiplier s a) :=
    timeScale_eq_neg_log_multiplier Q s a b (by linarith) haa hab hfa hfb
  have hY0 : 0 < Y := by linarith
  have hhalf : θ * (Y / 2) ≤ Real.pi := by dsimp [θ]; linarith [mul_pos hθ hY0]
  have hnorm (v : ℂ) (hva : v ≠ (a : ℂ)) (hvb : v ≠ (b : ℂ))
      (hvband : bandTime a b θ v ∈ strip θ (Y / 2)) : ‖v‖ ≤ η / 4 := by
    have hd := bandChart_root_distance_bound a b θ (Y / 2) (bandTime a b θ v)
      hab hθ (by linarith) hhalf hvband
    rw [bandChart_bandTime a b θ v (ne_of_lt hab) (ne_of_gt hθ) hva hvb] at hd
    have hda : ‖v - (a : ℂ)‖ ≤ η / 8 := by
      apply hd.1.trans
      have hh : (b - a) * Real.pi / (θ * (Y / 2)) ≤ 5 * Real.pi / (Y / 2) := by
        rw [← div_div]
        have he : (b - a) * Real.pi / θ = ((b - a) / θ) * Real.pi := by ring
        rw [he]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hratio Real.pi_pos.le) (by linarith)
      exact hh.trans hYlarge
    have ht := norm_add_le (v - (a : ℂ)) (a : ℂ)
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] at ht
    linarith
  have hinput (v : ℂ) (hv : ‖v‖ ≤ η / 4) :
      (1 - (s : ℂ)) * (v - (a : ℂ)) ∈ Metric.ball 0 Q.radius ∧
      (1 - (s : ℂ)) * (v - (b : ℂ)) ∈ Metric.ball 0 Q.radius := by
    have hm : ‖1 - (s : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 - s)]
      linarith
    have he (r : ℝ) (hr : |r| ≤ η / 8) :
        (1 - (s : ℂ)) * (v - (r : ℂ)) ∈ Metric.ball 0 Q.radius := by
      rw [Metric.mem_ball, dist_zero_right, norm_mul]
      have ht := norm_sub_le v (r : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at ht
      have hh := mul_le_mul_of_nonneg_right hm (norm_nonneg (v - (r : ℂ)))
      linarith [Q.radius_pos]
    exact ⟨he a ha, he b hb⟩
  have hbase : u ≠ (a : ℂ) ∧ u ≠ (b : ℂ) ∧ u.im ≠ 0 ∧ ‖u‖ ≤ η / 4 ∧
      bandTime a b θ u ∈ strip θ (Y / 2) := by
    have hband : bandTime a b θ u ∈ strip θ (Y / 2) := by
      constructor <;> linarith [hsource.1, hsource.2]
    exact ⟨hua, hub, hui, hnorm u hua hub hband, hband⟩
  have hall : ∀ N : ℕ, ∀ k ≤ N, orbit u s k ≠ (a : ℂ) ∧ orbit u s k ≠ (b : ℂ) ∧
      (orbit u s k).im ≠ 0 ∧ ‖orbit u s k‖ ≤ η / 4 ∧
      bandTime a b θ (orbit u s k) ∈ strip θ (Y / 2) := by
    intro N
    induction N with
    | zero =>
      intro k hk
      have hk0 : k = 0 := by omega
      subst k
      simpa using hbase
    | succ N ih =>
      have hN := ih N (le_refl _)
      have hin := hinput (orbit u s N) hN.2.2.2.1
      have hdrift := actual_bandTime_re_drift Q s a b (orbit u s N) hs hs1 haa hab hb0 hfa hfb
        hN.1 hN.2.1 hκr hin.1 hin.2
      have hnewroots : orbit u s (N + 1) ≠ (a : ℂ) ∧ orbit u s (N + 1) ≠ (b : ℂ) := by
        simpa only [orbit_succ] using And.intro hdrift.1 hdrift.2.1
      have hnewi : (orbit u s (N + 1)).im ≠ 0 := by
        rw [orbit_succ]
        have hn1 : ‖orbit u s N‖ ≤ 1 := hN.2.2.2.1.trans (by linarith)
        rcases lt_or_gt_of_ne hN.2.2.1 with hi | hi
        · exact ne_of_lt (unfolding_im_neg s _ hs.le (by linarith) hn1 hi)
        · exact ne_of_gt (unfolding_im_pos s _ hs.le (by linarith) hn1 hi)
      have hnewnorm : ‖orbit u s (N + 1)‖ < η := by
        rw [orbit_succ]
        exact (unfolding_norm_le s _ η hη hηq hs.le hsη hN.2.2.2.1).trans_lt (by linarith)
      have hdall : ∀ k < N + 1, (bandTime a b θ (orbit u s k)).re + 3 / 4 ≤
          (bandTime a b θ (orbit u s (k + 1))).re := by
        intro k hk
        have hkdata := ih k (by omega)
        have hki := hinput (orbit u s k) hkdata.2.2.2.1
        have hh := actual_bandTime_re_drift Q s a b (orbit u s k) hs hs1 haa hab hb0 hfa hfb
          hkdata.1 hkdata.2.1 hκr hki.1 hki.2
        simpa only [orbit_succ] using hh.2.2
      have hfinite := finite_true_lens_residual_sum A B Γ u s a b θ (Y / 2) M (N + 1)
        hab hθ hθ1 (by linarith) hhalf hratio hM
        (fun k hk => ⟨(ih k (by omega)).1, (ih k (by omega)).2.1⟩)
        (fun k hk => (ih k (by omega)).2.2.2.2)
        (fun k hk => hlocalres _ ((ih k (by omega)).2.2.2.1.trans_lt (by linarith))) hdall
      have hψstep : ∀ k < N + 1,
          lensModel s a b θ e₁ e₂ (unfolding s (orbit u s k)) -
            lensModel s a b θ e₁ e₂ (orbit u s k) - 1 = descendedTerm A B Γ 2 (orbit u s k) s 0 := by
        intro k hk
        rw [hθeq]
        exact hlocalstep _ ((ih k (by omega)).2.2.2.1.trans_lt (by linarith)) (ih k (by omega)).2.2.1
      have hphase := finite_phase_bound (lensModel s a b θ e₁ e₂)
        (fun v => descendedTerm A B Γ 2 v s 0) (bandTime a b θ) u s (N + 1)
        (Real.pi + 2 * P) 1 hψstep (hfinite.trans hE)
        (by rw [hθeq]; exact hlocalphase u (hbase.2.2.2.1.trans_lt (by linarith)))
        (by rw [hθeq]; exact hlocalphase _ hnewnorm)
      have hnewband : bandTime a b θ (orbit u s (N + 1)) ∈ strip θ (Y / 2) := by
        have hphase' := abs_le.mp hphase
        constructor <;> linarith [hsource.1, hsource.2]
      have hnew := And.intro hnewroots.1 (And.intro hnewroots.2
        (And.intro hnewi (And.intro (hnorm _ hnewroots.1 hnewroots.2 hnewband) hnewband)))
      intro k hk
      by_cases hkN : k ≤ N
      · exact ih k hkN
      · have he : k = N + 1 := by omega
        simpa only [he] using hnew
  intro k
  exact hall k k (le_refl _)

end Kneser.ActualLensBootstrap
end
