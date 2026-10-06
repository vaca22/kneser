import Kneser.ActualReflectedLensModel
import Kneser.ActualLensDynamics

/-! Actual inverse-orbit finite bootstrap. The last inverse residual is
bounded in the local neighborhood before strip re-entry is proved. -/

noncomputable section
set_option maxHeartbeats 1000000
namespace Kneser.ActualInverseLensBootstrap

open Kneser.ActualReflectedLensModel Kneser.ActualLensGeometry Kneser.ActualLensBounds
open Kneser.ActualLensModel Kneser.ActualLensFiniteError Kneser.GrowingBandGeometry
open Kneser.GrowingBandKernel Kneser.FiniteSeparatedKernelBounds
open Kneser.EvenPreparedOrbitDiscs Kneser.ExponentialUnfolding
open Kneser.RealExponentialPetal Kneser.PositiveKoenigsOrbit
open scoped BigOperators

def inverseOrbit (s : ℝ) (u : ℂ) : ℕ → ℂ
  | 0 => u
  | k + 1 => inverseStep s (inverseOrbit s u k)

@[simp] theorem inverseOrbit_zero (s : ℝ) (u : ℂ) : inverseOrbit s u 0 = u := rfl
@[simp] theorem inverseOrbit_succ (s : ℝ) (u : ℂ) (k : ℕ) :
    inverseOrbit s u (k + 1) = inverseStep s (inverseOrbit s u k) := rfl

theorem norm_of_lens_time (a b θ Y η : ℝ) (u : ℂ)
    (hab : a < b) (hθ : 0 < θ) (hY : 0 < Y) (hYθ : θ * Y ≤ Real.pi)
    (hratio : (b - a) / θ ≤ 5) (_hη : 0 < η) (ha : |a| ≤ η / 8)
    (hlarge : 5 * Real.pi / Y ≤ η / 8)
    (hua : u ≠ (a : ℂ)) (hub : u ≠ (b : ℂ))
    (hband : bandTime a b θ u ∈ strip θ Y) : ‖u‖ ≤ η / 4 := by
  have hd := bandChart_root_distance_bound a b θ Y (bandTime a b θ u) hab hθ hY hYθ hband
  rw [bandChart_bandTime a b θ u (ne_of_lt hab) (ne_of_gt hθ) hua hub] at hd
  have hda : ‖u - (a : ℂ)‖ ≤ η / 8 := by
    apply hd.1.trans
    have hh : (b - a) * Real.pi / (θ * Y) ≤ 5 * Real.pi / Y := by
      rw [← div_div]
      have he : (b - a) * Real.pi / θ = ((b - a) / θ) * Real.pi := by ring
      rw [he]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hratio Real.pi_pos.le) hY.le
    exact hh.trans hlarge
  have ht := norm_add_le (u - (a : ℂ)) (a : ℂ)
  rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] at ht
  linarith

theorem finite_inverse_residual_sum (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (u : ℂ) (s a b θ Y M : ℝ) (N : ℕ) (hab : a < b) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hY : 1 ≤ Y) (hYθ : θ * Y ≤ Real.pi)
    (hratio : (b - a) / θ ≤ 5) (hM : 0 ≤ M)
    (hroots : ∀ k < N, inverseOrbit s u k ≠ (a : ℂ) ∧ inverseOrbit s u k ≠ (b : ℂ))
    (hband : ∀ k < N, bandTime a b θ (inverseOrbit s u k) ∈ strip θ Y)
    (hres : ∀ k < N, ‖descendedTerm A B Γ 2 (inverseOrbit s u k) s 0‖ ≤
      M * (‖inverseOrbit s u k - (a : ℂ)‖ * ‖inverseOrbit s u k - (b : ℂ)‖) ^ 2)
    (hstep : ∀ k < N, (bandTime a b θ (inverseOrbit s u (k + 1))).re + 3 / 4 ≤
      (bandTime a b θ (inverseOrbit s u k)).re) :
    (∑ k ∈ Finset.range N, ‖descendedTerm A B Γ 2 (inverseOrbit s u k) s 0‖) ≤
      errorBound M Y θ := by
  let x : ℕ → ℝ := fun k => -(bandTime a b θ (inverseOrbit s u k)).re
  have hs : ∀ k < N, x k + 3 / 4 ≤ x (k + 1) := by
    intro k hk
    dsimp only [x]
    linarith only [hstep k hk]
  have h₁ := finite_rational_kernel_bound x N (3 / 4) Y (by norm_num) hY hs
  have h₂ := finite_exponential_cubic_bound x N (3 / 4) θ (by norm_num) hθ hθ1 hs
  have hsum : (∑ k ∈ Finset.range N, ‖descendedTerm A B Γ 2 (inverseOrbit s u k) s 0‖) ≤
      ∑ k ∈ Finset.range N,
        (2 * M * smallConstant ^ 2 * ((x k ^ 2 + Y ^ 2) ^ 2)⁻¹ +
          2 * M * largeConstant ^ 2 * θ ^ 4 * Real.exp (-2 * θ * |x k|)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hkN := Finset.mem_range.mp hk
    have hp := true_lens_residual_kernel A B Γ s a b θ Y M (inverseOrbit s u k) hab hθ
      (by linarith) hYθ hratio (hroots k hkN).1 (hroots k hkN).2
      (hband k hkN) (hres k hkN) hM
    simpa only [x, neg_sq, abs_neg] using hp
  apply hsum.trans
  rw [Finset.sum_add_distrib]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have h₁' := mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 2 * M * smallConstant ^ 2 by positivity)
  have h₂' := mul_le_mul_of_nonneg_left h₂ (show 0 ≤ 2 * M * largeConstant ^ 2 by positivity)
  simp_rw [mul_assoc, ← Finset.mul_sum] at h₂'
  dsimp [errorBound]
  convert add_le_add h₁' h₂' using 1
  all_goals first | rfl | ring

theorem sum_range_shift (a : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, a (k + 1)) + a 0 = (∑ k ∈ Finset.range N, a k) + a N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, Finset.sum_range_succ]; linarith

theorem finite_inverse_model_telescope (ψ f : ℂ → ℂ) (s : ℝ) (u : ℂ) (N : ℕ)
    (hstep : ∀ k < N, ψ (inverseOrbit s u (k + 1)) - ψ (inverseOrbit s u k) + 1 =
      -f (inverseOrbit s u (k + 1))) :
    ψ (inverseOrbit s u N) - ψ u + N = -∑ k ∈ Finset.range N, f (inverseOrbit s u (k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hi := ih (fun k hk => hstep k (by omega))
    have hn := hstep N (by omega)
    rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    linear_combination hi + hn

theorem inverse_phase_bound (ψ f τ : ℂ → ℂ) (s : ℝ) (u : ℂ) (N : ℕ) (B E : ℝ)
    (hstep : ∀ k < N, ψ (inverseOrbit s u (k + 1)) - ψ (inverseOrbit s u k) + 1 =
      -f (inverseOrbit s u (k + 1)))
    (herror : (∑ k ∈ Finset.range N, ‖f (inverseOrbit s u (k + 1))‖) ≤ E)
    (hstart : |(ψ u - τ u).im| ≤ B)
    (hend : |(ψ (inverseOrbit s u N) - τ (inverseOrbit s u N)).im| ≤ B) :
    |(τ (inverseOrbit s u N)).im - (τ u).im| ≤ 2 * B + E := by
  have ht := finite_inverse_model_telescope ψ f s u N hstep
  have hh : |(ψ (inverseOrbit s u N)).im - (ψ u).im| ≤ E := by
    have hn := (norm_sum_le (Finset.range N) (fun k => f (inverseOrbit s u (k + 1)))).trans herror
    have him := Complex.abs_im_le_norm (-∑ k ∈ Finset.range N, f (inverseOrbit s u (k + 1)))
    have he := congrArg Complex.im ht
    simp only [Complex.add_im, Complex.sub_im, Complex.natCast_im, add_zero] at he
    rw [← he] at him
    exact him.trans (by simpa only [norm_neg] using hn)
  have he : (τ (inverseOrbit s u N)).im - (τ u).im =
      ((ψ (inverseOrbit s u N)).im - (ψ u).im) + (ψ u - τ u).im -
        (ψ (inverseOrbit s u N) - τ (inverseOrbit s u N)).im := by simp
  rw [he]
  calc
    _ ≤ |(ψ (inverseOrbit s u N)).im - (ψ u).im + (ψ u - τ u).im| +
      |(ψ (inverseOrbit s u N) - τ (inverseOrbit s u N)).im| := abs_sub _ _
    _ ≤ (|(ψ (inverseOrbit s u N)).im - (ψ u).im| + |(ψ u - τ u).im|) +
      |(ψ (inverseOrbit s u N) - τ (inverseOrbit s u N)).im| := by gcongr; exact abs_add_le _ _
    _ ≤ 2 * B + E := by linarith

theorem nonreal_true_inverse_lens_invariant (Q : QuotientControl)
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
    (hua : u ≠ (a : ℂ)) (hub : u ≠ (b : ℂ)) (hui : u.im ≠ 0)
    (hsource : bandTime a b (-Real.log (multiplier s a)) u ∈
      strip (-Real.log (multiplier s a)) Y) :
    ∀ k : ℕ, inverseOrbit s u k ≠ (a : ℂ) ∧ inverseOrbit s u k ≠ (b : ℂ) ∧
      (inverseOrbit s u k).im ≠ 0 ∧ ‖inverseOrbit s u k‖ ≤ η / 4 ∧
      bandTime a b (-Real.log (multiplier s a)) (inverseOrbit s u k) ∈
        strip (-Real.log (multiplier s a)) (Y / 2) := by
  let θ := -Real.log (multiplier s a)
  have hs1 : s < 1 / 2 := by linarith
  have hab : a < b := by linarith
  have haa : -1 < a := by have hh := (abs_le.mp ha).1; linarith
  have haη : |a| < η := ha.trans_lt (by linarith)
  have hbη : |b| < η := hb.trans_lt (by linarith)
  have hκr : (1 - s) * (b - a) < Q.radius := by
    have hm : (1 - s) * (b - a) ≤ b - a := by nlinarith
    linarith [(abs_le.mp ha).1, (abs_le.mp hb).2]
  have hθeq := timeScale_eq_neg_log_multiplier Q s a b (by linarith) haa hab hfa hfb
  change timeScale Q ((1 - s) * (b - a)) = θ at hθeq
  obtain ⟨hθ, hratio⟩ := timeScale_pos_and_gap_bound Q s a b hs hs1 hab hκr
  rw [hθeq] at hθ hratio
  have hhalf : θ * (Y / 2) ≤ Real.pi := by linarith [mul_pos hθ (show 0 < Y by linarith)]
  have hnorm (v : ℂ) (hva : v ≠ (a : ℂ)) (hvb : v ≠ (b : ℂ))
      (hvband : bandTime a b θ v ∈ strip θ (Y / 2)) : ‖v‖ ≤ η / 4 :=
    norm_of_lens_time a b θ (Y / 2) η v hab hθ (by linarith) hhalf hratio hη ha hYlarge hva hvb hvband
  have hbase : u ≠ (a : ℂ) ∧ u ≠ (b : ℂ) ∧ u.im ≠ 0 ∧ ‖u‖ ≤ η / 4 ∧
      bandTime a b θ u ∈ strip θ (Y / 2) := by
    have hband : bandTime a b θ u ∈ strip θ (Y / 2) := by constructor <;> linarith [hsource.1, hsource.2]
    exact ⟨hua, hub, hui, hnorm u hua hub hband, hband⟩
  have hall : ∀ N : ℕ, ∀ k ≤ N, inverseOrbit s u k ≠ (a : ℂ) ∧ inverseOrbit s u k ≠ (b : ℂ) ∧
      (inverseOrbit s u k).im ≠ 0 ∧ ‖inverseOrbit s u k‖ ≤ η / 4 ∧
      bandTime a b θ (inverseOrbit s u k) ∈ strip θ (Y / 2) := by
    intro N
    induction N with
    | zero =>
      intro k hk
      have hk0 : k = 0 := by omega
      subst k
      simpa using hbase
    | succ N ih =>
      have hN := ih N (le_refl _)
      have hnewi : (inverseOrbit s u (N + 1)).im ≠ 0 := by
        rw [inverseOrbit_succ]
        exact inverseStep_im_ne_zero s _ (by linarith) hN.2.2.1
      have hnewroots : inverseOrbit s u (N + 1) ≠ (a : ℂ) ∧ inverseOrbit s u (N + 1) ≠ (b : ℂ) := by
        constructor <;> intro he <;> apply hnewi <;> rw [he, Complex.ofReal_im]
      have hnewbound : ‖inverseOrbit s u (N + 1)‖ ≤ 3 * η / 4 := by
        rw [inverseOrbit_succ]
        exact inverseStep_small η s _ hη (by linarith) hs.le hsη hN.2.2.2.1
      have hnewnorm : ‖inverseOrbit s u (N + 1)‖ < η := hnewbound.trans_lt (by linarith)
      have hdall : ∀ k < N + 1, (bandTime a b θ (inverseOrbit s u (k + 1))).re + 3 / 4 ≤
          (bandTime a b θ (inverseOrbit s u k)).re := by
        intro k hk
        rw [inverseOrbit_succ]
        exact inverse_bandTime_re_drift Q η s a b _ hη hηq hηr hs hsη haη hbη ha0 hb0 hfa hfb
          (ih k (by omega)).2.2.2.1 (ih k (by omega)).2.2.1
      have hfinite := finite_inverse_residual_sum A B Γ u s a b θ (Y / 2) M (N + 1)
        hab hθ hθ1 (by linarith) hhalf hratio hM
        (fun k hk => ⟨(ih k (by omega)).1, (ih k (by omega)).2.1⟩)
        (fun k hk => (ih k (by omega)).2.2.2.2)
        (fun k hk => hlocalres _ ((ih k (by omega)).2.2.2.1.trans_lt (by linarith))) hdall
      have hlast : ‖descendedTerm A B Γ 2 (inverseOrbit s u (N + 1)) s 0‖ ≤ 1 := by
        apply (hlocalres _ hnewnorm).trans
        apply (mul_le_mul_of_nonneg_left ?_ hM).trans hMη
        have hdist (r : ℝ) (hr : |r| ≤ η / 8) : ‖inverseOrbit s u (N + 1) - (r : ℂ)‖ ≤ η := by
          have hh := norm_sub_le (inverseOrbit s u (N + 1)) (r : ℂ)
          rw [Complex.norm_real, Real.norm_eq_abs] at hh
          linarith
        have hh := mul_le_mul (hdist a ha) (hdist b hb) (norm_nonneg _) hη.le
        exact (pow_le_pow_left₀ (by positivity) hh 2).trans_eq (by ring)
      have hshift := sum_range_shift (fun k => ‖descendedTerm A B Γ 2 (inverseOrbit s u k) s 0‖) (N + 1)
      simp only [inverseOrbit_zero] at hshift
      have herr : (∑ k ∈ Finset.range (N + 1), ‖descendedTerm A B Γ 2 (inverseOrbit s u (k + 1)) s 0‖) ≤ 2 := by
        linarith only [hshift, hlast, hfinite.trans hE, norm_nonneg (descendedTerm A B Γ 2 u s 0)]
      have hψstep : ∀ k < N + 1,
          lensModel s a b θ e₁ e₂ (inverseOrbit s u (k + 1)) -
            lensModel s a b θ e₁ e₂ (inverseOrbit s u k) + 1 =
              -descendedTerm A B Γ 2 (inverseOrbit s u (k + 1)) s 0 := by
        intro k hk
        rw [inverseOrbit_succ]
        exact hlocalstep _ (ih k (by omega)).2.2.2.1 (ih k (by omega)).2.2.1
      have hphase := inverse_phase_bound (lensModel s a b θ e₁ e₂)
        (fun v => descendedTerm A B Γ 2 v s 0) (bandTime a b θ) s u (N + 1)
        (Real.pi + 2 * P) 2 hψstep herr
        (hlocalphase u (hbase.2.2.2.1.trans_lt (by linarith))) (hlocalphase _ hnewnorm)
      have hnewband : bandTime a b θ (inverseOrbit s u (N + 1)) ∈ strip θ (Y / 2) := by
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

end Kneser.ActualInverseLensBootstrap
end
