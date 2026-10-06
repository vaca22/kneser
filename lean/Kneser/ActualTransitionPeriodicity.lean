import Kneser.ActualQuantitativeGateTransition
import Kneser.ActualGateNextImage

/-!
The actual moving transition has the Fatou translation law.  Injectivity
comes from the true compact coordinate expansion and a Cauchy derivative
estimate; the actual next orbit point remains in the same source chart.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.ActualTransitionPeriodicity

open Filter Set Metric Kneser.ActualQuantitativeGateTransition
open Kneser.ActualBilateralGate Kneser.ActualDeepCoordinateData Kneser.ActualGateAbel
open Kneser.FullCanonicalImageGate Kneser.StableHolomorphicInverse
open scoped Topology

theorem closed_mono (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 16) :
    z ∈ closedBall (0 : ℂ) 64 := closedBall_subset_closedBall (by norm_num) hz

theorem repellingChart_zero_eq
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R Y : ℝ) (N M : ℕ)
    (V : ℝ → ℂ → ℂ) (ht : ActualTransitionData U H e₁ e₂ A B Γ R N M Y V)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 64) :
    repellingChart U H e₁ e₂ A B Γ N Y 0 z =
      canonicalGateInZeta N (chartCenter Y + z) - canonicalGateInZeta N (chartCenter Y) := by
  have h := (ht.bilateral.canonical _ (chartPoint_in_gate N Y ht.height z hz)).2
  dsimp only [repellingChart]
  rw [h, canonicalGateInZeta_eq N (chartCenter Y + z)]
  rfl

theorem repellingChart_zero_approximates_identity
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R Y : ℝ) (N M : ℕ)
    (V : ℝ → ℂ → ℂ) (ht : ActualTransitionData U H e₁ e₂ A B Γ R N M Y V) :
    ApproximatesLinearOn (repellingChart U H e₁ e₂ A B Γ N Y 0)
      (ContinuousLinearMap.id ℂ ℂ) (ball (0 : ℂ) 32) (1 / 4) := by
  let F := repellingChart U H e₁ e₂ A B Γ N Y 0
  apply approximation_of_deriv_bound F
  · intro z hz
    have hz64 : z ∈ closedBall (0 : ℂ) 64 :=
      (ball_subset_closedBall hz) |> closedBall_subset_closedBall (by norm_num)
    exact ((ht.bilateral.spatial _ (chartPoint_in_gate N Y ht.height z hz64)).2.2.1.comp_of_eq
      (chartPoint_analytic N Y ht.height z hz64) rfl).sub analyticAt_const
  · intro z hz
    have hz' : chartCenter Y + z ∈ ball (chartCenter Y) 32 := by
      simpa [mem_ball, dist_eq_norm] using hz
    have heq : F =ᶠ[𝓝 z] (fun w => canonicalGateInZeta N (chartCenter Y + w) -
        canonicalGateInZeta N (chartCenter Y)) := by
      have hn : ∀ᶠ w in 𝓝 z, w ∈ ball (0 : ℂ) 32 := isOpen_ball.mem_nhds hz
      exact hn.mono fun w hw => repellingChart_zero_eq U H e₁ e₂ A B Γ R Y N M V ht w
        ((ball_subset_closedBall hw) |> closedBall_subset_closedBall (by norm_num))
    have hd := (((ht.geometry _ hz').1.hasStrictDerivAt.hasDerivAt.comp z
      ((hasDerivAt_id z).const_add (chartCenter Y))).sub_const (canonicalGateInZeta N (chartCenter Y))).deriv
    simp only [Function.comp_def, mul_one] at hd
    rw [heq.deriv_eq, hd]
    exact (ht.geometry _ hz').2

/-- Uniform coordinate convergence and genuine Cauchy estimates force the
moving repelling chart to be injective on the entire larger source disc. -/
theorem eventually_repellingChart_approximates_identity
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R Y : ℝ) (N M : ℕ)
    (V : ℝ → ℂ → ℂ) (ht : ActualTransitionData U H e₁ e₂ A B Γ R N M Y V) :
    ∀ᶠ s : ℝ in 𝓝[>] 0,
      ApproximatesLinearOn (repellingChart U H e₁ e₂ A B Γ N Y s)
        (ContinuousLinearMap.id ℂ ℂ) (ball (0 : ℂ) 32) (1 / 2) := by
  let F := repellingChart U H e₁ e₂ A B Γ N Y
  let D := repellingChartCoefficient U H e₁ e₂ A B Γ N Y
  have ha0 : AnalyticOnNhd ℂ (F 0) (closedBall (0 : ℂ) 64) := by
    intro z hz
    exact ((ht.bilateral.spatial _ (chartPoint_in_gate N Y ht.height z hz)).2.2.1.comp_of_eq
      (chartPoint_analytic N Y ht.height z hz) rfl).sub analyticAt_const
  have hDa : AnalyticOnNhd ℂ D (closedBall (0 : ℂ) 64) := by
    intro z hz
    exact (ht.bilateral.coefficient _ (chartPoint_in_gate N Y ht.height z hz)).2.comp_of_eq
      (chartPoint_analytic N Y ht.height z hz) rfl
  obtain ⟨MD, hMD⟩ := (isCompact_closedBall (0 : ℂ) 64).exists_bound_of_continuousOn hDa.continuousOn
  obtain ⟨hPc, hPg⟩ := chart_compact_gate N Y ht.height
  obtain ⟨C, hC, hU⟩ := ht.bilateral.uniform _ hPc hPg
  let K : ℝ := max MD 0 + C
  have hFa : ∀ᶠ s : ℝ in 𝓝[>] 0, DiffContOnCl ℂ (F s) (ball (0 : ℂ) 64) := by
    filter_upwards [ht.bilateral.positive _ hPc hPg] with s hs
    have ha : AnalyticOnNhd ℂ (F s) (closedBall (0 : ℂ) 64) := by
      intro z hz
      exact ((hs _ (mem_image_of_mem (chartPoint Y) hz)).2.comp_of_eq
        (chartPoint_analytic N Y ht.height z hz) rfl).sub analyticAt_const
    exact ha.differentiableOn.mono closure_ball_subset_closedBall |>.diffContOnCl
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ h => h.le).filter_mono nhdsWithin_le_nhds
  have hlim : Tendsto (fun s : ℝ => K * s) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (fun s : ℝ => s) (𝓝 (0 : ℝ)) (𝓝 0)).const_mul K).mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, K * s ≤ 4 :=
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 4))).mono fun _ h => h.le
  filter_upwards [hFa, hU, hpos, hle, hsmall] with s hs hu hsp hs1 hks
  suffices hh : ApproximatesLinearOn (F s) (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * 16)) (1 / 2) by
    simpa only [show (2 : ℝ) * 16 = 32 by norm_num, F] using hh
  apply approximates_identity_of_disc_error (F 0) (F s) 16 (K * s) (by norm_num)
    (by simpa only [show (2 : ℝ) * 16 = 32 by norm_num] using
      repellingChart_zero_approximates_identity U H e₁ e₂ A B Γ R Y N M V ht)
  · have hh := hs.sub (ha0.differentiableOn.mono closure_ball_subset_closedBall |>.diffContOnCl)
    convert hh using 1 <;> norm_num
    funext w
    rfl
  · intro z hz
    have hz64 : z ∈ closedBall (0 : ℂ) 64 := by
      simpa only [show (4 : ℝ) * 16 = 64 by norm_num] using hz
    have he : ‖F s z - F 0 z - (s : ℂ) * D z‖ ≤ C * s ^ (6 / 5 : ℝ) := by
      convert (hu _ (mem_image_of_mem (chartPoint Y) hz64)).2 using 1
      congr 1
      dsimp [F, D, repellingChart, repellingChartCoefficient]
      ring
    have hp : s ^ (6 / 5 : ℝ) ≤ s := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hsp hs1 (by norm_num : (1 : ℝ) ≤ 6 / 5)
    have hd : ‖D z‖ ≤ max MD 0 := (hMD z hz64).trans (le_max_left _ _)
    have heq : F s z - F 0 z = (F s z - F 0 z - (s : ℂ) * D z) + (s : ℂ) * D z := by ring
    rw [heq]
    calc
      _ ≤ ‖F s z - F 0 z - (s : ℂ) * D z‖ + ‖(s : ℂ) * D z‖ := norm_add_le _ _
      _ ≤ C * s ^ (6 / 5 : ℝ) + s * max MD 0 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsp]
        exact add_le_add he (mul_le_mul_of_nonneg_left hd hsp.le)
      _ ≤ K * s := by dsimp [K]; nlinarith [mul_le_mul_of_nonneg_left hp hC]
  · norm_num; exact hks

theorem eventually_repellingChart_injective
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R Y : ℝ) (N M : ℕ)
    (V : ℝ → ℂ → ℂ) (ht : ActualTransitionData U H e₁ e₂ A B Γ R N M Y V) :
    ∀ᶠ s : ℝ in 𝓝[>] 0,
      InjOn (repellingChart U H e₁ e₂ A B Γ N Y s) (ball (0 : ℂ) 32) := by
  filter_upwards [eventually_repellingChart_approximates_identity U H e₁ e₂ A B Γ R Y N M V ht] with s hs
  intro x hx y hy heq
  have h := norm_sub_le_two_mul_norm_image_sub _ 16 (by
    simpa only [show (2 : ℝ) * 16 = 32 by norm_num] using hs) x y
    (by simpa only [show (2 : ℝ) * 16 = 32 by norm_num] using hx)
    (by simpa only [show (2 : ℝ) * 16 = 32 by norm_num] using hy)
  rw [heq, sub_self, norm_zero, mul_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

theorem inner_ball_mem (w : ℂ) (hw : w ∈ ball (0 : ℂ) 2) :
    w ∈ ball (0 : ℂ) 4 ∧ w + 1 ∈ ball (0 : ℂ) 4 := by
  have hn : ‖w‖ < 2 := by simpa only [mem_ball, dist_zero_right] using hw
  have h := norm_add_le w (1 : ℂ)
  rw [norm_one] at h
  constructor <;> simp only [mem_ball, dist_zero_right] <;> linarith

theorem source_ball_mem (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 16) :
    z ∈ ball (0 : ℂ) 32 := by
  have hn : ‖z‖ ≤ 16 := by simpa only [mem_closedBall, dist_zero_right] using hz
  simp only [mem_ball, dist_zero_right]; linarith

/-- Algebraic identification on the actual source chart; its inverse and
next-image hypotheses are discharged by the actual existence theorems below. -/
theorem translation_of_chart_abel
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N M : ℕ) (Y : ℝ)
    (V : ℝ → ℂ → ℂ) (s : ℝ)
    (hInv : ∀ w ∈ ball (0 : ℂ) 4, V s w ∈ closedBall (0 : ℂ) 16 ∧
      repellingChart U H e₁ e₂ A B Γ N Y s (V s w) = w)
    (hInj : InjOn (repellingChart U H e₁ e₂ A B Γ N Y s) (ball (0 : ℂ) 32))
    (hnext : ∀ z ∈ closedBall (0 : ℂ) 16,
      ActualGateNextImage.translatedStep Y (s : ℂ) z ∈ ball (0 : ℂ) 32)
    (hAbel : ∀ z ∈ closedBall (0 : ℂ) 16,
      forwardCoordinate U H e₁ e₂ A B Γ N (ExponentialUnfolding.unfolding s (chartPoint Y z)) s =
        forwardCoordinate U H e₁ e₂ A B Γ N (chartPoint Y z) s + 1 ∧
      backwardCoordinate U H e₁ e₂ A B Γ N (ExponentialUnfolding.unfolding s (chartPoint Y z)) s =
        backwardCoordinate U H e₁ e₂ A B Γ N (chartPoint Y z) s + 1) :
    ∀ w ∈ ball (0 : ℂ) 2,
      transitionValue U H e₁ e₂ A B Γ N M Y V s (w + 1) =
        transitionValue U H e₁ e₂ A B Γ N M Y V s w + 1 ∧
      transitionValue U H e₁ e₂ A B Γ N M Y V s (w + 1) - (w + 1) =
        transitionValue U H e₁ e₂ A B Γ N M Y V s w - w := by
  intro w hw
  obtain ⟨hw4, hw14⟩ := inner_ball_mem w hw
  have hz := (hInv w hw4).1
  have hz1 := (hInv (w + 1) hw14).1
  have ha := hAbel _ hz
  have hstep : ExponentialUnfolding.unfolding s (chartPoint Y (V s w)) =
      chartPoint Y (ActualGateNextImage.translatedStep Y s (V s w)) :=
    ActualGateNextImage.translatedStep_chart_identity Y s (V s w)
  have hP : attractingChart U H e₁ e₂ A B Γ N Y s
      (ActualGateNextImage.translatedStep Y s (V s w)) =
      attractingChart U H e₁ e₂ A B Γ N Y s (V s w) + 1 := by
    dsimp only [attractingChart]
    rw [← hstep]
    exact ha.1
  have hS : repellingChart U H e₁ e₂ A B Γ N Y s
      (ActualGateNextImage.translatedStep Y s (V s w)) =
      repellingChart U H e₁ e₂ A B Γ N Y s (V s w) + 1 := by
    dsimp only [repellingChart]
    rw [← hstep, ha.2]
    ring
  have he : V s (w + 1) = ActualGateNextImage.translatedStep Y s (V s w) := by
    apply hInj (source_ball_mem _ hz1) (hnext _ hz)
    rw [(hInv (w + 1) hw14).2, hS, (hInv w hw4).2]
  have ht : transitionValue U H e₁ e₂ A B Γ N M Y V s (w + 1) =
      transitionValue U H e₁ e₂ A B Γ N M Y V s w + 1 := by
    dsimp only [transitionValue]
    rw [he, hP]
    ring
  exact ⟨ht, by rw [ht]; ring⟩

theorem pred_gate_length
    (R : ℝ) (N : ℕ) (hR : 64 ≤ R) (hmargin : R + 72 ≤ 3 * (N : ℝ) / 4) :
    ∃ n : ℕ, N = n + 1 ∧ R + 64 + 4 ≤ 3 * (n : ℝ) / 4 := by
  have hN : 1 ≤ N := by
    by_contra hh
    have hzero : N = 0 := by omega
    rw [hzero] at hmargin
    norm_num at hmargin
    linarith
  refine ⟨N - 1, (Nat.sub_add_cancel hN).symm, ?_⟩
  have hc : (N : ℝ) = ((N - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel hN).symm
  linarith

theorem repellingChart_zero_injective
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R Y : ℝ) (N M : ℕ)
    (V : ℝ → ℂ → ℂ) (ht : ActualTransitionData U H e₁ e₂ A B Γ R N M Y V) :
    InjOn (repellingChart U H e₁ e₂ A B Γ N Y 0) (ball (0 : ℂ) 32) := by
  have hquarter := repellingChart_zero_approximates_identity U H e₁ e₂ A B Γ R Y N M V ht
  have hhalf : ApproximatesLinearOn (repellingChart U H e₁ e₂ A B Γ N Y 0)
      (ContinuousLinearMap.id ℂ ℂ) (ball (0 : ℂ) (2 * 16)) (1 / 2) := by
    intro x hx y hy
    have h := hquarter x (by simpa only [show (2 : ℝ) * 16 = 32 by norm_num] using hx)
      y (by simpa only [show (2 : ℝ) * 16 = 32 by norm_num] using hy)
    norm_num at h ⊢
    nlinarith [norm_nonneg (x - y)]
  intro x hx y hy he
  have h := norm_sub_le_two_mul_norm_image_sub _ 16 hhalf x y
    (by simpa only [show (2 : ℝ) * 16 = 32 by norm_num] using hx)
    (by simpa only [show (2 : ℝ) * 16 = 32 by norm_num] using hy)
  rw [he, sub_self, norm_zero, mul_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

/-- The moving actual horn transition has translation law and periodic
displacement on a common image neighborhood containing the Fourier segment. -/
theorem eventually_transition_translation
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R Y : ℝ) (N M : ℕ)
    (V : ℝ → ℂ → ℂ) (ht : ActualTransitionData U H e₁ e₂ A B Γ R N M Y V)
    (hR : 64 ≤ R) (hl : LocalAbelData U H e₁ e₂ A B Γ R) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ w ∈ ball (0 : ℂ) 2,
      transitionValue U H e₁ e₂ A B Γ N M Y V s (w + 1) =
        transitionValue U H e₁ e₂ A B Γ N M Y V s w + 1 ∧
      transitionValue U H e₁ e₂ A B Γ N M Y V s (w + 1) - (w + 1) =
        transitionValue U H e₁ e₂ A B Γ N M Y V s w - w := by
  obtain ⟨n, hN, hlen⟩ := pred_gate_length R N hR ht.length_margin
  have hAbel : CompactGateAbel U H e₁ e₂ A B Γ 64 N := by
    rw [hN]
    exact gate_abel_of_local_data U H e₁ e₂ A B Γ R 64 hl n hlen
  obtain ⟨hPc, hPg⟩ := chart_compact_gate N Y ht.height
  have hnext := ActualGateNextImage.eventually_translatedStep_mem_ball_twentyFour
    N (64 * ((N : ℝ) + 1)) Y le_rfl ht.height
  filter_upwards [ht.inverse_positive,
    eventually_repellingChart_injective U H e₁ e₂ A B Γ R Y N M V ht,
    hnext, hAbel _ hPc hPg] with s hs hinj hstep ha
  apply translation_of_chart_abel U H e₁ e₂ A B Γ N M Y V s hs.1 hinj
  · intro z hz
    exact ball_subset_ball (by norm_num : (24 : ℝ) ≤ 32) (hstep z hz).1
  · intro z hz
    exact ha _ (mem_image_of_mem (chartPoint Y) (closed_mono z hz))

theorem transition_zero_translation
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R Y : ℝ) (N M : ℕ)
    (V : ℝ → ℂ → ℂ) (ht : ActualTransitionData U H e₁ e₂ A B Γ R N M Y V)
    (hR : 64 ≤ R) (hl : LocalAbelData U H e₁ e₂ A B Γ R) :
    ∀ w ∈ ball (0 : ℂ) 2,
      transitionValue U H e₁ e₂ A B Γ N M Y V 0 (w + 1) =
        transitionValue U H e₁ e₂ A B Γ N M Y V 0 w + 1 ∧
      transitionValue U H e₁ e₂ A B Γ N M Y V 0 (w + 1) - (w + 1) =
        transitionValue U H e₁ e₂ A B Γ N M Y V 0 w - w := by
  obtain ⟨n, hN, hlen⟩ := pred_gate_length R N hR ht.length_margin
  have hAbel : ∀ u ∈ gate 64 N,
      forwardCoordinate U H e₁ e₂ A B Γ N (ExponentialUnfolding.unfolding 0 u) 0 =
        forwardCoordinate U H e₁ e₂ A B Γ N u 0 + 1 ∧
      backwardCoordinate U H e₁ e₂ A B Γ N (ExponentialUnfolding.unfolding 0 u) 0 =
        backwardCoordinate U H e₁ e₂ A B Γ N u 0 + 1 := by
    rw [hN]
    exact gate_zero_abel_of_local_data U H e₁ e₂ A B Γ R 64 hl n hlen
  apply translation_of_chart_abel U H e₁ e₂ A B Γ N M Y V 0 ht.inverse_zero
    (repellingChart_zero_injective U H e₁ e₂ A B Γ R Y N M V ht)
  · intro z hz
    exact ball_subset_ball (by norm_num : (18 : ℝ) ≤ 32)
      (ActualGateNextImage.translatedStep_zero_mem_ball_eighteen N
        (64 * ((N : ℝ) + 1)) Y le_rfl ht.height z hz)
  · intro z hz
    exact hAbel _ (chartPoint_in_gate N Y ht.height z (closed_mono z hz))

/-- The explicit first-order correction is itself periodic, by uniqueness
of the actual one-sided derivative and the proved moving translation law. -/
theorem correction_periodic
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R Y : ℝ) (N M : ℕ)
    (V : ℝ → ℂ → ℂ) (ht : ActualTransitionData U H e₁ e₂ A B Γ R N M Y V)
    (hR : 64 ≤ R) (hl : LocalAbelData U H e₁ e₂ A B Γ R) :
    ∀ w ∈ ball (0 : ℂ) 2,
      transitionCorrection U H e₁ e₂ A B Γ N M Y V (w + 1) =
        transitionCorrection U H e₁ e₂ A B Γ N M Y V w := by
  intro w hw
  obtain ⟨hw4, hw14⟩ := inner_ball_mem w hw
  let T := transitionValue U H e₁ e₂ A B Γ N M Y V
  let D := transitionCorrection U H e₁ e₂ A B Γ N M Y V
  obtain ⟨C, hC, hU⟩ := ht.uniform
  have hleft : QuantitativeHornExpansion.PowerExpansion (fun s => T s (w + 1)) (D (w + 1)) (6 / 5) :=
    ⟨C, hC, hU.mono fun s hs => hs _ hw14⟩
  have hright : QuantitativeHornExpansion.PowerExpansion (fun s => T s w) (D w) (6 / 5) :=
    ⟨C, hC, hU.mono fun s hs => hs _ hw4⟩
  have heq : (fun s : ℝ => T s (w + 1)) =ᶠ[𝓝[>] 0] (fun s => T s w + 1) :=
    (eventually_transition_translation U H e₁ e₂ A B Γ R Y N M V ht hR hl).mono
      fun s hs => (hs w hw).1
  have heq0 : T 0 (w + 1) = T 0 w + 1 :=
    (transition_zero_translation U H e₁ e₂ A B Γ R Y N M V ht hR hl w hw).1
  have hdl := (hleft.hasDerivWithinAt (by norm_num : (1 : ℝ) < 6 / 5)).mono Ioi_subset_Ici_self
  have hdr := ((hright.hasDerivWithinAt (by norm_num : (1 : ℝ) < 6 / 5)).add_const 1).mono Ioi_subset_Ici_self
  have hdr' := hdr.congr_of_eventuallyEq heq heq0
  calc
    D (w + 1) = derivWithin (fun s => T s (w + 1)) (Ioi 0) 0 :=
      (hdl.derivWithin (uniqueDiffWithinAt_Ioi 0)).symm
    _ = D w := hdr'.derivWithin (uniqueDiffWithinAt_Ioi 0)

/-- The reciprocal chart chain factor cancels in the correction, leaving
exactly the physical-coordinate variation and spatial Jacobian ratio. -/
theorem transitionCorrection_eq_physical
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R Y : ℝ) (N M : ℕ)
    (V : ℝ → ℂ → ℂ) (ht : ActualTransitionData U H e₁ e₂ A B Γ R N M Y V)
    (w : ℂ) (hw : w ∈ ball (0 : ℂ) 4) :
    transitionCorrection U H e₁ e₂ A B Γ N M Y V w =
      forwardCoefficient U H e₁ e₂ A B Γ N (chartPoint Y (V 0 w)) -
        ActualNormalizationAnchorExpansion.anchorCoefficient U H e₁ e₂ A B Γ M -
        (deriv (fun u => forwardCoordinate U H e₁ e₂ A B Γ N u 0) (chartPoint Y (V 0 w)) /
          deriv (fun u => backwardCoordinate U H e₁ e₂ A B Γ N u 0) (chartPoint Y (V 0 w))) *
            backwardCoefficient U H e₁ e₂ A B Γ N (chartPoint Y (V 0 w)) := by
  have hratio := (chart_derivative_ratio U H e₁ e₂ A B Γ R Y N ht.bilateral ht.height
    (V 0 w) (closed_mono _ (ht.inverse_zero w hw).1)).2
  dsimp only [transitionCorrection, attractingChartCoefficient, repellingChartCoefficient]
  rw [hratio]
  ring

end Kneser.ActualTransitionPeriodicity

end
