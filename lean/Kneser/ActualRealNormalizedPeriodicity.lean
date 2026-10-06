import Kneser.ActualRealNormalizedTransition
import Kneser.ActualTransitionPeriodicity

/-! The same centered inverse and actual real-anchor transition used at
all orders satisfy the true Fatou translation law.  The next orbit point
and source injectivity are obtained from the actual chart geometry. -/

set_option autoImplicit false
noncomputable section
namespace Kneser.ActualRealNormalizedPeriodicity

open Filter Set Metric Kneser.ActualRealNormalizedTransition
open Kneser.ActualCenteredGatePacket Kneser.AllOrderSingleInverse
open Kneser.ActualQuantitativeGateTransition Kneser.ActualBilateralGate
open Kneser.ActualGateAbel Kneser.ActualTransitionPeriodicity
open Kneser.CommonQuadraticBaseline Kneser.StableHolomorphicInverse
open scoped Topology

theorem inner_ball_three (w : ℂ) (hw : w ∈ ball (0 : ℂ) 2) :
    w ∈ ball (0 : ℂ) 3 ∧ w + 1 ∈ ball (0 : ℂ) 3 := by
  have hn : ‖w‖ < 2 := by simpa only [mem_ball, dist_zero_right] using hw
  have ht := norm_add_le w (1 : ℂ)
  rw [norm_one] at ht
  constructor <;> simp only [mem_ball, dist_zero_right] <;> linarith

theorem affine_injective (f : ℂ → ℂ)
    (hf : ApproximatesLinearOn f (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * 12)) (1 / 2)) : InjOn f (ball (0 : ℂ) 24) := by
  intro x hx y hy he
  have hh := norm_sub_le_two_mul_norm_image_sub f 12 hf x y
    (by simpa only [show (2 : ℝ) * 12 = 24 by norm_num] using hx)
    (by simpa only [show (2 : ℝ) * 12 = 24 by norm_num] using hy)
  rw [he, sub_self, norm_zero, mul_zero] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

theorem translation_of_centered_abel (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ) (s : ℝ)
    (hInv : ∀ w ∈ ball (0 : ℂ) 3, V s w ∈ closedBall (0 : ℂ) 12 ∧
      centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y s (V s w) = w)
    (hInj : InjOn (centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y s)
      (ball (0 : ℂ) 24))
    (hnext : ∀ z ∈ closedBall (0 : ℂ) 12,
      Kneser.ActualGateNextImage.translatedStep Y s z ∈ ball (0 : ℂ) 24)
    (hAbel : ∀ z ∈ closedBall (0 : ℂ) 12,
      forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N
        (Kneser.ExponentialUnfolding.unfolding s (chartPoint Y z)) s =
        forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N (chartPoint Y z) s + 1 ∧
      backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N
        (Kneser.ExponentialUnfolding.unfolding s (chartPoint Y z)) s =
        backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N (chartPoint Y z) s + 1) :
    ∀ w ∈ ball (0 : ℂ) 2,
      transition U H A B e Γ N M Y V s (w + 1) = transition U H A B e Γ N M Y V s w + 1 := by
  intro w hw
  obtain ⟨hw3, hw13⟩ := inner_ball_three w hw
  have hz := (hInv w hw3).1
  have hz1 := (hInv (w + 1) hw13).1
  have ha := hAbel _ hz
  have hstep := Kneser.ActualGateNextImage.translatedStep_chart_identity Y s (V s w)
  change Kneser.ExponentialUnfolding.unfolding s (chartPoint Y (V s w)) =
    chartPoint Y (Kneser.ActualGateNextImage.translatedStep Y s (V s w)) at hstep
  have hS : centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y s
      (Kneser.ActualGateNextImage.translatedStep Y s (V s w)) =
      centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y s (V s w) + 1 := by
    dsimp only [centeredRepelling, repellingChart]
    rw [← hstep, ha.2]
    ring
  have hz1b : V s (w + 1) ∈ ball (0 : ℂ) 24 :=
    (show dist (V s (w + 1)) 0 ≤ 12 from hz1).trans_lt (by norm_num)
  have he : V s (w + 1) = Kneser.ActualGateNextImage.translatedStep Y s (V s w) := by
    apply hInj hz1b (hnext _ hz)
    rw [(hInv (w + 1) hw13).2, hS, (hInv w hw3).2]
  dsimp only [transition, Kneser.ActualRealAnchorHigherGate.normalizedCoordinate]
  rw [he, ← hstep, ha.1]
  ring

theorem eventually_transition_translation (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R : ℝ) (N M M₀ : ℕ) (Y : ℝ) (Vold V : ℝ → ℂ → ℂ)
    (ht : ActualTransitionData U H (first (e 1)) (second (e 1)) A B (Γ 1) R N M₀ Y Vold)
    (hR : 64 ≤ R) (hl : LocalAbelData U H (first (e 1)) (second (e 1)) A B (Γ 1) R)
    (hv : InverseData (centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y) V 12) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ w ∈ ball (0 : ℂ) 2,
      transition U H A B e Γ N M Y V s (w + 1) = transition U H A B e Γ N M Y V s w + 1 := by
  obtain ⟨n, hN, hlen⟩ := pred_gate_length R N hR ht.length_margin
  have hAbel : CompactGateAbel U H (first (e 1)) (second (e 1)) A B (Γ 1) 64 N := by
    rw [hN]
    exact gate_abel_of_local_data U H (first (e 1)) (second (e 1)) A B (Γ 1) R 64 hl n hlen
  obtain ⟨hPc, hPg⟩ := chart_compact_gate N Y ht.height
  have hnext := Kneser.ActualGateNextImage.eventually_translatedStep_mem_ball_twentyFour
    N (64 * ((N : ℝ) + 1)) Y le_rfl ht.height
  filter_upwards [hv.2.2.1, hv.2.2.2.2.1, hnext, hAbel _ hPc hPg] with s hs hf hn ha
  apply translation_of_centered_abel U H A B e Γ N M Y V s
    (by simpa only [show (12 : ℝ) / 4 = 3 by norm_num] using hs.1) (affine_injective _ hf)
  · intro z hz
    exact (hn z (closedBall_subset_closedBall (by norm_num) hz)).1
  · intro z hz
    exact ha _ (mem_image_of_mem (chartPoint Y) (closedBall_subset_closedBall (by norm_num) hz))

theorem transition_zero_translation (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R : ℝ) (N M M₀ : ℕ) (Y : ℝ) (Vold V : ℝ → ℂ → ℂ)
    (ht : ActualTransitionData U H (first (e 1)) (second (e 1)) A B (Γ 1) R N M₀ Y Vold)
    (hR : 64 ≤ R) (hl : LocalAbelData U H (first (e 1)) (second (e 1)) A B (Γ 1) R)
    (hv : InverseData (centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y) V 12) :
    ∀ w ∈ ball (0 : ℂ) 2,
      transition U H A B e Γ N M Y V 0 (w + 1) = transition U H A B e Γ N M Y V 0 w + 1 := by
  obtain ⟨n, hN, hlen⟩ := pred_gate_length R N hR ht.length_margin
  have hAbel : ∀ u ∈ gate 64 N,
      forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N
        (Kneser.ExponentialUnfolding.unfolding 0 u) 0 =
        forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u 0 + 1 ∧
      backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N
        (Kneser.ExponentialUnfolding.unfolding 0 u) 0 =
        backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u 0 + 1 := by
    rw [hN]
    exact gate_zero_abel_of_local_data U H (first (e 1)) (second (e 1)) A B (Γ 1) R 64 hl n hlen
  apply translation_of_centered_abel U H A B e Γ N M Y V 0
    (by simpa only [show (12 : ℝ) / 4 = 3 by norm_num] using hv.1)
    (affine_injective _ hv.2.2.2.1)
  · intro z hz
    exact ball_subset_ball (by norm_num : (18 : ℝ) ≤ 24)
      (Kneser.ActualGateNextImage.translatedStep_zero_mem_ball_eighteen N
        (64 * ((N : ℝ) + 1)) Y le_rfl ht.height z (closedBall_subset_closedBall (by norm_num) hz))
  · intro z hz
    exact hAbel _ (chartPoint_in_gate N Y ht.height z (closedBall_subset_closedBall (by norm_num) hz))

end Kneser.ActualRealNormalizedPeriodicity
