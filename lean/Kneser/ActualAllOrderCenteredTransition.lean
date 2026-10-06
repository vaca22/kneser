import Kneser.ActualCenteredGatePacket
import Kneser.AllOrderSingleInverse
import Kneser.ActualTransitionPeriodicity

/-! One actual centered inverse, and all finite expansions of its actual
centered transition.  The original first-order transition and all higher
orbit preparations use the same roots, gate and baseline. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Kneser.ActualAllOrderCenteredTransition

open Filter Set Metric Kneser.ActualBilateralGate Kneser.ActualGateAbel
open Kneser.ActualQuantitativeGateTransition Kneser.ActualHigherFinitePacket
open Kneser.ActualCenteredGatePacket Kneser.AllOrderSingleInverse
open Kneser.AllOrderCompactGate Kneser.CommonQuadraticBaseline
open Kneser.HigherGateIntegerRemainder Kneser.HigherGateTransport
open Kneser.ActualDeepCoordinateData
open scoped Topology

def AllOrders (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (N : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ) : Prop :=
  InverseData (centeredRepelling U H e₁ e₂ A B Γ N Y) V 12 ∧
  ∀ m : ℕ, 1 ≤ m →
    (∃ d : ℕ → ℂ → ℂ, FinitePacket V d m (ball (0 : ℂ) 3)) ∧
    (∃ b : ℕ → ℂ → ℂ, FinitePacket
      (fun s z => centeredAttracting U H e₁ e₂ A B Γ N Y s (V s z)) b m (ball (0 : ℂ) 3))

theorem all_orders_of_actual_data (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Y : ℝ) (N M : ℕ) (Vold : ℝ → ℂ → ℂ)
    (ht : ActualTransitionData U H (first (e 1)) (second (e 1)) A B (Γ 1) R N M Y Vold)
    (hab : AbsoluteIntegerGateExpansions U H A B e Γ N) :
    ∃ V : ℝ → ℂ → ℂ, AllOrders U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y V := by
  let F := centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y
  let Q := centeredAttracting U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y
  let D := fun z => repellingChartCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y z -
    repellingChartCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y 0
  let E := fun z => attractingChartCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y z -
    attractingChartCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y 0
  have hclosed : closedBall (0 : ℂ) 48 ⊆ closedBall (0 : ℂ) 64 :=
    closedBall_subset_closedBall (by norm_num)
  have hFa0 : AnalyticOnNhd ℂ (F 0) (closedBall (0 : ℂ) 48) := by
    intro z hz
    exact (((ht.bilateral.spatial _ (chartPoint_in_gate N Y ht.height z (hclosed hz))).2.2.1.comp_of_eq
      (chartPoint_analytic N Y ht.height z (hclosed hz)) rfl).sub analyticAt_const).sub analyticAt_const
  obtain ⟨hPc, hPg⟩ := chart_compact_gate N Y ht.height
  have hFa : ∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (F s) (closedBall (0 : ℂ) 48) := by
    filter_upwards [ht.bilateral.positive _ hPc hPg] with s hs z hz
    exact (((hs _ (mem_image_of_mem (chartPoint Y) (hclosed hz))).2.comp_of_eq
      (chartPoint_analytic N Y ht.height z (hclosed hz)) rfl).sub analyticAt_const).sub analyticAt_const
  have hquarter : ApproximatesLinearOn (F 0) (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) 24) (1 / 4) := by
    intro x hx y hy
    have hh := Kneser.ActualTransitionPeriodicity.repellingChart_zero_approximates_identity
      U H (first (e 1)) (second (e 1)) A B (Γ 1) R Y N M Vold ht x
      ((ball_subset_ball (by norm_num)) hx) y ((ball_subset_ball (by norm_num)) hy)
    convert hh using 1
    congr 1
    dsimp [F, centeredRepelling]
    ring
  have hpack : ∀ m : ℕ, 1 ≤ m → ∃ c a : ℕ → ℂ → ℂ,
      NormalizedFiniteData F c D m (ball (0 : ℂ) 56) ∧
      NormalizedFiniteData Q a E m (ball (0 : ℂ) 56) := by
    intro m hm
    have hv : chartPoint Y 0 ∈ gate 64 N := chartPoint_in_gate N Y ht.height 0 (by simp)
    obtain ⟨n, L, hp⟩ := exists_packet_of_actual_data U H A B e Γ R N ht.bilateral hab _ hv m hm
    have hpc := centered_packet_of_packet U H A B e Γ N m n L Y ht.height hp
    exact ⟨_, _, hpc.2, hpc.1⟩
  obtain ⟨V, hV, hm⟩ := exists_single_inverse_all_orders F Q D E 12 56 (by norm_num) (by norm_num)
    (by simp [F, centeredRepelling])
    (by convert hquarter using 1 <;> norm_num)
    (by convert hFa0 using 1 <;> norm_num)
    (by convert hFa using 1 <;> norm_num) hpack
  exact ⟨V, hV, by simpa only [show (12 : ℝ) / 4 = 3 by norm_num, Q] using hm⟩

/-- The actual endpoint derives every input, including common preparation,
true gate geometry, orbit coefficients and the single centered inverse. -/
theorem exists_actual_all_order_centered_transition :
    ∃ U H A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F : ℂ × ℂ → ℂ,
    ∃ e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ, ∃ Γ : ℕ → ℂ × ℂ → ℂ,
    ∃ R : ℝ, ∃ N M : ℕ, ∃ Y : ℝ, ∃ Vold V : ℝ → ℂ → ℂ,
      Kneser.ReflectedOrbitChainCoefficient.ActualPreparationData
        U H (first (e 1)) (second (e 1)) A B K F (Γ 1) ∧
      ActualTransitionData U H (first (e 1)) (second (e 1)) A B (Γ 1) R N M Y Vold ∧
      AbsoluteIntegerGateExpansions U H A B e Γ N ∧
      AllOrders U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y V := by
  obtain ⟨U, H, A, B, K, F, e, Γ, hdata, hprep, _ha, _hr, _hca, _hcr⟩ :=
    Kneser.ActualBilateralHigherPreparation.exists_actual_bilateral_common_all_orders
  obtain ⟨Rl, _hRl, hl⟩ := local_abel_data_of_actual U H (first (e 1)) (second (e 1)) A B K F (Γ 1) hdata
  obtain ⟨Rp, hRp, hp⟩ := exists_actual_gate_spatial_data U H A B K F e Γ hdata
  obtain ⟨Rd, hd⟩ := Kneser.ActualBaselineDeep.deep_data_of_actual
    U H (first (e 1)) (second (e 1)) A B K F (Γ 1) hdata
  let R := max Rp (max Rl Rd)
  have hR : 64 ≤ R := hRp.trans (le_max_left _ _)
  have hlocal : LocalAbelData U H (first (e 1)) (second (e 1)) A B (Γ 1) R :=
    hl.mono ((le_max_left Rl Rd).trans (le_max_right Rp (max Rl Rd)))
  have hdeep : DeepCoordinateData U H (first (e 1)) (second (e 1)) A B (Γ 1) R :=
    hd.mono ((le_max_right Rl Rd).trans (le_max_right _ _))
  obtain ⟨N, M, Y, Vold, ht⟩ := exists_transition_data_of_deep
    U H (first (e 1)) (second (e 1)) A B (Γ 1) R hdeep
  have hN : R + 64 + 4 ≤ 3 * (N : ℝ) / 4 := by linarith [ht.length_margin]
  have hfinite := fixedGateAllFiniteExpansions_of_actual U H A B K F e Γ hdata hprep R hR hlocal N hN
  have hregular := hp R (le_max_left _ _) N hN
  have hab := absoluteIntegerGateExpansions_of_regular U H A B e Γ N hfinite hregular
  obtain ⟨V, hV⟩ := all_orders_of_actual_data U H A B e Γ R Y N M Vold ht hab
  exact ⟨U, H, A, B, K, F, e, Γ, R, N, M, Y, Vold, V, hdata, ht, hab, hV⟩

end Kneser.ActualAllOrderCenteredTransition
