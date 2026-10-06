import Kneser.AllOrderCompactGate
import Kneser.ActualHigherFinitePacket

/-! A single genuine inverse family serves every finite Taylor order.
Only spatial coordinate packets, holomorphy and an actual affine bound
are inputs; all inverse and transition expansions are conclusions. -/

set_option autoImplicit false
noncomputable section
namespace Kneser.AllOrderSingleInverse

open Filter Set Metric Kneser.ActualHigherFinitePacket
open Kneser.FiniteExpansionHolomorphy Kneser.StableHolomorphicInverse
open Kneser.AllOrderCompactGate
open scoped Topology

def InverseData (F V : ℝ → ℂ → ℂ) (r : ℝ) : Prop :=
  (∀ z ∈ ball (0 : ℂ) (r / 4), V 0 z ∈ closedBall (0 : ℂ) r ∧ F 0 (V 0 z) = z) ∧
  AnalyticOnNhd ℂ (V 0) (ball (0 : ℂ) (r / 4)) ∧
  (∀ᶠ s : ℝ in 𝓝[>] 0,
    (∀ z ∈ ball (0 : ℂ) (r / 4), V s z ∈ closedBall (0 : ℂ) r ∧ F s (V s z) = z) ∧
    AnalyticOnNhd ℂ (V s) (ball (0 : ℂ) (r / 4))) ∧
  ApproximatesLinearOn (F 0) (ContinuousLinearMap.id ℂ ℂ) (ball (0 : ℂ) (2 * r)) (1 / 2) ∧
  (∀ᶠ s : ℝ in 𝓝[>] 0, ApproximatesLinearOn (F s) (ContinuousLinearMap.id ℂ ℂ)
    (ball (0 : ℂ) (2 * r)) (1 / 2)) ∧
  AnalyticOnNhd ℂ (F 0) (ball (0 : ℂ) (2 * r))

theorem exists_single_inverse_all_orders (F A : ℝ → ℂ → ℂ) (D E : ℂ → ℂ)
    (r R : ℝ) (hr : 0 < r) (hR : 4 * r < R)
    (h00 : F 0 0 = 0)
    (hF0 : ApproximatesLinearOn (F 0) (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * r)) (1 / 4))
    (ha0 : AnalyticOnNhd ℂ (F 0) (closedBall (0 : ℂ) (4 * r)))
    (ha : ∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (F s) (closedBall (0 : ℂ) (4 * r)))
    (hpack : ∀ m : ℕ, 1 ≤ m → ∃ c a : ℕ → ℂ → ℂ,
      NormalizedFiniteData F c D m (ball (0 : ℂ) R) ∧
      NormalizedFiniteData A a E m (ball (0 : ℂ) R)) :
    ∃ V : ℝ → ℂ → ℂ, InverseData F V r ∧
      (∀ m : ℕ, 1 ≤ m →
        (∃ d : ℕ → ℂ → ℂ, FinitePacket V d m (ball (0 : ℂ) (r / 4))) ∧
        (∃ b : ℕ → ℂ → ℂ, FinitePacket (fun s z => A s (V s z)) b m
          (ball (0 : ℂ) (r / 4)))) := by
  have hsub : closedBall (0 : ℂ) (4 * r) ⊆ ball (0 : ℂ) R := by
    intro z hz
    exact (show dist z 0 ≤ 4 * r from hz).trans_lt hR
  obtain ⟨c₁, _a₁, hc₁, _ha₁⟩ := hpack 1 (by omega)
  obtain ⟨C₀, _hC₀, hlin⟩ := hc₁.2.2 0 (by omega)
    (closedBall (0 : ℂ) (4 * r)) (isCompact_closedBall _ _) hsub
  have hlin' : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ closedBall (0 : ℂ) (4 * r),
      ‖F s u - F 0 u‖ ≤ C₀ * s := by
    filter_upwards [hlin] with s hs u hu
    simpa only [complexPolynomial, zero_add, Finset.sum_range_one, pow_zero, one_mul,
      (hc₁.2.1 u (hsub hu)).1, pow_one] using hs u hu
  have hlim : Tendsto (fun s : ℝ => C₀ * s) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (fun s : ℝ => s) (𝓝 (0 : ℝ)) (𝓝 0)).const_mul C₀).mono_left
      nhdsWithin_le_nhds
  have hdisc (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) (4 * r))) :
      DiffContOnCl ℂ f (ball (0 : ℂ) (4 * r)) :=
    hf.differentiableOn.mono closure_ball_subset_closedBall |>.diffContOnCl
  obtain ⟨V, hV0, hVa0, hV, _hVlim⟩ := exists_stable_inverse_family F r (fun s => C₀ * s)
    hr h00 hF0 (hdisc _ ha0) (ha.mono fun _ hs => hdisc _ hs) hlim hlin'
  have hhalf : ApproximatesLinearOn (F 0) (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * r)) (1 / 2) := by
    intro x hx y hy
    exact (hF0 x hx y hy).trans (by norm_num; nlinarith [norm_nonneg (x-y)])
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, C₀ * s ≤ r / 4 :=
    (hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < r / 4))).mono fun _ h => h.le
  have hhalfMoving : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ApproximatesLinearOn (F s) (ContinuousLinearMap.id ℂ ℂ)
        (ball (0 : ℂ) (2 * r)) (1 / 2) := by
    filter_upwards [ha, hlin', hsmall] with s hs hb hε
    exact approximates_identity_of_disc_error (F 0) (F s) r (C₀ * s) hr hF0
      (by convert (hdisc _ hs).sub (hdisc _ ha0) using 1; rfl) hb hε
  have hzeroAnalytic : AnalyticOnNhd ℂ (F 0) (ball (0 : ℂ) (2 * r)) :=
    ha0.mono (by intro z hz; exact ball_subset_closedBall (ball_subset_ball (by linarith) hz))
  refine ⟨V, ⟨hV0, hVa0, hV.mono (fun _ hs => ⟨hs.1, hs.2.1⟩), hhalf, hhalfMoving, hzeroAnalytic⟩, ?_⟩
  intro m hm
  obtain ⟨c, a, hc, ha'⟩ := hpack m hm
  obtain ⟨CF, hCF, hEF⟩ := hc.2.2 m le_rfl
    (closedBall (0 : ℂ) (4 * r)) (isCompact_closedBall _ _) hsub
  obtain ⟨CA, hCA, hEA⟩ := ha'.2.2 m le_rfl
    (closedBall (0 : ℂ) (4 * r)) (isCompact_closedBall _ _) hsub
  have hball : ball (0 : ℂ) (4 * r) ⊆ ball (0 : ℂ) R := ball_subset_ball hR.le
  have hca : ∀ j ≤ m, AnalyticOnNhd ℂ (c j) (ball (0 : ℂ) (4 * r)) :=
    fun j hj => (hc.1 j hj).mono hball
  have haa : ∀ j ≤ m, AnalyticOnNhd ℂ (a j) (closedBall (0 : ℂ) (4 * r)) :=
    fun j hj => (ha'.1 j hj).mono hsub
  have hc0 : ∀ u ∈ ball (0 : ℂ) (4 * r), c 0 u = F 0 u :=
    fun u hu => (hc.2.1 u (hball hu)).1
  have ha0v : ∀ u ∈ ball (0 : ℂ) (4 * r), a 0 u = A 0 u :=
    fun u hu => (ha'.2.1 u (hball hu)).1
  exact ⟨global_finite_inverse_expansion F V c m r CF hr hCF hV0
      (hV.mono fun _ hs => hs.1) hhalf hhalfMoving hzeroAnalytic hca hc0 hEF,
    global_finite_transition_expansion F V A c a m r CF CA hr hCF hCA hV0
      (hV.mono fun _ hs => hs.1) hhalf hhalfMoving hzeroAnalytic hca haa hc0 ha0v hEF hEA⟩

end Kneser.AllOrderSingleInverse
