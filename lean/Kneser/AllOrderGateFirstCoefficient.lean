import Kneser.AllOrderSingleInverse
import Kneser.AllOrderScalarCoherence
import Kneser.QuantitativeGateTransition

/-! Exact first coefficients for the same all-orders moving inverse.
The actual inverse's continuity and right derivative are derived from its
genuine inverse equations and coordinate packets. Any finite transition
packet consequently has the explicit spatial chain-rule coefficient. -/

set_option autoImplicit false
noncomputable section

namespace Kneser.AllOrderGateFirstCoefficient

open Filter Set Metric
open scoped Topology
open Kneser.AllOrderCompactGate Kneser.AllOrderSingleInverse Kneser.ActualHigherFinitePacket
open Kneser.FiniteExpansionHolomorphy Kneser.AllOrderGateFourier Kneser.AllOrderScalarCoherence
open Kneser.QuantitativeHornExpansion

def gateCorrection (F V A : ℝ → ℂ → ℂ) (D E : ℂ → ℂ) (z : ℂ) : ℂ :=
  E (V 0 z) - (deriv (A 0) (V 0 z) / deriv (F 0) (V 0 z)) * D (V 0 z)

theorem finitePacket_pointwise (T : ℝ → ℂ → ℂ) (b : ℕ → ℂ → ℂ) (m : ℕ) (U : Set ℂ)
    (h : FinitePacket T b m U) (z : ℂ) (hz : z ∈ U) :
    ScalarExpansion (fun s => T s z) (fun j => b j z) m := by
  obtain ⟨C, hC, he⟩ := h.2.2 {z} isCompact_singleton (by simpa using hz)
  exact ⟨h.2.1 z hz, C, hC, he.mono fun s hs => hs z (mem_singleton z)⟩

theorem scalarExpansion_one_powerExpansion (f : ℝ → ℂ) (c : ℕ → ℂ)
    (h : ScalarExpansion f c 1) : PowerExpansion f (c 1) 2 := by
  obtain ⟨C, hC, he⟩ := h.2
  refine ⟨C, hC, ?_⟩
  filter_upwards [he] with s hs
  rw [Real.rpow_two]
  simpa only [scalarPolynomial, Finset.sum_range_succ, Finset.sum_range_zero,
    Finset.sum_empty, zero_add, pow_zero, pow_one, one_mul, h.1, sub_add_eq_sub_sub] using hs

theorem normalizedFiniteData_analytic (F : ℝ → ℂ → ℂ) (c : ℕ → ℂ → ℂ) (D : ℂ → ℂ)
    (R : ℝ) (h : NormalizedFiniteData F c D 1 (ball (0 : ℂ) R)) :
    AnalyticOnNhd ℂ (F 0) (ball (0 : ℂ) R) ∧ AnalyticOnNhd ℂ D (ball (0 : ℂ) R) := by
  constructor
  · intro u hu
    have hn : ∀ᶠ v : ℂ in 𝓝 u, v ∈ ball (0 : ℂ) R := isOpen_ball.mem_nhds hu
    exact (h.1 0 (by omega) u hu).congr
      (hn.mono fun v hv => (h.2.1 v hv).1)
  · intro u hu
    have hn : ∀ᶠ v : ℂ in 𝓝 u, v ∈ ball (0 : ℂ) R := isOpen_ball.mem_nhds hu
    exact (h.1 1 le_rfl u hu).congr
      (hn.mono fun v hv => (h.2.1 v hv).2)

theorem hasDerivWithinAt_transition_of_normalized_packets
    (F V A : ℝ → ℂ → ℂ) (c a : ℕ → ℂ → ℂ) (D E : ℂ → ℂ)
    (r R : ℝ) (hr : 0 < r) (hR : 4 * r < R)
    (hV : InverseData F V r)
    (hF : NormalizedFiniteData F c D 1 (ball (0 : ℂ) R))
    (hA : NormalizedFiniteData A a E 1 (ball (0 : ℂ) R)) :
    ∀ z ∈ ball (0 : ℂ) (r / 4),
      HasDerivWithinAt (fun s : ℝ => A s (V s z))
        (E (V 0 z) - (deriv (A 0) (V 0 z) / deriv (F 0) (V 0 z)) * D (V 0 z))
        (Ici 0) 0 := by
  have hsub : closedBall (0 : ℂ) (4 * r) ⊆ ball (0 : ℂ) R :=
    fun z hz => (show dist z 0 ≤ 4 * r from hz).trans_lt hR
  have hball : ball (0 : ℂ) (4 * r) ⊆ ball (0 : ℂ) R := ball_subset_ball hR.le
  have hsmall : closedBall (0 : ℂ) r ⊆ closedBall (0 : ℂ) (4 * r) :=
    closedBall_subset_closedBall (by linarith)
  have hinner : closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) (2 * r) := by
    intro z hz
    exact (show dist z 0 ≤ r from hz).trans_lt (by linarith)
  obtain ⟨CF, hCF, hEF⟩ := hF.2.2 1 le_rfl (closedBall (0 : ℂ) (4 * r))
    (isCompact_closedBall _ _) hsub
  obtain ⟨CA, _hCA, hEA⟩ := hA.2.2 1 le_rfl (closedBall (0 : ℂ) (4 * r))
    (isCompact_closedBall _ _) hsub
  obtain ⟨d, hd⟩ := global_finite_inverse_expansion F V c 1 r CF hr hCF hV.1
    (hV.2.2.1.mono fun _ hs => hs.1) hV.2.2.2.1 hV.2.2.2.2.1 hV.2.2.2.2.2
    (fun j hj => (hF.1 j hj).mono hball)
    (fun u hu => (hF.2.1 u (hball hu)).1) hEF
  have hFfirst : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ closedBall (0 : ℂ) (4 * r),
      ‖F s u - F 0 u - (s : ℂ) * D u‖ ≤ CF * s ^ (2 : ℕ) := by
    filter_upwards [hEF] with s hs u hu
    simpa [complexPolynomial, Finset.sum_range_succ, (hF.2.1 u (hsub hu)).1,
      (hF.2.1 u (hsub hu)).2, sub_add_eq_sub_sub] using hs u hu
  have hAfirst : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ closedBall (0 : ℂ) (4 * r),
      ‖A s u - A 0 u - (s : ℂ) * E u‖ ≤ CA * s ^ (2 : ℕ) := by
    filter_upwards [hEA] with s hs u hu
    simpa [complexPolynomial, Finset.sum_range_succ, (hA.2.1 u (hsub hu)).1,
      (hA.2.1 u (hsub hu)).2, sub_add_eq_sub_sub] using hs u hu
  have hEps (C : ℝ) : Tendsto (fun s : ℝ => C * s) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (fun s : ℝ => s) (𝓝 (0 : ℝ)) (𝓝 0)).const_mul C).mono_left
      nhdsWithin_le_nhds
  have hDanalytic := (normalizedFiniteData_analytic F c D R hF).2
  have hAanalytic := (normalizedFiniteData_analytic A a E R hA).1
  have hEanalytic := (normalizedFiniteData_analytic A a E R hA).2
  intro z hz
  have hv0 := hV.1 z hz
  have hvr := scalarExpansion_one_powerExpansion _ _ (finitePacket_pointwise V d 1 _ hd z hz)
  have hvder := hvr.hasDerivWithinAt (by norm_num : (1 : ℝ) < 2)
  have hvlim : Tendsto (fun s : ℝ => V s z) (𝓝[>] 0) (𝓝 (V 0 z)) :=
    hvder.continuousWithinAt.tendsto.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  have hDlim := (hDanalytic _ (hsub (hsmall hv0.1))).continuousAt.tendsto.comp hvlim
  have hElim := (hEanalytic _ (hsub (hsmall hv0.1))).continuousAt.tendsto.comp hvlim
  have hneq : deriv (F 0) (V 0 z) ≠ 0 := by
    have hn := Kneser.StableHolomorphicInverse.norm_deriv_lower (F 0) r hV.2.2.2.1
      hV.2.2.2.2.2 (V 0 z) (hinner hv0.1)
    exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hn)
  have hinv : ∀ᶠ s : ℝ in 𝓝[>] 0, F s (V s z) = F 0 (V 0 z) := by
    filter_upwards [hV.2.2.1] with s hs
    rw [(hs.1 z hz).2, hv0.2]
  have hRemF : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖F s (V s z) - F 0 (V s z) - (s : ℂ) * D (V s z)‖ ≤ |s| * (CF * s) := by
    filter_upwards [hFfirst, hV.2.2.1, self_mem_nhdsWithin] with s hs hvs hsp
    change 0 < s at hsp
    exact (hs _ (hsmall (hvs.1 z hz).1)).trans_eq (by rw [abs_of_pos hsp]; ring)
  have hRemA : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖A s (V s z) - A 0 (V s z) - (s : ℂ) * E (V s z)‖ ≤ |s| * (CA * s) := by
    filter_upwards [hAfirst, hV.2.2.1, self_mem_nhdsWithin] with s hs hvs hsp
    change 0 < s at hsp
    exact (hs _ (hsmall (hvs.1 z hz).1)).trans_eq (by rw [abs_of_pos hsp]; ring)
  exact Kneser.GateInverseDerivative.hasDerivWithinAt_gate_composition F A (fun s => V s z) D E
    (fun s => CF * s) (fun s => CA * s) _ _
    (hV.2.2.2.2.2 _ (hinner hv0.1)).hasStrictDerivAt hneq
    (hAanalytic _ (hsub (hsmall hv0.1))).differentiableAt.hasDerivAt hvlim hinv hDlim hElim
    (hEps CF) (hEps CA) hRemF hRemA

theorem finitePacket_first_coefficient_eq (F V A : ℝ → ℂ → ℂ)
    (c a b : ℕ → ℂ → ℂ) (D E : ℂ → ℂ) (m : ℕ) (r R : ℝ)
    (hm : 1 ≤ m) (hr : 0 < r) (hR : 4 * r < R)
    (hV : InverseData F V r)
    (hF : NormalizedFiniteData F c D 1 (ball (0 : ℂ) R))
    (hA : NormalizedFiniteData A a E 1 (ball (0 : ℂ) R))
    (hb : FinitePacket (fun s z => A s (V s z)) b m (ball (0 : ℂ) (r / 4))) :
    ∀ z ∈ ball (0 : ℂ) (r / 4), b 1 z =
      E (V 0 z) - (deriv (A 0) (V 0 z) / deriv (F 0) (V 0 z)) * D (V 0 z) := by
  intro z hz
  have he := scalarExpansion_one_powerExpansion _ _
    (scalarExpansion_truncate (finitePacket_pointwise _ b m _ hb z hz) hm)
  have hd := he.hasDerivWithinAt (by norm_num : (1 : ℝ) < 2)
  have htrue := hasDerivWithinAt_transition_of_normalized_packets F V A c a D E r R hr hR hV hF hA z hz
  exact (hd.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans
    (htrue.derivWithin (uniqueDiffWithinAt_Ici 0))

theorem transition_powerExpansion_with_explicit_coefficient (F V A : ℝ → ℂ → ℂ)
    (c a b : ℕ → ℂ → ℂ) (D E : ℂ → ℂ) (m : ℕ) (r R : ℝ)
    (hm : 1 ≤ m) (hr : 0 < r) (hR : 4 * r < R)
    (hV : InverseData F V r)
    (hF : NormalizedFiniteData F c D 1 (ball (0 : ℂ) R))
    (hA : NormalizedFiniteData A a E 1 (ball (0 : ℂ) R))
    (hb : FinitePacket (fun s z => A s (V s z)) b m (ball (0 : ℂ) (r / 4))) :
    ∀ z ∈ ball (0 : ℂ) (r / 4), PowerExpansion (fun s => A s (V s z))
      (E (V 0 z) - (deriv (A 0) (V 0 z) / deriv (F 0) (V 0 z)) * D (V 0 z)) 2 := by
  intro z hz
  have he := scalarExpansion_one_powerExpansion _ _
    (scalarExpansion_truncate (finitePacket_pointwise _ b m _ hb z hz) hm)
  rwa [finitePacket_first_coefficient_eq F V A c a b D E m r R hm hr hR hV hF hA hb z hz] at he

theorem gateCorrection_analytic_of_finitePacket (F V A : ℝ → ℂ → ℂ)
    (c a b : ℕ → ℂ → ℂ) (D E : ℂ → ℂ) (m : ℕ) (r R : ℝ)
    (hm : 1 ≤ m) (hr : 0 < r) (hR : 4 * r < R)
    (hV : InverseData F V r)
    (hF : NormalizedFiniteData F c D 1 (ball (0 : ℂ) R))
    (hA : NormalizedFiniteData A a E 1 (ball (0 : ℂ) R))
    (hb : FinitePacket (fun s z => A s (V s z)) b m (ball (0 : ℂ) (r / 4))) :
    AnalyticOnNhd ℂ (gateCorrection F V A D E) (ball (0 : ℂ) (r / 4)) := by
  have heq := finitePacket_first_coefficient_eq F V A c a b D E m r R hm hr hR hV hF hA hb
  intro z hz
  have hn : ∀ᶠ w : ℂ in 𝓝 z, w ∈ ball (0 : ℂ) (r / 4) := isOpen_ball.mem_nhds hz
  exact (hb.1 1 hm z hz).congr (hn.mono fun w hw => heq w hw)

theorem fourier_first_coefficient_eq (F V A : ℝ → ℂ → ℂ)
    (c a b : ℕ → ℂ → ℂ) (D E : ℂ → ℂ) (m : ℕ) (r R : ℝ)
    (hm : 1 ≤ m) (hr : 0 < r) (hR : 4 * r < R)
    (hV : InverseData F V r)
    (hF : NormalizedFiniteData F c D 1 (ball (0 : ℂ) R))
    (hA : NormalizedFiniteData A a E 1 (ball (0 : ℂ) R))
    (hb : FinitePacket (fun s z => A s (V s z)) b m (ball (0 : ℂ) (r / 4)))
    (hGate : ∀ x ∈ Icc (0 : ℝ) 1, Kneser.GateFourierDerivative.gatePoint 0 x ∈ ball (0 : ℂ) (r / 4)) :
    ∀ n : ℤ, fourierCoefficient n b 1 =
      Kneser.GateFourierDerivative.gateCorrectionCoefficient n 0 (gateCorrection F V A D E) := by
  intro n
  rw [show 1 = 0 + 1 by rfl, fourierCoefficient_succ]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
  dsimp only
  rw [finitePacket_first_coefficient_eq F V A c a b D E m r R hm hr hR hV hF hA hb _ (hGate x hx')]
  rfl

end Kneser.AllOrderGateFirstCoefficient

end
