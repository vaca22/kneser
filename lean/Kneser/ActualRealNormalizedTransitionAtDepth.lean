import Kneser.ActualRealNormalizedTransition

/-! One fixed actual preparation admits the entire real-anchor transition
and all-order packets above any prescribed finite depth.  This permits the
same witnesses to meet the independently constructed global lens bounds. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Kneser.ActualRealNormalizedTransitionAtDepth

open Filter Set Metric Kneser.ActualBilateralGate Kneser.ActualGateAbel
open Kneser.ActualQuantitativeGateTransition Kneser.ActualHigherFinitePacket
open Kneser.ActualCenteredGatePacket Kneser.AllOrderSingleInverse Kneser.AllOrderCompactGate
open Kneser.CommonQuadraticBaseline Kneser.ActualDeepCoordinateData
open Kneser.HigherGateIntegerRemainder Kneser.HigherGateTransport
open Kneser.ActualRealAnchorHigherGate Kneser.ActualRealAnchorFinitePacket
open Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit Kneser.RealNormalizationAnchor
open scoped Topology

open Kneser.ActualRealNormalizedTransition

theorem exists_real_normalized_transition_at_depth (U H A B : ℂ → ℂ)
    (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (hdata : Kneser.ReflectedOrbitChainCoefficient.ActualPreparationData
      U H (first (e 1)) (second (e 1)) A B K F (Γ 1))
    (hprep : ∀ n, Kneser.CommonPreparedFamily.Prepared A B F n (e n) (Γ n)) (D : ℝ) :
    ∃ R : ℝ, ∃ N M M₀ : ℕ, ∃ Y : ℝ, ∃ Vold V : ℝ → ℂ → ℂ,
      Kneser.ReflectedOrbitChainCoefficient.ActualPreparationData
        U H (first (e 1)) (second (e 1)) A B K F (Γ 1) ∧
      (∀ n, Kneser.CommonPreparedFamily.Prepared A B F n (e n) (Γ n)) ∧
      D ≤ R ∧ 64 ≤ R ∧
      LocalAbelData U H (first (e 1)) (second (e 1)) A B (Γ 1) R ∧
      DeepCoordinateData U H (first (e 1)) (second (e 1)) A B (Γ 1) R ∧
      AbsoluteIntegerGateExpansions U H A B e Γ N ∧
      R + 2 ≤ (inverseCoordinate (orbit normalizationAnchor 0 M)).re ∧
      ActualTransitionData U H (first (e 1)) (second (e 1)) A B (Γ 1) R N M₀ Y Vold ∧
      InverseData (centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y) V 12 ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (transition U H A B e Γ N M Y V s) (ball (0 : ℂ) 3)) ∧
      ∀ m : ℕ, 1 ≤ m → ∃ b : ℕ → ℂ → ℂ,
        FinitePacket (transition U H A B e Γ N M Y V) b m (ball (0 : ℂ) 3) := by
  obtain ⟨Rl, _hRl, hl⟩ := local_abel_data_of_actual U H (first (e 1)) (second (e 1)) A B K F (Γ 1) hdata
  obtain ⟨Rp, hRp, hp⟩ := exists_actual_gate_spatial_data U H A B K F e Γ hdata
  obtain ⟨Rd, hd⟩ := Kneser.ActualBaselineDeep.deep_data_of_actual
    U H (first (e 1)) (second (e 1)) A B K F (Γ 1) hdata
  let R := max D (max Rp (max Rl Rd))
  have hR : 64 ≤ R := hRp.trans ((le_max_left Rp (max Rl Rd)).trans (le_max_right D _))
  have hlocal : LocalAbelData U H (first (e 1)) (second (e 1)) A B (Γ 1) R :=
    hl.mono (((le_max_left Rl Rd).trans (le_max_right Rp (max Rl Rd))).trans (le_max_right D _))
  have hdeep : DeepCoordinateData U H (first (e 1)) (second (e 1)) A B (Γ 1) R :=
    hd.mono (((le_max_right Rl Rd).trans (le_max_right Rp _)).trans (le_max_right D _))
  obtain ⟨N, M₀, Y, Vold, ht⟩ := exists_transition_data_of_deep
    U H (first (e 1)) (second (e 1)) A B (Γ 1) R hdeep
  have hN : R + 64 + 4 ≤ 3 * (N : ℝ) / 4 := by linarith [ht.length_margin]
  have hfinite := fixedGateAllFiniteExpansions_of_actual U H A B K F e Γ hdata hprep R hR hlocal N hN
  have hregular := hp R ((le_max_left Rp _).trans (le_max_right D _)) N hN
  have hab := absoluteIntegerGateExpansions_of_regular U H A B e Γ N hfinite hregular
  obtain ⟨V, hV, _hm⟩ := Kneser.ActualAllOrderCenteredTransition.all_orders_of_actual_data U H A B e Γ R Y N M₀ Vold ht hab
  obtain ⟨M, hM, _hMa⟩ := Kneser.RealNormalizationAnchor.exists_anchor_enters_petal (R + 2)
  have hentry : R + 2 ≤ (inverseCoordinate (orbit normalizationAnchor 0 M)).re := by
    have hh : R + 2 < (inverseCoordinate (orbit normalizationAnchor 0 M)).re := hM
    exact hh.le
  exact ⟨R, N, M, M₀, Y, Vold, V, hdata, hprep, le_max_left _ _, hR, hlocal, hdeep, hab, hentry, ht, hV,
    transition_positive_analytic U H A B e Γ R N M M₀ Y Vold V ht hV,
    real_normalized_transition_all_orders U H A B K F e Γ hdata hprep R hR hlocal hdeep N M M₀ Y Vold V ht hab hV hentry⟩

end Kneser.ActualRealNormalizedTransitionAtDepth
