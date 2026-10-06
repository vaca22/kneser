import Kneser.ActualFixedGateGrowingContainment
import Kneser.ActualRealNormalizedTransitionAtDepth
import Kneser.ActualAnchorKoenigsIdentification

/-! One actual all-order transition is identified with the true growing
transition normalized by the genuine real Koenigs anchor. Fixed gate
containment, finite entry, actual logarithmic height and branch constants
are all derived from the same preparation. -/

set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
namespace Kneser.ActualAllOrderGlobalIdentification

open Set Metric Filter Complex
open Kneser.ReflectedOrbitChainCoefficient Kneser.CommonQuadraticBaseline
open Kneser.ActualHolomorphicGrowingLens Kneser.GrowingBandGeometry
open Kneser.ActualGrowingCoordinateInverse Kneser.GrowingLensSpatialHolomorphy
open Kneser.ActualQuantitativeGateTransition Kneser.ActualCenteredGatePacket
open Kneser.AllOrderSingleInverse Kneser.AllOrderCompactGate
open Kneser.ActualRealNormalizedTransitionAtDepth Kneser.ActualFixedGateGrowingContainment
open Kneser.ActualBandTimeConfluence Kneser.ActualLocalGrowingTransitionBridge
open Kneser.ActualLensPreparedCoordinateBridge Kneser.ActualAnchorKoenigsIdentification
open Kneser.RealNormalizationAnchor Kneser.ParabolicExponentialOrbit Kneser.ExponentialUnfolding
open scoped Topology

theorem exists_global_identified_transition_of_actual_data
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H (first (e 1)) (second (e 1)) A B K F (Γ 1))
    (hprep : ∀ n, Kneser.CommonPreparedFamily.Prepared A B F n (e n) (Γ n))
    (Dmin : ℝ) :
    ∃ R Yg Y η Mg P : ℝ, ∃ N M M₀ : ℕ, ∃ Vold V : ℝ → ℂ → ℂ,
      Dmin ≤ R ∧
      ActualTransitionData U H (first (e 1)) (second (e 1)) A B (Γ 1) R N M₀ Yg Vold ∧
      InverseData (centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Yg) V 12 ∧
      (∀ m : ℕ, 1 ≤ m → ∃ b : ℕ → ℂ → ℂ,
        FinitePacket (Kneser.ActualRealNormalizedTransition.transition U H A B e Γ N M Yg V)
          b m (ball (0 : ℂ) 3)) ∧
      ∀ᶠ s : ℝ in 𝓝[>] 0, ∃ a b θ : ℝ, ∃ Vg : ℂ → ℂ,
        LensControl (first (e 1)) (second (e 1)) A B (Γ 1) s a b θ Y η Mg P ∧
        AnalyticOnNhd ℂ Vg (strip θ (3 * Y + boundaryMargin P)) ∧
        (∀ w ∈ strip θ (3 * Y + boundaryMargin P), Vg w ∈ strip θ (3 * Y) ∧
          repellingCoordinate A B (Γ 1) s a b θ (first (e 1) s) (second (e 1) s) (Vg w) = w) ∧
        ∀ w ∈ ball (0 : ℂ) 3,
          w + gateConstant A B (Γ 1) s a b θ Yg (first (e 1) s) (second (e 1) s)
            ∈ strip θ (3 * Y + boundaryMargin P) ∧
          Kneser.ActualRealNormalizedTransition.transition U H A B e Γ N M Yg V s w =
            Kneser.ActualNormalizedGrowingTransition.transition A B (Γ 1) s a b θ
              realAnchor ((a+b)/2) (first (e 1) s) (second (e 1) s) Vg
              (w + gateConstant A B (Γ 1) s a b θ Yg (first (e 1) s) (second (e 1) s) -
                Kneser.ActualNormalizedGrowingTransition.repellingConstant A B (Γ 1) s a b θ
                  ((a+b)/2) (first (e 1) s) (second (e 1) s)) := by
  obtain ⟨Y,sl,η,Mg,P,hY,hsl,_hslh,hlens⟩ :=
    exists_actual_lens_control U H (first (e 1)) (second (e 1)) A B K F (Γ 1) hdata
  obtain ⟨a₁,b₁,θ₁,hc₁⟩ := hlens (sl/2) (by linarith) (by linarith)
  have hP : 0 ≤ P := (norm_nonneg (first (e 1) ((sl/2 : ℝ) : ℂ))).trans hc₁.first_model_bound
  have hB : 0 ≤ boundaryMargin P := by unfold boundaryMargin; positivity
  let Dg := 3 * Y + 2 * boundaryMargin P
  have hDg : 0 ≤ Dg := by dsimp [Dg]; linarith
  obtain ⟨Da,hDa,hanchor⟩ := exists_actual_anchor_koenigs_identification
    U H (first (e 1)) (second (e 1)) A B K F (Γ 1) hdata
  let D := max Dmin (max Da (Dg+14))
  obtain ⟨R,N,M,M₀,Yg,Vold,V,_hd,_hp,hDR,hR,hl,hd,hab,hentry,ht,hv,hTa,hpack⟩ :=
    exists_real_normalized_transition_at_depth U H A B K F e Γ hdata hprep D
  have hDaR : Da ≤ R := ((le_max_left Da (Dg+14)).trans (le_max_right Dmin _)).trans hDR
  have hdeep : Dg + 14 ≤ Yg := by
    have hDgR : Dg + 14 ≤ R := ((le_max_right Da (Dg+14)).trans (le_max_right Dmin _)).trans hDR
    linarith [ht.length_margin,ht.height,Nat.cast_nonneg (α := ℝ) N]
  have hYg : 64 ≤ Yg := by linarith [ht.height,Nat.cast_nonneg (α := ℝ) N]
  have hC : 0 < Yg + 13 + Dg + 1 := by linarith
  have heθ := actual_theta_uniform_small U H (first (e 1)) (second (e 1)) A B K F (Γ 1)
    hdata (2 * Real.pi / (Yg + 13 + Dg + 1)) (by positivity)
  have heTime := fixed_gate_time_uniform U H (first (e 1)) (second (e 1)) A B K F (Γ 1)
    hdata N Yg ht.height
  have heAnchor := hanchor M (by linarith [hentry])
  obtain ⟨sb,hsb,_hsbh,hbridge⟩ := exists_actual_coordinate_bridge_threshold
    U H (first (e 1)) (second (e 1)) A B K F (Γ 1) hdata
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < min sl sb :=
    (eventually_lt_nhds (lt_min hsl hsb)).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  refine ⟨R,Yg,Y,η,Mg,P,N,M,M₀,Vold,V,(le_max_left Dmin _).trans hDR,ht,hv,hpack,?_⟩
  filter_upwards [heθ,heTime,heAnchor,hsmall,hpos,hv.2.2.1] with s hsθ hsTime hsAnchor hsSmall hs hsV
  obtain ⟨a,b,θ,hc⟩ := hlens s hs (hsSmall.trans_le (min_le_left _ _))
  obtain ⟨Vplus,Vg,_hVplus,hVg,_hsp,hsg⟩ :=
    actual_bilateral_holomorphic_strip_inverses (first (e 1)) (second (e 1)) A B (Γ 1)
      s a b θ Y η Mg P hc
  have hθ := hsθ a b hc.left_neg hc.right_pos hc.left_fixed hc.right_fixed
  rw [←hc.theta_actual] at hθ
  have hheight : Yg + 13 + Dg < height θ := by
    have hh : θ * (Yg+13+Dg+1) < 2 * Real.pi := (lt_div_iff₀ hC).mp hθ.2
    have hh' : Yg+13+Dg+1 < height θ := (lt_div_iff₀ hc.theta_pos).mpr (by nlinarith)
    linarith
  have htime := hsTime a b hc.left_neg hc.right_pos hc.left_fixed hc.right_fixed
  rw [←hc.theta_actual] at htime
  have hpoints := fixed_gate_points_in_growing_lens a b θ Yg Dg hdeep hheight htime hYg
  have hb := hbridge s a b θ Y η Mg P hs (hsSmall.trans_le (min_le_right _ _)) hc
  have ha := hsAnchor a b hc.left_neg hc.right_pos hc.left_fixed hc.right_fixed
  refine ⟨a,b,θ,Vg,hc,hVg,hsg,?_⟩
  intro w hw
  have hsV' : ∀ w ∈ ball (0 : ℂ) 3, V s w ∈ closedBall (0 : ℂ) 12 ∧
      centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Yg s (V s w) = w := by
    simpa only [show (12 : ℝ)/4=3 by norm_num] using hsV.1
  have hb' := fun Z hZ hu => hb Z hZ hu N
  have hh := real_normalized_eq_growing U H A B e Γ s a b θ Y η Mg P Yg N M hc hb'
    hpoints (V s) hsV' Vg hsg w hw
  refine ⟨hh.1,?_⟩
  change Kneser.ActualRealNormalizedTransition.transition U H A B e Γ N M Yg V s w = _
  exact hh.2.trans (normalized_global_shift_identity U H (first (e 1)) (second (e 1)) A B (Γ 1)
    s a b θ Yg realAnchor ((a+b)/2) M Vg w ha)

end Kneser.ActualAllOrderGlobalIdentification
end
