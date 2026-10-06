import Kneser.ActualRealNormalizedTransition
import Kneser.ActualUpperHornGateBridge

/-! The single centered inverse used at every order has exactly the
canonical parabolic baseline. Its real anchor is transported by the
actual finite orbit; no agreement of independently chosen entries is
assumed. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Kneser.ActualCenteredBaselineBridge

open Set Metric Filter Complex
open Kneser.ActualQuantitativeGateTransition Kneser.ActualTransitionPeriodicity
open Kneser.ActualCenteredGatePacket Kneser.AllOrderSingleInverse
open Kneser.ActualDeepCoordinateData Kneser.CanonicalBasinExtension
open Kneser.ActualNormalizationAnchorExpansion Kneser.RealNormalizationAnchor
open Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.FatouBasinExtension Kneser.ParabolicFatouHolomorphic
open Kneser.CommonQuadraticBaseline

theorem repellingChart_zero_origin (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (R Y : ℝ) (N M : ℕ) (V : ℝ → ℂ → ℂ)
    (ht : ActualTransitionData U H e₁ e₂ A B Γ R N M Y V) :
    repellingChart U H e₁ e₂ A B Γ N Y 0 0 = 0 := by
  rw [repellingChart_zero_eq U H e₁ e₂ A B Γ R Y N M V ht 0 (by simp)]
  simp

theorem centered_inverse_zero_eq (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (R Y : ℝ) (N M : ℕ) (Vold V : ℝ → ℂ → ℂ)
    (ht : ActualTransitionData U H e₁ e₂ A B Γ R N M Y Vold)
    (hv : InverseData (centeredRepelling U H e₁ e₂ A B Γ N Y) V 12)
    (w : ℂ) (hw : w ∈ ball (0 : ℂ) 3) : V 0 w = Vold 0 w := by
  have hw' : w ∈ ball (0 : ℂ) (12 / 4) := by
    simpa only [show (12 : ℝ) / 4 = 3 by norm_num] using hw
  have hn := hv.1 w hw'
  have ho := ht.inverse_zero w (ball_subset_ball (by norm_num) hw)
  apply repellingChart_zero_injective U H e₁ e₂ A B Γ R Y N M Vold ht
  · exact (closedBall_subset_ball (by norm_num)) hn.1
  · exact (closedBall_subset_ball (by norm_num)) ho.1
  · simpa only [centeredRepelling,
      repellingChart_zero_origin U H e₁ e₂ A B Γ R Y N M Vold ht, sub_zero, ho.2] using hn.2

theorem anchor_zero_eq_global_of_entry
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R R₀ : ℝ) (M : ℕ)
    (hs : CanonicalSeedData R₀) (hRR : R₀ ≤ R)
    (hd : DeepCoordinateData U H e₁ e₂ A B Γ R)
    (hentry : orbit normalizationAnchor 0 M ∈ petal (R + 1)) :
    anchorValue U H e₁ e₂ A B Γ M 0 = globalAttracting R₀ normalizationAnchor := by
  have hp : (parabolicMap^[M]) normalizationAnchor ∈ petal R₀ := by
    rw [← unfolding_orbit_zero_eq_iterate]
    change R₀ < _
    change R + 1 < _ at hentry
    linarith
  have he : Entry parabolicMap (petal R₀) normalizationAnchor M :=
    ⟨hp, iterate_analytic_jacobian _ parabolicMap_analytic_jacobian normalizationAnchor M⟩
  have hg := extend_eq_transport _ _ _ hs.attracting_map hs.attracting_abel normalizationAnchor M he
  unfold anchorValue
  simp only [Complex.ofReal_zero]
  rw [hd.attracting_canonical _ hentry]
  simpa only [globalAttracting, transport, unfolding_orbit_zero_eq_iterate] using hg.symm

theorem real_normalized_zero_eq_original
    (U H A B : ℂ → ℂ) (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ)
    (Γ : ℕ → ℂ × ℂ → ℂ) (R R₀ Y : ℝ) (N M M₀ : ℕ) (Vold V : ℝ → ℂ → ℂ)
    (hs : CanonicalSeedData R₀) (hRR : R₀ ≤ R)
    (hd : DeepCoordinateData U H (first (e 1)) (second (e 1)) A B (Γ 1) R)
    (ht : ActualTransitionData U H (first (e 1)) (second (e 1)) A B (Γ 1) R N M₀ Y Vold)
    (hv : InverseData (centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y) V 12)
    (hentry : R + 2 ≤ (inverseCoordinate (orbit normalizationAnchor 0 M)).re)
    (w : ℂ) (hw : w ∈ ball (0 : ℂ) 3) :
    Kneser.ActualRealNormalizedTransition.transition U H A B e Γ N M Y V 0 w =
      transitionValue U H (first (e 1)) (second (e 1)) A B (Γ 1) N M₀ Y Vold 0 w := by
  have hM : orbit normalizationAnchor 0 M ∈ petal (R + 1) := by change R + 1 < _; linarith
  have hn := anchor_zero_eq_global_of_entry U H (first (e 1)) (second (e 1)) A B (Γ 1)
    R R₀ M hs hRR hd hM
  have ho := anchor_zero_eq_global U H (first (e 1)) (second (e 1)) A B (Γ 1)
    R R₀ N M₀ Y Vold hs hRR hd ht
  have hV := centered_inverse_zero_eq U H (first (e 1)) (second (e 1)) A B (Γ 1)
    R Y N M₀ Vold V ht hv w hw
  unfold Kneser.ActualRealNormalizedTransition.transition
    Kneser.ActualRealAnchorHigherGate.normalizedCoordinate transitionValue attractingChart
  rw [hV, hn, ho]

end Kneser.ActualCenteredBaselineBridge
end
