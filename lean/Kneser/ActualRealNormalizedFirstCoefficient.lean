import Kneser.ActualAllOrderHornParameter
import Kneser.AllOrderGateFirstCoefficient

/-! The all-orders horn logarithm has the manuscript's explicit first
coefficient for the SAME centered inverse and SAME real anchor. The
repelling correction is a spatial difference at the fixed chart anchor;
it is never silently replaced by the raw repelling correction. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Kneser.ActualRealNormalizedFirstCoefficient

open Filter Set Metric
open scoped Topology
open Kneser.ActualBilateralGate Kneser.ActualGateAbel Kneser.ActualDeepCoordinateData
open Kneser.ActualQuantitativeGateTransition Kneser.ActualHigherFinitePacket
open Kneser.ActualCenteredGatePacket Kneser.ActualRealNormalizedTransition
open Kneser.ActualRealAnchorHigherGate Kneser.ActualRealAnchorFinitePacket
open Kneser.CommonQuadraticBaseline Kneser.HigherGateIntegerRemainder
open Kneser.AllOrderSingleInverse Kneser.AllOrderCompactGate Kneser.AllOrderGateFirstCoefficient
open Kneser.AllOrderGateFourier Kneser.AllOrderGateExtraction Kneser.AllOrderHornExpansion
open Kneser.AllOrderParameterExpansion Kneser.ActualAllOrderHornParameter
open Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit Kneser.RealNormalizationAnchor
open Kneser.GateFourierDerivative

def normalizedChart (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (N M : ℕ) (Y : ℝ) (s : ℝ) (z : ℂ) : ℂ :=
  normalizedCoordinate U H A B e Γ N M s (chartPoint Y z)

def centeredRepellingCorrection (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (N : ℕ) (Y : ℝ) (z : ℂ) : ℂ :=
  backwardCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N (chartPoint Y z) -
    backwardCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N (chartPoint Y 0)

def physicalCorrection (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ) (z : ℂ) : ℂ :=
  let u := chartPoint Y (V 0 z)
  forwardCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N u -
    Kneser.ActualNormalizationAnchorExpansion.anchorCoefficient
      U H (first (e 1)) (second (e 1)) A B (Γ 1) M -
    (deriv (fun v => forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v 0) u /
      deriv (fun v => backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v 0) u) *
    (backwardCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N u -
      backwardCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N (chartPoint Y 0))

theorem normalized_centered_chart_derivative_ratio (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Y : ℝ) (N M : ℕ)
    (hg : BilateralGateData U H (first (e 1)) (second (e 1)) A B (Γ 1) R 64 N)
    (hY : 64 * ((N : ℝ) + 1) + 64 ≤ Y) (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 64) :
    deriv (normalizedChart U H A B e Γ N M Y 0) z /
      deriv (centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y 0) z =
    deriv (fun u => forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u 0)
      (chartPoint Y z) /
    deriv (fun u => backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u 0)
      (chartPoint Y z) := by
  have hqa : normalizedChart U H A B e Γ N M Y 0 = fun z =>
      attractingChart U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y 0 z -
        Kneser.ActualNormalizationAnchorExpansion.anchorValue
          U H (first (e 1)) (second (e 1)) A B (Γ 1) M 0 := rfl
  have hfc : centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y 0 = fun z =>
      repellingChart U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y 0 z -
        repellingChart U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y 0 0 := rfl
  rw [hqa, hfc, deriv_sub_const, deriv_sub_const]
  exact (chart_derivative_ratio U H (first (e 1)) (second (e 1)) A B (Γ 1) R Y N hg hY z hz).2

theorem exists_actual_first_source_packets (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ)
    (F : ℂ × ℂ → ℂ) (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (hdata : Kneser.ReflectedOrbitChainCoefficient.ActualPreparationData
      U H (first (e 1)) (second (e 1)) A B K F (Γ 1))
    (hprep : ∀ n, Kneser.CommonPreparedFamily.Prepared A B F n (e n) (Γ n))
    (R : ℝ) (hR : 64 ≤ R)
    (hlocal : LocalAbelData U H (first (e 1)) (second (e 1)) A B (Γ 1) R)
    (hdeep : DeepCoordinateData U H (first (e 1)) (second (e 1)) A B (Γ 1) R)
    (N M M₀ : ℕ) (Y : ℝ) (Vold : ℝ → ℂ → ℂ)
    (ht : ActualTransitionData U H (first (e 1)) (second (e 1)) A B (Γ 1) R N M₀ Y Vold)
    (hab : AbsoluteIntegerGateExpansions U H A B e Γ N)
    (hentry : R + 2 ≤ (inverseCoordinate (orbit normalizationAnchor 0 M)).re) :
    ∃ c a : ℕ → ℂ → ℂ,
      NormalizedFiniteData
        (centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y)
        c (centeredRepellingCorrection U H A B e Γ N Y) 1 (ball (0 : ℂ) 56) ∧
      NormalizedFiniteData (normalizedChart U H A B e Γ N M Y) a
        (fun z => firstCorrection U H A B e Γ N M (chartPoint Y z)) 1 (ball (0 : ℂ) 56) := by
  have hN : R + 64 + 4 ≤ 3 * (N : ℝ) / 4 := by linarith [ht.length_margin]
  obtain ⟨n, L, hp⟩ := exists_packet_of_actual_data U H A B e Γ R N ht.bilateral hab (chartPoint Y 0)
    (chartPoint_in_gate N Y ht.height 0 (by simp)) 1 le_rfl
  have hc := (centered_packet_of_packet U H A B e Γ N 1 n L Y ht.height hp).2
  obtain ⟨na, La, hpa, _hsa⟩ := real_anchor_packet U H A B K F e Γ hdata hprep R hR hlocal hdeep
    N M hN ht.bilateral hentry 1 le_rfl
  have hqa : AnalyticOnNhd ℂ (chartPoint Y) (ball (0 : ℂ) 56) := by
    intro z hz
    exact chartPoint_analytic N Y ht.height z
      (closedBall_subset_closedBall (by norm_num) (ball_subset_closedBall hz))
  have hqm : MapsTo (chartPoint Y) (ball (0 : ℂ) 56) (interior (gate 64 N)) :=
    fun z hz => chartPoint_in_interior N Y ht.height z (ball_subset_closedBall hz)
  have ha := Kneser.FinitePacketPullback.normalizedFiniteData_pullback _ _ _ (chartPoint Y)
    1 _ _ hpa hqa hqm
  exact ⟨_, _, hc, ha⟩

theorem actual_finitePacket_first_coefficient (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ)
    (F : ℂ × ℂ → ℂ) (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (hdata : Kneser.ReflectedOrbitChainCoefficient.ActualPreparationData
      U H (first (e 1)) (second (e 1)) A B K F (Γ 1))
    (hprep : ∀ n, Kneser.CommonPreparedFamily.Prepared A B F n (e n) (Γ n))
    (R : ℝ) (hR : 64 ≤ R)
    (hlocal : LocalAbelData U H (first (e 1)) (second (e 1)) A B (Γ 1) R)
    (hdeep : DeepCoordinateData U H (first (e 1)) (second (e 1)) A B (Γ 1) R)
    (N M M₀ : ℕ) (Y : ℝ) (Vold V : ℝ → ℂ → ℂ)
    (ht : ActualTransitionData U H (first (e 1)) (second (e 1)) A B (Γ 1) R N M₀ Y Vold)
    (hab : AbsoluteIntegerGateExpansions U H A B e Γ N)
    (hv : InverseData (centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y) V 12)
    (hentry : R + 2 ≤ (inverseCoordinate (orbit normalizationAnchor 0 M)).re)
    (m : ℕ) (hm : 1 ≤ m) (b : ℕ → ℂ → ℂ)
    (hb : FinitePacket (transition U H A B e Γ N M Y V) b m (ball (0 : ℂ) 3)) :
    ∀ z ∈ ball (0 : ℂ) 3, b 1 z = physicalCorrection U H A B e Γ N M Y V z := by
  obtain ⟨c, a, hc, ha⟩ := exists_actual_first_source_packets U H A B K F e Γ hdata hprep R hR
    hlocal hdeep N M M₀ Y Vold ht hab hentry
  have hb' : FinitePacket (fun s z => normalizedChart U H A B e Γ N M Y s (V s z)) b m
      (ball (0 : ℂ) (12 / 4)) := by
    rw [show (12 : ℝ) / 4 = 3 by norm_num]
    exact hb
  have heq := finitePacket_first_coefficient_eq
    (centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y) V
    (normalizedChart U H A B e Γ N M Y) c a b
    (centeredRepellingCorrection U H A B e Γ N Y)
    (fun z => firstCorrection U H A B e Γ N M (chartPoint Y z)) m 12 56 hm
    (by norm_num) (by norm_num) hv hc ha hb'
  intro z hz
  have hz' : z ∈ ball (0 : ℂ) (12 / 4) := by simpa only [show (12 : ℝ) / 4 = 3 by norm_num] using hz
  have hw : V 0 z ∈ closedBall (0 : ℂ) 64 :=
    closedBall_subset_closedBall (by norm_num) (hv.1 z hz').1
  have hh := heq z hz'
  rw [normalized_centered_chart_derivative_ratio U H A B e Γ R Y N M ht.bilateral ht.height _ hw] at hh
  exact hh

theorem actual_fourier_first_coefficient (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ)
    (F : ℂ × ℂ → ℂ) (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (hdata : Kneser.ReflectedOrbitChainCoefficient.ActualPreparationData
      U H (first (e 1)) (second (e 1)) A B K F (Γ 1))
    (hprep : ∀ n, Kneser.CommonPreparedFamily.Prepared A B F n (e n) (Γ n))
    (R : ℝ) (hR : 64 ≤ R)
    (hlocal : LocalAbelData U H (first (e 1)) (second (e 1)) A B (Γ 1) R)
    (hdeep : DeepCoordinateData U H (first (e 1)) (second (e 1)) A B (Γ 1) R)
    (N M M₀ : ℕ) (Y : ℝ) (Vold V : ℝ → ℂ → ℂ)
    (ht : ActualTransitionData U H (first (e 1)) (second (e 1)) A B (Γ 1) R N M₀ Y Vold)
    (hab : AbsoluteIntegerGateExpansions U H A B e Γ N)
    (hv : InverseData (centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y) V 12)
    (hentry : R + 2 ≤ (inverseCoordinate (orbit normalizationAnchor 0 M)).re)
    (m : ℕ) (hm : 1 ≤ m) (b : ℕ → ℂ → ℂ)
    (hb : FinitePacket (transition U H A B e Γ N M Y V) b m (ball (0 : ℂ) 3)) :
    ∀ n : ℤ, fourierCoefficient n b 1 =
      gateCorrectionCoefficient n 0 (physicalCorrection U H A B e Γ N M Y V) := by
  have heq := actual_finitePacket_first_coefficient U H A B K F e Γ hdata hprep R hR hlocal hdeep
    N M M₀ Y Vold V ht hab hv hentry m hm b hb
  intro n
  rw [show 1 = 0 + 1 by rfl, fourierCoefficient_succ]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
  dsimp only
  rw [heq _ (real_gate_mem_ball_three x hx')]

theorem actual_explicitParameter_first_coefficient (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ)
    (F : ℂ × ℂ → ℂ) (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (hdata : Kneser.ReflectedOrbitChainCoefficient.ActualPreparationData
      U H (first (e 1)) (second (e 1)) A B K F (Γ 1))
    (hprep : ∀ n, Kneser.CommonPreparedFamily.Prepared A B F n (e n) (Γ n))
    (R : ℝ) (hR : 64 ≤ R)
    (hlocal : LocalAbelData U H (first (e 1)) (second (e 1)) A B (Γ 1) R)
    (hdeep : DeepCoordinateData U H (first (e 1)) (second (e 1)) A B (Γ 1) R)
    (N M M₀ : ℕ) (Y : ℝ) (Vold V : ℝ → ℂ → ℂ)
    (ht : ActualTransitionData U H (first (e 1)) (second (e 1)) A B (Γ 1) R N M₀ Y Vold)
    (hab : AbsoluteIntegerGateExpansions U H A B e Γ N)
    (hv : InverseData (centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y) V 12)
    (hentry : R + 2 ≤ (inverseCoordinate (orbit normalizationAnchor 0 M)).re)
    (m : ℕ) (hm : 1 ≤ m) (b : ℕ → ℂ → ℂ)
    (hb : FinitePacket (transition U H A B e Γ N M Y V) b m (ball (0 : ℂ) 3))
    (r : ℂ → ℂ) (hr0 : r 0 = 0) (hrd : HasDerivAt r (1 / 2) 0) :
    ∀ n : ℤ, gateFourierCoefficient n 0 (transition U H A B e Γ N M Y V 0) ≠ 0 →
      explicitCoefficient n b m r 1 = Kneser.hornKappa n
        (gateFourierCoefficient n 0 (transition U H A B e Γ N M Y V 0))
        (gateCorrectionCoefficient n 0 (physicalCorrection U H A B e Γ N M Y V))
        (gateCorrectionCoefficient 0 0 (physicalCorrection U H A B e Γ N M Y V)) := by
  have hT := transition_positive_analytic U H A B e Γ R N M M₀ Y Vold V ht hv
  have hf := gateFourier_scalarExpansion_of_set (transition U H A B e Γ N M Y V) b m
    (ball (0 : ℂ) 3) real_gate_mem_ball_three hb hT
  have heq := actual_fourier_first_coefficient U H A B K F e Γ hdata hprep R hR hlocal hdeep
    N M M₀ Y Vold V ht hab hv hentry m hm b hb
  intro n hB
  have hc : fourierCoefficient n b 0 ≠ 0 := by rwa [(hf n).1]
  unfold explicitCoefficient
  rw [parameterReference_first_coefficient _ m hm r hr0 hrd,
    logReference_first_coefficient n _ _ m hm hc, (hf n).1, heq n, heq 0]
  ring

theorem coherent_horn_first_coefficient (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ)
    (F : ℂ × ℂ → ℂ) (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (hdata : Kneser.ReflectedOrbitChainCoefficient.ActualPreparationData
      U H (first (e 1)) (second (e 1)) A B K F (Γ 1))
    (hprep : ∀ n, Kneser.CommonPreparedFamily.Prepared A B F n (e n) (Γ n))
    (R : ℝ) (hR : 64 ≤ R)
    (hlocal : LocalAbelData U H (first (e 1)) (second (e 1)) A B (Γ 1) R)
    (hdeep : DeepCoordinateData U H (first (e 1)) (second (e 1)) A B (Γ 1) R)
    (N M M₀ : ℕ) (Y : ℝ) (Vold V : ℝ → ℂ → ℂ)
    (ht : ActualTransitionData U H (first (e 1)) (second (e 1)) A B (Γ 1) R N M₀ Y Vold)
    (hab : AbsoluteIntegerGateExpansions U H A B e Γ N)
    (hv : InverseData (centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y) V 12)
    (hentry : R + 2 ≤ (inverseCoordinate (orbit normalizationAnchor 0 M)).re)
    (p r : ℂ → ℂ) (hr0 : r 0 = 0) (hrd : HasDerivAt r (1 / 2) 0)
    (hh : CoherentHornData (transition U H A B e Γ N M Y V) p r) :
    ∀ n : ℤ, gateFourierCoefficient n 0 (transition U H A B e Γ N M Y V 0) ≠ 0 →
      ∃ a : ℕ → ℂ, a 0 = 0 ∧
        (∀ m : ℕ, ParameterExpansion (logarithm (transition U H A B e Γ N M Y V) n) p a m) ∧
        a 1 = Kneser.hornKappa n
          (gateFourierCoefficient n 0 (transition U H A B e Γ N M Y V 0))
          (gateCorrectionCoefficient n 0 (physicalCorrection U H A B e Γ N M Y V))
          (gateCorrectionCoefficient 0 0 (physicalCorrection U H A B e Γ N M Y V)) := by
  intro n hB
  obtain ⟨a, ha0, ha, _hbranch, hident⟩ := hh n hB
  obtain ⟨b, hb, heq⟩ := hident 1 le_rfl
  refine ⟨a, ha0, ha, ?_⟩
  exact (heq 1 le_rfl).trans (actual_explicitParameter_first_coefficient U H A B K F e Γ hdata hprep
    R hR hlocal hdeep N M M₀ Y Vold V ht hab hv hentry 1 le_rfl b hb r hr0 hrd n hB)

/-- One actual exponential preparation, actual centered moving inverse,
real normalization anchor, and actual multiplier parameter support every
order. Its coherent logarithmic coefficient sequence has the explicit
orbit-series first coefficient. No coordinate, inverse, Fourier or
parameter expansion is assumed by this existence theorem. -/
theorem exists_actual_physical_coherent_horn_expansion :
    ∃ U H A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F : ℂ × ℂ → ℂ,
    ∃ e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ, ∃ Γ : ℕ → ℂ × ℂ → ℂ,
    ∃ R : ℝ, ∃ N M M₀ : ℕ, ∃ Y : ℝ, ∃ Vold V : ℝ → ℂ → ℂ, ∃ p r : ℂ → ℂ,
      Kneser.ReflectedOrbitChainCoefficient.ActualPreparationData
        U H (first (e 1)) (second (e 1)) A B K F (Γ 1) ∧
      ActualTransitionData U H (first (e 1)) (second (e 1)) A B (Γ 1) R N M₀ Y Vold ∧
      InverseData (centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y) V 12 ∧
      AnalyticAt ℂ p 0 ∧ p 0 = 0 ∧ HasDerivAt p 2 0 ∧
      (∀ x : ℂ, p (x ^ 2) = -Complex.log (Kneser.ExponentialPreparedModel.rootMultiplier U x) *
        Complex.log (Kneser.ExponentialPreparedModel.rootMultiplier U (-x))) ∧
      AnalyticAt ℂ r 0 ∧ r 0 = 0 ∧ HasDerivAt r (1 / 2) 0 ∧
      (∀ᶠ z : ℂ in 𝓝 0, r (p z) = z) ∧ (∀ᶠ z : ℂ in 𝓝 0, p (r z) = z) ∧
      CoherentHornData (transition U H A B e Γ N M Y V) p r ∧
      ∀ n : ℤ, gateFourierCoefficient n 0 (transition U H A B e Γ N M Y V 0) ≠ 0 →
        ∃ a : ℕ → ℂ, a 0 = 0 ∧
          (∀ m : ℕ, ParameterExpansion (logarithm (transition U H A B e Γ N M Y V) n) p a m) ∧
          a 1 = Kneser.hornKappa n
            (gateFourierCoefficient n 0 (transition U H A B e Γ N M Y V 0))
            (gateCorrectionCoefficient n 0 (physicalCorrection U H A B e Γ N M Y V))
            (gateCorrectionCoefficient 0 0 (physicalCorrection U H A B e Γ N M Y V)) := by
  obtain ⟨U, H, A, B, K, F, e, Γ, R, N, M, M₀, Y, Vold, V,
    hdata, hprep, hR, hlocal, hdeep, hab, hentry, ht, hv, hT, hpacket⟩ :=
    exists_actual_real_normalized_transition_with_data
  obtain ⟨p, hpa, hp0, hpd, hproduct⟩ :=
    Kneser.ActualCommonMultiplierParameter.exists_parameter_of_actual_data
      U H (first (e 1)) (second (e 1)) A B K F (Γ 1) hdata
  obtain ⟨r, hra, hr0, hrd, hl, hright, hhorn⟩ :=
    coherent_horn_data_of_actual_packets _ p hpacket hT hpa hp0 hpd
  exact ⟨U, H, A, B, K, F, e, Γ, R, N, M, M₀, Y, Vold, V, p, r,
    hdata, ht, hv, hpa, hp0, hpd, hproduct, hra, hr0, hrd, hl, hright, hhorn,
    coherent_horn_first_coefficient U H A B K F e Γ hdata hprep R hR hlocal hdeep
      N M M₀ Y Vold V ht hab hv hentry p r hr0 hrd hhorn⟩

end Kneser.ActualRealNormalizedFirstCoefficient

end
