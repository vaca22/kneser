import Kneser.ActualAllOrderCenteredTransition
import Kneser.ActualRealAnchorFinitePacket
import Kneser.FinitePacketPullback

/-! Arbitrary finite expansions of one genuine transition, normalized at
the manuscript's real anchor.  Its common moving inverse is constructed
from the actual centered repelling family. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Kneser.ActualRealNormalizedTransition

open Filter Set Metric Kneser.ActualBilateralGate Kneser.ActualGateAbel
open Kneser.ActualQuantitativeGateTransition Kneser.ActualHigherFinitePacket
open Kneser.ActualCenteredGatePacket Kneser.AllOrderSingleInverse Kneser.AllOrderCompactGate
open Kneser.CommonQuadraticBaseline Kneser.ActualDeepCoordinateData
open Kneser.HigherGateIntegerRemainder Kneser.HigherGateTransport
open Kneser.ActualRealAnchorHigherGate Kneser.ActualRealAnchorFinitePacket
open Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit Kneser.RealNormalizationAnchor
open scoped Topology

def transition (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ) (s : ℝ) (z : ℂ) : ℂ :=
  normalizedCoordinate U H A B e Γ N M s (chartPoint Y (V s z))

theorem real_normalized_transition_all_orders (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ)
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
    (hentry : R + 2 ≤ (inverseCoordinate (orbit normalizationAnchor 0 M)).re) :
    ∀ m : ℕ, 1 ≤ m → ∃ b : ℕ → ℂ → ℂ,
      FinitePacket (transition U H A B e Γ N M Y V) b m (ball (0 : ℂ) 3) := by
  intro m hm
  let f := centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y
  let q := fun s z => normalizedCoordinate U H A B e Γ N M s (chartPoint Y z)
  have hN : R + 64 + 4 ≤ 3 * (N : ℝ) / 4 := by linarith [ht.length_margin]
  obtain ⟨n, L, hp⟩ := exists_packet_of_actual_data U H A B e Γ R N ht.bilateral hab (chartPoint Y 0)
    (chartPoint_in_gate N Y ht.height 0 (by simp)) m hm
  have hc := (centered_packet_of_packet U H A B e Γ N m n L Y ht.height hp).2
  obtain ⟨na, La, hpa, _hsa⟩ := real_anchor_packet U H A B K F e Γ hdata hprep R hR hlocal hdeep
    N M hN ht.bilateral hentry m hm
  have hqa : AnalyticOnNhd ℂ (chartPoint Y) (ball (0 : ℂ) 56) := by
    intro z hz
    exact chartPoint_analytic N Y ht.height z
      (closedBall_subset_closedBall (by norm_num) (ball_subset_closedBall hz))
  have hqm : MapsTo (chartPoint Y) (ball (0 : ℂ) 56) (interior (gate 64 N)) :=
    fun z hz => chartPoint_in_interior N Y ht.height z (ball_subset_closedBall hz)
  have ha := Kneser.FinitePacketPullback.normalizedFiniteData_pullback _ _ _ (chartPoint Y)
    m _ _ hpa hqa hqm
  have hsub : closedBall (0 : ℂ) 48 ⊆ ball (0 : ℂ) 56 := by
    intro z hz
    exact (show dist z 0 ≤ 48 from hz).trans_lt (by norm_num)
  obtain ⟨CF, hCF, hEF⟩ := hc.2.2 m le_rfl _ (isCompact_closedBall _ _) hsub
  obtain ⟨CA, hCA, hEA⟩ := ha.2.2 m le_rfl _ (isCompact_closedBall _ _) hsub
  obtain ⟨b, hb⟩ := global_finite_transition_expansion f V q _ _ m 12 CF CA
    (by norm_num) hCF hCA hv.1 (hv.2.2.1.mono fun _ hs => hs.1)
    hv.2.2.2.1 hv.2.2.2.2.1 hv.2.2.2.2.2
    (by intro j hj; exact (hc.1 j hj).mono (ball_subset_ball (by norm_num)))
    (by intro j hj; exact (ha.1 j hj).mono (by simpa only [show (4 : ℝ) * 12 = 48 by norm_num] using hsub))
    (fun u hu => (hc.2.1 u ((ball_subset_ball (by norm_num)) hu)).1)
    (fun u hu => (ha.2.1 u ((ball_subset_ball (by norm_num)) hu)).1)
    (by simpa only [show (4 : ℝ) * 12 = 48 by norm_num] using hEF)
    (by simpa only [show (4 : ℝ) * 12 = 48 by norm_num] using hEA)
  refine ⟨b, ?_⟩
  norm_num only [show (12 : ℝ) / 4 = 3 by norm_num] at hb
  exact hb

/-- Spatial holomorphy is derived for the actual moving transition, not
postulated as an input to its eventual Fourier expansion. -/
theorem transition_positive_analytic (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R : ℝ) (N M M₀ : ℕ) (Y : ℝ) (Vold V : ℝ → ℂ → ℂ)
    (ht : ActualTransitionData U H (first (e 1)) (second (e 1)) A B (Γ 1) R N M₀ Y Vold)
    (hv : InverseData (centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y) V 12) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (transition U H A B e Γ N M Y V s) (ball (0 : ℂ) 3) := by
  obtain ⟨hPc, hPg⟩ := chart_compact_gate N Y ht.height
  filter_upwards [ht.bilateral.positive _ hPc hPg, hv.2.2.1] with s hp hs z hz
  have hz' : z ∈ ball (0 : ℂ) (12 / 4) := by simpa only [show (12 : ℝ) / 4 = 3 by norm_num] using hz
  have hw64 : V s z ∈ closedBall (0 : ℂ) 64 := closedBall_subset_closedBall (by norm_num) (hs.1 z hz').1
  have hchart : AnalyticAt ℂ (fun w => normalizedCoordinate U H A B e Γ N M s (chartPoint Y w)) (V s z) := ((hp _ (mem_image_of_mem (chartPoint Y) hw64)).1.comp_of_eq
    (chartPoint_analytic N Y ht.height _ hw64) rfl).sub analyticAt_const
  exact hchart.comp_of_eq (hs.2 z hz') rfl

/-- Unconditional genuine real normalization and one common actual inverse
are constructed before the requested order. -/
theorem exists_actual_real_normalized_transition_with_data :
    ∃ U H A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F : ℂ × ℂ → ℂ,
    ∃ e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ, ∃ Γ : ℕ → ℂ × ℂ → ℂ,
    ∃ R : ℝ, ∃ N M M₀ : ℕ, ∃ Y : ℝ, ∃ Vold V : ℝ → ℂ → ℂ,
      Kneser.ReflectedOrbitChainCoefficient.ActualPreparationData
        U H (first (e 1)) (second (e 1)) A B K F (Γ 1) ∧
      (∀ n, Kneser.CommonPreparedFamily.Prepared A B F n (e n) (Γ n)) ∧
      64 ≤ R ∧
      LocalAbelData U H (first (e 1)) (second (e 1)) A B (Γ 1) R ∧
      DeepCoordinateData U H (first (e 1)) (second (e 1)) A B (Γ 1) R ∧
      AbsoluteIntegerGateExpansions U H A B e Γ N ∧
      R + 2 ≤ (inverseCoordinate (orbit normalizationAnchor 0 M)).re ∧
      ActualTransitionData U H (first (e 1)) (second (e 1)) A B (Γ 1) R N M₀ Y Vold ∧
      InverseData (centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y) V 12 ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (transition U H A B e Γ N M Y V s) (ball (0 : ℂ) 3)) ∧
      ∀ m : ℕ, 1 ≤ m → ∃ b : ℕ → ℂ → ℂ,
        FinitePacket (transition U H A B e Γ N M Y V) b m (ball (0 : ℂ) 3) := by
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
  obtain ⟨N, M₀, Y, Vold, ht⟩ := exists_transition_data_of_deep
    U H (first (e 1)) (second (e 1)) A B (Γ 1) R hdeep
  have hN : R + 64 + 4 ≤ 3 * (N : ℝ) / 4 := by linarith [ht.length_margin]
  have hfinite := fixedGateAllFiniteExpansions_of_actual U H A B K F e Γ hdata hprep R hR hlocal N hN
  have hregular := hp R (le_max_left _ _) N hN
  have hab := absoluteIntegerGateExpansions_of_regular U H A B e Γ N hfinite hregular
  obtain ⟨V, hV, _hm⟩ := Kneser.ActualAllOrderCenteredTransition.all_orders_of_actual_data U H A B e Γ R Y N M₀ Vold ht hab
  obtain ⟨M, hM, _hMa⟩ := Kneser.RealNormalizationAnchor.exists_anchor_enters_petal (R + 2)
  have hentry : R + 2 ≤ (inverseCoordinate (orbit normalizationAnchor 0 M)).re := by
    have hh : R + 2 < (inverseCoordinate (orbit normalizationAnchor 0 M)).re := hM
    exact hh.le
  exact ⟨U, H, A, B, K, F, e, Γ, R, N, M, M₀, Y, Vold, V, hdata, hprep, hR, hlocal, hdeep, hab, hentry, ht, hV,
    transition_positive_analytic U H A B e Γ R N M M₀ Y Vold V ht hV,
    real_normalized_transition_all_orders U H A B K F e Γ hdata hprep R hR hlocal hdeep N M M₀ Y Vold V ht hab hV hentry⟩


theorem exists_actual_real_normalized_transition_all_orders :
    ∃ U H A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F : ℂ × ℂ → ℂ,
    ∃ e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ, ∃ Γ : ℕ → ℂ × ℂ → ℂ,
    ∃ R : ℝ, ∃ N M M₀ : ℕ, ∃ Y : ℝ, ∃ Vold V : ℝ → ℂ → ℂ,
      Kneser.ReflectedOrbitChainCoefficient.ActualPreparationData
        U H (first (e 1)) (second (e 1)) A B K F (Γ 1) ∧
      ActualTransitionData U H (first (e 1)) (second (e 1)) A B (Γ 1) R N M₀ Y Vold ∧
      InverseData (centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y) V 12 ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (transition U H A B e Γ N M Y V s) (ball (0 : ℂ) 3)) ∧
      ∀ m : ℕ, 1 ≤ m → ∃ b : ℕ → ℂ → ℂ,
        FinitePacket (transition U H A B e Γ N M Y V) b m (ball (0 : ℂ) 3) := by
  obtain ⟨U, H, A, B, K, F, e, Γ, R, N, M, M₀, Y, Vold, V,
    hdata, _hprep, _hR, _hlocal, _hdeep, _hab, _hentry, ht, hv, hT, hpacket⟩ :=
    exists_actual_real_normalized_transition_with_data
  exact ⟨U, H, A, B, K, F, e, Γ, R, N, M, M₀, Y, Vold, V, hdata, ht, hv, hT, hpacket⟩

end Kneser.ActualRealNormalizedTransition
