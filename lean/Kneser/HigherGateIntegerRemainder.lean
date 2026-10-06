import Kneser.HigherGateConsistency
import Kneser.UniformAsymptoticTruncation
import Kneser.ActualPreparedSpatialHolomorphy
import Kneser.ReflectedPreparedSpatialHolomorphy
import Kneser.ActualBaselineDeep

/-! The true fixed-gate normalized coordinates have compact-uniform
O(s^(m+1)) remainders. The integer estimate is obtained from the proved
expansion one order further, with coefficient bounds derived by sampling.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Kneser.HigherGateIntegerRemainder

open Filter Set Kneser.ActualBilateralGate Kneser.HigherGateTransport
open Kneser.HigherGateConsistency Kneser.CommonQuadraticBaseline
open Kneser.ReflectedOrbitChainCoefficient Kneser.ActualGateAbel
open Kneser.ParabolicExponentialOrbit Kneser.RepellingExponentialOrbit
open Kneser.AsymptoticBalance
open scoped Topology

def GateSpatialHolomorphy (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ) (N : ℕ) : Prop :=
  ∀ S : Set ℂ, IsCompact S → S ⊆ gate 64 N →
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
      AnalyticAt ℂ (fun v => forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v s) u ∧
      AnalyticAt ℂ (fun v => backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v s) u

theorem exists_actual_gate_spatial_data
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H (first (e 1)) (second (e 1)) A B K F (Γ 1)) :
    ∃ R₀ : ℝ, 64 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ N : ℕ,
      R + 64 + 4 ≤ 3 * (N : ℝ) / 4 → GateSpatialHolomorphy U H A B e Γ N := by
  rcases hdata with ⟨hU, hU0, _hUd, _hH, _hHne, _hHlog, _hA, _hB, _hA0, _hB0,
    _he₁, _he₂, _hF, hΓ, _hEven, hK0, hK, _hq, _hroots, hfactor, _hprep, _hresidue⟩
  have hKne : K 0 0 ≠ 0 := by rw [hK0]; norm_num
  obtain ⟨Ra, _hRa, ha⟩ :=
    Kneser.ActualPreparedSpatialHolomorphy.exists_holomorphic_actualPreparedCoordinate
      U H (first (e 1)) (second (e 1)) A B K (Γ 1) hU hU0 hK hKne hfactor hΓ
  obtain ⟨Rr, _hRr, hr⟩ :=
    Kneser.ReflectedPreparedSpatialHolomorphy.exists_holomorphic_actualInversePreparedCoordinate
      U H (first (e 1)) (second (e 1)) A B K (Γ 1) hU hU0 hK hKne hfactor hΓ
  refine ⟨max 64 (max Ra Rr), le_max_left _ _, ?_⟩
  intro R hR N hN S hS hSg
  have hRpos : 0 < R := by have hh := (le_max_left 64 (max Ra Rr)).trans hR; linarith
  have hRaR : Ra ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hRrR : Rr ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hR)
  have hqa : ∀ Z : ℝ, 0 ≤ Z → ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      DifferentiableOn ℂ
        (fun u => Kneser.PreparedActualFirstOrder.actualPreparedCoordinate
          U H (first (e 1)) (second (e 1)) A B (Γ 1) u s)
        (Kneser.PreparedSpatialHolomorphy.boundedPetal R Z) := by
    intro Z hZ
    obtain ⟨s₀, C, hs₀, _hC, hh⟩ := ha R hRaR Z hZ
    exact ⟨s₀, hs₀, fun s hs hss => (hh s hs hss).1⟩
  have hqr : ∀ Z : ℝ, 0 ≤ Z → ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      DifferentiableOn ℂ
        (fun u => Kneser.ReflectedPreparedFirstOrder.actualInversePreparedCoordinate
          U H (first (e 1)) (second (e 1)) A B (Γ 1) u s)
        (Kneser.PreparedSpatialHolomorphy.boundedPetal R Z) := by
    intro Z hZ
    obtain ⟨s₀, C, hs₀, _hC, hh⟩ := hr R hRrR Z hZ
    exact ⟨s₀, hs₀, fun s hs hss => (hh s hs hss).1⟩
  have hfa := moving_spatial_holomorphy
    (fun s u => Kneser.PreparedActualFirstOrder.actualPreparedCoordinate
      U H (first (e 1)) (second (e 1)) A B (Γ 1) u s)
    (fun p => Kneser.ExponentialUnfolding.orbit p.2 p.1 N) R hRpos hqa S hS
    (fun u _ => Kneser.ParabolicOverlapGate.analyticAt_forward_orbit_joint u 0 N)
    (fun u hu => gate_forward_entry u N R (by linarith) (hSg hu))
  have hfr := moving_spatial_holomorphy
    (fun s u => Kneser.ReflectedPreparedFirstOrder.actualInversePreparedCoordinate
      U H (first (e 1)) (second (e 1)) A B (Γ 1) u s)
    (fun p => inverseOrbit (-p.2) p.1 N) R hRpos hqr S hS
    (fun u hu => analyticAt_backward_transport_joint u N (hSg hu))
    (fun u hu => gate_backward_entry u N R (by linarith) (hSg hu))
  filter_upwards [hfa, hfr] with s hsA hsR u hu
  exact ⟨(hsA u hu).sub analyticAt_const, (hsR u hu).neg.add analyticAt_const⟩

def IntegerGateExpansions (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ) (N : ℕ) : Prop :=
  ∀ m n : ℕ, (m + 1) * (m + 1) + (m + 1) + 1 ≤ n + 1 →
    ∃ L : ℕ, ∀ S : Set ℂ, IsCompact S → S ⊆ gate 64 N →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S, ∀ v ∈ S,
        ‖(forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s -
          forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v s) -
          polynomial (HigherGateTransport.forwardCoefficient U H A B n (e n) (Γ n) N L) m u v s‖ ≤
          C * s ^ ((m : ℝ) + 1) ∧
        ‖(backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s -
          backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v s) -
          polynomial (HigherGateTransport.backwardCoefficient U H A B n (e n) (Γ n) N L) m u v s‖ ≤
          C * s ^ ((m : ℝ) + 1)


def AbsoluteIntegerGateExpansions (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ) (N : ℕ) : Prop :=
  ∀ m n : ℕ, (m + 1) * (m + 1) + (m + 1) + 1 ≤ n + 1 →
    ∃ L : ℕ, ∀ S : Set ℂ, IsCompact S → S ⊆ gate 64 N →
      (∀ u ∈ S, ∀ j ≤ m + 1, Summable (fun k => ‖Kneser.HigherOrderCutoff.termCoefficient
        (Kneser.HigherMovingOrbitDiscs.descendedTerm A B (Γ n) (n + 1)
          (Kneser.HigherGateSeeds.forwardSeed N L) u) j k‖)) ∧
      (∀ u ∈ S, ∀ j ≤ m + 1, Summable (fun k => ‖Kneser.HigherOrderCutoff.termCoefficient
        (Kneser.ReflectedHigherMovingPreparedCoordinate.shiftedTerm A B (Γ n) (n + 1)
          (Kneser.HigherGateSeeds.backwardSeed N L) u) j k‖)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S, ∀ v ∈ S,
        ‖(forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s -
          forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v s) -
          polynomial (HigherGateTransport.forwardCoefficient U H A B n (e n) (Γ n) N L) m u v s‖ ≤
          C * s ^ ((m : ℝ) + 1) ∧
        ‖(backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s -
          backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v s) -
          polynomial (HigherGateTransport.backwardCoefficient U H A B n (e n) (Γ n) N L) m u v s‖ ≤
          C * s ^ ((m : ℝ) + 1)

theorem absoluteIntegerGateExpansions_of_regular (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ) (N : ℕ)
    (ht : FixedGateAllFiniteExpansions U H A B e Γ N)
    (hregular : GateSpatialHolomorphy U H A B e Γ N) :
    AbsoluteIntegerGateExpansions U H A B e Γ N := by
  intro m n hn
  obtain ⟨L, hL⟩ := ht (m + 1) (by omega) n hn
  refine ⟨L, ?_⟩
  intro S hS hSg
  obtain ⟨_hsuma, _hsumr, C, hC, hb⟩ := hL S hS hSg
  have hreg := hregular S hS hSg
  have hba : ∀ᶠ s : ℝ in 𝓝[>] 0, ∃ M : ℝ, ∀ p ∈ S ×ˢ S,
      ‖forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N p.1 s -
        forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N p.2 s‖ ≤ M := by
    filter_upwards [hreg] with s hs
    obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn
      (fun u hu => (hs u hu).1.continuousAt.continuousWithinAt)
    exact ⟨2 * B, fun p hp => (norm_sub_le _ _).trans
      ((add_le_add (hB p.1 hp.1) (hB p.2 hp.2)).trans_eq (by ring))⟩
  have hbr : ∀ᶠ s : ℝ in 𝓝[>] 0, ∃ M : ℝ, ∀ p ∈ S ×ˢ S,
      ‖backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N p.1 s -
        backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N p.2 s‖ ≤ M := by
    filter_upwards [hreg] with s hs
    obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn
      (fun u hu => (hs u hu).2.continuousAt.continuousWithinAt)
    exact ⟨2 * B, fun p hp => (norm_sub_le _ _).trans
      ((add_le_add (hB p.1 hp.1) (hB p.2 hp.2)).trans_eq (by ring))⟩
  obtain ⟨Da, hDa, ha⟩ := Kneser.AsymptoticCoefficientUniqueness.truncate_one_uniform
    (fun (s : ℝ) (p : ℂ × ℂ) => forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N p.1 s -
      forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N p.2 s)
    (fun j p => HigherGateTransport.forwardCoefficient U H A B n (e n) (Γ n) N L p.1 j -
      HigherGateTransport.forwardCoefficient U H A B n (e n) (Γ n) N L p.2 j)
    m (S ×ˢ S) C (gamma (m + 1) (n + 1)) hC (gamma_pos _ _ hn)
    (hb.mono (fun s hs p hp => (hs p.1 hp.1 p.2 hp.2).1)) hba
  obtain ⟨Dr, hDr, hr⟩ := Kneser.AsymptoticCoefficientUniqueness.truncate_one_uniform
    (fun (s : ℝ) (p : ℂ × ℂ) => backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N p.1 s -
      backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N p.2 s)
    (fun j p => HigherGateTransport.backwardCoefficient U H A B n (e n) (Γ n) N L p.1 j -
      HigherGateTransport.backwardCoefficient U H A B n (e n) (Γ n) N L p.2 j)
    m (S ×ˢ S) C (gamma (m + 1) (n + 1)) hC (gamma_pos _ _ hn)
    (hb.mono (fun s hs p hp => (hs p.1 hp.1 p.2 hp.2).2)) hbr
  refine ⟨_hsuma, _hsumr, Da + Dr, by positivity, ?_⟩
  filter_upwards [ha, hr, self_mem_nhdsWithin] with s hsa hsr hs u hu v hv
  have ht : 0 ≤ s ^ ((m : ℝ) + 1) := (Real.rpow_pos_of_pos hs _).le
  exact ⟨(hsa (u, v) ⟨hu, hv⟩).trans (mul_le_mul_of_nonneg_right (by linarith) ht),
    (hsr (u, v) ⟨hu, hv⟩).trans (mul_le_mul_of_nonneg_right (by linarith) ht)⟩


theorem integerGateExpansions_of_regular (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ) (N : ℕ)
    (ht : FixedGateAllFiniteExpansions U H A B e Γ N)
    (hregular : GateSpatialHolomorphy U H A B e Γ N) :
    IntegerGateExpansions U H A B e Γ N := by
  intro m n hn
  obtain ⟨L, hL⟩ := absoluteIntegerGateExpansions_of_regular U H A B e Γ N ht hregular m n hn
  exact ⟨L, fun S hS hSg => (hL S hS hSg).2.2⟩

theorem exists_actual_same_gate_integer_expansions :
    ∃ U H A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F : ℂ × ℂ → ℂ,
    ∃ e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ, ∃ Γ : ℕ → ℂ × ℂ → ℂ,
    ∃ R : ℝ, ∃ N : ℕ,
      ActualPreparationData U H (first (e 1)) (second (e 1)) A B K F (Γ 1) ∧
      (∀ n, Kneser.CommonPreparedFamily.Prepared A B F n (e n) (Γ n)) ∧
      64 ≤ R ∧ R + 64 + 4 ≤ 3 * (N : ℝ) / 4 ∧
      FixedGateAllFiniteExpansions U H A B e Γ N ∧
      GateSpatialHolomorphy U H A B e Γ N ∧ IntegerGateExpansions U H A B e Γ N ∧
      BilateralGateData U H (first (e 1)) (second (e 1)) A B (Γ 1) R 64 N := by
  obtain ⟨U, H, A, B, K, F, e, Γ, hdata, hprep, _ha, _hr, _hca, _hcr⟩ :=
    Kneser.ActualBilateralHigherPreparation.exists_actual_bilateral_common_all_orders
  obtain ⟨Rl, _hRl, hl⟩ := local_abel_data_of_actual U H (first (e 1)) (second (e 1))
    A B K F (Γ 1) hdata
  obtain ⟨Rp, hRp, hp⟩ := exists_actual_gate_spatial_data U H A B K F e Γ hdata
  obtain ⟨Rd, hd⟩ := Kneser.ActualBaselineDeep.deep_data_of_actual
    U H (first (e 1)) (second (e 1)) A B K F (Γ 1) hdata
  let R : ℝ := max Rp (max Rl Rd)
  have hR : 64 ≤ R := hRp.trans (le_max_left _ _)
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * (R + 64 + 4) / 3)
  have hN' : R + 64 + 4 ≤ 3 * (N : ℝ) / 4 := by linarith
  have hlocal : LocalAbelData U H (first (e 1)) (second (e 1)) A B (Γ 1) R :=
    hl.mono ((le_max_left Rl Rd).trans (le_max_right Rp (max Rl Rd)))
  have ht := fixedGateAllFiniteExpansions_of_actual U H A B K F e Γ hdata hprep R hR hlocal N hN'
  have hregular := hp R (le_max_left _ _) N hN'
  exact ⟨U, H, A, B, K, F, e, Γ, R, N, hdata, hprep, hR, hN', ht, hregular,
    integerGateExpansions_of_regular U H A B e Γ N ht hregular,
    bilateral_gate_data_of_deep U H (first (e 1)) (second (e 1)) A B (Γ 1) R
      (hd.mono ((le_max_right Rl Rd).trans (le_max_right _ _))) N (by linarith)⟩

end Kneser.HigherGateIntegerRemainder
