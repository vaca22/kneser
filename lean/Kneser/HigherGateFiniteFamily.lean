import Kneser.FirstOrderFiniteConsistency
import Kneser.FiniteExpansionHolomorphy

/-! Genuine finite orbit-series coefficient lists give analytic finite
Taylor families on the interior of the same actual overlap gate. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Kneser.HigherGateFiniteFamily

open Filter Set Kneser.ActualBilateralGate Kneser.HigherGateTransport
open Kneser.HigherGateIntegerRemainder Kneser.CommonQuadraticBaseline
open Kneser.FiniteExpansionHolomorphy
open scoped Topology

theorem normalized_finite_family (f : ℝ → ℂ → ℂ) (c : ℕ → ℂ → ℂ)
    (m : ℕ) (G U : Set ℂ) (hU : IsOpen U) (hUG : U ⊆ G) (v : ℂ) (hv : v ∈ G)
    (hregular : ∀ S : Set ℂ, IsCompact S → S ⊆ G →
      ∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (f s) S)
    (hexp : ∀ S : Set ℂ, IsCompact S → S ⊆ G →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S, ∀ w ∈ S,
        ‖(f s u - f s w) - Kneser.AsymptoticCoefficientUniqueness.polynomial
          (fun j => c j u - c j w) m s‖ ≤ C * s ^ ((m : ℝ) + 1)) :
    (∀ j ≤ m, AnalyticOnNhd ℂ (fun u => c j u - c j v) U) ∧
    ∀ j ≤ m, ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ K,
        ‖(f s u - f s v) - complexPolynomial (fun j u => c j u - c j v) j s u‖ ≤
          C * s ^ (j + 1) := by
  have hF : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (fun u => f s u - f s v) K := by
    intro K hK hKU
    filter_upwards [hregular K hK (hKU.trans hUG)] with s hs u hu
    exact (hs u hu).sub analyticAt_const
  have hE : ∀ j ≤ m, ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ K,
        ‖(f s u - f s v) - complexPolynomial (fun j u => c j u - c j v) j s u‖ ≤
          C * s ^ (j + 1) := by
    intro j hj K hK hKU
    let S : Set ℂ := insert v K
    have hS : IsCompact S := hK.insert v
    have hSg : S ⊆ G := by
      intro u hu
      rcases mem_insert_iff.mp hu with rfl | hu
      · exact hv
      · exact hUG (hKU hu)
    obtain ⟨C, hC, hb⟩ := hexp S hS hSg
    have hmain : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ K,
        ‖(f s u - f s v) - Kneser.AsymptoticCoefficientUniqueness.polynomial
          (fun k => c k u - c k v) m s‖ ≤ C * s ^ ((m : ℝ) + 1) :=
      hb.mono (fun s hs u hu => hs u (mem_insert_of_mem v hu) v (mem_insert v K))
    have hbound : ∀ᶠ s : ℝ in 𝓝[>] 0, ∃ B : ℝ, ∀ u ∈ K, ‖f s u - f s v‖ ≤ B := by
      filter_upwards [hregular S hS hSg] with s hs
      obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn (fun u hu => (hs u hu).continuousAt.continuousWithinAt)
      exact ⟨2 * B, fun u hu => (norm_sub_le _ _).trans ((add_le_add
        (hB u (mem_insert_of_mem v hu)) (hB v (mem_insert v K))).trans_eq (by ring))⟩
    obtain ⟨D, hD, hd⟩ := Kneser.AsymptoticCoefficientUniqueness.truncate_uniform_integer
      (fun s u => f s u - f s v) (fun k u => c k u - c k v) m j hj K C hC hmain hbound
    refine ⟨D, hD, ?_⟩
    have hp : (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) := by push_cast; ring
    simpa only [hp, Real.rpow_natCast, Kneser.AsymptoticCoefficientUniqueness.polynomial,
      complexPolynomial] using hd
  exact ⟨coefficients_analyticOnNhd (fun s u => f s u - f s v) (fun j u => c j u - c j v)
    m U hU hF (fun j hj K hK hKU => by
      obtain ⟨C, _hC, hb⟩ := hE j hj K hK hKU
      exact ⟨C, hb⟩), hE⟩

theorem actual_bilateral_finite_family (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ) (N : ℕ)
    (hregular : GateSpatialHolomorphy U H A B e Γ N)
    (hint : IntegerGateExpansions U H A B e Γ N)
    (v : ℂ) (hv : v ∈ gate 64 N) (m : ℕ) :
    ∃ n L : ℕ,
      (∀ j ≤ m, AnalyticOnNhd ℂ (fun u => HigherGateTransport.forwardCoefficient
        U H A B n (e n) (Γ n) N L u j - HigherGateTransport.forwardCoefficient
          U H A B n (e n) (Γ n) N L v j) (interior (gate 64 N))) ∧
      (∀ j ≤ m, AnalyticOnNhd ℂ (fun u => HigherGateTransport.backwardCoefficient
        U H A B n (e n) (Γ n) N L u j - HigherGateTransport.backwardCoefficient
          U H A B n (e n) (Γ n) N L v j) (interior (gate 64 N))) ∧
      (∀ j ≤ m, ∀ K : Set ℂ, IsCompact K → K ⊆ interior (gate 64 N) →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ K,
          ‖(forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s -
            forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v s) -
            HigherGateTransport.polynomial (HigherGateTransport.forwardCoefficient
              U H A B n (e n) (Γ n) N L) j u v s‖ ≤ C * s ^ (j + 1) ∧
          ‖(backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s -
            backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v s) -
            HigherGateTransport.polynomial (HigherGateTransport.backwardCoefficient
              U H A B n (e n) (Γ n) N L) j u v s‖ ≤ C * s ^ (j + 1)) := by
  let n := (m + 1) * (m + 1) + (m + 1)
  obtain ⟨L, hL⟩ := hint m n (by dsimp [n]; omega)
  have ha := normalized_finite_family
    (fun s u => forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s)
    (fun j u => HigherGateTransport.forwardCoefficient U H A B n (e n) (Γ n) N L u j)
    m (gate 64 N) (interior (gate 64 N)) isOpen_interior interior_subset v hv
    (fun S hS hSg => (hregular S hS hSg).mono fun s hs u hu => (hs u hu).1)
    (fun S hS hSg => by
      obtain ⟨C, hC, hb⟩ := hL S hS hSg
      exact ⟨C, hC, hb.mono fun s hs u hu w hw => (hs u hu w hw).1⟩)
  have hr := normalized_finite_family
    (fun s u => backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s)
    (fun j u => HigherGateTransport.backwardCoefficient U H A B n (e n) (Γ n) N L u j)
    m (gate 64 N) (interior (gate 64 N)) isOpen_interior interior_subset v hv
    (fun S hS hSg => (hregular S hS hSg).mono fun s hs u hu => (hs u hu).2)
    (fun S hS hSg => by
      obtain ⟨C, hC, hb⟩ := hL S hS hSg
      exact ⟨C, hC, hb.mono fun s hs u hu w hw => (hs u hu w hw).2⟩)
  refine ⟨n, L, ha.1, hr.1, ?_⟩
  intro j hj K hK hKU
  obtain ⟨Ca, hCa, hea⟩ := ha.2 j hj K hK hKU
  obtain ⟨Cr, hCr, her⟩ := hr.2 j hj K hK hKU
  refine ⟨Ca + Cr, by positivity, ?_⟩
  filter_upwards [hea, her, self_mem_nhdsWithin] with s hsA hsR hs u hu
  have hp : 0 ≤ s ^ (j + 1) := pow_nonneg hs.le _
  exact ⟨(hsA u hu).trans (mul_le_mul_of_nonneg_right (by linarith) hp),
    (hsR u hu).trans (mul_le_mul_of_nonneg_right (by linarith) hp)⟩

end Kneser.HigherGateFiniteFamily
