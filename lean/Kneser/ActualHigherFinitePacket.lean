import Kneser.HigherGateFiniteFamily

/-! One finite gate packet retains actual maps, absolutely convergent
orbit-series coefficients, their spatial holomorphy, exact baseline and
first coefficient, and every lower compact-uniform integer remainder.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Kneser.ActualHigherFinitePacket

open Filter Set Kneser.ActualBilateralGate Kneser.HigherGateTransport
open Kneser.CommonQuadraticBaseline Kneser.HigherGateIntegerRemainder
open Kneser.HigherGateFiniteFamily Kneser.FiniteExpansionHolomorphy
open Kneser.FirstOrderFiniteConsistency
open scoped Topology

def NormalizedFiniteData (f : ℝ → ℂ → ℂ) (c : ℕ → ℂ → ℂ) (d : ℂ → ℂ)
    (m : ℕ) (U : Set ℂ) : Prop :=
  (∀ j ≤ m, AnalyticOnNhd ℂ (c j) U) ∧
  (∀ u ∈ U, c 0 u = f 0 u ∧ c 1 u = d u) ∧
  ∀ j ≤ m, ∀ K : Set ℂ, IsCompact K → K ⊆ U →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ K,
      ‖f s u - complexPolynomial c j s u‖ ≤ C * s ^ (j + 1)

def Packet (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (N m n L : ℕ) (v : ℂ) : Prop :=
  NormalizedFiniteData
    (fun s u => forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s -
      forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v s)
    (fun j u => HigherGateTransport.forwardCoefficient U H A B n (e n) (Γ n) N L u j -
      HigherGateTransport.forwardCoefficient U H A B n (e n) (Γ n) N L v j)
    (fun u => ActualBilateralGate.forwardCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N u -
      ActualBilateralGate.forwardCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N v)
    m (interior (gate 64 N)) ∧
  NormalizedFiniteData
    (fun s u => backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s -
      backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v s)
    (fun j u => HigherGateTransport.backwardCoefficient U H A B n (e n) (Γ n) N L u j -
      HigherGateTransport.backwardCoefficient U H A B n (e n) (Γ n) N L v j)
    (fun u => ActualBilateralGate.backwardCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N u -
      ActualBilateralGate.backwardCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N v)
    m (interior (gate 64 N)) ∧
  ∀ u ∈ gate 64 N, ∀ j ≤ m + 1,
    Summable (fun k => ‖Kneser.HigherOrderCutoff.termCoefficient
      (Kneser.HigherMovingOrbitDiscs.descendedTerm A B (Γ n) (n + 1)
        (Kneser.HigherGateSeeds.forwardSeed N L) u) j k‖) ∧
    Summable (fun k => ‖Kneser.HigherOrderCutoff.termCoefficient
      (Kneser.ReflectedHigherMovingPreparedCoordinate.shiftedTerm A B (Γ n) (n + 1)
        (Kneser.HigherGateSeeds.backwardSeed N L) u) j k‖)

theorem exists_packet_of_actual_data (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R : ℝ) (N : ℕ)
    (hg : BilateralGateData U H (first (e 1)) (second (e 1)) A B (Γ 1) R 64 N)
    (hab : AbsoluteIntegerGateExpansions U H A B e Γ N)
    (v : ℂ) (hv : v ∈ gate 64 N) (m : ℕ) (hm : 1 ≤ m) :
    ∃ n L : ℕ, Packet U H A B e Γ N m n L v := by
  let n := (m + 1) * (m + 1) + (m + 1)
  obtain ⟨L, hL⟩ := hab m n (by dsimp [n]; omega)
  have ha := normalized_finite_family
    (fun s u => forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s)
    (fun j u => HigherGateTransport.forwardCoefficient U H A B n (e n) (Γ n) N L u j)
    m (gate 64 N) (interior (gate 64 N)) isOpen_interior interior_subset v hv
    (fun S hS hSg => (hg.positive S hS hSg).mono fun s hs u hu => (hs u hu).1)
    (fun S hS hSg => by
      obtain ⟨_hsa, _hsr, C, hC, hb⟩ := hL S hS hSg
      exact ⟨C, hC, hb.mono fun s hs u hu w hw => (hs u hu w hw).1⟩)
  have hr := normalized_finite_family
    (fun s u => backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s)
    (fun j u => HigherGateTransport.backwardCoefficient U H A B n (e n) (Γ n) N L u j)
    m (gate 64 N) (interior (gate 64 N)) isOpen_interior interior_subset v hv
    (fun S hS hSg => (hg.positive S hS hSg).mono fun s hs u hu => (hs u hu).2)
    (fun S hS hSg => by
      obtain ⟨_hsa, _hsr, C, hC, hb⟩ := hL S hS hSg
      exact ⟨C, hC, hb.mono fun s hs u hu w hw => (hs u hu w hw).2⟩)
  have hlow (u : ℂ) (hu : u ∈ interior (gate 64 N)) :
      (HigherGateTransport.forwardCoefficient U H A B n (e n) (Γ n) N L u 0 -
        HigherGateTransport.forwardCoefficient U H A B n (e n) (Γ n) N L v 0 =
        forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u 0 -
          forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v 0) ∧
      (HigherGateTransport.backwardCoefficient U H A B n (e n) (Γ n) N L u 0 -
        HigherGateTransport.backwardCoefficient U H A B n (e n) (Γ n) N L v 0 =
        backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u 0 -
          backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v 0) ∧
      (HigherGateTransport.forwardCoefficient U H A B n (e n) (Γ n) N L u 1 -
        HigherGateTransport.forwardCoefficient U H A B n (e n) (Γ n) N L v 1 =
        ActualBilateralGate.forwardCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N u -
          ActualBilateralGate.forwardCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N v) ∧
      (HigherGateTransport.backwardCoefficient U H A B n (e n) (Γ n) N L u 1 -
        HigherGateTransport.backwardCoefficient U H A B n (e n) (Γ n) N L v 1 =
        ActualBilateralGate.backwardCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N u -
          ActualBilateralGate.backwardCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N v) := by
    let S : Set ℂ := {u, v}
    have hS : IsCompact S := ((Set.finite_singleton v).insert u).isCompact
    have hSg : S ⊆ gate 64 N := by
      intro z hz
      rcases mem_insert_iff.mp hz with rfl | hz
      · exact interior_subset hu
      · exact (mem_singleton_iff.mp hz) ▸ hv
    obtain ⟨_hsa, _hsr, C, hC, hb⟩ := hL S hS hSg
    exact actual_pair_first_coefficients U H A B e Γ R N m n L hg hm u v
      (interior_subset hu) hv C hC
      (hb.mono fun s hs => hs u (by simp [S]) v (by simp [S]))
  refine ⟨n, L, ⟨ha.1, (fun u hu => ⟨(hlow u hu).1, (hlow u hu).2.2.1⟩), ha.2⟩,
    ⟨hr.1, (fun u hu => ⟨(hlow u hu).2.1, (hlow u hu).2.2.2⟩), hr.2⟩, ?_⟩
  intro u hu j hj
  have hs := hL {u} isCompact_singleton (by simpa using hu)
  exact ⟨hs.1 u (by simp) j hj, hs.2.1 u (by simp) j hj⟩

theorem exists_actual_finite_packets :
    ∃ U H A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F : ℂ × ℂ → ℂ,
    ∃ e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ, ∃ Γ : ℕ → ℂ × ℂ → ℂ,
    ∃ R : ℝ, ∃ N : ℕ,
      Kneser.ReflectedOrbitChainCoefficient.ActualPreparationData
        U H (first (e 1)) (second (e 1)) A B K F (Γ 1) ∧
      BilateralGateData U H (first (e 1)) (second (e 1)) A B (Γ 1) R 64 N ∧
      ∀ v ∈ gate 64 N, ∀ m : ℕ, 1 ≤ m → ∃ n L : ℕ, Packet U H A B e Γ N m n L v := by
  obtain ⟨U, H, A, B, K, F, e, Γ, R, N, hdata, _hprep, _hR, _hN,
    ht, hreg, _hint, hg⟩ := exists_actual_same_gate_integer_expansions
  have hab := absoluteIntegerGateExpansions_of_regular U H A B e Γ N ht hreg
  exact ⟨U, H, A, B, K, F, e, Γ, R, N, hdata, hg,
    fun v hv m hm => exists_packet_of_actual_data U H A B e Γ R N hg hab v hv m hm⟩

end Kneser.ActualHigherFinitePacket
