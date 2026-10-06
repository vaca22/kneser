import Kneser.HigherGateTransport
import Kneser.AsymptoticTruncation

/-! On the fixed actual overlap gate, normalized finite expansion
coefficients are independent of both the preparation degree and the
later petal-entry length. This follows from the proved actual remainders.
-/

set_option autoImplicit false
noncomputable section
namespace Kneser.HigherGateConsistency

open Filter Set Kneser.HigherGateTransport Kneser.ActualBilateralGate
open Kneser.CommonQuadraticBaseline Kneser.AsymptoticBalance
open scoped Topology

def GateExpansion (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (N m n L : ℕ) : Prop :=
  ∀ S : Set ℂ, IsCompact S → S ⊆ gate 64 N →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S, ∀ v ∈ S,
      ‖(forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s -
        forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v s) -
        polynomial (forwardCoefficient U H A B n (e n) (Γ n) N L) m u v s‖ ≤
        C * s ^ ((m : ℝ) + gamma m (n + 1)) ∧
      ‖(backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s -
        backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v s) -
        polynomial (backwardCoefficient U H A B n (e n) (Γ n) N L) m u v s‖ ≤
        C * s ^ ((m : ℝ) + gamma m (n + 1))

theorem exists_gateExpansion (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ) (N : ℕ)
    (ht : FixedGateAllFiniteExpansions U H A B e Γ N)
    (m n : ℕ) (hm : 1 ≤ m) (hn : m * m + m + 1 ≤ n + 1) :
    ∃ L, GateExpansion U H A B e Γ N m n L := by
  obtain ⟨L, hL⟩ := ht m hm n hn
  refine ⟨L, ?_⟩
  intro S hS hSg
  exact (hL S hS hSg).2.2

theorem coefficients_eq_of_gateExpansions (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (N m n₁ n₂ L₁ L₂ : ℕ)
    (hn₁ : m * m + m + 1 ≤ n₁ + 1) (hn₂ : m * m + m + 1 ≤ n₂ + 1)
    (h₁ : GateExpansion U H A B e Γ N m n₁ L₁)
    (h₂ : GateExpansion U H A B e Γ N m n₂ L₂)
    (u v : ℂ) (hu : u ∈ gate 64 N) (hv : v ∈ gate 64 N) :
    ∀ j ≤ m,
      forwardCoefficient U H A B n₁ (e n₁) (Γ n₁) N L₁ u j -
        forwardCoefficient U H A B n₁ (e n₁) (Γ n₁) N L₁ v j =
      forwardCoefficient U H A B n₂ (e n₂) (Γ n₂) N L₂ u j -
        forwardCoefficient U H A B n₂ (e n₂) (Γ n₂) N L₂ v j ∧
      backwardCoefficient U H A B n₁ (e n₁) (Γ n₁) N L₁ u j -
        backwardCoefficient U H A B n₁ (e n₁) (Γ n₁) N L₁ v j =
      backwardCoefficient U H A B n₂ (e n₂) (Γ n₂) N L₂ u j -
        backwardCoefficient U H A B n₂ (e n₂) (Γ n₂) N L₂ v j := by
  let S : Set ℂ := {u, v}
  have hS : IsCompact S := ((Set.finite_singleton v).insert u).isCompact
  have huS : u ∈ S := by simp [S]
  have hvS : v ∈ S := by simp [S]
  have hSg : S ⊆ gate 64 N := by
    intro z hz
    simp only [S, mem_insert_iff, mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> assumption
  obtain ⟨C₁, hC₁, hb₁⟩ := h₁ S hS hSg
  obtain ⟨C₂, hC₂, hb₂⟩ := h₂ S hS hSg
  have ha₁ := hb₁.mono (fun s hs => (hs u huS v hvS).1)
  have ha₂ := hb₂.mono (fun s hs => (hs u huS v hvS).1)
  have hr₁ := hb₁.mono (fun s hs => (hs u huS v hvS).2)
  have hr₂ := hb₂.mono (fun s hs => (hs u huS v hvS).2)
  have ha := Kneser.AsymptoticCoefficientUniqueness.coefficients_unique_of_common_expansions
    (fun s => forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s -
      forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v s)
    (fun j => forwardCoefficient U H A B n₁ (e n₁) (Γ n₁) N L₁ u j -
      forwardCoefficient U H A B n₁ (e n₁) (Γ n₁) N L₁ v j)
    (fun j => forwardCoefficient U H A B n₂ (e n₂) (Γ n₂) N L₂ u j -
      forwardCoefficient U H A B n₂ (e n₂) (Γ n₂) N L₂ v j)
    m C₁ C₂ (gamma m (n₁ + 1)) (gamma m (n₂ + 1)) hC₁ hC₂
    (gamma_pos _ _ hn₁) (gamma_pos _ _ hn₂) ha₁ ha₂
  have hr := Kneser.AsymptoticCoefficientUniqueness.coefficients_unique_of_common_expansions
    (fun s => backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s -
      backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v s)
    (fun j => backwardCoefficient U H A B n₁ (e n₁) (Γ n₁) N L₁ u j -
      backwardCoefficient U H A B n₁ (e n₁) (Γ n₁) N L₁ v j)
    (fun j => backwardCoefficient U H A B n₂ (e n₂) (Γ n₂) N L₂ u j -
      backwardCoefficient U H A B n₂ (e n₂) (Γ n₂) N L₂ v j)
    m C₁ C₂ (gamma m (n₁ + 1)) (gamma m (n₂ + 1)) hC₁ hC₂
    (gamma_pos _ _ hn₁) (gamma_pos _ _ hn₂) hr₁ hr₂
  exact fun j hj => ⟨ha j hj, hr j hj⟩

theorem coefficients_eq_of_different_gate_orders (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (N m M n₁ n₂ L₁ L₂ : ℕ) (hmM : m ≤ M)
    (hn₁ : m * m + m + 1 ≤ n₁ + 1) (hn₂ : M * M + M + 1 ≤ n₂ + 1)
    (h₁ : GateExpansion U H A B e Γ N m n₁ L₁)
    (h₂ : GateExpansion U H A B e Γ N M n₂ L₂)
    (u v : ℂ) (hu : u ∈ gate 64 N) (hv : v ∈ gate 64 N) :
    ∀ j ≤ m,
      forwardCoefficient U H A B n₁ (e n₁) (Γ n₁) N L₁ u j -
        forwardCoefficient U H A B n₁ (e n₁) (Γ n₁) N L₁ v j =
      forwardCoefficient U H A B n₂ (e n₂) (Γ n₂) N L₂ u j -
        forwardCoefficient U H A B n₂ (e n₂) (Γ n₂) N L₂ v j ∧
      backwardCoefficient U H A B n₁ (e n₁) (Γ n₁) N L₁ u j -
        backwardCoefficient U H A B n₁ (e n₁) (Γ n₁) N L₁ v j =
      backwardCoefficient U H A B n₂ (e n₂) (Γ n₂) N L₂ u j -
        backwardCoefficient U H A B n₂ (e n₂) (Γ n₂) N L₂ v j := by
  let S : Set ℂ := {u, v}
  have hS : IsCompact S := ((Set.finite_singleton v).insert u).isCompact
  have huS : u ∈ S := by simp [S]
  have hvS : v ∈ S := by simp [S]
  have hSg : S ⊆ gate 64 N := by
    intro z hz
    simp only [S, mem_insert_iff, mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> assumption
  obtain ⟨C₁, hC₁, hb₁⟩ := h₁ S hS hSg
  obtain ⟨C₂, hC₂, hb₂⟩ := h₂ S hS hSg
  have ha₁ := hb₁.mono (fun s hs => (hs u huS v hvS).1)
  have ha₂ := hb₂.mono (fun s hs => (hs u huS v hvS).1)
  have hr₁ := hb₁.mono (fun s hs => (hs u huS v hvS).2)
  have hr₂ := hb₂.mono (fun s hs => (hs u huS v hvS).2)
  have ha := Kneser.AsymptoticCoefficientUniqueness.coefficients_unique_of_different_orders
    (fun s => forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s -
      forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v s)
    (fun j => forwardCoefficient U H A B n₁ (e n₁) (Γ n₁) N L₁ u j -
      forwardCoefficient U H A B n₁ (e n₁) (Γ n₁) N L₁ v j)
    (fun j => forwardCoefficient U H A B n₂ (e n₂) (Γ n₂) N L₂ u j -
      forwardCoefficient U H A B n₂ (e n₂) (Γ n₂) N L₂ v j)
    m M hmM C₁ C₂ (gamma m (n₁ + 1)) (gamma M (n₂ + 1)) hC₁ hC₂
    (gamma_pos _ _ hn₁) (gamma_pos _ _ hn₂) ha₁ ha₂
  have hr := Kneser.AsymptoticCoefficientUniqueness.coefficients_unique_of_different_orders
    (fun s => backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s -
      backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v s)
    (fun j => backwardCoefficient U H A B n₁ (e n₁) (Γ n₁) N L₁ u j -
      backwardCoefficient U H A B n₁ (e n₁) (Γ n₁) N L₁ v j)
    (fun j => backwardCoefficient U H A B n₂ (e n₂) (Γ n₂) N L₂ u j -
      backwardCoefficient U H A B n₂ (e n₂) (Γ n₂) N L₂ v j)
    m M hmM C₁ C₂ (gamma m (n₁ + 1)) (gamma M (n₂ + 1)) hC₁ hC₂
    (gamma_pos _ _ hn₁) (gamma_pos _ _ hn₂) hr₁ hr₂
  exact fun j hj => ⟨ha j hj, hr j hj⟩

end Kneser.HigherGateConsistency
