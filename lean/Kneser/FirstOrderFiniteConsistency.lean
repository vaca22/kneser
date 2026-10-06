import Kneser.HigherGateIntegerRemainder
import Kneser.QuantitativeHornExpansion

/-! Finite all-orders coefficient lists recover the actual zero-parameter
coordinate and the already proved first orbit-series coefficient. -/

noncomputable section
namespace Kneser.FirstOrderFiniteConsistency

open Filter Set Kneser.AsymptoticCoefficientUniqueness
open Kneser.QuantitativeHornExpansion Kneser.ActualBilateralGate
open Kneser.CommonQuadraticBaseline
open scoped Topology

theorem first_coefficients_of_integer_expansion (f : ℝ → ℂ) (c : ℕ → ℂ)
    (m : ℕ) (hm : 1 ≤ m) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᶠ s : ℝ in 𝓝[>] 0, ‖f s - polynomial c m s‖ ≤ C * s ^ ((m : ℝ) + 1))
    (d : ℂ) (q : ℝ) (hq : 1 < q) (hf : PowerExpansion f d q) :
    c 0 = f 0 ∧ c 1 = d := by
  obtain ⟨D, hD, hd⟩ := hf
  let b : ℕ → ℂ := fun j => if j = 0 then f 0 else d
  have hp : ∀ s, polynomial b 1 s = f 0 + (s : ℂ) * d := by
    intro s
    simp [polynomial, b, Finset.sum_range_succ]
  have hdb : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖f s - polynomial b 1 s‖ ≤ D * s ^ (((1 : ℕ) : ℝ) + (q - 1)) := by
    filter_upwards [hd] with s hs
    rw [hp]
    simpa only [Nat.cast_one, show (1 : ℝ) + (q - 1) = q by ring, sub_add_eq_sub_sub] using hs
  have he := coefficients_unique_of_different_orders f b c 1 m hm D C (q - 1) 1
    hD hC (by linarith) (by norm_num) hdb hb
  exact ⟨(he 0 (by omega)).symm.trans (by simp [b]),
    (he 1 le_rfl).symm.trans (by simp [b])⟩

theorem paired_powerExpansion (f : ℝ → ℂ → ℂ) (D : ℂ → ℂ) (q C : ℝ)
    (hC : 0 ≤ C) (u v : ℂ)
    (hb : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖f s u - f 0 u - (s : ℂ) * D u‖ ≤ C * s ^ q ∧
      ‖f s v - f 0 v - (s : ℂ) * D v‖ ≤ C * s ^ q) :
    PowerExpansion (fun s => f s u - f s v) (D u - D v) q := by
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [hb] with s hs
  have he : (f s u - f s v) - (f 0 u - f 0 v) - (s : ℂ) * (D u - D v) =
      (f s u - f 0 u - (s : ℂ) * D u) - (f s v - f 0 v - (s : ℂ) * D v) := by ring
  rw [he]
  exact (norm_sub_le _ _).trans ((add_le_add hs.1 hs.2).trans_eq (by ring))

theorem actual_pair_first_coefficients
    (U H A B : ℂ → ℂ) (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ)
    (Γ : ℕ → ℂ × ℂ → ℂ) (R : ℝ) (N m n L : ℕ)
    (hg : BilateralGateData U H (first (e 1)) (second (e 1)) A B (Γ 1) R 64 N)
    (hm : 1 ≤ m) (u v : ℂ) (hu : u ∈ gate 64 N) (hv : v ∈ gate 64 N)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖(forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s -
        forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v s) -
        HigherGateTransport.polynomial (HigherGateTransport.forwardCoefficient
          U H A B n (e n) (Γ n) N L) m u v s‖ ≤ C * s ^ ((m : ℝ) + 1) ∧
      ‖(backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s -
        backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v s) -
        HigherGateTransport.polynomial (HigherGateTransport.backwardCoefficient
          U H A B n (e n) (Γ n) N L) m u v s‖ ≤ C * s ^ ((m : ℝ) + 1)) :
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
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact hu
    · exact (Set.mem_singleton_iff.mp hz) ▸ hv
  obtain ⟨D, hD, hd⟩ := hg.uniform S hS hSg
  have ha := paired_powerExpansion
    (fun s z => forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N z s)
    (ActualBilateralGate.forwardCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N)
    (6 / 5) D hD u v
    (hd.mono fun s hs => ⟨(hs u (by simp [S])).1, (hs v (by simp [S])).1⟩)
  have hr := paired_powerExpansion
    (fun s z => backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N z s)
    (ActualBilateralGate.backwardCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N)
    (6 / 5) D hD u v
    (hd.mono fun s hs => ⟨(hs u (by simp [S])).2, (hs v (by simp [S])).2⟩)
  have heA := first_coefficients_of_integer_expansion _ _ m hm C hC
    (hb.mono fun s hs => hs.1) _ (6 / 5) (by norm_num) ha
  have heR := first_coefficients_of_integer_expansion _ _ m hm C hC
    (hb.mono fun s hs => hs.2) _ (6 / 5) (by norm_num) hr
  exact ⟨heA.1, heR.1, heA.2, heR.2⟩

end Kneser.FirstOrderFiniteConsistency
