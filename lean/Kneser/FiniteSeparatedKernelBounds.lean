import Kneser.SeparatedKernelBounds

/-! Finite-bootstrap versions of the uniform kernel sums. No information
about the true orbit after the controlled finite segment is required. -/

set_option autoImplicit false
noncomputable section
namespace Kneser.FiniteSeparatedKernelBounds

open Kneser.SeparatedKernelBounds
open scoped BigOperators

def extendFinite (x : ℕ → ℝ) (N : ℕ) (c : ℝ) (k : ℕ) : ℝ :=
  if k ≤ N then x k else x N + c * (k - N : ℕ)

theorem extendFinite_eq (x : ℕ → ℝ) (N : ℕ) (c : ℝ) (k : ℕ) (hk : k ≤ N) :
    extendFinite x N c k = x k := by simp [extendFinite, hk]

theorem extendFinite_step (x : ℕ → ℝ) (N : ℕ) (c : ℝ)
    (hstep : ∀ k : ℕ, k < N → x k + c ≤ x (k + 1)) :
    ∀ k, extendFinite x N c k + c ≤ extendFinite x N c (k + 1) := by
  intro k
  by_cases hk : k < N
  · rw [extendFinite_eq x N c k (by omega), extendFinite_eq x N c (k + 1) (by omega)]
    exact hstep k hk
  · have hkN : N ≤ k := by omega
    by_cases he : k = N
    · subst k
      simp [extendFinite]
    · have hk' : ¬k ≤ N := by omega
      have hks : ¬k + 1 ≤ N := by omega
      have hdiff : k + 1 - N = k - N + 1 := by omega
      simp only [extendFinite, if_neg hk', if_neg hks, hdiff, Nat.cast_add, Nat.cast_one]
      linarith

theorem finite_rational_kernel_bound (x : ℕ → ℝ) (N : ℕ) (c Y : ℝ)
    (hc : 0 < c) (hY : 1 ≤ Y)
    (hstep : ∀ k : ℕ, k < N → x k + c ≤ x (k + 1)) :
    (∑ k ∈ Finset.range N, ((x k ^ 2 + Y ^ 2) ^ 2)⁻¹) ≤ (2 + Real.pi / c) / Y ^ 3 := by
  obtain ⟨hs, hb⟩ := rational_orbit_kernel_bound (extendFinite x N c) c Y hc hY
    (extendFinite_step x N c hstep)
  have he : (∑ k ∈ Finset.range N, ((x k ^ 2 + Y ^ 2) ^ 2)⁻¹) =
      ∑ k ∈ Finset.range N, (((extendFinite x N c k) ^ 2 + Y ^ 2) ^ 2)⁻¹ := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [extendFinite_eq x N c k (Nat.le_of_lt (Finset.mem_range.mp hk))]
  rw [he]
  exact (hs.sum_le_tsum (Finset.range N) (fun k _ => by positivity)).trans hb

theorem finite_exponential_cubic_bound (x : ℕ → ℝ) (N : ℕ) (c θ : ℝ)
    (hc : 0 < c) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hstep : ∀ k : ℕ, k < N → x k + c ≤ x (k + 1)) :
    (∑ k ∈ Finset.range N, θ ^ 4 * Real.exp (-2 * θ * |x k|)) ≤
      (Real.exp (2 * c) / c) * θ ^ 3 := by
  obtain ⟨hs, hb⟩ := exponential_cubic_orbit_bound (extendFinite x N c) c θ hc hθ hθ1
    (extendFinite_step x N c hstep)
  have he : (∑ k ∈ Finset.range N, θ ^ 4 * Real.exp (-2 * θ * |x k|)) =
      ∑ k ∈ Finset.range N, θ ^ 4 * Real.exp (-2 * θ * |extendFinite x N c k|) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [extendFinite_eq x N c k (Nat.le_of_lt (Finset.mem_range.mp hk))]
  rw [he]
  exact (hs.sum_le_tsum (Finset.range N) (fun k _ => by positivity)).trans hb

end Kneser.FiniteSeparatedKernelBounds
end
