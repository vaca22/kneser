import Kneser.AsymptoticTruncation
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Compact bounds for finite asymptotic coefficients follow from actual
sample values, by inverting a finite Vandermonde matrix. No regularity or
boundedness of the unknown coefficient functions is assumed. -/

noncomputable section
namespace Kneser.FinitePolynomialCoefficientBounds

open Filter Set Matrix Kneser.AsymptoticCoefficientUniqueness
open scoped Topology BigOperators

theorem coefficient_eq_inverse_samples (m : ℕ) (t : Fin (m + 1) → ℝ)
    (ht : Function.Injective t) (c : ℕ → ℂ) (j : Fin (m + 1)) :
    c j = ∑ i : Fin (m + 1),
      (vandermonde (fun i => (t i : ℂ)))⁻¹ j i * polynomial c m (t i) := by
  let A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
    vandermonde (fun i => (t i : ℂ))
  have hti : Function.Injective (fun i => (t i : ℂ)) :=
    Complex.ofReal_injective.comp ht
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr (det_vandermonde_ne_zero_iff.mpr hti)
  have hp : A *ᵥ (fun k : Fin (m + 1) => c k) =
      (fun i => polynomial c m (t i)) := by
    funext i
    simp only [A, mulVec, dotProduct, vandermonde_apply, polynomial]
    exact Fin.sum_univ_eq_sum_range (fun k : ℕ => (t i : ℂ) ^ k * c k) (m + 1)
  have he : A⁻¹ *ᵥ (fun i => polynomial c m (t i)) = (fun k : Fin (m + 1) => c k) := by
    rw [← hp, mulVec_mulVec, nonsing_inv_mul A hdet, one_mulVec]
  exact (congrFun he j).symm

theorem coefficient_bound_of_samples (m : ℕ) (t : Fin (m + 1) → ℝ)
    (ht : Function.Injective t) (c : ℕ → ℂ) (B : Fin (m + 1) → ℝ)
    (hb : ∀ i, ‖polynomial c m (t i)‖ ≤ B i) (j : Fin (m + 1)) :
    ‖c j‖ ≤ ∑ i : Fin (m + 1),
      ‖(vandermonde (fun i => (t i : ℂ)))⁻¹ j i‖ * B i := by
  rw [coefficient_eq_inverse_samples m t ht c j]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _)

theorem exists_uniform_coefficient_bound {α : Type*} (f : ℝ → α → ℂ)
    (c : ℕ → α → ℂ) (m : ℕ) (S : Set α) (C γ : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
      ‖f s u - polynomial (fun j => c j u) m s‖ ≤ C * s ^ ((m : ℝ) + γ))
    (hf : ∀ᶠ s : ℝ in 𝓝[>] 0, ∃ B : ℝ, ∀ u ∈ S, ‖f s u‖ ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ u ∈ S, ∀ j ≤ m, ‖c j u‖ ≤ D := by
  have hh := hbound.and hf
  rw [eventually_nhdsWithin_iff] at hh
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hh
  let t : Fin (m + 1) → ℝ := fun i => r * ((i : ℕ) + 1) / ((m : ℝ) + 2)
  have htpos (i : Fin (m + 1)) : 0 < t i := by dsimp [t]; positivity
  have htr (i : Fin (m + 1)) : t i < r := by
    have hi : (i : ℝ) < (m : ℝ) + 1 := by exact_mod_cast i.isLt
    dsimp [t]
    apply (div_lt_iff₀ (by positivity : 0 < (m : ℝ) + 2)).mpr
    nlinarith
  have hti : Function.Injective t := by
    intro i j hij
    apply Fin.ext
    have hij' : (i : ℝ) = (j : ℝ) := by
      dsimp [t] at hij
      have hd : (m : ℝ) + 2 ≠ 0 := by positivity
      apply_fun (fun x : ℝ => x * ((m : ℝ) + 2) / r) at hij
      field_simp [hd, hr.ne'] at hij
      nlinarith
    exact_mod_cast hij'
  have hs (i : Fin (m + 1)) := hball
    (show dist (t i) 0 < r by simpa [dist_zero_right, Real.norm_eq_abs, abs_of_pos (htpos i)] using htr i)
    (htpos i)
  choose B hB using fun i => (hs i).2
  let E : Fin (m + 1) → ℝ := fun i => B i + C * (t i) ^ ((m : ℝ) + γ)
  let D : ℝ := ∑ j : Fin (m + 1), ∑ i : Fin (m + 1),
    ‖(vandermonde (fun i => (t i : ℂ)))⁻¹ j i‖ * |E i|
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro u hu j hj
  let jf : Fin (m + 1) := ⟨j, by omega⟩
  have hb (i : Fin (m + 1)) : ‖polynomial (fun k => c k u) m (t i)‖ ≤ |E i| := by
    have hn := norm_sub_le (f (t i) u) (f (t i) u - polynomial (fun k => c k u) m (t i))
    have he : f (t i) u - (f (t i) u - polynomial (fun k => c k u) m (t i)) =
        polynomial (fun k => c k u) m (t i) := by ring
    rw [he] at hn
    exact (hn.trans (add_le_add (hB i u hu) ((hs i).1 u hu))).trans (le_abs_self _)
  have hc := coefficient_bound_of_samples m t hti (fun k => c k u) (fun i => |E i|) hb jf
  have hsingle : (∑ i : Fin (m + 1),
      ‖(vandermonde (fun i => (t i : ℂ)))⁻¹ jf i‖ * |E i|) ≤ D := by
    exact Finset.single_le_sum
      (f := fun k : Fin (m + 1) => ∑ i : Fin (m + 1),
        ‖(vandermonde (fun i => (t i : ℂ)))⁻¹ k i‖ * |E i|)
      (fun k _ => by positivity) (Finset.mem_univ jf)
  exact hc.trans hsingle

end Kneser.FinitePolynomialCoefficientBounds
