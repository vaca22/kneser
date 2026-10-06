import Kneser.CauchyHeadTaylor
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual arbitrary-degree Cauchy remainder estimates, with no Taylor
remainder or termwise infinite differentiation hypothesis. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Kneser.CauchyHigherTaylor

open Complex Metric Filter
open scoped Topology BigOperators

def coefficient (f : ℂ → ℂ) (j : ℕ) : ℂ := iteratedDeriv j f 0 / (j.factorial : ℂ)

def polynomial (f : ℂ → ℂ) (d : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.range d, s ^ j * coefficient f j

theorem norm_coefficient_le (f : ℂ → ℂ) (R M : ℝ) (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball 0 R))
    (hbound : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ M) (j : ℕ) :
    ‖coefficient f j‖ ≤ M / R ^ j := by
  have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hR hf hbound
  have hfact : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  rw [coefficient, norm_div, Complex.norm_natCast]
  apply (div_le_div_of_nonneg_right hd hfact.le).trans_eq
  field_simp

/-- For every finite degree, the remainder follows from the actual Taylor
series, the derived Cauchy coefficient bounds and the geometric series. -/
theorem norm_remainder_le (f : ℂ → ℂ) (R M : ℝ) (d : ℕ) (s : ℂ)
    (hR : 0 < R) (hM : 0 ≤ M) (hf : DiffContOnCl ℂ f (ball 0 R))
    (hbound : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ M) (hs : ‖s‖ ≤ R / 2) :
    ‖f s - polynomial f d s‖ ≤ 2 * M * ‖s‖ ^ d / R ^ d := by
  let q : ℝ := ‖s‖ / R
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqhalf : q ≤ 1 / 2 := (div_le_iff₀ hR).mpr (by linarith)
  have hsball : s ∈ ball (0 : ℂ) R := by
    simp only [mem_ball, dist_zero_right]
    linarith
  let T : ℕ → ℂ := fun j => s ^ j * coefficient f j
  have hhas : HasSum T (f s) := by
    have ht := Complex.hasSum_taylorSeries_on_ball hf.differentiableOn hsball
    convert ht using 1 <;> first | rfl | (funext j; dsimp [T, coefficient]; simp only [sub_zero, smul_eq_mul, div_eq_mul_inv]; ring)
  have hterm : ∀ j, ‖T j‖ ≤ M * q ^ j := by
    intro j
    dsimp [T]
    rw [norm_mul, norm_pow]
    apply (mul_le_mul_of_nonneg_left (norm_coefficient_le f R M hR hf hbound j)
      (by positivity : 0 ≤ ‖s‖ ^ j)).trans_eq
    dsimp [q]
    rw [div_pow]
    ring
  have htail : ∀ k, ‖T (k + d)‖ ≤ (M * q ^ d) * (1 / 2 : ℝ) ^ k := by
    intro k
    apply (hterm (k + d)).trans
    rw [pow_add]
    have hk := pow_le_pow_left₀ hq0 hqhalf k
    calc
      M * (q ^ k * q ^ d) = (M * q ^ d) * q ^ k := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hk (mul_nonneg hM (pow_nonneg hq0 d))
  have hmaj : Summable (fun k : ℕ => (M * q ^ d) * (1 / 2 : ℝ) ^ k) :=
    summable_geometric_two.mul_left _
  have hnorm : Summable (fun k => ‖T (k + d)‖) :=
    hmaj.of_nonneg_of_le (fun _ => norm_nonneg _) htail
  have heq : f s - polynomial f d s = ∑' k : ℕ, T (k + d) := by
    have ht := hhas.summable.sum_add_tsum_nat_add d
    rw [hhas.tsum_eq] at ht
    change polynomial f d s + (∑' k : ℕ, T (k + d)) = f s at ht
    linear_combination -ht
  rw [heq]
  calc
    ‖∑' k : ℕ, T (k + d)‖ ≤ ∑' k : ℕ, ‖T (k + d)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℕ, (M * q ^ d) * (1 / 2 : ℝ) ^ k := hnorm.tsum_le_tsum htail hmaj
    _ = 2 * M * ‖s‖ ^ d / R ^ d := by
      rw [tsum_mul_left, tsum_geometric_two]
      dsimp [q]
      rw [div_pow]
      ring

end Kneser.CauchyHigherTaylor

end
