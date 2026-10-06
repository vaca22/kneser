import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Convergent orbit corrections

The orbit-sum construction used for the normalized parabolic Fatou coordinate is
formalized here. The analytic estimate on the actual parabolic orbit is an
explicit hypothesis: this file does not establish that estimate for the
exponential map. From that estimate it proves absolute convergence, and from
the definition of the defect it proves the Abel equation.
-/

namespace Kneser

open scoped BigOperators

section Comparison

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

/-- The majorant used for a parabolic orbit is summable for every integer
exponent at least two. No sign assumption on `C` is needed for this statement. -/
theorem summable_parabolic_majorant (C : ℝ) {q : ℕ} (hq : 2 ≤ q) :
    Summable (fun k : ℕ => C / ((k : ℝ) + 1) ^ q) := by
  have hbase : Summable (fun k : ℕ => 1 / (k : ℝ) ^ q) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  have hshift := (summable_nat_add_iff 1).mpr hbase
  simpa only [Nat.cast_add, Nat.cast_one, mul_one_div] using hshift.mul_left C

omit [CompleteSpace E] in
/-- A `k⁻q` norm bound, `q ≥ 2`, proves absolute convergence. -/
theorem summable_norm_of_parabolic_bound (a : ℕ → E) (C : ℝ) {q : ℕ}
    (hq : 2 ≤ q) (hbound : ∀ k, ‖a k‖ ≤ C / ((k : ℝ) + 1) ^ q) :
    Summable (fun k => ‖a k‖) := by
  exact (summable_parabolic_majorant C hq).of_nonneg_of_le
    (fun k => norm_nonneg (a k)) hbound

/-- Absolute convergence of the orbit terms implies convergence in the target
Banach space. -/
theorem summable_of_parabolic_bound (a : ℕ → E) (C : ℝ) {q : ℕ}
    (hq : 2 ≤ q) (hbound : ∀ k, ‖a k‖ ≤ C / ((k : ℝ) + 1) ^ q) :
    Summable a :=
  (summable_norm_of_parabolic_bound a C hq hbound).of_norm

/-- The first-order chain-rule term has the same summable decay as the direct
parameter term: the one power lost to orbit velocity is supplied by the spatial
derivative. This is the bound structure in the series for `Adot`. -/
theorem first_order_term_bound (a b d : ℕ → ℂ) (C₁ C₂ C₃ : ℝ)
    (hC₂ : 0 ≤ C₂) (q k : ℕ)
    (ha : ‖a k‖ ≤ C₁ / ((k : ℝ) + 1) ^ q)
    (hb : ‖b k‖ ≤ C₂ / ((k : ℝ) + 1) ^ (q + 1))
    (hd : ‖d k‖ ≤ C₃ * ((k : ℝ) + 1)) :
    ‖a k + b k * d k‖ ≤ (C₁ + C₂ * C₃) / ((k : ℝ) + 1) ^ q := by
  have ht : 0 < (k : ℝ) + 1 := by positivity
  have hp : 0 < ((k : ℝ) + 1) ^ q := pow_pos ht _
  have hmul : ‖b k * d k‖ ≤ C₂ * C₃ / ((k : ℝ) + 1) ^ q := by
    calc
      ‖b k * d k‖ = ‖b k‖ * ‖d k‖ := norm_mul _ _
      _ ≤ (C₂ / ((k : ℝ) + 1) ^ (q + 1)) * (C₃ * ((k : ℝ) + 1)) :=
        mul_le_mul hb hd (norm_nonneg _) (div_nonneg hC₂ (le_of_lt (pow_pos ht _)))
      _ = C₂ * C₃ / ((k : ℝ) + 1) ^ q := by
        rw [pow_succ]
        field_simp
  calc
    ‖a k + b k * d k‖ ≤ ‖a k‖ + ‖b k * d k‖ := norm_add_le _ _
    _ ≤ C₁ / ((k : ℝ) + 1) ^ q + C₂ * C₃ / ((k : ℝ) + 1) ^ q := add_le_add ha hmul
    _ = (C₁ + C₂ * C₃) / ((k : ℝ) + 1) ^ q := by rw [add_div]

/-- Absolute convergence of the explicit first-order orbit coefficient follows
from the direct-term, spatial-derivative, and orbit-velocity estimates. -/
theorem summable_norm_first_order_terms (a b d : ℕ → ℂ) (C₁ C₂ C₃ : ℝ)
    (hC₂ : 0 ≤ C₂) {q : ℕ} (hq : 2 ≤ q)
    (ha : ∀ k, ‖a k‖ ≤ C₁ / ((k : ℝ) + 1) ^ q)
    (hb : ∀ k, ‖b k‖ ≤ C₂ / ((k : ℝ) + 1) ^ (q + 1))
    (hd : ∀ k, ‖d k‖ ≤ C₃ * ((k : ℝ) + 1)) :
    Summable (fun k => ‖a k + b k * d k‖) := by
  apply summable_norm_of_parabolic_bound _ (C₁ + C₂ * C₃) hq
  intro k
  exact first_order_term_bound a b d C₁ C₂ C₃ hC₂ q k (ha k) (hb k) (hd k)

/-- The first-order orbit coefficient is a convergent complex series. -/
theorem summable_first_order_terms (a b d : ℕ → ℂ) (C₁ C₂ C₃ : ℝ)
    (hC₂ : 0 ≤ C₂) {q : ℕ} (hq : 2 ≤ q)
    (ha : ∀ k, ‖a k‖ ≤ C₁ / ((k : ℝ) + 1) ^ q)
    (hb : ∀ k, ‖b k‖ ≤ C₂ / ((k : ℝ) + 1) ^ (q + 1))
    (hd : ∀ k, ‖d k‖ ≤ C₃ * ((k : ℝ) + 1)) :
    Summable (fun k => a k + b k * d k) :=
  (summable_norm_first_order_terms a b d C₁ C₂ C₃ hC₂ hq ha hb hd).of_norm

end Comparison

section Orbit

variable {X : Type*}

/-- Evaluate a defect along a forward orbit. -/
def orbitTerm (f : X → X) (F : X → ℂ) (u : X) (k : ℕ) : ℂ :=
  F ((f^[k]) u)

/-- The explicitly constructed error in the approximate Abel equation. -/
def coordinateDefect (f : X → X) (Ψ : X → ℂ) (v : X) : ℂ :=
  Ψ (f v) - Ψ v - 1

/-- The corrected coordinate is the initial approximate coordinate plus its
absolutely convergent defect series. Summability is required by the theorems,
so the default value of Lean's `tsum` for a divergent series is never used. -/
noncomputable def correctedCoordinate (f : X → X) (Ψ F : X → ℂ) (u : X) : ℂ :=
  Ψ u + ∑' k : ℕ, orbitTerm f F u k

@[simp] theorem orbitTerm_zero (f : X → X) (F : X → ℂ) (u : X) :
    orbitTerm f F u 0 = F u := rfl

theorem orbitTerm_shift (f : X → X) (F : X → ℂ) (u : X) (k : ℕ) :
    orbitTerm f F (f u) k = orbitTerm f F u (k + 1) := by
  simp only [orbitTerm, Function.iterate_succ_apply]

/-- Convergence at an orbit point propagates to the next point. -/
theorem summable_orbitTerm_shift (f : X → X) (F : X → ℂ) (u : X)
    (hs : Summable (orbitTerm f F u)) : Summable (orbitTerm f F (f u)) := by
  exact ((summable_nat_add_iff 1).mpr hs).congr
    (fun k => (orbitTerm_shift f F u k).symm)

/-- Removing the first orbit term gives the exact shift identity for the sum. -/
theorem orbit_sum_shift (f : X → X) (F : X → ℂ) (u : X)
    (hs : Summable (orbitTerm f F u)) :
    (∑' k : ℕ, orbitTerm f F (f u) k) =
      (∑' k : ℕ, orbitTerm f F u k) - F u := by
  have heq := hs.tsum_eq_zero_add
  simp only [orbitTerm_zero] at heq
  rw [tsum_congr (orbitTerm_shift f F u)]
  linear_combination -heq

/-- The orbit correction satisfies the Abel equation. The defect identity is
the definition `F = Ψ ∘ f - Ψ - 1`, not an assumption of the Abel equation. -/
theorem correctedCoordinate_abel (f : X → X) (Ψ F : X → ℂ) (u : X)
    (hF : F u = Ψ (f u) - Ψ u - 1)
    (hs : Summable (orbitTerm f F u)) :
    correctedCoordinate f Ψ F (f u) = correctedCoordinate f Ψ F u + 1 := by
  unfold correctedCoordinate
  rw [orbit_sum_shift f F u hs, hF]
  ring

/-- A decay estimate establishes convergence and the Abel equation together. -/
theorem correctedCoordinate_abel_of_bound (f : X → X) (Ψ F : X → ℂ)
    (u : X) (C : ℝ) {q : ℕ} (hq : 2 ≤ q)
    (hF : F u = Ψ (f u) - Ψ u - 1)
    (hbound : ∀ k, ‖orbitTerm f F u k‖ ≤ C / ((k : ℝ) + 1) ^ q) :
    correctedCoordinate f Ψ F (f u) = correctedCoordinate f Ψ F u + 1 := by
  apply correctedCoordinate_abel f Ψ F u hF
  exact summable_of_parabolic_bound (orbitTerm f F u) C hq hbound

/-- Finite versions of the orbit sum telescope exactly. -/
theorem orbit_sum_telescoping (f : X → X) (Ψ F : X → ℂ) (u : X)
    (hF : ∀ v, F v = Ψ (f v) - Ψ v - 1) (n : ℕ) :
    Ψ u + ∑ k ∈ Finset.range n, orbitTerm f F u k = Ψ ((f^[n]) u) - (n : ℂ) := by
  induction n with
  | zero => simp [orbitTerm]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rw [← add_assoc, ih]
    simp only [orbitTerm, hF, Function.iterate_succ_apply', Nat.cast_add, Nat.cast_one]
    ring

/-- The corrected coordinate is also the normalized forward-orbit limit. This
limit is deduced from the summable defect, rather than supplied as a hypothesis. -/
theorem correctedCoordinate_limit (f : X → X) (Ψ F : X → ℂ) (u : X)
    (hF : ∀ v, F v = Ψ (f v) - Ψ v - 1)
    (hs : Summable (orbitTerm f F u)) :
    Filter.Tendsto (fun n : ℕ => Ψ ((f^[n]) u) - (n : ℂ)) Filter.atTop
      (nhds (correctedCoordinate f Ψ F u)) := by
  have ht : Filter.Tendsto
      (fun n : ℕ => Ψ u + ∑ k ∈ Finset.range n, orbitTerm f F u k)
      Filter.atTop (nhds (correctedCoordinate f Ψ F u)) :=
    tendsto_const_nhds.add hs.tendsto_sum_tsum_nat
  exact ht.congr' (Filter.Eventually.of_forall
    (fun n => orbit_sum_telescoping f Ψ F u hF n))

/-- A parabolic majorant proves the normalized orbit limit exists. -/
theorem correctedCoordinate_limit_of_bound (f : X → X) (Ψ F : X → ℂ)
    (u : X) (C : ℝ) {q : ℕ} (hq : 2 ≤ q)
    (hF : ∀ v, F v = Ψ (f v) - Ψ v - 1)
    (hbound : ∀ k, ‖orbitTerm f F u k‖ ≤ C / ((k : ℝ) + 1) ^ q) :
    Filter.Tendsto (fun n : ℕ => Ψ ((f^[n]) u) - (n : ℂ)) Filter.atTop
      (nhds (correctedCoordinate f Ψ F u)) := by
  apply correctedCoordinate_limit f Ψ F u hF
  exact summable_of_parabolic_bound (orbitTerm f F u) C hq hbound

/-- End-to-end construction from an approximate coordinate: a norm estimate on
its explicitly defined defect proves absolute convergence, the Abel equation,
and the normalized orbit limit. No Fatou coordinate or Abel identity is assumed. -/
theorem fatou_coordinate_of_defect_bound (f : X → X) (Ψ : X → ℂ)
    (u : X) (C : ℝ) {q : ℕ} (hq : 2 ≤ q)
    (hbound : ∀ k, ‖orbitTerm f (coordinateDefect f Ψ) u k‖ ≤
      C / ((k : ℝ) + 1) ^ q) :
    Summable (fun k => ‖orbitTerm f (coordinateDefect f Ψ) u k‖) ∧
    correctedCoordinate f Ψ (coordinateDefect f Ψ) (f u) =
      correctedCoordinate f Ψ (coordinateDefect f Ψ) u + 1 ∧
    Filter.Tendsto (fun n : ℕ => Ψ ((f^[n]) u) - (n : ℂ)) Filter.atTop
      (nhds (correctedCoordinate f Ψ (coordinateDefect f Ψ) u)) := by
  refine ⟨summable_norm_of_parabolic_bound _ C hq hbound, ?_, ?_⟩
  · exact correctedCoordinate_abel_of_bound f Ψ (coordinateDefect f Ψ) u C hq rfl hbound
  · exact correctedCoordinate_limit_of_bound f Ψ (coordinateDefect f Ψ) u C hq
      (fun _ => rfl) hbound

end Orbit

end Kneser
