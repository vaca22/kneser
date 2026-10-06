import Kneser.AnalyticRootRemainderJets
import Kneser.ParabolicFatouCoordinate
import Mathlib.Algebra.Ring.GeomSum

/-! Actual polynomial correction directions and their nonzero triangular jets. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Kneser.ActualCorrectionDirections

open Filter Kneser.ExponentialUnfolding Kneser.ExponentialPreparedQuadratic
open Kneser.ExponentialMatrixDividedDifference Kneser.PreparedTwoRootDivision
open Kneser.AnalyticRootRemainderJets Kneser.ParabolicFatouCoordinate
open scoped Topology BigOperators

def direction (U : ℂ → ℂ) (n : ℕ) (p : Pair) : ℂ :=
  symmetricCofactor U p.1 p.2 *
    ∑ j ∈ Finset.range (n + 1), unfolding (p.1 ^ 2) p.2 ^ j * p.2 ^ (n - j)

theorem analyticAt_direction {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) (n : ℕ) :
    AnalyticAt ℂ (direction U n) 0 := by
  have hK : AnalyticAt ℂ (fun p : Pair => symmetricCofactor U p.1 p.2) 0 :=
    analyticAt_symmetricCofactor hU analyticAt_fst rfl analyticAt_snd
  have hf : AnalyticAt ℂ (fun p : Pair => unfolding (p.1 ^ 2) p.2) 0 := by
    have hx : AnalyticAt ℂ (fun p : Pair => p.1 ^ 2) 0 := analyticAt_fst.pow 2
    exact ((hx.neg.add ((analyticAt_const.sub hx).mul analyticAt_snd)).cexp).sub analyticAt_const
  apply hK.mul
  exact Finset.analyticAt_fun_sum _ (fun j _ => (hf.pow j).mul (analyticAt_snd.pow (n - j)))

theorem direction_even (U : ℂ → ℂ) (n : ℕ) (p : Pair) :
    direction U n (reflectFirst p) = direction U n p := by
  simp only [direction, reflectFirst, symmetricCofactor_even, neg_sq]

/-- This is the genuine cofactor of the correction of the monomial u^(n+1). -/
theorem direction_factor (U : ℂ → ℂ) (n : ℕ) (x u : ℂ)
    (hf : unfolding (x ^ 2) u - u = rootProduct U x u * symmetricCofactor U x u) :
    unfolding (x ^ 2) u ^ (n + 1) - u ^ (n + 1) = rootProduct U x u * direction U n (x, u) := by
  have h := (Commute.all (unfolding (x ^ 2) u) u).mul_geom_sum₂ (n + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [hf] at h
  simpa only [direction, mul_assoc] using h.symm

/-- At the merger the ith correction has a zero of exactly i−1 and leading
coefficient i/2, proved from the actual exponential quotient. -/
theorem exists_direction_leading {U : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0)
    (hK0 : symmetricCofactor U 0 0 = 1 / 2) (n : ℕ) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ G 0 = ((n : ℂ) + 1) / 2 ∧
      (∀ u, direction U n (0, u) = u ^ n * G u) := by
  obtain ⟨E, L, hE, _hL, hE0, _hL0, _hEd, _hLd, hexp, _hEL⟩ := exists_exponential_quotient
  let G : ℂ → ℂ := fun u => symmetricCofactor U 0 u *
    ∑ j ∈ Finset.range (n + 1), E u ^ j
  have hGa : AnalyticAt ℂ G 0 :=
    (analyticAt_symmetricCofactor hU analyticAt_const rfl analyticAt_id).mul
      (Finset.analyticAt_fun_sum _ (fun j _ => hE.pow j))
  refine ⟨G, hGa, ?_, ?_⟩
  · simp [G, hK0, hE0]
    ring
  · intro u
    have hf : unfolding (0 ^ 2) u = u * E u := by
      simpa [unfolding, ParabolicExponentialOrbit.parabolicMap] using hexp u
    dsimp [direction, G]
    rw [hf]
    have hsum :
        (∑ j ∈ Finset.range (n + 1), (u * E u) ^ j * u ^ (n - j)) =
          u ^ n * ∑ j ∈ Finset.range (n + 1), E u ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [mul_pow]
      calc
        u ^ j * E u ^ j * u ^ (n - j) =
            (u ^ j * u ^ (n - j)) * E u ^ j := by ring
        _ = u ^ n * E u ^ j := by rw [← pow_add, Nat.add_sub_of_le hjn]
    rw [hsum]
    ring

/-- The actual remainder matrix is triangular at the merger, with the
nonzero diagonal required for arbitrary finite preparation. -/
theorem remainder_coefficient_triangular {U : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hK0 : symmetricCofactor U 0 0 = 1 / 2)
    (a b : ℕ → ℂ → ℂ) (C : Pair → ℂ) (hC : AnalyticAt ℂ C 0)
    (m n : ℕ)
    (hfactor : ∀ᶠ p in 𝓝 (0 : Pair),
      direction U n p = AnalyticRootDivision.remainder U a b m p + rootProduct U p.1 p.2 ^ m * C p)
    (r : ℕ) (hr : r < 2 * m) (hrn : r ≤ n) :
    coefficient a b r 0 = if r = n then ((n : ℂ) + 1) / 2 else 0 := by
  obtain ⟨G, hG, hG0, hleading⟩ := exists_direction_leading hU hK0 n
  rw [coefficient_eq_jet hU0 a b C hC m hfactor r hr]
  have heq : (fun u => direction U n (0, u)) = (fun u => u ^ n * G u) := funext hleading
  rw [heq, iteratedDeriv_power_mul_zero hG n r hrn]
  by_cases heq : r = n
  · subst r
    simp only [ite_true, hG0]
    field_simp [show (n.factorial : ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero n]
  · simp only [if_neg heq, zero_div]

end Kneser.ActualCorrectionDirections

end
