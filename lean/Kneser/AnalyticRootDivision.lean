import Kneser.ExponentialPreparedQuadratic

/-!
Constructive division of an even analytic germ by arbitrary powers of the
actual product of the coalescing roots.  The remainders are genuine finite
polynomials with coefficients analytic in the unsplit parameter.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Kneser.AnalyticRootDivision

open Filter Kneser.PreparedTwoRootDivision Kneser.ExponentialPreparedModel
open Kneser.ExponentialPreparedQuadratic Kneser.ExponentialMatrixDividedDifference
open Kneser.AnalyticEvenDescent
open Kneser.ExponentialLogDefect
open scoped Topology BigOperators

/-- Analytic two-root division with an actual degree-one remainder. -/
theorem exists_linear_remainder {B : Pair → ℂ} {U : ℂ → ℂ}
    (hB : AnalyticAt ℂ B 0) (hBeven : ∀ p, B (reflectFirst p) = B p)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0) (hUd : deriv U 0 ≠ 0)
    (hdistinct : ∀ᶠ x in 𝓝 0, U x = U (-x) ↔ x = 0) :
    ∃ a b : ℂ → ℂ, ∃ C : Pair → ℂ,
      AnalyticAt ℂ a 0 ∧ AnalyticAt ℂ b 0 ∧ AnalyticAt ℂ C 0 ∧
      (∀ p, C (reflectFirst p) = C p) ∧
      (∀ᶠ p in 𝓝 (0 : Pair),
        B p = a (p.1 ^ 2) + b (p.1 ^ 2) * p.2 + rootProduct U p.1 p.2 * C p) := by
  have hcurve : AnalyticAt ℂ (fun x => (x, U x)) 0 := analyticAt_id.prod hU
  have hcurve0 : ((0 : ℂ), U 0) = (0 : Pair) := by simp [hU0]
  have hv : AnalyticAt ℂ (fun x => B (x, U x)) 0 := hB.comp_of_eq hcurve hcurve0
  obtain ⟨e₁, e₂, he₁, he₂, heval⟩ := exists_analytic_quadratic_interpolant hU hUd hv
  let T : Pair → ℂ := fun p => B p - (e₁ (p.1 ^ 2) + 2 * e₂ (p.1 ^ 2) * p.2)
  have he₁p : AnalyticAt ℂ (fun p : Pair => e₁ (p.1 ^ 2)) 0 :=
    he₁.comp_of_eq (f := fun p : Pair => p.1 ^ 2) (analyticAt_fst.pow 2) (by simp)
  have he₂p : AnalyticAt ℂ (fun p : Pair => e₂ (p.1 ^ 2)) 0 :=
    he₂.comp_of_eq (f := fun p : Pair => p.1 ^ 2) (analyticAt_fst.pow 2) (by simp)
  have hT : AnalyticAt ℂ T 0 := hB.sub (he₁p.add ((analyticAt_const.mul he₂p).mul analyticAt_snd))
  have hTeven : ∀ p, T (reflectFirst p) = T p := by
    intro p
    dsimp [T, reflectFirst]
    rw [show B (-p.1, p.2) = B p from hBeven p, neg_sq]
  have hzero : ∀ᶠ x in 𝓝 0, T (x, U x) = 0 ∧ T (x, U (-x)) = 0 := by
    filter_upwards [heval] with x hx
    dsimp [T]
    constructor
    · linear_combination -hx.1
    · rw [← hBeven (x, U (-x))]
      dsimp [reflectFirst]
      linear_combination -hx.2
  obtain ⟨D, hD, hfactor⟩ := exists_two_root_factor hT hU hU0 hdistinct hzero
  let C := symmetrizeFirst D
  have hfactorC : ∀ᶠ p in 𝓝 (0 : Pair), T p = rootProduct U p.1 p.2 * C p := by
    filter_upwards [hfactor, reflectFirst_tendsto.eventually hfactor] with p hp hnp
    rw [hTeven] at hnp
    simp only [reflectFirst, neg_neg] at hnp
    dsimp [rootProduct, C, symmetrizeFirst, reflectFirst]
    linear_combination (hp + hnp) / 2
  refine ⟨e₁, fun s => 2 * e₂ s, C, he₁, analyticAt_const.mul he₂,
    analyticAt_symmetrizeFirst hD, symmetrizeFirst_even D, ?_⟩
  filter_upwards [hfactorC] with p hp
  dsimp [T] at hp
  linear_combination hp

/-- The degree less than 2m polynomial remainder, written in the q-adic basis. -/
def remainder (U : ℂ → ℂ) (a b : ℕ → ℂ → ℂ) (m : ℕ) (p : Pair) : ℂ :=
  ∑ j ∈ Finset.range m, rootProduct U p.1 p.2 ^ j * (a j (p.1 ^ 2) + b j (p.1 ^ 2) * p.2)

theorem exists_power_remainder {B : Pair → ℂ} {U : ℂ → ℂ}
    (hB : AnalyticAt ℂ B 0) (hBeven : ∀ p, B (reflectFirst p) = B p)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0) (hUd : deriv U 0 ≠ 0)
    (hdistinct : ∀ᶠ x in 𝓝 0, U x = U (-x) ↔ x = 0) (m : ℕ) :
    ∃ a b : ℕ → ℂ → ℂ, ∃ C : Pair → ℂ,
      (∀ j < m, AnalyticAt ℂ (a j) 0 ∧ AnalyticAt ℂ (b j) 0) ∧
      AnalyticAt ℂ C 0 ∧ (∀ p, C (reflectFirst p) = C p) ∧
      (∀ᶠ p in 𝓝 (0 : Pair), B p = remainder U a b m p + rootProduct U p.1 p.2 ^ m * C p) := by
  induction m with
  | zero =>
      refine ⟨fun _ _ => 0, fun _ _ => 0, B, by simp, hB, hBeven, ?_⟩
      exact Eventually.of_forall (fun p => by simp [remainder])
  | succ m ih =>
      obtain ⟨a, b, C, hab, hC, hCeven, hfactor⟩ := ih
      obtain ⟨a₁, b₁, D, ha₁, hb₁, hD, hDeven, hCD⟩ :=
        exists_linear_remainder hC hCeven hU hU0 hUd hdistinct
      let a' : ℕ → ℂ → ℂ := fun j => if j = m then a₁ else a j
      let b' : ℕ → ℂ → ℂ := fun j => if j = m then b₁ else b j
      have hrem : ∀ p, remainder U a' b' (m + 1) p =
          remainder U a b m p + rootProduct U p.1 p.2 ^ m *
            (a₁ (p.1 ^ 2) + b₁ (p.1 ^ 2) * p.2) := by
        intro p
        unfold remainder
        rw [Finset.sum_range_succ]
        simp only [a', b', if_pos rfl]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        have hjm : j ≠ m := Nat.ne_of_lt (Finset.mem_range.mp hj)
        simp only [hjm, if_false]
      refine ⟨a', b', D, ?_, hD, hDeven, ?_⟩
      · intro j hj
        by_cases heq : j = m
        · simpa only [a', b', heq, if_pos rfl] using And.intro ha₁ hb₁
        · have hjm : j < m := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) heq
          simpa only [a', b', heq, if_false] using hab j hjm
      · filter_upwards [hfactor, hCD] with p hp hcp
        rw [hrem, pow_succ]
        rw [hp, hcp]
        ring

end Kneser.AnalyticRootDivision

end
