import Kneser.AnalyticRootDivision
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Genuine low Taylor jets of the constructive coalescing-root remainder. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Kneser.AnalyticRootRemainderJets

open Filter Kneser.AnalyticRootDivision Kneser.ExponentialPreparedQuadratic
open Kneser.PreparedTwoRootDivision
open scoped Topology BigOperators

def coefficient (a b : ℕ → ℂ → ℂ) (j : ℕ) (s : ℂ) : ℂ :=
  if j % 2 = 0 then a (j / 2) s else b (j / 2) s

theorem coefficient_even (a b : ℕ → ℂ → ℂ) (j : ℕ) (s : ℂ) :
    coefficient a b (2 * j) s = a j s := by simp [coefficient, Nat.mul_comm]

theorem coefficient_odd (a b : ℕ → ℂ → ℂ) (j : ℕ) (s : ℂ) :
    coefficient a b (2 * j + 1) s = b j s := by
  have hdiv : (2 * j + 1) / 2 = j := by omega
  have hmod : (2 * j + 1) % 2 = 1 := by omega
  simp [coefficient, hdiv, hmod]

theorem analyticAt_coefficient (a b : ℕ → ℂ → ℂ) (m : ℕ)
    (hab : ∀ j < m, AnalyticAt ℂ (a j) 0 ∧ AnalyticAt ℂ (b j) 0)
    (j : ℕ) (hj : j < 2 * m) : AnalyticAt ℂ (coefficient a b j) 0 := by
  have hdiv : j / 2 < m := by omega
  unfold coefficient
  split
  · exact (hab _ hdiv).1
  · exact (hab _ hdiv).2

def remainderBasis (U : ℂ → ℂ) (j : ℕ) (p : Pair) : ℂ :=
  rootProduct U p.1 p.2 ^ (j / 2) * if j % 2 = 0 then 1 else p.2

theorem remainder_eq_coefficients (U : ℂ → ℂ) (a b : ℕ → ℂ → ℂ)
    (m : ℕ) (p : Pair) :
    remainder U a b m p =
      ∑ j ∈ Finset.range (2 * m), coefficient a b j (p.1 ^ 2) * remainderBasis U j p := by
  induction m with
  | zero => simp [remainder]
  | succ m ih =>
      have hdim : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
      unfold remainder at ih ⊢
      rw [Finset.sum_range_succ, hdim, Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
      have hdiv₀ : (2 * m) / 2 = m := by omega
      have hmod₀ : (2 * m) % 2 = 0 := by omega
      have hdiv₁ : (2 * m + 1) / 2 = m := by omega
      have hmod₁ : (2 * m + 1) % 2 = 1 := by omega
      rw [coefficient_even, coefficient_odd]
      simp only [remainderBasis, hdiv₀, hmod₀, hdiv₁, hmod₁, ite_true, one_ne_zero,
        ite_false, mul_one]
      ring

theorem remainder_eq_fin_coefficients (U : ℂ → ℂ) (a b : ℕ → ℂ → ℂ)
    (m : ℕ) (p : Pair) :
    remainder U a b m p =
      ∑ j : Fin (2 * m), coefficient a b j.val (p.1 ^ 2) * remainderBasis U j.val p := by
  rw [remainder_eq_coefficients]
  exact (Fin.sum_univ_eq_sum_range
    (fun j => coefficient a b j (p.1 ^ 2) * remainderBasis U j p) (2 * m)).symm

theorem remainder_at_zero (U : ℂ → ℂ) (hU0 : U 0 = 0)
    (a b : ℕ → ℂ → ℂ) (m : ℕ) (u : ℂ) :
    remainder U a b m (0, u) =
      ∑ j ∈ Finset.range (2 * m), coefficient a b j 0 * u ^ j := by
  induction m with
  | zero => simp [remainder]
  | succ m ih =>
      have hdim : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
      unfold remainder at ih ⊢
      rw [Finset.sum_range_succ, hdim, Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
      rw [coefficient_even, coefficient_odd]
      simp only [rootProduct, neg_zero, hU0, sub_zero, zero_pow (by norm_num : 2 ≠ 0)]
      rw [← pow_two, ← pow_mul]
      ring

theorem iteratedDeriv_power_mul_zero {G : ℂ → ℂ} (hG : AnalyticAt ℂ G 0)
    (m n : ℕ) (hn : n ≤ m) :
    iteratedDeriv n (fun u : ℂ => u ^ m * G u) 0 =
      if n = m then (m.factorial : ℂ) * G 0 else 0 := by
  have hp : ContDiffAt ℂ n (fun u : ℂ => u ^ m) 0 := by fun_prop
  have hGc : ContDiffAt ℂ n G 0 := hG.contDiffAt
  have hd := iteratedDeriv_mul hp hGc
  change iteratedDeriv n (fun u : ℂ => u ^ m * G u) 0 = _ at hd
  rw [hd]
  by_cases hnm : n = m
  · subst n
    rw [if_pos rfl]
    rw [Finset.sum_eq_single m]
    · simp [Nat.descFactorial_self]
    · intro j hj hjm
      simp only [iteratedDeriv_fun_pow_zero, if_neg hjm, Nat.cast_zero, mul_zero, zero_mul]
    · intro hm
      exact False.elim (hm (Finset.mem_range.mpr (Nat.lt_succ_self m)))
  · rw [if_neg hnm]
    apply Finset.sum_eq_zero
    intro j hj
    have hjm : j ≠ m := by have h := Finset.mem_range.mp hj; omega
    simp only [iteratedDeriv_fun_pow_zero, if_neg hjm, Nat.cast_zero, mul_zero, zero_mul]

/-- The actual finite-polynomial coefficient is the true Taylor jet of the
original germ; no remainder uniqueness hypothesis is needed. -/
theorem coefficient_eq_jet {B : Pair → ℂ} {U : ℂ → ℂ}
    (hU0 : U 0 = 0) (a b : ℕ → ℂ → ℂ) (C : Pair → ℂ)
    (hC : AnalyticAt ℂ C 0) (m : ℕ)
    (hfactor : ∀ᶠ p in 𝓝 (0 : Pair),
      B p = remainder U a b m p + rootProduct U p.1 p.2 ^ m * C p)
    (n : ℕ) (hn : n < 2 * m) :
    coefficient a b n 0 = iteratedDeriv n (fun u => B (0, u)) 0 / (n.factorial : ℂ) := by
  have hcurve : Tendsto (fun u : ℂ => ((0 : ℂ), u)) (𝓝 0) (𝓝 (0 : Pair)) := by
    exact continuous_const.prodMk continuous_id |>.tendsto 0
  have hCa : AnalyticAt ℂ (fun u : ℂ => C (0, u)) 0 :=
    hC.comp_of_eq (f := fun u : ℂ => (0, u)) (analyticAt_const.prod analyticAt_id) rfl
  have heq : (fun u : ℂ => B (0, u)) =ᶠ[𝓝 0]
      (fun u => (∑ j ∈ Finset.range (2 * m), coefficient a b j 0 * u ^ j) +
        u ^ (2 * m) * C (0, u)) := by
    filter_upwards [hcurve.eventually hfactor] with u hu
    rw [hu, remainder_at_zero U hU0]
    simp only [rootProduct, neg_zero, hU0, sub_zero]
    rw [← pow_two, ← pow_mul]
  have hpoly : ContDiffAt ℂ n
      (fun u : ℂ => ∑ j ∈ Finset.range (2 * m), coefficient a b j 0 * u ^ j) 0 := by fun_prop
  have htail : ContDiffAt ℂ n (fun u : ℂ => u ^ (2 * m) * C (0, u)) 0 :=
    (by fun_prop : ContDiffAt ℂ n (fun u : ℂ => u ^ (2 * m)) 0).mul
      hCa.contDiffAt
  have hd : iteratedDeriv n (fun u => B (0, u)) 0 =
      coefficient a b n 0 * (n.factorial : ℂ) := by
    rw [heq.iteratedDeriv_eq, iteratedDeriv_fun_add hpoly htail,
      iteratedDeriv_power_mul_zero hCa _ _ hn.le, if_neg (Nat.ne_of_lt hn), add_zero,
      iteratedDeriv_fun_sum]
    · rw [Finset.sum_eq_single n]
      · simp [Nat.descFactorial_self]
      · intro j hj hjn
        simp only [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero,
          if_neg (Ne.symm hjn), Nat.cast_zero, mul_zero]
      · intro hne
        exact False.elim (hne (Finset.mem_range.mpr hn))
    · intro j hj
      fun_prop
  rw [hd, mul_div_cancel_right₀ _ (by exact_mod_cast Nat.factorial_ne_zero n)]

end Kneser.AnalyticRootRemainderJets

end
