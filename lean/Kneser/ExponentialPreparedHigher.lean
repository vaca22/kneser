import Kneser.ActualCorrectionDirections
import Kneser.AnalyticFiniteLinearSystem

/-!
Arbitrary finite-order preparation of the actual exponential logarithmic
defect.  The correction coefficients are constructed by analytic root
division and a Cramer system whose determinant is proved nonzero at merger.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Kneser.ExponentialPreparedHigher

open Filter Matrix Kneser.ExponentialUnfolding Kneser.ExponentialPreparedQuadratic
open Kneser.ExponentialMatrixDividedDifference Kneser.PreparedTwoRootDivision
open Kneser.AnalyticRootDivision Kneser.AnalyticRootRemainderJets
open Kneser.ActualCorrectionDirections Kneser.AnalyticFiniteLinearSystem
open Kneser.ExponentialLogDefect Kneser.ExponentialPreparedModel
open scoped Topology BigOperators

def correction (m : ℕ) (e : Fin (2 * m) → ℂ → ℂ) (s u : ℂ) : ℂ :=
  ∑ i : Fin (2 * m), e i s * u ^ (i.val + 1)

theorem correction_zero (m : ℕ) (e : Fin (2 * m) → ℂ → ℂ) (s : ℂ) :
    correction m e s 0 = 0 := by simp [correction]

theorem correction_difference (U : ℂ → ℂ) (m : ℕ)
    (e : Fin (2 * m) → ℂ → ℂ) (x u : ℂ)
    (hf : unfolding (x ^ 2) u - u = rootProduct U x u * symmetricCofactor U x u) :
    correction m e (x ^ 2) (unfolding (x ^ 2) u) - correction m e (x ^ 2) u =
      rootProduct U x u * ∑ i : Fin (2 * m), e i (x ^ 2) * direction U i.val (x, u) := by
  simp only [correction, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← mul_sub, direction_factor U i.val x u hf]
  ring

/-- The correction system has proved nonzero diagonal, not an assumed
analytic preparation or matrix-invertibility input. -/
theorem exists_correction_to_power {U : ℂ → ℂ} {φ : Pair → ℂ}
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0) (hUd : deriv U 0 ≠ 0)
    (hdistinct : ∀ᶠ x in 𝓝 0, U x = U (-x) ↔ x = 0)
    (hK0 : symmetricCofactor U 0 0 = 1 / 2)
    (hφ : AnalyticAt ℂ φ 0) (hφeven : ∀ p, φ (reflectFirst p) = φ p) (m : ℕ) :
    ∃ e : Fin (2 * m) → ℂ → ℂ, ∃ Γ : Pair → ℂ,
      (∀ i, AnalyticAt ℂ (e i) 0) ∧ AnalyticAt ℂ Γ 0 ∧
      (∀ p, Γ (reflectFirst p) = Γ p) ∧
      (∀ᶠ p in 𝓝 (0 : Pair),
        φ p + (∑ i : Fin (2 * m), e i (p.1 ^ 2) * direction U i.val p) =
          rootProduct U p.1 p.2 ^ m * Γ p) := by
  classical
  have hdirs : ∀ i : Fin (2 * m),
      ∃ a b : ℕ → ℂ → ℂ, ∃ C : Pair → ℂ,
        (∀ j < m, AnalyticAt ℂ (a j) 0 ∧ AnalyticAt ℂ (b j) 0) ∧
        AnalyticAt ℂ C 0 ∧ (∀ p, C (reflectFirst p) = C p) ∧
        (∀ᶠ p in 𝓝 (0 : Pair), direction U i.val p =
          remainder U a b m p + rootProduct U p.1 p.2 ^ m * C p) := by
    intro i
    exact exists_power_remainder (analyticAt_direction hU i.val) (direction_even U i.val)
      hU hU0 hUd hdistinct m
  choose a b C hab hCa hCeven hfactor using hdirs
  obtain ⟨aφ, bφ, Cφ, habφ, hCφ, hCφeven, hfactorφ⟩ :=
    exists_power_remainder hφ hφeven hU hU0 hUd hdistinct m
  let M : ℂ → Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ :=
    fun s r i => coefficient (a i) (b i) r.val s
  let v : ℂ → Fin (2 * m) → ℂ := fun s r => -coefficient aφ bφ r.val s
  have hM : ∀ r i, AnalyticAt ℂ (fun s => M s r i) 0 := by
    intro r i
    exact analyticAt_coefficient (a i) (b i) m (hab i) r.val r.isLt
  have hv : ∀ r, AnalyticAt ℂ (fun s => v s r) 0 := by
    intro r
    exact (analyticAt_coefficient aφ bφ m habφ r.val r.isLt).neg
  have hMtri : (M 0).IsLowerTriangular := by
    intro r i hri
    have hri' : r.val < i.val := hri
    have ht := remainder_coefficient_triangular hU hU0 hK0 (a i) (b i) (C i)
      (hCa i) m i.val (hfactor i) r.val r.isLt hri'.le
    simpa only [M, if_neg (Nat.ne_of_lt hri')] using ht
  have hMdiag : ∀ i, M 0 i i = ((i.val : ℂ) + 1) / 2 := by
    intro i
    have ht := remainder_coefficient_triangular hU hU0 hK0 (a i) (b i) (C i)
      (hCa i) m i.val (hfactor i) i.val i.isLt le_rfl
    simpa only [M, ite_true] using ht
  have hdet : (M 0).det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular _ hMtri]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    rw [hMdiag]
    apply div_ne_zero _ (by norm_num)
    exact_mod_cast Nat.succ_ne_zero i.val
  obtain ⟨sol, hsola, hsol⟩ := exists_analytic_solution M v hM hv hdet
  let e : Fin (2 * m) → ℂ → ℂ := fun i s => sol s i
  let Γ : Pair → ℂ := fun p => Cφ p + ∑ i : Fin (2 * m), e i (p.1 ^ 2) * C i p
  have hΓ : AnalyticAt ℂ Γ 0 := by
    apply hCφ.add
    apply Finset.analyticAt_fun_sum
    intro i hi
    exact ((hsola i).comp_of_eq (f := fun p : Pair => p.1 ^ 2)
      (analyticAt_fst.pow 2) (by simp)).mul (hCa i)
  have hΓeven : ∀ p, Γ (reflectFirst p) = Γ p := by
    intro p
    dsimp [Γ, reflectFirst]
    rw [show Cφ (-p.1, p.2) = Cφ p from hCφeven p, neg_sq]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [show C i (-p.1, p.2) = C i p from hCeven i p]
  have hpowsq : Tendsto (fun p : Pair => p.1 ^ 2) (𝓝 0) (𝓝 (0 : ℂ)) := by
    convert (analyticAt_fst.pow 2 : AnalyticAt ℂ (fun p : Pair => p.1 ^ 2) 0).continuousAt.tendsto using 1 <;> first | rfl | norm_num
  have hfactorall : ∀ᶠ p in 𝓝 (0 : Pair), ∀ i : Fin (2 * m),
      direction U i.val p = remainder U (a i) (b i) m p + rootProduct U p.1 p.2 ^ m * C i p :=
    Filter.eventually_all.mpr hfactor
  refine ⟨e, Γ, hsola, hΓ, hΓeven, ?_⟩
  filter_upwards [hfactorφ, hfactorall, hpowsq.eventually hsol] with p hp hpi hs
  have hcoeff : ∀ r : Fin (2 * m), coefficient aφ bφ r.val (p.1 ^ 2) +
      ∑ i : Fin (2 * m), e i (p.1 ^ 2) * coefficient (a i) (b i) r.val (p.1 ^ 2) = 0 := by
    intro r
    have hrow := congrFun hs r
    dsimp [M, v, Matrix.mulVec, dotProduct] at hrow
    dsimp [e]
    simpa only [mul_comm, ← add_eq_zero_iff_eq_neg, add_comm] using hrow
  have hrem : remainder U aφ bφ m p +
      ∑ i : Fin (2 * m), e i (p.1 ^ 2) * remainder U (a i) (b i) m p = 0 := by
    simp_rw [remainder_eq_fin_coefficients, Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro r hr
    calc
      coefficient aφ bφ r.val (p.1 ^ 2) * remainderBasis U r.val p +
          ∑ i : Fin (2 * m), e i (p.1 ^ 2) *
            (coefficient (a i) (b i) r.val (p.1 ^ 2) * remainderBasis U r.val p) =
          (coefficient aφ bφ r.val (p.1 ^ 2) +
            ∑ i : Fin (2 * m), e i (p.1 ^ 2) * coefficient (a i) (b i) r.val (p.1 ^ 2)) *
              remainderBasis U r.val p := by
        rw [add_mul, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hcoeff r, zero_mul]
  rw [hp]
  simp_rw [hpi, mul_add, Finset.sum_add_distrib]
  dsimp [Γ]
  rw [mul_add, Finset.mul_sum]
  have hcomm : ∀ i : Fin (2 * m),
      e i (p.1 ^ 2) * (rootProduct U p.1 p.2 ^ m * C i p) =
        rootProduct U p.1 p.2 ^ m * (e i (p.1 ^ 2) * C i p) := by intro i; ring
  simp_rw [hcomm]
  linear_combination hrem

/-- Preparation to every positive order, retaining the actual paired
logarithmic residue expression. -/
theorem exists_prepared_order {U : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0) (hUd : deriv U 0 ≠ 0)
    (hroots : ∀ᶠ x in 𝓝 0, unfolding (x ^ 2) (U x) = U x ∧
      unfolding (x ^ 2) (U (-x)) = U (-x))
    (hdistinct : ∀ᶠ x in 𝓝 0, U x = U (-x) ↔ x = 0) (m : ℕ) :
    ∃ e : Fin (2 * m) → ℂ → ℂ, ∃ F Γ : Pair → ℂ,
      (∀ i, AnalyticAt ℂ (e i) 0) ∧ AnalyticAt ℂ F 0 ∧ AnalyticAt ℂ Γ 0 ∧
      (∀ p, F (reflectFirst p) = F p) ∧ (∀ p, Γ (reflectFirst p) = Γ p) ∧
      (∀ᶠ p in 𝓝 (0 : Pair),
        F p + correction m e (p.1 ^ 2) (unfolding (p.1 ^ 2) p.2) -
          correction m e (p.1 ^ 2) p.2 = rootProduct U p.1 p.2 ^ (m + 1) * Γ p) ∧
      (∀ᶠ p in 𝓝 (0 : Pair), p.1 ≠ 0 → F p =
        Complex.log (1 + (p.2 - U (-p.1)) * symmetricCofactor U p.1 p.2) /
          Complex.log (rootMultiplier U p.1) +
        Complex.log (1 + (p.2 - U p.1) * symmetricCofactor U p.1 p.2) /
          Complex.log (rootMultiplier U (-p.1)) - 1) := by
  obtain ⟨F, φ, hF, hφ, hFeven, hφeven, hFfactor, hresidue⟩ :=
    exists_analytic_log_defect hU hU0 hUd hroots hdistinct
  have hK0 := symmetricCofactor_zero hU hU0 hroots hdistinct
  obtain ⟨e, Γ, he, hΓ, hΓeven, hprepared⟩ :=
    exists_correction_to_power hU hU0 hUd hdistinct hK0 hφ hφeven m
  refine ⟨e, F, Γ, he, hF, hΓ, hFeven, hΓeven, ?_, hresidue⟩
  have hfst : Tendsto (fun p : Pair => p.1) (𝓝 0) (𝓝 (0 : ℂ)) := continuous_fst.tendsto 0
  have hfactor := eventually_symmetricCofactor_factor hU hroots hdistinct
  filter_upwards [hFfactor, hprepared, hfst.eventually hfactor] with p hFp hprep hfac
  have hP := correction_difference U m e p.1 p.2 (hfac p.2)
  change F p = rootProduct U p.1 p.2 * φ p at hFp
  rw [hFp]
  have hleft : rootProduct U p.1 p.2 * φ p +
      correction m e (p.1 ^ 2) (unfolding (p.1 ^ 2) p.2) - correction m e (p.1 ^ 2) p.2 =
      rootProduct U p.1 p.2 *
        (φ p + ∑ i : Fin (2 * m), e i (p.1 ^ 2) * direction U i.val p) := by
    linear_combination hP
  rw [hleft, hprep, pow_succ]
  ring

/-- For every N=m+1 the actual exponential roots, polynomial correction,
cofactor and q^N residual are constructed, with no preparation input. -/
theorem exists_actual_prepared_order (m : ℕ) :
    ∃ U a b : ℂ → ℂ, ∃ e : Fin (2 * m) → ℂ → ℂ,
    ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : Pair → ℂ,
      AnalyticAt ℂ U 0 ∧ U 0 = 0 ∧ deriv U 0 ≠ 0 ∧
      AnalyticAt ℂ a 0 ∧ AnalyticAt ℂ b 0 ∧ a 0 = 0 ∧ b 0 = 0 ∧
      (∀ i, AnalyticAt ℂ (e i) 0) ∧ AnalyticAt ℂ F 0 ∧ AnalyticAt ℂ Γ 0 ∧
      K 0 0 = 1 / 2 ∧ ContinuousAt (fun p : Pair => K p.1 p.2) 0 ∧
      (∀ p, F (reflectFirst p) = F p) ∧ (∀ p, Γ (reflectFirst p) = Γ p) ∧
      (∀ x u, ExponentialRootPolynomial.rootPolynomial a b (x ^ 2) u = rootProduct U x u) ∧
      (∀ᶠ x in 𝓝 0, unfolding (x ^ 2) (U x) = U x ∧ unfolding (x ^ 2) (U (-x)) = U (-x)) ∧
      (∀ᶠ s in 𝓝 0, ∀ u, unfolding s u - u =
        ExponentialRootPolynomial.rootPolynomial a b s u * K s u) ∧
      (∀ᶠ p in 𝓝 (0 : Pair),
        F p + correction m e (p.1 ^ 2) (unfolding (p.1 ^ 2) p.2) - correction m e (p.1 ^ 2) p.2 =
          ExponentialRootPolynomial.rootPolynomial a b (p.1 ^ 2) p.2 ^ (m + 1) * Γ p) ∧
      (∀ᶠ p in 𝓝 (0 : Pair), p.1 ≠ 0 → F p =
        Complex.log (1 + (p.2 - U (-p.1)) * symmetricCofactor U p.1 p.2) /
          Complex.log (rootMultiplier U p.1) +
        Complex.log (1 + (p.2 - U p.1) * symmetricCofactor U p.1 p.2) /
          Complex.log (rootMultiplier U (-p.1)) - 1) := by
  obtain ⟨U, a, b, hU, hU0, hUd, ha, hb, ha0, hb0, _hasum, _hbprod, hq,
    hroots, hdistinct⟩ := ExponentialRootPolynomial.exists_analytic_rootPolynomial
  obtain ⟨e, F, Γ, he, hF, hΓ, hFeven, hΓeven, hprepared, hresidue⟩ :=
    exists_prepared_order hU hU0 hUd hroots hdistinct m
  refine ⟨U, a, b, e, descendedCofactor U, F, Γ, hU, hU0, hUd, ha, hb, ha0, hb0,
    he, hF, hΓ, ?_, continuousAt_descendedCofactor hU 0, hFeven, hΓeven, hq,
    hroots, ?_, ?_, hresidue⟩
  · simpa only [descendedCofactor, Complex.sqrt_zero] using
      symmetricCofactor_zero hU hU0 hroots hdistinct
  · have hsqrt : Tendsto Complex.sqrt (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
      simpa only [Complex.sqrt_zero] using
        (Complex.continuousAt_sqrt (Or.inl (by simp : (0 : ℝ) ≤ (0 : ℂ).re))).tendsto
    filter_upwards [hsqrt.eventually (eventually_symmetricCofactor_factor hU hroots hdistinct)] with s hs u
    have hf := hs u
    rw [← hq (Complex.sqrt s) u, AnalyticEvenDescent.square_sqrt] at hf
    exact hf
  · filter_upwards [hprepared] with p hp
    rw [hq]
    exact hp

end Kneser.ExponentialPreparedHigher

end
