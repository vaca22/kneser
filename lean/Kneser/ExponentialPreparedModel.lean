import Kneser.ExponentialMatrixDividedDifference

/-!
# Constructive ingredients for the prepared logarithmic model

The logarithmic multiplier residue and the finite polynomial interpolation
are constructed analytically at the merging fixed points. No preparation
polynomial or Weierstrass division conclusion is an axiom of this file.
-/

noncomputable section

namespace Kneser.ExponentialPreparedModel

open Kneser.ExponentialUnfolding Kneser.ExponentialRootPolynomial
open Kneser.ExponentialMatrixDividedDifference Kneser.AnalyticEvenDescent
open Filter
open scoped Topology

def rootMultiplier (U : ℂ → ℂ) (x : ℂ) : ℂ := (1 - x ^ 2) * (1 + U x)

theorem analyticAt_rootMultiplier {U : ℂ → ℂ} (hU : AnalyticAt ℂ U 0) :
    AnalyticAt ℂ (rootMultiplier U) 0 := by
  change AnalyticAt ℂ (fun x => (1 - x ^ 2) * (1 + U x)) 0
  fun_prop

theorem hasDerivAt_rootMultiplier_zero {U : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0) :
    HasDerivAt (rootMultiplier U) (deriv U 0) 0 := by
  have h := (((hasDerivAt_id (0 : ℂ)).pow 2).const_sub 1).mul
    (hU.hasStrictDerivAt.hasDerivAt.const_add 1)
  convert h using 1 <;> first | rfl | simp [hU0]

/-- The actual residue denominator has its simple zero extracted, including
its nonzero leading coefficient. -/
theorem exists_log_multiplier_factor {U : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ H 0 = deriv U 0 ∧
      (∀ x, Complex.log (rootMultiplier U x) = x * H x) := by
  have hM0 : rootMultiplier U 0 = 1 := by simp [rootMultiplier, hU0]
  have hslit : rootMultiplier U 0 ∈ Complex.slitPlane := by
    simp [hM0, Complex.mem_slitPlane_iff]
  have hLa := (analyticAt_rootMultiplier hU).clog hslit
  have hLd : HasDerivAt (fun x => Complex.log (rootMultiplier U x)) (deriv U 0) 0 := by
    have h := (hasDerivAt_rootMultiplier_zero hU hU0).clog hslit
    convert h using 1 <;> first | rfl | simp [hM0]
  obtain ⟨R, hRa, hR⟩ := hLa.exists_eq_sum_add_pow_mul 2
  let H : ℂ → ℂ := fun x => deriv U 0 + x * R x
  have hHa : AnalyticAt ℂ H 0 := by dsimp [H]; fun_prop
  refine ⟨H, hHa, by simp [H], ?_⟩
  intro x
  have ht := hR x
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    iteratedDeriv_zero, iteratedDeriv_one] at ht
  norm_num [smul_eq_mul, hM0, hLd.deriv] at ht
  dsimp [H]
  linear_combination ht

/-- An odd analytic difference admits a genuine analytic quotient by x. -/
theorem exists_odd_difference_factor {v : ℂ → ℂ} (hv : AnalyticAt ℂ v 0) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ H 0 = 2 * deriv v 0 ∧
      (∀ x, v x - v (-x) = x * H x) := by
  have hneg : AnalyticAt ℂ (fun x => v (-x)) 0 := by
    exact hv.comp_of_eq (f := fun x : ℂ => -x) analyticAt_id.neg (by simp)
  have ha : AnalyticAt ℂ (fun x => v x - v (-x)) 0 := hv.sub hneg
  have hd : HasDerivAt (fun x => v x - v (-x)) (2 * deriv v 0) 0 := by
    have hvd := hv.hasStrictDerivAt.hasDerivAt
    have hnd := hvd.comp_of_eq 0 ((hasDerivAt_id (0 : ℂ)).neg) (by simp)
    convert hvd.sub hnd using 1 <;> first | rfl | ring
  obtain ⟨R, hRa, hR⟩ := ha.exists_eq_sum_add_pow_mul 2
  let H : ℂ → ℂ := fun x => 2 * deriv v 0 + x * R x
  have hHa : AnalyticAt ℂ H 0 := by dsimp [H]; fun_prop
  refine ⟨H, hHa, by simp [H], ?_⟩
  intro x
  have ht := hR x
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    iteratedDeriv_zero, iteratedDeriv_one, neg_zero, sub_self] at ht
  norm_num [smul_eq_mul, hd.deriv] at ht
  dsimp [H]
  linear_combination ht

/-- The derivative of a quadratic correction is interpolated at the two
merging roots, with coefficients analytic in the original parameter x². -/
theorem exists_analytic_quadratic_interpolant {U v : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0) (hUne : deriv U 0 ≠ 0) (hv : AnalyticAt ℂ v 0) :
    ∃ e₁ e₂ : ℂ → ℂ, AnalyticAt ℂ e₁ 0 ∧ AnalyticAt ℂ e₂ 0 ∧
      (∀ᶠ x in 𝓝 0, e₁ (x ^ 2) + 2 * U x * e₂ (x ^ 2) = v x ∧
        e₁ (x ^ 2) + 2 * U (-x) * e₂ (x ^ 2) = v (-x)) := by
  obtain ⟨G, hGa, hG0, hG⟩ := exists_odd_difference_factor hU
  obtain ⟨H, hHa, hH0, hH⟩ := exists_odd_difference_factor hv
  have hGne : G 0 ≠ 0 := by rw [hG0]; exact mul_ne_zero (by norm_num) hUne
  let E₂ : ℂ → ℂ := fun x => H x / (2 * G x)
  have hE₂a : AnalyticAt ℂ E₂ 0 := hHa.div (analyticAt_const.mul hGa)
    (mul_ne_zero (by norm_num) hGne)
  let E₂e : ℂ → ℂ := fun x => (E₂ x + E₂ (-x)) / 2
  have hE₂even : ∀ x, E₂e (-x) = E₂e x := by
    intro x; dsimp [E₂e]; simp only [neg_neg, add_comm]
  have hE₂ea : AnalyticAt ℂ E₂e 0 := by
    exact (hE₂a.add (hE₂a.comp_of_eq analyticAt_id.neg (by simp))).div_const
  let E₁ : ℂ → ℂ := fun x => v x - 2 * U x * E₂e x
  have hE₁a : AnalyticAt ℂ E₁ 0 := hv.sub ((analyticAt_const.mul hU).mul hE₂ea)
  let E₁e : ℂ → ℂ := fun x => (E₁ x + E₁ (-x)) / 2
  have hE₁even : ∀ x, E₁e (-x) = E₁e x := by
    intro x; dsimp [E₁e]; simp only [neg_neg, add_comm]
  have hE₁ea : AnalyticAt ℂ E₁e 0 := by
    exact (hE₁a.add (hE₁a.comp_of_eq analyticAt_id.neg (by simp))).div_const
  obtain ⟨e₁, he₁a, he₁⟩ := exists_analytic_descent hE₁even hE₁ea
  obtain ⟨e₂, he₂a, he₂⟩ := exists_analytic_descent hE₂even hE₂ea
  have hGevent : ∀ᶠ x in 𝓝 0, G x ≠ 0 := hGa.continuousAt.eventually_ne hGne
  have hneg : Tendsto (fun x : ℂ => -x) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using continuous_neg.continuousAt.tendsto (x := (0 : ℂ))
  have hrel (x : ℂ) (hx : G x ≠ 0) :
      v x - v (-x) = 2 * (U x - U (-x)) * E₂ x := by
    rw [hH, hG]
    dsimp [E₂]
    field_simp
  refine ⟨e₁, e₂, he₁a, he₂a, ?_⟩
  filter_upwards [hGevent, hneg.eventually hGevent] with x hx hnx
  have h₁ := hrel x hx
  have h₂ := hrel (-x) hnx
  simp only [neg_neg] at h₂
  have hrels : v x - v (-x) = 2 * (U x - U (-x)) * E₂e x := by
    dsimp [E₂e]
    linear_combination (h₁ - h₂) / 2
  rw [he₁, he₂]
  dsimp [E₁e, E₁]
  rw [hE₂even]
  constructor
  · linear_combination -hrels / 2
  · linear_combination hrels / 2

/-- The numerator of the paired logarithmic defect after extracting the
simple zero in each residue denominator. -/
def logDefectNumerator (U H : ℂ → ℂ) (x u : ℂ) : ℂ :=
  Complex.log (1 + (u - U (-x)) * symmetricCofactor U x u) / H x -
    Complex.log (1 + (u - U x) * symmetricCofactor U x u) / H (-x)

theorem logDefectNumerator_zero (U H : ℂ → ℂ) (u : ℂ) :
    logDefectNumerator U H 0 u = 0 := by
  simp [logDefectNumerator]

theorem logDefectNumerator_odd (U H : ℂ → ℂ) (x u : ℂ) :
    logDefectNumerator U H (-x) u = -logDefectNumerator U H x u := by
  simp only [logDefectNumerator, neg_neg, symmetricCofactor_even]
  ring

theorem analyticAt_logDefectNumerator {U H : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => logDefectNumerator U H p.1 p.2) (0, 0) := by
  have hUx : AnalyticAt ℂ (fun p : ℂ × ℂ => U p.1) (0, 0) :=
    hU.comp_of_eq (f := fun p : ℂ × ℂ => p.1) analyticAt_fst rfl
  have hUn : AnalyticAt ℂ (fun p : ℂ × ℂ => U (-p.1)) (0, 0) :=
    hU.comp_of_eq (f := fun p : ℂ × ℂ => -p.1) analyticAt_fst.neg (by simp)
  have hHx : AnalyticAt ℂ (fun p : ℂ × ℂ => H p.1) (0, 0) :=
    hH.comp_of_eq (f := fun p : ℂ × ℂ => p.1) analyticAt_fst rfl
  have hHn : AnalyticAt ℂ (fun p : ℂ × ℂ => H (-p.1)) (0, 0) :=
    hH.comp_of_eq (f := fun p : ℂ × ℂ => -p.1) analyticAt_fst.neg (by simp)
  have hK : AnalyticAt ℂ (fun p : ℂ × ℂ => symmetricCofactor U p.1 p.2) (0, 0) :=
    analyticAt_symmetricCofactor hU analyticAt_fst rfl analyticAt_snd
  have h₁ := (analyticAt_const.add ((analyticAt_snd.sub hUn).mul hK)).clog
    (show 1 + ((0 : ℂ) - U (-(0 : ℂ))) * symmetricCofactor U 0 0 ∈
      Complex.slitPlane by simp [hU0, Complex.mem_slitPlane_iff])
  have h₂ := (analyticAt_const.add ((analyticAt_snd.sub hUx).mul hK)).clog
    (show 1 + ((0 : ℂ) - U 0) * symmetricCofactor U 0 0 ∈
      Complex.slitPlane by simp [hU0, Complex.mem_slitPlane_iff])
  exact (h₁.div hHx hHne).sub (h₂.div hHn (by simpa only [neg_zero] using hHne))

/-- Away from x=0, the analytic numerator divided by x equals the actual
paired reciprocal-log-multiplier expression. -/
theorem logDefectNumerator_residue_pair (U H : ℂ → ℂ)
    (hH : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (x u : ℂ) (hx : x ≠ 0) (hHx : H x ≠ 0) (hHnx : H (-x) ≠ 0) :
    logDefectNumerator U H x u / x =
      Complex.log (1 + (u - U (-x)) * symmetricCofactor U x u) /
        Complex.log (rootMultiplier U x) +
      Complex.log (1 + (u - U x) * symmetricCofactor U x u) /
        Complex.log (rootMultiplier U (-x)) := by
  rw [hH x, hH (-x)]
  unfold logDefectNumerator
  field_simp
  ring

def polynomialCorrection (e₁ e₂ : ℂ → ℂ) (s u : ℂ) : ℂ :=
  e₁ s * u + e₂ s * u ^ 2

/-- The two correction directions have their genuine cofactor extracted. -/
theorem polynomialCorrection_difference (e₁ e₂ : ℂ → ℂ)
    (s u q K : ℂ) (hf : unfolding s u - u = q * K) :
    polynomialCorrection e₁ e₂ s (unfolding s u) - polynomialCorrection e₁ e₂ s u =
      q * K * (e₁ s + e₂ s * (unfolding s u + u)) := by
  unfold polynomialCorrection
  linear_combination (e₁ s + e₂ s * (unfolding s u + u)) * hf

/-- Differentiating the genuine fixed-point factor gives its exact multiplier,
which is needed to evaluate the logarithmic defect at each root. -/
theorem rootMultiplier_eq_one_add_gap_cofactor (U : ℂ → ℂ) (x : ℂ)
    (hroot : unfolding (x ^ 2) (U x) = U x)
    (hfactor : ∀ u, unfolding (x ^ 2) u - u =
      (u - U x) * (u - U (-x)) * symmetricCofactor U x u) :
    rootMultiplier U x = 1 + (U x - U (-x)) * symmetricCofactor U x (U x) := by
  have hexp : Complex.exp (-(x ^ 2) + (1 - x ^ 2) * U x) = 1 + U x := by
    change Complex.exp (-(x ^ 2) + (1 - x ^ 2) * U x) - 1 = U x at hroot
    linear_combination hroot
  have hd : HasDerivAt (fun u => unfolding (x ^ 2) u - u)
      (rootMultiplier U x - 1) (U x) := by
    have h := (hasDerivAt_unfolding_spatial (x ^ 2) (U x)).sub (hasDerivAt_id (U x))
    convert h using 1 <;> first | rfl | (rw [hexp]; dsimp [rootMultiplier]; ring)
  have hK := (analyticAt_symmetricCofactor_spatial U x (U x)).hasStrictDerivAt.hasDerivAt
  have hprod : HasDerivAt
      (fun u => (u - U x) * (u - U (-x)) * symmetricCofactor U x u)
      ((U x - U (-x)) * symmetricCofactor U x (U x)) (U x) := by
    have h := (((hasDerivAt_id (U x)).sub_const (U x)).mul
      ((hasDerivAt_id (U x)).sub_const (U (-x)))).mul hK
    convert h using 1 <;> first | rfl | simp
  have hdf := hprod.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u => hfactor u))
  have heq := hd.unique hdf
  linear_combination heq

theorem logDefectNumerator_at_root (U H : ℂ → ℂ)
    (hH : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (x : ℂ) (hHx : H x ≠ 0)
    (hroot : unfolding (x ^ 2) (U x) = U x)
    (hfactor : ∀ u, unfolding (x ^ 2) u - u =
      (u - U x) * (u - U (-x)) * symmetricCofactor U x u) :
    logDefectNumerator U H x (U x) = x := by
  have hm := rootMultiplier_eq_one_add_gap_cofactor U x hroot hfactor
  unfold logDefectNumerator
  rw [← hm, hH x]
  simp [hHx]

end Kneser.ExponentialPreparedModel

end
