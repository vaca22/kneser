import Kneser.ExponentialRootPolynomial
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Entire exponential second divided difference

A three by three matrix exponential constructs the divided difference at
arbitrary nodes, including coincident nodes. Its exact Newton identity is
proved from triangularity and commutation, without dividing by node gaps.
-/

noncomputable section

namespace Kneser.ExponentialMatrixDividedDifference

open scoped Matrix.Norms.Frobenius Topology
open Matrix Filter

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℂ

/-- An upper bidiagonal matrix whose exponential records Newton differences. -/
def nodeMatrix (a b c : ℂ) : Mat3 := !![a, 1, 0; 0, b, 1; 0, 0, c]

def entryLM (i j : Fin 3) : Mat3 →ₗ[ℂ] ℂ where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def entryCLM (i j : Fin 3) : Mat3 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (entryLM i j)

@[simp] theorem entryCLM_apply (i j : Fin 3) (M : Mat3) : entryCLM i j M = M i j := rfl

theorem nodeMatrix_triangular (a b c : ℂ) : (nodeMatrix a b c).BlockTriangular id := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [nodeMatrix]

theorem triangular_mul_diag {M N : Mat3}
    (hM : M.BlockTriangular id) (hN : N.BlockTriangular id) (i : Fin 3) :
    (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · rw [hM hlt]
      simp
    · rw [hN hgt]
      simp
  · simp

theorem triangular_pow_diag {M : Mat3} (hM : M.BlockTriangular id)
    (n : ℕ) (i : Fin 3) : (M ^ n) i i = (M i i) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, triangular_mul_diag (hM.pow n) hM, ih, pow_succ]

theorem triangular_exp_diag {M : Mat3} (hM : M.BlockTriangular id) (i : Fin 3) :
    NormedSpace.exp M i i = Complex.exp (M i i) := by
  have hm := (entryCLM i i).hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) M)
  have hc := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (M i i)
  have heq : (fun n : ℕ => entryCLM i i (((Nat.factorial n : ℂ)⁻¹) • M ^ n)) =
      (fun n : ℕ => ((Nat.factorial n : ℂ)⁻¹) • (M i i) ^ n) := by
    funext n
    simp [triangular_pow_diag hM]
  rw [heq] at hm
  have h := hm.unique hc
  convert (by simpa only [entryCLM_apply, ← Complex.exp_eq_exp_ℂ] using h) using 1 <;> rfl

/-- The first and second Newton divided differences, extended at all nodes. -/
def firstDifference (a b c : ℂ) : ℂ := NormedSpace.exp (nodeMatrix a b c) 0 1
def secondDifference (a b c : ℂ) : ℂ := NormedSpace.exp (nodeMatrix a b c) 0 2

theorem matrix_exp_relations (a b c : ℂ) :
    (b - a) * firstDifference a b c = Complex.exp b - Complex.exp a ∧
      (c - b) * (NormedSpace.exp (nodeMatrix a b c) 1 2) =
        Complex.exp c - Complex.exp b ∧
      (c - a) * secondDifference a b c =
        NormedSpace.exp (nodeMatrix a b c) 1 2 - firstDifference a b c := by
  let T := nodeMatrix a b c
  let E := NormedSpace.exp T
  have hcomm : T * E = E * T := (Commute.refl T).exp_right.eq
  have hdiag (i : Fin 3) := triangular_exp_diag (nodeMatrix_triangular a b c) i
  have h01 := congrArg (fun M : Mat3 => M 0 1) hcomm
  have h12 := congrArg (fun M : Mat3 => M 1 2) hcomm
  have h02 := congrArg (fun M : Mat3 => M 0 2) hcomm
  have hd0 : E 0 0 = Complex.exp a := by simpa [E, T, nodeMatrix] using hdiag 0
  have hd1 : E 1 1 = Complex.exp b := by simpa [E, T, nodeMatrix] using hdiag 1
  have hd2 : E 2 2 = Complex.exp c := by simpa [E, T, nodeMatrix] using hdiag 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three] at h01 h12 h02
  simp [T, nodeMatrix] at h01 h12 h02
  change (b - a) * E 0 1 = _ ∧ (c - b) * E 1 2 = _ ∧
    (c - a) * E 0 2 = E 1 2 - E 0 1
  constructor
  · linear_combination -h01 + hd1 - hd0
  constructor
  · linear_combination -h12 + hd2 - hd1
  · linear_combination -h02

/-- Newton's interpolation formula holds even when the three nodes coincide. -/
theorem exponential_newton_identity (a b c : ℂ) :
    Complex.exp c = Complex.exp a + (c - a) * firstDifference a b c +
      (c - a) * (c - b) * secondDifference a b c := by
  obtain ⟨h01, h12, h02⟩ := matrix_exp_relations a b c
  linear_combination -h01 - h12 - (c - b) * h02

def diagonalLM : (Fin 3 → ℂ) →ₗ[ℂ] Mat3 where
  toFun v := Matrix.diagonal v
  map_add' _ _ := (Matrix.diagonal_add _ _).symm
  map_smul' _ _ := by simp [Matrix.diagonal_smul]

def diagonalCLM : (Fin 3 → ℂ) →L[ℂ] Mat3 :=
  LinearMap.toContinuousLinearMap diagonalLM

@[simp] theorem diagonalCLM_apply (v : Fin 3 → ℂ) :
    diagonalCLM v = Matrix.diagonal v := rfl

theorem analyticAt_nodeMatrix {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a b c : E → ℂ} {z : E}
    (ha : AnalyticAt ℂ a z) (hb : AnalyticAt ℂ b z) (hc : AnalyticAt ℂ c z) :
    AnalyticAt ℂ (fun x => nodeMatrix (a x) (b x) (c x)) z := by
  have hv : AnalyticAt ℂ (fun x => ![a x, b x, c x]) z := by
    apply AnalyticAt.pi
    intro i
    fin_cases i <;> dsimp <;> assumption
  have hd := ((diagonalCLM).analyticAt _).comp hv
  have ht := hd.add (analyticAt_const (v := nodeMatrix 0 0 0))
  convert ht using 1
  funext x
  change nodeMatrix (a x) (b x) (c x) = Matrix.diagonal ![a x, b x, c x] + nodeMatrix 0 0 0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nodeMatrix]

theorem analyticAt_secondDifference {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a b c : E → ℂ} {z : E}
    (ha : AnalyticAt ℂ a z) (hb : AnalyticAt ℂ b z) (hc : AnalyticAt ℂ c z) :
    AnalyticAt ℂ (fun x => secondDifference (a x) (b x) (c x)) z := by
  exact ((entryCLM 0 2).analyticAt _).comp
    ((NormedSpace.exp_analytic (𝕂 := ℂ) _).comp (analyticAt_nodeMatrix ha hb hc))

open Kneser.ExponentialUnfolding Kneser.ExponentialRootPolynomial

/-- An entire candidate for the cofactor of the two-root fixed-point polynomial. -/
def cofactor (s a b u : ℂ) : ℂ := Complex.exp (-s) * (1 - s) ^ 2 *
  secondDifference ((1 - s) * a) ((1 - s) * b) ((1 - s) * u)

theorem analyticAt_cofactor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {s a b u : E → ℂ} {z : E}
    (hs : AnalyticAt ℂ s z) (ha : AnalyticAt ℂ a z)
    (hb : AnalyticAt ℂ b z) (hu : AnalyticAt ℂ u z) :
    AnalyticAt ℂ (fun x => cofactor (s x) (a x) (b x) (u x)) z := by
  have hmu : AnalyticAt ℂ (fun x => 1 - s x) z := analyticAt_const.sub hs
  exact ((hs.neg.cexp).mul (hmu.pow 2)).mul
    (analyticAt_secondDifference (hmu.mul ha) (hmu.mul hb) (hmu.mul hu))

/-- At two distinct actual fixed points this candidate is the genuine cofactor. -/
theorem unfolding_two_fixedPoints_factor (s a b u : ℂ)
    (ha : unfolding s a = a) (hb : unfolding s b = b) (hne : a ≠ b) :
    unfolding s u - u = (u - a) * (u - b) * cofactor s a b u := by
  let mu := 1 - s
  let D := firstDifference (mu * a) (mu * b) (mu * u)
  let G := secondDifference (mu * a) (mu * b) (mu * u)
  have hea : Complex.exp (-s) * Complex.exp (mu * a) = 1 + a := by
    rw [← Complex.exp_add]
    change Complex.exp (-s + (1 - s) * a) = 1 + a
    change Complex.exp (-s + (1 - s) * a) - 1 = a at ha
    linear_combination ha
  have heb : Complex.exp (-s) * Complex.exp (mu * b) = 1 + b := by
    rw [← Complex.exp_add]
    change Complex.exp (-s + (1 - s) * b) = 1 + b
    change Complex.exp (-s + (1 - s) * b) - 1 = b at hb
    linear_combination hb
  have hdiff := (matrix_exp_relations (mu * a) (mu * b) (mu * u)).1
  change (mu * b - mu * a) * D = _ at hdiff
  have hslope : (b - a) * (Complex.exp (-s) * mu * D) = (b - a) * 1 := by
    linear_combination Complex.exp (-s) * hdiff + heb - hea
  have hslope' : Complex.exp (-s) * mu * D = 1 :=
    mul_left_cancel₀ (sub_ne_zero.mpr (Ne.symm hne)) hslope
  have hn := exponential_newton_identity (mu * a) (mu * b) (mu * u)
  change Complex.exp (mu * u) = Complex.exp (mu * a) +
    (mu * u - mu * a) * D + (mu * u - mu * a) * (mu * u - mu * b) * G at hn
  have hexpu : Complex.exp (-s + mu * u) = Complex.exp (-s) * Complex.exp (mu * u) :=
    Complex.exp_add _ _
  change Complex.exp (-s + mu * u) - 1 - u =
    (u - a) * (u - b) * (Complex.exp (-s) * mu ^ 2 * G)
  linear_combination hexpu + Complex.exp (-s) * hn + hea + (u - a) * hslope'

/-- Symmetrization makes the cofactor even in the Morse coordinate everywhere. -/
def symmetricCofactor (U : ℂ → ℂ) (x u : ℂ) : ℂ :=
  (cofactor (x ^ 2) (U x) (U (-x)) u +
    cofactor (x ^ 2) (U (-x)) (U x) u) / 2

theorem symmetricCofactor_even (U : ℂ → ℂ) (x u : ℂ) :
    symmetricCofactor U (-x) u = symmetricCofactor U x u := by
  simp only [symmetricCofactor, neg_sq, neg_neg, add_comm]

theorem analyticAt_symmetricCofactor {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : ℂ → ℂ} {x u : E → ℂ} {z : E}
    (hU : AnalyticAt ℂ U 0) (hx : AnalyticAt ℂ x z) (hx0 : x z = 0)
    (hu : AnalyticAt ℂ u z) :
    AnalyticAt ℂ (fun w => symmetricCofactor U (x w) (u w)) z := by
  have hUx : AnalyticAt ℂ (fun w => U (x w)) z := by
    have h : AnalyticAt ℂ U (x z) := hx0.symm ▸ hU
    exact h.comp hx
  have hUn : AnalyticAt ℂ (fun w => U (-x w)) z := by
    have h : AnalyticAt ℂ U (-x z) := by simpa only [hx0, neg_zero] using hU
    exact h.comp (f := fun w : E => -(x w)) hx.neg
  exact ((analyticAt_cofactor (hx.pow 2) hUx hUn hu).add
    (analyticAt_cofactor (hx.pow 2) hUn hUx hu)).div_const

/-- For fixed root values, the entire cofactor is analytic in the spatial
variable at every point; no parameter-locality assumption is needed. -/
theorem analyticAt_symmetricCofactor_spatial (U : ℂ → ℂ) (x u : ℂ) :
    AnalyticAt ℂ (fun w => symmetricCofactor U x w) u := by
  exact ((analyticAt_cofactor analyticAt_const analyticAt_const analyticAt_const analyticAt_id).add
    (analyticAt_cofactor analyticAt_const analyticAt_const analyticAt_const analyticAt_id)).div_const

theorem symmetricCofactor_fixedPoints_factor (U : ℂ → ℂ) (x u : ℂ)
    (h₁ : unfolding (x ^ 2) (U x) = U x)
    (h₂ : unfolding (x ^ 2) (U (-x)) = U (-x)) (hne : U x ≠ U (-x)) :
    unfolding (x ^ 2) u - u =
      (u - U x) * (u - U (-x)) * symmetricCofactor U x u := by
  have h := unfolding_two_fixedPoints_factor (x ^ 2) (U x) (U (-x)) u h₁ h₂ hne
  have h' := unfolding_two_fixedPoints_factor (x ^ 2) (U (-x)) (U x) u h₂ h₁ hne.symm
  unfold symmetricCofactor
  linear_combination (h + h') / 2

/-- Coalescing fixed points still have the exact analytic factor. The equation
at the double root is obtained by continuity, rather than an assumed division. -/
theorem eventually_symmetricCofactor_factor {U : ℂ → ℂ}
    (hUa : AnalyticAt ℂ U 0)
    (hroots : ∀ᶠ x in 𝓝 0, unfolding (x ^ 2) (U x) = U x ∧
      unfolding (x ^ 2) (U (-x)) = U (-x))
    (hdistinct : ∀ᶠ x in 𝓝 0, U x = U (-x) ↔ x = 0) :
    ∀ᶠ x in 𝓝 0, ∀ u, unfolding (x ^ 2) u - u =
      (u - U x) * (u - U (-x)) * symmetricCofactor U x u := by
  have hzero (u : ℂ) : unfolding (0 ^ 2) u - u =
      (u - U 0) * (u - U (-0)) * symmetricCofactor U 0 u := by
    let F : ℂ → ℂ := fun x => unfolding (x ^ 2) u - u
    let G : ℂ → ℂ := fun x =>
      (u - U x) * (u - U (-x)) * symmetricCofactor U x u
    have hFa : AnalyticAt ℂ F 0 := by dsimp [F, unfolding]; fun_prop
    have hUn : AnalyticAt ℂ (fun x => U (-x)) 0 := by
      have h : AnalyticAt ℂ U (-(0 : ℂ)) := by simpa only [neg_zero] using hUa
      exact h.comp analyticAt_id.neg
    have hGa : AnalyticAt ℂ G 0 :=
      (((analyticAt_const.sub hUa).mul (analyticAt_const.sub hUn))).mul
        (analyticAt_symmetricCofactor hUa analyticAt_id rfl analyticAt_const)
    have heq : F =ᶠ[𝓝[≠] 0] G := by
      filter_upwards [hroots.filter_mono nhdsWithin_le_nhds,
        hdistinct.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hd hxne
      exact symmetricCofactor_fixedPoints_factor U x u hx.1 hx.2
        (fun he => hxne ((hd.mp he)))
    exact tendsto_nhds_unique_of_eventuallyEq
      (hFa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (hGa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) heq
  filter_upwards [hroots, hdistinct] with x hx hd u
  by_cases hx0 : x = 0
  · simpa only [hx0] using hzero u
  · exact symmetricCofactor_fixedPoints_factor U x u hx.1 hx.2
      (fun he => hx0 (hd.mp he))

theorem symmetricCofactor_zero {U : ℂ → ℂ}
    (hUa : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hroots : ∀ᶠ x in 𝓝 0, unfolding (x ^ 2) (U x) = U x ∧
      unfolding (x ^ 2) (U (-x)) = U (-x))
    (hdistinct : ∀ᶠ x in 𝓝 0, U x = U (-x) ↔ x = 0) :
    symmetricCofactor U 0 0 = 1 / 2 := by
  have hfactor : ∀ u, unfolding 0 u - u = u ^ 2 * symmetricCofactor U 0 u := by
    have hf := (eventually_symmetricCofactor_factor hUa hroots hdistinct).self_of_nhds
    simpa [hU0, pow_two] using hf
  have ha : AnalyticAt ℂ Complex.exp 0 := by fun_prop
  obtain ⟨R, hRa, hR⟩ := ha.exists_eq_sum_add_pow_mul 3
  let L : ℂ → ℂ := fun u => 1 / 2 + u * R u
  have hLa : AnalyticAt ℂ L 0 := by dsimp [L]; fun_prop
  have hL0 : L 0 = 1 / 2 := by simp [L]
  have hTaylor (u : ℂ) : unfolding 0 u - u = u ^ 2 * L u := by
    have h := hR u
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      iteratedDeriv_eq_iterate, Complex.iter_deriv_exp, Complex.exp_zero] at h
    norm_num [smul_eq_mul] at h
    dsimp [unfolding, L]
    simp only [neg_zero, sub_zero, one_mul, zero_add]
    linear_combination h
  have hKa : AnalyticAt ℂ (fun u => symmetricCofactor U 0 u) 0 :=
    analyticAt_symmetricCofactor hUa analyticAt_const rfl analyticAt_id
  have heq : (fun u => symmetricCofactor U 0 u) =ᶠ[𝓝[≠] 0] L := by
    filter_upwards [self_mem_nhdsWithin] with u hune
    apply mul_left_cancel₀ (pow_ne_zero 2 hune)
    exact (hfactor u).symm.trans (hTaylor u)
  have h := tendsto_nhds_unique_of_eventuallyEq
    (hKa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hLa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) heq
  exact h.trans hL0

/-- The concrete descent to the original parameter is independent of the
choice of square-root branch because the Morse cofactor is even. -/
def descendedCofactor (U : ℂ → ℂ) (s u : ℂ) : ℂ :=
  symmetricCofactor U (Complex.sqrt s) u

theorem analyticAt_descendedCofactor_curve {U v : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0) (hv : AnalyticAt ℂ v 0) :
    AnalyticAt ℂ (fun s => descendedCofactor U s (v s)) 0 := by
  let F : ℂ → ℂ := fun x => symmetricCofactor U x (v (x ^ 2))
  have hve : AnalyticAt ℂ (fun x => v (x ^ 2)) 0 := by
    exact hv.comp_of_eq (f := fun x : ℂ => x ^ 2) (analyticAt_id.pow 2) (by simp)
  have hFa : AnalyticAt ℂ F 0 :=
    analyticAt_symmetricCofactor hU analyticAt_id rfl hve
  have hFeven : ∀ x, F (-x) = F x := by
    intro x
    dsimp [F]
    rw [neg_sq, symmetricCofactor_even]
  have hd := Kneser.AnalyticEvenDescent.analyticAt_even_sqrt hFeven hFa
  convert hd using 1
  funext s
  simp only [descendedCofactor, F, Kneser.AnalyticEvenDescent.square_sqrt]

theorem continuousAt_sqrt_substitution (K : ℂ → ℂ → ℂ) (u : ℂ)
    (hK : ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) (0, u)) :
    ContinuousAt (fun p : ℂ × ℂ => K (Complex.sqrt p.1) p.2) (0, u) := by
  have hsqrt0 : ContinuousAt Complex.sqrt (0 : ℂ) :=
    Complex.continuousAt_sqrt (Or.inl (by simp))
  have hsqrt : ContinuousAt (fun p : ℂ × ℂ => Complex.sqrt p.1) (0, u) :=
    hsqrt0.comp_of_eq (f := fun p : ℂ × ℂ => p.1) continuousAt_fst rfl
  have hp : ContinuousAt (fun p : ℂ × ℂ => (Complex.sqrt p.1, p.2)) (0, u) :=
    hsqrt.prodMk continuousAt_snd
  exact ContinuousAt.comp_of_eq
    (g := fun p : ℂ × ℂ => K p.1 p.2)
    (f := fun p : ℂ × ℂ => (Complex.sqrt p.1, p.2)) hK hp (by simp)

theorem continuousAt_descendedCofactor {U : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0) (u : ℂ) :
    ContinuousAt (fun p : ℂ × ℂ => descendedCofactor U p.1 p.2) (0, u) := by
  have hK : AnalyticAt ℂ (fun p : ℂ × ℂ => symmetricCofactor U p.1 p.2) (0, u) :=
    analyticAt_symmetricCofactor hU analyticAt_fst rfl analyticAt_snd
  exact continuousAt_sqrt_substitution (symmetricCofactor U) u hK.continuousAt

/-- An actual cofactor exists, with analytic dependence along every analytic
parameter curve, joint continuity, and its exact two-root factorization. -/
theorem exists_actual_cofactor :
    ∃ a b : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ,
      AnalyticAt ℂ a 0 ∧ AnalyticAt ℂ b 0 ∧ a 0 = 0 ∧ b 0 = 0 ∧
      K 0 0 = 1 / 2 ∧
      (∀ v : ℂ → ℂ, AnalyticAt ℂ v 0 → AnalyticAt ℂ (fun s => K s (v s)) 0) ∧
      (∀ u, ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) (0, u)) ∧
      (∀ᶠ s in 𝓝 0, ∀ u, unfolding s u - u = rootPolynomial a b s u * K s u) := by
  obtain ⟨U, a, b, hUa, hU0, hUd, haa, hba, ha0, hb0, ha, hb, hq,
    hroots, hdistinct⟩ := exists_analytic_rootPolynomial
  refine ⟨a, b, descendedCofactor U, haa, hba, ha0, hb0, ?_,
    (fun v hv => analyticAt_descendedCofactor_curve hUa hv),
    continuousAt_descendedCofactor hUa, ?_⟩
  · simpa only [descendedCofactor, Complex.sqrt_zero] using
      symmetricCofactor_zero hUa hU0 hroots hdistinct
  · have hsqrt : Tendsto Complex.sqrt (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
      simpa only [Complex.sqrt_zero] using
        (Complex.continuousAt_sqrt (Or.inl (by simp : (0 : ℝ) ≤ (0 : ℂ).re))).tendsto
    have hf := hsqrt.eventually (eventually_symmetricCofactor_factor hUa hroots hdistinct)
    filter_upwards [hf] with s hs u
    have h := hs u
    rw [← hq (Complex.sqrt s) u, Kneser.AnalyticEvenDescent.square_sqrt] at h
    exact h

/-- The actual cofactor proves the leading root-polynomial coefficient and
the nondegenerate discriminant derivative directly from the unfolding. -/
theorem exists_actual_cofactor_discriminant :
    ∃ a b : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ,
      AnalyticAt ℂ a 0 ∧ AnalyticAt ℂ b 0 ∧ a 0 = 0 ∧ b 0 = 0 ∧
      K 0 0 = 1 / 2 ∧ deriv b 0 = -2 ∧
      AnalyticAt ℂ (fun s => a s ^ 2 - 4 * b s) 0 ∧
      HasDerivAt (fun s => a s ^ 2 - 4 * b s) 8 0 ∧
      (∀ v : ℂ → ℂ, AnalyticAt ℂ v 0 → AnalyticAt ℂ (fun s => K s (v s)) 0) ∧
      (∀ u, ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) (0, u)) ∧
      (∀ᶠ s in 𝓝 0, ∀ u, unfolding s u - u = rootPolynomial a b s u * K s u) := by
  obtain ⟨a, b, K, haa, hba, ha0, hb0, hK0, hcurve, hcont, hfactor⟩ := exists_actual_cofactor
  have hKa : AnalyticAt ℂ (fun s => K s 0) 0 := hcurve (fun _ => 0) analyticAt_const
  have hbprod := hba.hasStrictDerivAt.hasDerivAt.mul hKa.hasStrictDerivAt.hasDerivAt
  have heq : (fun s => unfolding s 0) =ᶠ[𝓝 0] (fun s => b s * K s 0) := by
    filter_upwards [hfactor] with s hs
    simpa [rootPolynomial] using hs 0
  have hbprod' := hbprod.congr_of_eventuallyEq heq
  have hd : HasDerivAt (fun s => unfolding s 0) (-1) 0 := by
    have h := hasDerivAt_unfolding_parameter 0 0
    convert h using 1 <;> first | rfl | simp
  have hder := hd.unique hbprod'
  have hbder : deriv b 0 = -2 := by
    simp only [hK0, hb0, zero_mul, add_zero] at hder
    linear_combination -2 * hder
  have hDa : AnalyticAt ℂ (fun s => a s ^ 2 - 4 * b s) 0 :=
    (haa.pow 2).sub (analyticAt_const.mul hba)
  have hDd : HasDerivAt (fun s => a s ^ 2 - 4 * b s) 8 0 := by
    have h := (haa.hasStrictDerivAt.hasDerivAt.pow 2).sub
      (hba.hasStrictDerivAt.hasDerivAt.const_mul 4)
    convert h using 1 <;> first | rfl | norm_num [ha0, hbder]
  exact ⟨a, b, K, haa, hba, ha0, hb0, hK0, hbder, hDa, hDd, hcurve, hcont, hfactor⟩

end Kneser.ExponentialMatrixDividedDifference

end
