import Kneser.ExponentialPreparedQuadratic
import Kneser.ParabolicFatouCoordinate

/-!
# Actual prepared model time on the attracting side

The canonical derivative slope fills the merging parameter. For each point
with negative real part the paired logarithms descend analytically to s.
The one-step identity is proved with explicit branch-domain inequalities.
-/

noncomputable section

namespace Kneser.ExponentialModelTime

open Kneser.ExponentialPreparedModel Kneser.ExponentialMatrixDividedDifference
open Kneser.ExponentialPreparedQuadratic Kneser.ExponentialUnfolding
open Kneser.AnalyticEvenDescent Kneser.ParabolicFatouCoordinate
open Filter
open scoped Topology

def modelNumerator (U H : ℂ → ℂ) (x u : ℂ) : ℂ :=
  Complex.log (U x - u) / H x - Complex.log (U (-x) - u) / H (-x)

theorem modelNumerator_zero (U H : ℂ → ℂ) (u : ℂ) : modelNumerator U H 0 u = 0 := by
  simp [modelNumerator]

theorem modelNumerator_odd (U H : ℂ → ℂ) (x u : ℂ) :
    modelNumerator U H (-x) u = -modelNumerator U H x u := by
  simp only [modelNumerator, neg_neg]
  ring

theorem analyticAt_dslope_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℂ (dslope f 0) 0 := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

theorem dslope_odd_even {f : ℂ → ℂ} (hzero : f 0 = 0)
    (hodd : ∀ x, f (-x) = -f x) (x : ℂ) : dslope f 0 (-x) = dslope f 0 x := by
  by_cases hx : x = 0
  · simp only [hx, neg_zero]
  · rw [dslope_of_ne f (neg_ne_zero.mpr hx), dslope_of_ne f hx,
      slope_def_field, slope_def_field, hodd x, hzero]
    field_simp [hx]
    ring

def logarithmicModel (U H : ℂ → ℂ) (s u : ℂ) : ℂ :=
  dslope (fun x => modelNumerator U H x u) 0 (Complex.sqrt s)

def preparedModelTime (U H e₁ e₂ : ℂ → ℂ) (s u : ℂ) : ℂ :=
  logarithmicModel U H s u + polynomialCorrection e₁ e₂ s u

/-- Each fixed point on the attracting side has a genuine analytic model
time in the original parameter, after cancellation of its two residues. -/
theorem analyticAt_preparedModelTime_parameter {U H e₁ e₂ : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (he₁ : AnalyticAt ℂ e₁ 0) (he₂ : AnalyticAt ℂ e₂ 0)
    (u : ℂ) (hu : u.re < 0) :
    AnalyticAt ℂ (fun s => preparedModelTime U H e₁ e₂ s u) 0 := by
  have hUn : AnalyticAt ℂ (fun x => U (-x)) 0 :=
    hU.comp_of_eq (f := fun x : ℂ => -x) analyticAt_id.neg (by simp)
  have hHn : AnalyticAt ℂ (fun x => H (-x)) 0 :=
    hH.comp_of_eq (f := fun x : ℂ => -x) analyticAt_id.neg (by simp)
  have hslit : U 0 - u ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simpa [hU0] using neg_pos.mpr hu
  have hslitn : U (-(0 : ℂ)) - u ∈ Complex.slitPlane := by simpa only [neg_zero] using hslit
  have hNa : AnalyticAt ℂ (fun x => modelNumerator U H x u) 0 :=
    (((hU.sub analyticAt_const).clog hslit).div hH hHne).sub
      (((hUn.sub analyticAt_const).clog hslitn).div hHn (by simpa only [neg_zero] using hHne))
  have hDa := analyticAt_dslope_zero hNa
  have hDeven : ∀ x, dslope (fun x => modelNumerator U H x u) 0 (-x) =
      dslope (fun x => modelNumerator U H x u) 0 x :=
    dslope_odd_even (modelNumerator_zero U H u) (fun x => modelNumerator_odd U H x u)
  have hlog := analyticAt_even_sqrt hDeven hDa
  have hP : AnalyticAt ℂ (fun s => polynomialCorrection e₁ e₂ s u) 0 :=
    (he₁.mul analyticAt_const).add (he₂.mul analyticAt_const)
  exact hlog.add hP

/-- The paired numerator is genuinely jointly analytic around every spatial
point on the attracting side, before its removable x-division. -/
theorem analyticAt_modelNumerator_pair {U H : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (u : ℂ) (hu : u.re < 0) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => modelNumerator U H p.1 p.2) (0, u) := by
  have hUp : AnalyticAt ℂ (fun p : ℂ × ℂ => U p.1) (0, u) :=
    hU.comp_of_eq (f := fun p : ℂ × ℂ => p.1) analyticAt_fst rfl
  have hUn : AnalyticAt ℂ (fun p : ℂ × ℂ => U (-p.1)) (0, u) :=
    hU.comp_of_eq (f := fun p : ℂ × ℂ => -p.1) analyticAt_fst.neg (by simp)
  have hHp : AnalyticAt ℂ (fun p : ℂ × ℂ => H p.1) (0, u) :=
    hH.comp_of_eq (f := fun p : ℂ × ℂ => p.1) analyticAt_fst rfl
  have hHn : AnalyticAt ℂ (fun p : ℂ × ℂ => H (-p.1)) (0, u) :=
    hH.comp_of_eq (f := fun p : ℂ × ℂ => -p.1) analyticAt_fst.neg (by simp)
  have hslit : U 0 - u ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simpa [hU0] using neg_pos.mpr hu
  have hslitn : U (-(0 : ℂ)) - u ∈ Complex.slitPlane := by simpa only [neg_zero] using hslit
  exact (((hUp.sub analyticAt_snd).clog hslit).div hHp hHne).sub
    (((hUn.sub analyticAt_snd).clog hslitn).div hHn (by simpa only [neg_zero] using hHne))

set_option maxHeartbeats 1000000 in
/-- The actual model time is analytic along every analytic spatial parameter
curve with an attracting-side initial point. -/
theorem analyticAt_preparedModelTime_curve {U H e₁ e₂ v : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (he₁ : AnalyticAt ℂ e₁ 0) (he₂ : AnalyticAt ℂ e₂ 0)
    (hv : AnalyticAt ℂ v 0) (hvneg : (v 0).re < 0) :
    AnalyticAt ℂ (fun s => preparedModelTime U H e₁ e₂ s (v s)) 0 := by
  let B : ℂ × ℂ → ℂ := fun p => modelNumerator U H p.1 p.2
  let N : ℂ → ℂ := fun x => modelNumerator U H x (v (x ^ 2))
  have hBa : AnalyticAt ℂ B (0, v 0) := analyticAt_modelNumerator_pair hU hU0 hH hHne (v 0) hvneg
  have hvs : AnalyticAt ℂ (fun x : ℂ => v (x ^ 2)) 0 :=
    hv.comp_of_eq (f := fun x : ℂ => x ^ 2) (analyticAt_id.pow 2) (by simp)
  have hcp : AnalyticAt ℂ (fun x : ℂ => (x, v (x ^ 2))) 0 := analyticAt_id.prod hvs
  have hNa : AnalyticAt ℂ N 0 :=
    hBa.comp_of_eq (f := fun x : ℂ => (x, v (x ^ 2))) hcp (by simp)
  have hN0 : N 0 = 0 := by simp [N, modelNumerator_zero]
  have hNodd : ∀ x, N (-x) = -N x := by
    intro x
    dsimp [N]
    rw [neg_sq, modelNumerator_odd]
  have hDeven := dslope_odd_even hN0 hNodd
  have hDa := analyticAt_even_sqrt hDeven (analyticAt_dslope_zero hNa)
  have hvsd : HasDerivAt (fun x : ℂ => v (x ^ 2)) 0 0 := by
    have h := hv.hasStrictDerivAt.hasDerivAt.comp_of_eq 0 ((hasDerivAt_id (0 : ℂ)).pow 2) (by simp)
    convert h using 1 <;> first | rfl | simp
  have hcd : HasDerivAt (fun x : ℂ => (x, v (x ^ 2))) ((1 : ℂ), 0) 0 :=
    (hasDerivAt_id (0 : ℂ)).prodMk hvsd
  have hfd : HasDerivAt (fun x : ℂ => (x, v 0)) ((1 : ℂ), 0) 0 :=
    (hasDerivAt_id (0 : ℂ)).prodMk (hasDerivAt_const 0 (v 0))
  have hderivEq : deriv N 0 = deriv (fun x => modelNumerator U H x (v 0)) 0 := by
    have h₁ := hBa.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hcd (by simp)
    have h₂ := hBa.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hfd rfl
    exact h₁.deriv.trans h₂.deriv.symm
  have heq : (fun s => logarithmicModel U H s (v s)) =
      (fun s => dslope N 0 (Complex.sqrt s)) := by
    funext s
    by_cases hs : s = 0
    · simp only [hs, logarithmicModel, Complex.sqrt_zero, dslope_same]
      exact hderivEq.symm
    · have hr : Complex.sqrt s ≠ 0 := by
        intro hz
        have hsq := square_sqrt s
        rw [hz, zero_pow (by norm_num : 2 ≠ 0)] at hsq
        exact hs hsq.symm
      rw [logarithmicModel, dslope_of_ne _ hr, dslope_of_ne _ hr, slope_def_field, slope_def_field]
      simp only [N, square_sqrt, modelNumerator_zero, hN0]
  have hlog : AnalyticAt ℂ (fun s => logarithmicModel U H s (v s)) 0 := by
    rw [heq]
    exact hDa
  have hP : AnalyticAt ℂ (fun s => polynomialCorrection e₁ e₂ s (v s)) 0 :=
    (he₁.mul hv).add (he₂.mul (hv.pow 2))
  exact hlog.add hP

theorem preparedModelTime_residue_pair (U H e₁ e₂ : ℂ → ℂ)
    (hH : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (x u : ℂ) (hx : x ≠ 0) (hHx : H x ≠ 0) (hHnx : H (-x) ≠ 0) :
    preparedModelTime U H e₁ e₂ (x ^ 2) u =
      Complex.log (U x - u) / Complex.log (rootMultiplier U x) +
      Complex.log (U (-x) - u) / Complex.log (rootMultiplier U (-x)) +
      polynomialCorrection e₁ e₂ (x ^ 2) u := by
  have heven : ∀ z, dslope (fun z => modelNumerator U H z u) 0 (-z) =
      dslope (fun z => modelNumerator U H z u) 0 z :=
    dslope_odd_even (modelNumerator_zero U H u) (fun z => modelNumerator_odd U H z u)
  unfold preparedModelTime logarithmicModel
  rw [even_sqrt_square heven x, dslope_of_ne _ hx, slope_def_field, modelNumerator_zero]
  rw [hH x, hH (-x)]
  unfold modelNumerator
  field_simp [hx, hHx, hHnx]
  ring

set_option maxHeartbeats 1000000 in
/-- With a consistent logarithmic branch, the actual prepared defect is the
actual one-step difference of the constructed model time. -/
theorem preparedModelTime_one_step (U H e₁ e₂ : ℂ → ℂ)
    (hH : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (x u F : ℂ) (hx : x ≠ 0) (hHx : H x ≠ 0) (hHnx : H (-x) ≠ 0)
    (hf : unfolding (x ^ 2) u - u = rootProduct U x u * symmetricCofactor U x u)
    (hF : F =
      Complex.log (1 + (u - U (-x)) * symmetricCofactor U x u) /
        Complex.log (rootMultiplier U x) +
      Complex.log (1 + (u - U x) * symmetricCofactor U x u) /
        Complex.log (rootMultiplier U (-x)) - 1)
    (ha : 0 < (U x - u).re) (hb : 0 < (U (-x) - u).re)
    (hra : 0 < (1 + (u - U (-x)) * symmetricCofactor U x u).re)
    (hrb : 0 < (1 + (u - U x) * symmetricCofactor U x u).re) :
    preparedModelTime U H e₁ e₂ (x ^ 2) (unfolding (x ^ 2) u) -
      preparedModelTime U H e₁ e₂ (x ^ 2) u - 1 =
      F + polynomialCorrection e₁ e₂ (x ^ 2) (unfolding (x ^ 2) u) -
        polynomialCorrection e₁ e₂ (x ^ 2) u := by
  have hpa : U x - unfolding (x ^ 2) u =
      (U x - u) * (1 + (u - U (-x)) * symmetricCofactor U x u) := by
    dsimp [rootProduct] at hf
    linear_combination -hf
  have hpb : U (-x) - unfolding (x ^ 2) u =
      (U (-x) - u) * (1 + (u - U x) * symmetricCofactor U x u) := by
    dsimp [rootProduct] at hf
    linear_combination -hf
  have hla : Complex.log (U x - unfolding (x ^ 2) u) - Complex.log (U x - u) =
      Complex.log (1 + (u - U (-x)) * symmetricCofactor U x u) := by
    rw [hpa, log_mul_of_re_pos ha hra]
    ring
  have hlb : Complex.log (U (-x) - unfolding (x ^ 2) u) - Complex.log (U (-x) - u) =
      Complex.log (1 + (u - U x) * symmetricCofactor U x u) := by
    rw [hpb, log_mul_of_re_pos hb hrb]
    ring
  rw [preparedModelTime_residue_pair U H e₁ e₂ hH x _ hx hHx hHnx,
    preparedModelTime_residue_pair U H e₁ e₂ hH x _ hx hHx hHnx]
  linear_combination (1 / Complex.log (rootMultiplier U x)) * hla +
    (1 / Complex.log (rootMultiplier U (-x))) * hlb - hF

end Kneser.ExponentialModelTime

end
