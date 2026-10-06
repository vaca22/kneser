import Kneser.ExponentialLogDefect
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-!
# The actual chain rule through an even square-parameter descent

Joint analyticity in the split parameter x, and evenness in x, suffice for
the first-order coefficient in s=x². Joint analyticity of the descended
function is not a hypothesis.
-/

noncomputable section

namespace Kneser.EvenDescentChainRule

open Kneser.AnalyticEvenDescent Kneser.PreparedTwoRootDivision
open Kneser.ExponentialLogDefect Filter
open scoped Topology

def squareParameter (x : ℂ) : ℂ := x ^ 2

theorem deriv_squareParameter (x : ℂ) : deriv squareParameter x = 2 * x := by
  have h := (hasDerivAt_id x).pow 2
  convert h.deriv using 1 <;> first | rfl | simp

theorem second_squareParameter_zero : iteratedDeriv 2 squareParameter 0 = 2 := by
  have hfun : deriv squareParameter = fun x => 2 * x := funext deriv_squareParameter
  rw [show 2 = 1 + 1 by decide, iteratedDeriv_succ', iteratedDeriv_one, hfun]
  convert ((hasDerivAt_id (0 : ℂ)).const_mul 2).deriv using 1 <;> first | rfl | simp

/-- The derivative of a genuine even descent is exactly half the second
derivative in the split parameter. -/
theorem deriv_even_descent {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (heven : ∀ x, f (-x) = f x) :
    deriv (fun s => f (Complex.sqrt s)) 0 = iteratedDeriv 2 f 0 / 2 := by
  let g : ℂ → ℂ := fun s => f (Complex.sqrt s)
  have hga : AnalyticAt ℂ g 0 := analyticAt_even_sqrt heven hf
  have hP : AnalyticAt ℂ squareParameter 0 := by
    change AnalyticAt ℂ (fun x : ℂ => x ^ 2) 0
    exact analyticAt_id.pow 2
  have heq : g ∘ squareParameter = f := by
    funext x
    exact even_sqrt_square heven x
  have hgP : ContDiffAt ℂ 2 g (squareParameter 0) := by
    simpa only [squareParameter, zero_pow (by norm_num : 2 ≠ 0)] using hga.contDiffAt
  have h := iteratedDeriv_comp_two (g := g) (f := squareParameter) (x := (0 : ℂ)) hgP hP.contDiffAt
  change iteratedDeriv 2 (g ∘ squareParameter) 0 = _ at h
  rw [heq, deriv_squareParameter, second_squareParameter_zero] at h
  simp only [squareParameter, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, zero_add] at h
  change deriv g 0 = _
  linear_combination -h / 2

theorem second_pair {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    iteratedDeriv 2 (fun x => (f x, g x)) 0 =
      (iteratedDeriv 2 f 0, iteratedDeriv 2 g 0) := by
  have hlocal : deriv (fun x => (f x, g x)) =ᶠ[𝓝 0]
      (fun x => (deriv f x, deriv g x)) := by
    filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with x hfx hgx
    exact (hfx.hasStrictDerivAt.hasDerivAt.prodMk hgx.hasStrictDerivAt.hasDerivAt).deriv
  have hd := hf.deriv.hasStrictDerivAt.hasDerivAt.prodMk hg.deriv.hasStrictDerivAt.hasDerivAt
  have h := hlocal.deriv_eq
  simp only [iteratedDeriv_succ', iteratedDeriv_one, iteratedDeriv_zero]
  exact h.trans hd.deriv

/-- The descended coefficient along a moving analytic spatial curve has
the usual parameter-plus-spatial chain rule, with both terms genuine. -/
theorem deriv_even_descent_curve {Q : ℂ × ℂ → ℂ} {w : ℂ → ℂ}
    (hQ : AnalyticAt ℂ Q (0, w 0))
    (heven : ∀ p, Q (reflectFirst p) = Q p)
    (hw : AnalyticAt ℂ w 0) :
    deriv (fun s => Q (Complex.sqrt s, w s)) 0 =
      deriv (fun s => Q (Complex.sqrt s, w 0)) 0 +
        deriv (fun u => Q (0, u)) (w 0) * deriv w 0 := by
  let c : ℂ → ℂ × ℂ := fun x => (x, w (x ^ 2))
  let d : ℂ → ℂ × ℂ := fun x => (x, w 0)
  let f : ℂ → ℂ := fun x => Q (c x)
  let g : ℂ → ℂ := fun x => Q (d x)
  have hwp : AnalyticAt ℂ (fun x => w (x ^ 2)) 0 :=
    hw.comp_of_eq (f := squareParameter) (by
      change AnalyticAt ℂ (fun x : ℂ => x ^ 2) 0
      exact analyticAt_id.pow 2) (by simp [squareParameter])
  have hca : AnalyticAt ℂ c 0 := analyticAt_id.prod hwp
  have hda : AnalyticAt ℂ d 0 := analyticAt_id.prod analyticAt_const
  have hc0 : c 0 = (0, w 0) := by simp [c]
  have hd0 : d 0 = (0, w 0) := rfl
  have hfa : AnalyticAt ℂ f 0 := hQ.comp_of_eq hca hc0
  have hga : AnalyticAt ℂ g 0 := hQ.comp_of_eq hda hd0
  have hfeven : ∀ x, f (-x) = f x := by
    intro x
    dsimp [f, c]
    rw [neg_sq]
    exact heven (x, w (x ^ 2))
  have hgeven : ∀ x, g (-x) = g x := by intro x; exact heven (x, w 0)
  have hwps : iteratedDeriv 2 (fun x => w (x ^ 2)) 0 = 2 * deriv w 0 := by
    have hP : AnalyticAt ℂ squareParameter 0 := by
      change AnalyticAt ℂ (fun x : ℂ => x ^ 2) 0
      exact analyticAt_id.pow 2
    have hwP : ContDiffAt ℂ 2 w (squareParameter 0) := by
      simpa only [squareParameter, zero_pow (by norm_num : 2 ≠ 0)] using hw.contDiffAt
    have h := iteratedDeriv_comp_two (g := w) (f := squareParameter) (x := (0 : ℂ)) hwP hP.contDiffAt
    change iteratedDeriv 2 (w ∘ squareParameter) 0 = _ at h
    rw [deriv_squareParameter, second_squareParameter_zero] at h
    simp only [squareParameter, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, zero_add] at h
    convert h using 1 <;> first | rfl | ring
  have hwpd : HasDerivAt (fun x => w (x ^ 2)) 0 0 := by
    have h := hw.hasStrictDerivAt.hasDerivAt.comp_of_eq 0 ((hasDerivAt_id (0 : ℂ)).pow 2) (by simp)
    convert h using 1 <;> first | rfl | simp
  have hcd : deriv c 0 = ((1 : ℂ), 0) :=
    ((hasDerivAt_id (0 : ℂ)).prodMk hwpd).deriv
  have hdd : deriv d 0 = ((1 : ℂ), 0) :=
    ((hasDerivAt_id (0 : ℂ)).prodMk (hasDerivAt_const 0 (w 0))).deriv
  have hcs : iteratedDeriv 2 c 0 = ((0 : ℂ), 2 * deriv w 0) := by
    have h := second_pair (f := id) (g := fun x => w (x ^ 2)) analyticAt_id hwp
    rw [hwps] at h
    simpa [c, iteratedDeriv_succ', iteratedDeriv_zero, deriv_id', deriv_const'] using h
  have hds : iteratedDeriv 2 d 0 = ((0 : ℂ), 0) := by
    have h := second_pair (f := id) (g := fun _ => w 0) analyticAt_id analyticAt_const
    simpa [d, iteratedDeriv_succ', iteratedDeriv_zero, deriv_id', deriv_const'] using h
  have hQc : ContDiffAt ℂ 2 Q (c 0) := by rw [hc0]; exact hQ.contDiffAt
  have hQd : ContDiffAt ℂ 2 Q (d 0) := by rw [hd0]; exact hQ.contDiffAt
  have h₂f := iteratedDeriv_vcomp_two (g := Q) (f := c) (x := (0 : ℂ)) hQc hca.contDiffAt
  have h₂g := iteratedDeriv_vcomp_two (g := Q) (f := d) (x := (0 : ℂ)) hQd hda.contDiffAt
  change iteratedDeriv 2 (Q ∘ c) 0 = _ at h₂f
  change iteratedDeriv 2 (Q ∘ d) 0 = _ at h₂g
  rw [hc0, hcd, hcs] at h₂f
  have hmap0 : (fderiv ℂ Q (0, w 0)) ((0 : ℂ), 0) = 0 := by
    change (fderiv ℂ Q (0, w 0)) (0 : ℂ × ℂ) = 0
    exact map_zero _
  rw [hd0, hdd, hds, hmap0, add_zero] at h₂g
  have hsp : deriv (fun u => Q (0, u)) (w 0) = (fderiv ℂ Q (0, w 0)) (0, 1) := by
    have hc : HasDerivAt (fun u : ℂ => ((0 : ℂ), u)) ((0 : ℂ), 1) (w 0) :=
      (hasDerivAt_const (w 0) 0).prodMk (hasDerivAt_id (w 0))
    exact (hQ.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq (w 0) hc rfl).deriv
  have hlin : (fderiv ℂ Q (0, w 0)) (0, 2 * deriv w 0) =
      2 * deriv (fun u => Q (0, u)) (w 0) * deriv w 0 := by
    rw [show ((0 : ℂ), 2 * deriv w 0) = (2 * deriv w 0) • ((0 : ℂ), 1) by simp,
      map_smul, ← hsp]
    simp only [smul_eq_mul]
    ring
  have hfdes := deriv_even_descent hfa hfeven
  have hgdes := deriv_even_descent hga hgeven
  have hfEq : (fun s => f (Complex.sqrt s)) = (fun s => Q (Complex.sqrt s, w s)) := by
    funext s; simp only [f, c, square_sqrt]
  have hgEq : (fun s => g (Complex.sqrt s)) = (fun s => Q (Complex.sqrt s, w 0)) := rfl
  rw [hfEq] at hfdes
  rw [hgEq] at hgdes
  rw [hfdes, hgdes]
  change iteratedDeriv 2 (Q ∘ c) 0 / 2 = iteratedDeriv 2 (Q ∘ d) 0 / 2 + _
  rw [h₂f, h₂g, hlin]
  ring

/-- The parameter coefficient is the explicit second x-derivative divided
by two; the spatial coefficient is evaluated on the actual parabolic slice. -/
theorem deriv_even_descent_curve_explicit {Q : ℂ × ℂ → ℂ} {w : ℂ → ℂ}
    (hQ : AnalyticAt ℂ Q (0, w 0))
    (heven : ∀ p, Q (reflectFirst p) = Q p)
    (hw : AnalyticAt ℂ w 0) :
    deriv (fun s => Q (Complex.sqrt s, w s)) 0 =
      iteratedDeriv 2 (fun x => Q (x, w 0)) 0 / 2 +
        deriv (fun u => Q (0, u)) (w 0) * deriv w 0 := by
  have hfixed : AnalyticAt ℂ (fun x => Q (x, w 0)) 0 :=
    hQ.comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
  rw [deriv_even_descent_curve hQ heven hw]
  rw [deriv_even_descent hfixed (fun x => heven (x, w 0))]

theorem hasDerivAt_even_descent_curve {Q : ℂ × ℂ → ℂ} {w : ℂ → ℂ}
    (hQ : AnalyticAt ℂ Q (0, w 0))
    (heven : ∀ p, Q (reflectFirst p) = Q p)
    (hw : AnalyticAt ℂ w 0) :
    HasDerivAt (fun s => Q (Complex.sqrt s, w s))
      (iteratedDeriv 2 (fun x => Q (x, w 0)) 0 / 2 +
        deriv (fun u => Q (0, u)) (w 0) * deriv w 0) 0 := by
  have hA := analyticAt_even_pair_descent_curve hQ heven hw
  have h := hA.hasStrictDerivAt.hasDerivAt
  rw [deriv_even_descent_curve_explicit hQ heven hw] at h
  exact h

end Kneser.EvenDescentChainRule

end
