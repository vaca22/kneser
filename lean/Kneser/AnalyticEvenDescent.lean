import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Tactic.NormNum

/-!
# Analytic descent through the square parameter

An even analytic germ `f(x)` is descended to `s=x²` by the actual function
`f (Complex.sqrt s)`.  Local inverse branches of the square map show
analyticity away from zero; continuity and removable singularities prove it
at zero.  This avoids assuming a convergent even-coefficient power series.
-/

noncomputable section

namespace Kneser.AnalyticEvenDescent

open Filter
open scoped Topology

@[simp] theorem square_sqrt (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  simp [Complex.sqrt]

/-- Sign invariance makes the principal square root agree with every local root. -/
theorem even_eq_of_square_eq {f : ℂ → ℂ} (heven : ∀ z, f (-z) = f z)
    {a b : ℂ} (hab : a ^ 2 = b ^ 2) : f a = f b := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hab with h | h
  · rw [h]
  · rw [h, heven]

/-- A descended even germ is analytic at each nonzero point where the original
germ is analytic at its square root, including points on the principal cut. -/
theorem analyticAt_even_sqrt_of_ne {f : ℂ → ℂ} (heven : ∀ z, f (-z) = f z)
    {s : ℂ} (hs : s ≠ 0) (hf : AnalyticAt ℂ f (Complex.sqrt s)) :
    AnalyticAt ℂ (fun t => f (Complex.sqrt t)) s := by
  let r : ℂ := Complex.sqrt s
  have hr2 : r ^ 2 = s := square_sqrt s
  have hrne : r ≠ 0 := by
    intro hr
    apply hs
    rw [← hr2, hr, zero_pow (by decide)]
  let P : ℂ → ℂ := fun z => z ^ 2
  have hPa : AnalyticAt ℂ P r := by fun_prop
  have hPder : HasDerivAt P (2 * r) r := by
    convert (hasDerivAt_id r).pow 2 using 1 <;> first | rfl | simp
  have hPne : deriv P r ≠ 0 := by
    rw [hPder.deriv]
    exact mul_ne_zero (by norm_num) hrne
  let R : ℂ → ℂ := hPa.hasStrictDerivAt.localInverse P (deriv P r) r hPne
  have hPr : P r = s := hr2
  have hRa : AnalyticAt ℂ R s := by
    simpa only [hPr] using hPa.analyticAt_localInverse hPne
  have hright : ∀ᶠ t in 𝓝 s, R t ^ 2 = t := by
    simpa only [hPr] using hPa.hasStrictDerivAt.eventually_right_inverse hPne
  have hleft : ∀ᶠ z in 𝓝 r, R (P z) = z :=
    hPa.hasStrictDerivAt.eventually_left_inverse hPne
  have hRs : R s = r := by simpa only [hPr] using hleft.self_of_nhds
  have hfa : AnalyticAt ℂ (fun t => f (R t)) s := hf.comp_of_eq hRa hRs
  apply hfa.congr
  filter_upwards [hright] with t ht
  exact even_eq_of_square_eq heven (ht.trans (square_sqrt t).symm)

/-- An even analytic germ descends analytically through `s=x²`.
The descending function is explicitly defined by the principal square root. -/
theorem analyticAt_even_sqrt {f : ℂ → ℂ} (heven : ∀ z, f (-z) = f z)
    (hf : AnalyticAt ℂ f 0) : AnalyticAt ℂ (fun s => f (Complex.sqrt s)) 0 := by
  have hsqrt : ContinuousAt Complex.sqrt 0 :=
    Complex.continuousAt_sqrt (Or.inl (by simp))
  have hcont : ContinuousAt (fun s => f (Complex.sqrt s)) 0 := by
    exact hf.continuousAt.comp_of_eq hsqrt Complex.sqrt_zero
  have hfa : ∀ᶠ s in 𝓝 0, AnalyticAt ℂ f (Complex.sqrt s) := by
    have hst : Tendsto Complex.sqrt (𝓝 0) (𝓝 0) := by
      simpa only [Complex.sqrt_zero] using hsqrt.tendsto
    exact hst.eventually hf.eventually_analyticAt
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ hcont
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hfa] with s hfs hs
  exact (analyticAt_even_sqrt_of_ne heven (by simpa using hs) hfs).differentiableAt

/-- Descent recovers the original germ on the square parameter exactly. -/
theorem even_sqrt_square {f : ℂ → ℂ} (heven : ∀ z, f (-z) = f z) (x : ℂ) :
    f (Complex.sqrt (x ^ 2)) = f x :=
  even_eq_of_square_eq heven (square_sqrt (x ^ 2))

/-- Existence of a descended analytic function is proved rather than assumed. -/
theorem exists_analytic_descent {f : ℂ → ℂ} (heven : ∀ z, f (-z) = f z)
    (hf : AnalyticAt ℂ f 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ ∀ x, g (x ^ 2) = f x := by
  exact ⟨fun s => f (Complex.sqrt s), analyticAt_even_sqrt heven hf,
    even_sqrt_square heven⟩

end Kneser.AnalyticEvenDescent

end
