import Kneser.ExponentialCuspParameter
import Kneser.AnalyticEvenDescent
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The actual analytic product of the two multiplier logarithms

The square parameter is resolved using the analytic Morse inverse already
constructed for the exponential unfolding. The product of the two logarithms
descends through `s=x²`; its derivative `2` is derived from the cusp's actual
quadratic coefficient, rather than assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.ExponentialMultiplierParameter

open Kneser.ExponentialCuspParameter Kneser.AnalyticEvenDescent
open Filter
open scoped Topology

/-- An analytic germ vanishing at zero has a constructed analytic linear
factor, whose constant value is the germ's actual derivative. -/
theorem exists_analytic_linear_factor (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hf0 : f 0 = 0) :
    ∃ L : ℂ → ℂ, AnalyticAt ℂ L 0 ∧ L 0 = deriv f 0 ∧ ∀ x, f x = x * L x := by
  obtain ⟨L, hLa, hL⟩ := hf.exists_eq_sum_add_pow_mul 1
  have heq : ∀ x, f x = x * L x := by
    intro x
    simpa [Finset.sum_range_succ, hf0, smul_eq_mul] using hL x
  have hder : HasDerivAt f (L 0) 0 := by
    have h := (hasDerivAt_id (0 : ℂ)).mul hLa.hasStrictDerivAt.hasDerivAt
    have hfun : f = fun x => x * L x := funext heq
    rw [hfun]
    convert h using 1 <;> first | rfl | simp
  exact ⟨L, hLa, hder.deriv.symm, heq⟩

/-- The actual square-root inverse has squared derivative `2`, as forced by
`cuspParameter(Vx)=x²` and the cusp's leading coefficient `1/2`. -/
theorem deriv_square_inverse_eq_two (V : ℂ → ℂ) (hVa : AnalyticAt ℂ V 0)
    (hV0 : V 0 = 0)
    (hSquare : ∀ᶠ x in nhds 0, cuspParameter (V x) = x ^ 2) :
    (deriv V 0) ^ 2 = 2 := by
  obtain ⟨H, hHa, hH0, hH⟩ := exists_analytic_quadratic_factor
  obtain ⟨W, hWa, hW0, hW⟩ := exists_analytic_linear_factor V hVa hV0
  have hlimH : Tendsto (fun x => H (V x)) (nhds 0) (nhds (H 0)) := by
    have hVlim : Tendsto V (nhds 0) (nhds 0) := by
      simpa only [hV0] using hVa.continuousAt.tendsto
    exact hHa.continuousAt.tendsto.comp hVlim
  have hlim : Tendsto (fun x => (W x) ^ 2 * H (V x)) (nhdsWithin 0 {0}ᶜ)
      (nhds ((W 0) ^ 2 * H 0)) :=
    ((hWa.continuousAt.tendsto.pow 2).mul hlimH).mono_left nhdsWithin_le_nhds
  have heq : ∀ᶠ x in nhdsWithin 0 {0}ᶜ, (W x) ^ 2 * H (V x) = 1 := by
    filter_upwards [hSquare.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxne
    have hx0 : x ≠ 0 := by simpa using hxne
    have hmul : x ^ 2 * ((W x) ^ 2 * H (V x)) = x ^ 2 * 1 := by
      calc
        _ = (V x) ^ 2 * H (V x) := by rw [hW]; ring
        _ = cuspParameter (V x) := (hH (V x)).symm
        _ = _ := by simpa using hx
    exact mul_left_cancel₀ (pow_ne_zero 2 hx0) hmul
  have hleading : (W 0) ^ 2 * H 0 = 1 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (heq.mono (fun x hx => hx.symm)))
  rw [hW0, hH0] at hleading
  linear_combination 2 * hleading

/-- The actual product of the multiplier logarithms is analytic in `s`,
vanishes at the cusp, and has complex derivative exactly `2`. -/
theorem exists_analytic_multiplier_parameter :
    ∃ V p : ℂ → ℂ, AnalyticAt ℂ V 0 ∧ V 0 = 0 ∧
      (∀ᶠ x in nhds 0, cuspParameter (V x) = x ^ 2) ∧
      AnalyticAt ℂ p 0 ∧ p 0 = 0 ∧ HasDerivAt p 2 0 ∧
      (∀ x, p (x ^ 2) = -Complex.log (1 + V x) * Complex.log (1 + V (-x))) := by
  obtain ⟨X, V, hXa, hVa, hX0, hV0, hXne, hXsquare, hright, hleft, hVsquare⟩ :=
    exists_analytic_morse_coordinate
  have hVderSquare := deriv_square_inverse_eq_two V hVa hV0 hVsquare
  let F : ℂ → ℂ := fun x => Complex.log (1 + V x)
  have hFa : AnalyticAt ℂ F 0 := by
    apply (analyticAt_const.add hVa).clog
    simpa only [Pi.add_apply, hV0, add_zero] using Complex.one_mem_slitPlane
  have hF0 : F 0 = 0 := by simp [F, hV0]
  have hFder : HasDerivAt F (deriv V 0) 0 := by
    have h := hVa.hasStrictDerivAt.hasDerivAt.const_add 1
    have hlog := h.clog (by simp [hV0])
    simpa [F, hV0] using hlog
  obtain ⟨L, hLa, hL0, hL⟩ := exists_analytic_linear_factor F hFa hF0
  have hLzero : L 0 = deriv V 0 := by rw [hL0, hFder.deriv]
  let Gx : ℂ → ℂ := fun x => L x * L (-x)
  have hLevenAnalytic : AnalyticAt ℂ (fun x => L (-x)) 0 := by
    have hLaneg : AnalyticAt ℂ L (-(0 : ℂ)) := by simpa only [neg_zero] using hLa
    exact hLaneg.comp analyticAt_id.neg
  have hGa : AnalyticAt ℂ Gx 0 := hLa.mul hLevenAnalytic
  have hGeven : ∀ x, Gx (-x) = Gx x := by
    intro x
    simp [Gx, mul_comm]
  obtain ⟨G, hGanalytic, hGdescend⟩ := exists_analytic_descent hGeven hGa
  have hG0 : G 0 = 2 := by
    have h := hGdescend (0 : ℂ)
    have heq : G 0 = (deriv V 0) ^ 2 := by
      simpa [Gx, hLzero, pow_two] using h
    exact heq.trans hVderSquare
  let p : ℂ → ℂ := fun s => s * G s
  have hpa : AnalyticAt ℂ p 0 := analyticAt_id.mul hGanalytic
  have hp0 : p 0 = 0 := by simp [p]
  have hpder : HasDerivAt p 2 0 := by
    convert (hasDerivAt_id (0 : ℂ)).mul hGanalytic.hasStrictDerivAt.hasDerivAt using 1
      <;> first | rfl | simp [hG0]
  refine ⟨V, p, hVa, hV0, hVsquare, hpa, hp0, hpder, ?_⟩
  intro x
  change x ^ 2 * G (x ^ 2) = -F x * F (-x)
  rw [hGdescend, hL x, hL (-x)]
  dsimp [Gx]
  ring

/-- The real part of the actual analytic parameter has right derivative `2`.
This restriction requires no assumed parameter-expansion coefficient. -/
theorem realPart_parameter_derivative (p : ℂ → ℂ) (hp : HasDerivAt p 2 0) :
    HasDerivWithinAt (fun s : ℝ => (p (s : ℂ)).re) 2 (Set.Ici 0) 0 := by
  have hp' : HasDerivAt p 2 ((0 : ℝ) : ℂ) := by simpa using hp
  simpa using hp'.real_of_complex.hasDerivWithinAt (s := Set.Ici 0)

/-- Analyticity of the constructed multiplier parameter gives its actual
second-order remainder after the proved linear coefficient `2`. -/
theorem exists_quadratic_multiplier_remainder (p : ℂ → ℂ)
    (hpa : AnalyticAt ℂ p 0) (hp0 : p 0 = 0) (hpder : HasDerivAt p 2 0) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ s, p s = 2 * s + s ^ 2 * R s := by
  obtain ⟨R, hRa, hR⟩ := hpa.exists_eq_sum_add_pow_mul 2
  refine ⟨R, hRa, ?_⟩
  intro s
  have hs := hR s
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    iteratedDeriv_zero, iteratedDeriv_one, hp0, hpder.deriv] at hs
  norm_num at hs
  simpa only [smul_eq_mul, mul_comm s (2 : ℂ)] using hs

end Kneser.ExponentialMultiplierParameter

end
