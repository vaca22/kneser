import Kneser.ExponentialMultiplierParameter
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# The actual second coefficient of the exponential multiplier parameter

The coefficient is extracted from the cusp equation and analytic Taylor
factors, rather than assumed as part of a root expansion.
-/

set_option autoImplicit false
set_option maxRecDepth 4000
noncomputable section

namespace Kneser.ExponentialMultiplierSecondOrder

open Kneser.ExponentialCuspParameter Kneser.ExponentialMultiplierParameter
open Filter Complex
open scoped Topology

theorem cancel_power_eventually (n : ℕ) (f g : ℂ → ℂ)
    (hf : ContinuousAt f 0) (hg : ContinuousAt g 0)
    (h : ∀ᶠ x in 𝓝 0, x ^ n * f x = x ^ n * g x) : f =ᶠ[𝓝 0] g := by
  have heq : f =ᶠ[𝓝[≠] 0] g := by
    filter_upwards [h.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxne
    exact mul_left_cancel₀ (pow_ne_zero n (by simpa using hxne)) hx
  have h0 : f 0 = g 0 := tendsto_nhds_unique
    (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' (heq.mono fun _ hx => hx.symm))
  filter_upwards [h] with x hx
  by_cases hx0 : x = 0
  · simpa only [hx0] using h0
  · exact mul_left_cancel₀ (pow_ne_zero n hx0) hx

theorem exists_affine_factor (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    ∃ K : ℂ → ℂ, AnalyticAt ℂ K 0 ∧ ∀ x, f x = f 0 + x * K x := by
  obtain ⟨K, hKa, _, hK⟩ := exists_analytic_linear_factor (fun x => f x - f 0)
    (hf.sub analyticAt_const) (by simp)
  refine ⟨K, hKa, ?_⟩
  intro x
  have h := hK x
  linear_combination h

theorem cusp_third_fourth_coefficients :
    iteratedDeriv 3 cuspParameter 0 = -2 ∧ iteratedDeriv 4 cuspParameter 0 = 3 := by
  have h2 : iteratedDeriv 2 cuspParameter = fun t => (1 - t) * Complex.exp (-t) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    funext t
    exact (hasDerivAt_deriv_cuspParameter t).deriv
  have h3 : iteratedDeriv 3 cuspParameter = fun t => (t - 2) * Complex.exp (-t) := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, h2]
    funext t
    have h := ((hasDerivAt_id t).const_sub 1).mul (hasDerivAt_id t).neg.cexp
    convert h.deriv using 1 <;> first | rfl | (dsimp; ring)
  have h4 : iteratedDeriv 4 cuspParameter = fun t => (3 - t) * Complex.exp (-t) := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, iteratedDeriv_succ, h3]
    funext t
    have h := ((hasDerivAt_id t).sub_const 2).mul (hasDerivAt_id t).neg.cexp
    convert h.deriv using 1 <;> first | rfl | (dsimp; ring)
  simp [h3, h4]

theorem exists_cusp_fourth_factor :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ H 0 = 1 / 8 ∧
      ∀ t, cuspParameter t = t ^ 2 * (1 / 2 - t / 3 + t ^ 2 * H t) := by
  obtain ⟨R, hRa, hR⟩ := (analyticAt_cuspParameter 0).exists_eq_sum_add_pow_mul 5
  obtain ⟨h3, h4⟩ := cusp_third_fourth_coefficients
  refine ⟨fun t => 1 / 8 + t * R t, by fun_prop, by simp, ?_⟩
  intro t
  have h := hR t
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    iteratedDeriv_zero, iteratedDeriv_one, cuspParameter_zero,
    deriv_cuspParameter_zero, second_deriv_cuspParameter_zero, h3, h4] at h
  norm_num [smul_eq_mul] at h
  exact h.trans (by ring)

theorem exists_log_cubic_factor :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
      ∀ t, Complex.log (1 + t) = t - t ^ 2 / 2 + t ^ 3 / 3 + t ^ 4 * R t := by
  let F : ℂ → ℂ := fun t => Complex.log (1 + t)
  have hFa : AnalyticAt ℂ F 0 := by
    exact (analyticAt_const.add analyticAt_id).clog (by simp)
  have hslit : ∀ᶠ t : ℂ in 𝓝 0, 1 + t ∈ Complex.slitPlane :=
    ((continuous_const.add continuous_id).tendsto' 0 1 (by simp)).eventually
      (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)
  have hd1 : deriv F =ᶠ[𝓝 0] (fun t : ℂ => (1 + t)⁻¹) := by
    filter_upwards [hslit] with t ht
    simpa only [F, id_eq, one_div] using (((hasDerivAt_id t).const_add 1).clog ht).deriv
  have hd2 : deriv (fun t : ℂ => (1 + t)⁻¹) =ᶠ[𝓝 0]
      (fun t : ℂ => -((1 + t)⁻¹) ^ 2) := by
    filter_upwards [hslit] with t ht
    have hn : 1 + t ≠ 0 := Complex.slitPlane_ne_zero ht
    have h := ((hasDerivAt_id t).const_add 1).inv hn
    convert h.deriv using 1 <;> first | rfl | (dsimp; field_simp)
  have hF1 : deriv F 0 = 1 := by simpa using hd1.self_of_nhds
  have hF2 : iteratedDeriv 2 F 0 = -1 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [hd1.deriv_eq, hd2.self_of_nhds]
    norm_num
  have hF3 : iteratedDeriv 3 F 0 = 2 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ,
      show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [(hd1.deriv.trans hd2).deriv_eq]
    have h := (((hasDerivAt_id (0 : ℂ)).const_add 1).inv (by norm_num)).pow 2 |>.neg
    convert h.deriv using 1 <;> first | rfl | norm_num
  obtain ⟨R, hRa, hR⟩ := hFa.exists_eq_sum_add_pow_mul 4
  refine ⟨R, hRa, ?_⟩
  intro t
  have h := hR t
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    iteratedDeriv_zero, iteratedDeriv_one, hF1, hF2, hF3] at h
  norm_num [F, smul_eq_mul] at h
  exact h.trans (by ring)

/-- Actual inverse coefficients: `α²=2`, the quadratic coefficient is `2/3`,
and `αγ=11/18`, forced by the cusp equation. -/
theorem exists_inverse_cubic_coefficients (V : ℂ → ℂ) (hVa : AnalyticAt ℂ V 0)
    (hV0 : V 0 = 0) (hSquare : ∀ᶠ x in 𝓝 0, cuspParameter (V x) = x ^ 2) :
    ∃ α γ : ℂ, ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
      α = deriv V 0 ∧ α ^ 2 = 2 ∧ α * γ = 11 / 18 ∧
      ∀ x, V x = α * x + (2 / 3) * x ^ 2 + γ * x ^ 3 + x ^ 4 * R x := by
  obtain ⟨H, hHa, hH0, hH⟩ := exists_cusp_fourth_factor
  obtain ⟨W, hWa, hW0, hW⟩ := exists_analytic_linear_factor V hVa hV0
  let α := W 0
  have hα : α ^ 2 = 2 := by
    dsimp [α]
    rw [hW0]
    exact deriv_square_inverse_eq_two V hVa hV0 hSquare
  have hαne : α ≠ 0 := by intro h; rw [h] at hα; norm_num at hα
  obtain ⟨K, hKa, hK⟩ := exists_affine_factor W hWa
  let β := K 0
  obtain ⟨J, hJa, hJ⟩ := exists_affine_factor K hKa
  let γ := J 0
  have hHV : AnalyticAt ℂ (fun x => H (V x)) 0 := hHa.comp_of_eq hVa hV0
  let Φ : ℂ → ℂ := fun x => α * K x + x * (K x) ^ 2 / 2 - (W x) ^ 3 / 3 +
    x * (W x) ^ 4 * H (V x)
  have hΦa : AnalyticAt ℂ Φ 0 := by
    exact (((analyticAt_const.mul hKa).add
      (analyticAt_id.mul (hKa.pow 2)).div_const).sub (hWa.pow 3).div_const).add
      ((analyticAt_id.mul (hWa.pow 4)).mul hHV)
  have hΦ : ∀ᶠ x in 𝓝 0, x ^ 3 * Φ x = x ^ 3 * (0 : ℂ) := by
    filter_upwards [hSquare] with x hx
    have hc := hH (V x)
    have hw := hW x
    have hk := hK x
    change W x = α + x * K x at hk
    have heq : cuspParameter (V x) - x ^ 2 = x ^ 3 * Φ x := by
      rw [hc]
      dsimp [Φ]
      rw [hw, hk]
      linear_combination x ^ 2 / 2 * hα
    rw [← heq, hx]
    ring
  have hΦzero := cancel_power_eventually 3 Φ (fun _ => 0) hΦa.continuousAt continuousAt_const hΦ
  have hβ : β = 2 / 3 := by
    have h := hΦzero.self_of_nhds
    have hα3 : α ^ 3 = 2 * α := by
      calc
        _ = α ^ 2 * α := by ring
        _ = _ := by rw [hα]
    have h' : α * β - α ^ 3 / 3 = 0 := by simpa [Φ, α, β] using h
    rw [hα3] at h'
    apply mul_left_cancel₀ hαne
    linear_combination h'
  let Ψ : ℂ → ℂ := fun x => α * J x + (K x) ^ 2 / 2 - α ^ 2 * K x -
    α * x * (K x) ^ 2 - x ^ 2 * (K x) ^ 3 / 3 + (W x) ^ 4 * H (V x)
  have hΨa : AnalyticAt ℂ Ψ 0 := by
    exact (((((analyticAt_const.mul hJa).add (hKa.pow 2).div_const).sub
      (analyticAt_const.mul hKa)).sub
      ((analyticAt_const.mul analyticAt_id).mul (hKa.pow 2))).sub
      ((analyticAt_id.pow 2).mul (hKa.pow 3)).div_const).add ((hWa.pow 4).mul hHV)
  have hΨ : ∀ᶠ x in 𝓝 0, x * Ψ x = x * (0 : ℂ) := by
    filter_upwards [hΦzero] with x hx
    have heq : Φ x = α * β - α ^ 3 / 3 + x * Ψ x := by
      dsimp [Φ, Ψ]
      rw [hK x, hJ x]
      ring
    have hbase : α * β - α ^ 3 / 3 = 0 := by rw [hβ]; linear_combination -α / 3 * hα
    rw [heq, hbase, zero_add] at hx
    simpa using hx
  have hΨzero := cancel_power_eventually 1 Ψ (fun _ => 0) hΨa.continuousAt continuousAt_const
    (by simpa only [pow_one] using hΨ)
  have hγ : α * γ = 11 / 18 := by
    have h := hΨzero.self_of_nhds
    have h' : α * γ + β ^ 2 / 2 - α ^ 2 * β + α ^ 4 * H (V 0) = 0 := by
      simpa [Ψ, α, β, γ] using h
    rw [hV0, hH0, hβ, show α ^ 4 = (α ^ 2) ^ 2 by ring, hα] at h'
    linear_combination h'
  obtain ⟨R, hRa, hR⟩ := exists_affine_factor J hJa
  refine ⟨α, γ, R, hRa, hW0, hα, hγ, ?_⟩
  intro x
  rw [hW x, hK x, hJ x, hR x]
  change x * (α + x * (β + x * (γ + x * R x))) = _
  rw [hβ]
  ring

/-- The logarithm of the actual multiplier branch has coefficients
`α`, `-1/3`, and `γ`, with an analytic fourth-order remainder. -/
theorem exists_branch_log_cubic_coefficients (V : ℂ → ℂ) (hVa : AnalyticAt ℂ V 0)
    (hV0 : V 0 = 0) (hSquare : ∀ᶠ x in 𝓝 0, cuspParameter (V x) = x ^ 2) :
    ∃ α γ : ℂ, ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
      α ^ 2 = 2 ∧ α * γ = 11 / 18 ∧
      ∀ x, Complex.log (1 + V x) = α * x - x ^ 2 / 3 + γ * x ^ 3 + x ^ 4 * R x := by
  obtain ⟨α, γ, RV, hRVa, hαder, hα, hαγ, hV⟩ :=
    exists_inverse_cubic_coefficients V hVa hV0 hSquare
  obtain ⟨Rlog, hRloga, hRlog⟩ := exists_log_cubic_factor
  have hRlogV : AnalyticAt ℂ (fun x => Rlog (V x)) 0 := hRloga.comp_of_eq hVa hV0
  let F : ℂ → ℂ := fun x => Complex.log (1 + V x)
  have hFa : AnalyticAt ℂ F 0 := (analyticAt_const.add hVa).clog (by simp [hV0])
  have hF0 : F 0 = 0 := by simp [F, hV0]
  have hFder : HasDerivAt F α 0 := by
    have h := (hVa.hasStrictDerivAt.hasDerivAt.const_add 1).clog (by simp [hV0])
    simpa only [F, hV0, add_zero, div_one, ← hαder] using h
  obtain ⟨L, hLa, hL0, hL⟩ := exists_analytic_linear_factor F hFa hF0
  have hLα : L 0 = α := hL0.trans hFder.deriv
  obtain ⟨B, hBa, hB⟩ := exists_affine_factor L hLa
  let b := B 0
  obtain ⟨C, hCa, hC⟩ := exists_affine_factor B hBa
  let W : ℂ → ℂ := fun x => α + (2 / 3) * x + γ * x ^ 2 + x ^ 3 * RV x
  let K : ℂ → ℂ := fun x => 2 / 3 + γ * x + x ^ 2 * RV x
  let J : ℂ → ℂ := fun x => γ + x * RV x
  have hWa : AnalyticAt ℂ W 0 := by dsimp [W]; fun_prop
  have hKa : AnalyticAt ℂ K 0 := by dsimp [K]; fun_prop
  have hJa : AnalyticAt ℂ J 0 := by dsimp [J]; fun_prop
  have hVW : ∀ x, V x = x * W x := by intro x; rw [hV]; dsimp [W]; ring
  have hWK : ∀ x, W x = α + x * K x := by intro x; dsimp [W, K]; ring
  have hKJ : ∀ x, K x = 2 / 3 + x * J x := by intro x; dsimp [K, J]; ring
  let LB : ℂ → ℂ := fun x => K x - (W x) ^ 2 / 2 + x * (W x) ^ 3 / 3 +
    x ^ 2 * (W x) ^ 4 * Rlog (V x)
  have hLBa : AnalyticAt ℂ LB 0 :=
    (((hKa.sub (hWa.pow 2).div_const).add
      (analyticAt_id.mul (hWa.pow 3)).div_const).add
      (((analyticAt_id.pow 2).mul (hWa.pow 4)).mul hRlogV))
  have hBeq : B =ᶠ[𝓝 0] LB := by
    apply cancel_power_eventually 2 B LB hBa.continuousAt hLBa.continuousAt
    exact Eventually.of_forall (fun x => by
      have ht := hRlog (V x)
      have hl := hL x
      dsimp [F] at hl
      rw [hl, hVW x, hB x, hLα] at ht
      dsimp [LB]
      rw [hVW x]
      rw [hWK x] at ht ⊢
      linear_combination ht)
  have hb : b = -1 / 3 := by
    have h := hBeq.self_of_nhds
    have h' : b = 2 / 3 - α ^ 2 / 2 := by simpa [LB, W, K, b] using h
    rw [hα] at h'
    linear_combination h'
  let LC : ℂ → ℂ := fun x => J x - K x * (W x + α) / 2 + (W x) ^ 3 / 3 +
    x * (W x) ^ 4 * Rlog (V x)
  have hLCa : AnalyticAt ℂ LC 0 :=
    (((hJa.sub (hKa.mul (hWa.add analyticAt_const)).div_const).add
      (hWa.pow 3).div_const).add ((analyticAt_id.mul (hWa.pow 4)).mul hRlogV))
  have hCeq : C =ᶠ[𝓝 0] LC := by
    apply cancel_power_eventually 1 C LC hCa.continuousAt hLCa.continuousAt
    filter_upwards [hBeq] with x hx
    have ht := hC x
    change B x = b + x * C x at ht
    have heq : LB x - b = x * LC x := by
      dsimp [LB, LC]
      rw [hWK x, hKJ x, hb]
      linear_combination -1 / 2 * hα
    rw [ht] at hx
    simp only [pow_one]
    rw [← heq]
    linear_combination hx
  have hCγ : C 0 = γ := by
    have h := hCeq.self_of_nhds
    have h' : C 0 = γ - (2 / 3) * (α + α) / 2 + α ^ 3 / 3 := by
      simpa [LC, J, W, K] using h
    have hα3 : α ^ 3 = 2 * α := by
      calc
        _ = α ^ 2 * α := by ring
        _ = _ := by rw [hα]
    rw [hα3] at h'
    linear_combination h'
  obtain ⟨R, hRa, hR⟩ := exists_affine_factor C hCa
  refine ⟨α, γ, R, hRa, hα, hαγ, ?_⟩
  intro x
  have hl := hL x
  dsimp [F] at hl
  rw [hl, hB x, hLα, hC x, hR x, hCγ]
  change x * (α + x * (b + x * (γ + x * R x))) = _
  rw [hb]
  ring

/-- The actual multiplier parameter has second Taylor coefficient `10/9`
and a constructed analytic cubic remainder. -/
theorem multiplier_second_order (V p : ℂ → ℂ)
    (hVa : AnalyticAt ℂ V 0) (hV0 : V 0 = 0)
    (hSquare : ∀ᶠ x in 𝓝 0, cuspParameter (V x) = x ^ 2)
    (hpa : AnalyticAt ℂ p 0) (hp0 : p 0 = 0) (hpder : HasDerivAt p 2 0)
    (hproduct : ∀ x, p (x ^ 2) = -Complex.log (1 + V x) * Complex.log (1 + V (-x))) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
      ∀ s, p s = 2 * s + (10 / 9) * s ^ 2 + s ^ 3 * R s := by
  obtain ⟨α, γ, RF, hRFa, hα, hαγ, hF⟩ :=
    exists_branch_log_cubic_coefficients V hVa hV0 hSquare
  obtain ⟨R, hRa, hR⟩ := hpa.exists_eq_sum_add_pow_mul 3
  let d : ℂ := iteratedDeriv 2 p 0 / 2
  have hpTaylor : ∀ s, p s = 2 * s + d * s ^ 2 + s ^ 3 * R s := by
    intro s
    have h := hR s
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      iteratedDeriv_zero, iteratedDeriv_one, hp0, hpder.deriv] at h
    norm_num [smul_eq_mul] at h
    dsimp [d]
    exact h.trans (by ring)
  let Q : ℂ → ℂ := fun x => γ ^ 2 * x + α * (RF x - RF (-x)) +
    (x / 3) * (RF x + RF (-x)) + γ * x ^ 2 * (RF x - RF (-x)) - x ^ 3 * RF x * RF (-x)
  have hRFneg : AnalyticAt ℂ (fun x => RF (-x)) 0 := by
    have hRF0 : AnalyticAt ℂ RF (-(0 : ℂ)) := by simpa only [neg_zero] using hRFa
    exact hRF0.comp analyticAt_id.neg
  have hQa : AnalyticAt ℂ Q 0 := by
    exact ((((analyticAt_const.mul analyticAt_id).add
      (analyticAt_const.mul (hRFa.sub hRFneg))).add
      (analyticAt_id.div_const.mul (hRFa.add hRFneg))).add
      ((analyticAt_const.mul (analyticAt_id.pow 2)).mul (hRFa.sub hRFneg))).sub
      (((analyticAt_id.pow 3).mul hRFa).mul hRFneg)
  have hRp : AnalyticAt ℂ (fun x => R (x ^ 2)) 0 :=
    hRa.comp_of_eq (analyticAt_id.pow 2) (by simp)
  let A : ℂ → ℂ := fun x => d + x ^ 2 * R (x ^ 2)
  let B : ℂ → ℂ := fun x => 10 / 9 + x * Q x
  have hAa : AnalyticAt ℂ A 0 := analyticAt_const.add ((analyticAt_id.pow 2).mul hRp)
  have hBa : AnalyticAt ℂ B 0 := analyticAt_const.add (analyticAt_id.mul hQa)
  have hAB : A =ᶠ[𝓝 0] B := by
    apply cancel_power_eventually 4 A B hAa.continuousAt hBa.continuousAt
    exact Eventually.of_forall (fun x => by
      have ht := hproduct x
      rw [hpTaylor, hF x, hF (-x)] at ht
      have hcoef : 2 * α * γ - (1 / 3 : ℂ) ^ 2 = 10 / 9 := by
        linear_combination 2 * hαγ
      dsimp [A, B, Q]
      linear_combination ht + x ^ 2 * hα + x ^ 4 * hcoef)
  have hd : d = 10 / 9 := by simpa [A, B] using hAB.self_of_nhds
  exact ⟨R, hRa, by simpa only [hd] using hpTaylor⟩

/-- Existence of the actual parameter with its proved quadratic coefficient. -/
theorem exists_actual_multiplier_second_order :
    ∃ V p R : ℂ → ℂ, AnalyticAt ℂ V 0 ∧ V 0 = 0 ∧
      (∀ᶠ x in 𝓝 0, cuspParameter (V x) = x ^ 2) ∧
      AnalyticAt ℂ p 0 ∧ p 0 = 0 ∧ HasDerivAt p 2 0 ∧
      (∀ x, p (x ^ 2) = -Complex.log (1 + V x) * Complex.log (1 + V (-x))) ∧
      AnalyticAt ℂ R 0 ∧ ∀ s, p s = 2 * s + (10 / 9) * s ^ 2 + s ^ 3 * R s := by
  obtain ⟨V, p, hVa, hV0, hSquare, hpa, hp0, hpder, hproduct⟩ :=
    exists_analytic_multiplier_parameter
  obtain ⟨R, hRa, hR⟩ := multiplier_second_order V p hVa hV0 hSquare hpa hp0 hpder hproduct
  exact ⟨V, p, R, hVa, hV0, hSquare, hpa, hp0, hpder, hproduct, hRa, hR⟩

/-- The constructed analytic cubic factor supplies an actual uniform norm
bound for the third-order remainder on a complex neighborhood. -/
theorem second_order_remainder_bound (p R : ℂ → ℂ) (hRa : AnalyticAt ℂ R 0)
    (hR : ∀ s, p s = 2 * s + (10 / 9) * s ^ 2 + s ^ 3 * R s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℂ in 𝓝 0,
      ‖p s - 2 * s - (10 / 9) * s ^ 2‖ ≤ C * ‖s‖ ^ 3 := by
  refine ⟨‖R 0‖ + 1, by positivity, ?_⟩
  have hbound : ∀ᶠ s : ℂ in 𝓝 0, ‖R s‖ ≤ ‖R 0‖ + 1 :=
    (hRa.continuousAt.norm.eventually (gt_mem_nhds (by linarith : ‖R 0‖ < ‖R 0‖ + 1))).mono
      (fun _ h => h.le)
  filter_upwards [hbound] with s hs
  have heq : p s - 2 * s - (10 / 9) * s ^ 2 = s ^ 3 * R s := by rw [hR]; ring
  rw [heq, norm_mul, norm_pow]
  exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring)

/-- The actual multiplier parameter satisfies `2s+(10/9)s²+O(‖s‖³)`.
The parameter derivative and quadratic coefficient are both conclusions. -/
theorem exists_actual_multiplier_second_order_bound :
    ∃ V p : ℂ → ℂ, ∃ C : ℝ, AnalyticAt ℂ V 0 ∧ V 0 = 0 ∧
      (∀ᶠ x in 𝓝 0, cuspParameter (V x) = x ^ 2) ∧
      AnalyticAt ℂ p 0 ∧ p 0 = 0 ∧ HasDerivAt p 2 0 ∧
      (∀ x, p (x ^ 2) = -Complex.log (1 + V x) * Complex.log (1 + V (-x))) ∧
      0 ≤ C ∧ ∀ᶠ s : ℂ in 𝓝 0, ‖p s - 2 * s - (10 / 9) * s ^ 2‖ ≤ C * ‖s‖ ^ 3 := by
  obtain ⟨V, p, R, hVa, hV0, hSquare, hpa, hp0, hpder, hproduct, hRa, hR⟩ :=
    exists_actual_multiplier_second_order
  obtain ⟨C, hC, hbound⟩ := second_order_remainder_bound p R hRa hR
  exact ⟨V, p, C, hVa, hV0, hSquare, hpa, hp0, hpder, hproduct, hC, hbound⟩

end Kneser.ExponentialMultiplierSecondOrder

end
