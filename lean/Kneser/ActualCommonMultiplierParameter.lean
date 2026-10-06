import Kneser.ActualResidueValue

/-! The analytic multiplier parameter is constructed from the SAME actual
preparation root germ.  Its derivative and its identification with the two
true ordered real multipliers are proved. -/

noncomputable section
namespace Kneser.ActualCommonMultiplierParameter

open Filter Kneser.ReflectedOrbitChainCoefficient Kneser.ExponentialPreparedModel
open Kneser.ActualResidueValue Kneser.ExponentialMultiplierParameter
open Kneser.AnalyticEvenDescent Kneser.PositiveKoenigsOrbit
open Kneser.ActualKoenigsIdentification
open scoped Topology

theorem actual_log_factor_square (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) : H 0 ^ 2 = 2 := by
  rcases hdata with ⟨hU, hU0, _hUd, hH, _hHne, hHlog, _hA, _hB, _hA0, _hB0,
    _he₁, _he₂, _hF, _hΓ, _hEven, _hK0, _hK, _hq, hroots, _hfactor, _hp, _hr⟩
  let V : ℂ → ℂ := fun x => rootMultiplier U x - 1
  have hVa : AnalyticAt ℂ V 0 := (analyticAt_rootMultiplier hU).sub analyticAt_const
  have hV0 : V 0 = 0 := by simp [V, rootMultiplier, hU0]
  have hVsquare : ∀ᶠ x in 𝓝 (0 : ℂ), Kneser.ExponentialCuspParameter.cuspParameter (V x) = x ^ 2 :=
    hroots.mono fun x hx => cusp_of_actual_root U x hx.1
  have hdSquare := deriv_square_inverse_eq_two V hVa hV0 hVsquare
  have hlogd : HasDerivAt (fun x => Complex.log (1 + V x)) (deriv V 0) 0 := by
    have hh := (hVa.hasStrictDerivAt.hasDerivAt.const_add 1).clog (by simp [hV0])
    simpa only [hV0, add_zero, div_one] using hh
  have hprod : HasDerivAt (fun x => x * H x) (H 0) 0 := by
    convert (hasDerivAt_id (0 : ℂ)).mul hH.hasStrictDerivAt.hasDerivAt using 1 <;> first | rfl | simp
  have hEq : (fun x => x * H x) =ᶠ[𝓝 0] (fun x => Complex.log (1 + V x)) :=
    Eventually.of_forall fun x => by
      change x * H x = Complex.log (1 + V x)
      rw [show 1 + V x = rootMultiplier U x by dsimp [V]; ring, hHlog]
  have hz := hprod.unique (hlogd.congr_of_eventuallyEq hEq)
  rwa [← hz] at hdSquare

theorem exists_parameter_of_actual_data (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ p : ℂ → ℂ, AnalyticAt ℂ p 0 ∧ p 0 = 0 ∧ HasDerivAt p 2 0 ∧
      ∀ x : ℂ, p (x ^ 2) = -Complex.log (rootMultiplier U x) * Complex.log (rootMultiplier U (-x)) := by
  have hH := hdata.2.2.2.1
  have hHlog := hdata.2.2.2.2.2.1
  have hsq := actual_log_factor_square U H e₁ e₂ A B K F Γ hdata
  let G : ℂ → ℂ := fun x => H x * H (-x)
  have hGa : AnalyticAt ℂ G 0 := hH.mul (hH.comp_of_eq analyticAt_id.neg (by simp))
  have hGeven : ∀ x, G (-x) = G x := by intro x; simp [G, mul_comm]
  obtain ⟨g, hga, hdesc⟩ := exists_analytic_descent hGeven hGa
  have hg0 : g 0 = 2 := by
    have hh := hdesc (0 : ℂ)
    simpa only [zero_pow (by norm_num : 2 ≠ 0), G, neg_zero, ← pow_two, hsq] using hh
  let p : ℂ → ℂ := fun s => s * g s
  refine ⟨p, analyticAt_id.mul hga, by simp [p], ?_, ?_⟩
  · convert (hasDerivAt_id (0 : ℂ)).mul hga.hasStrictDerivAt.hasDerivAt using 1 <;> first | rfl | simp [hg0]
  · intro x
    dsimp only [p]
    rw [hdesc, hHlog x, hHlog (-x)]
    dsimp [G]
    ring

theorem parameter_eq_real_of_matching (U p : ℂ → ℂ)
    (hp : ∀ x, p (x ^ 2) = -Complex.log (rootMultiplier U x) * Complex.log (rootMultiplier U (-x)))
    (s a b : ℝ) (x : ℂ) (hx : x ^ 2 = (s : ℂ)) (hs : s < 1) (ha : -1 < a) (hb : 0 < b)
    (hm : (U x = (a : ℂ) ∧ U (-x) = (b : ℂ)) ∨ (U x = (b : ℂ) ∧ U (-x) = (a : ℂ))) :
    p s = (-Real.log (multiplier s a) * Real.log (multiplier s b) : ℝ) := by
  have hμa : 0 < multiplier s a := mul_pos (by linarith) (by linarith)
  have hμb : 0 < multiplier s b := mul_pos (by linarith) (by linarith)
  have hh := hp x
  rw [hx] at hh
  rcases hm with hm | hm
  · rw [rootMultiplier_of_real_value U s a x hx hm.1,
      rootMultiplier_of_real_value U s b (-x) (by simpa only [neg_sq] using hx) hm.2,
      ← Complex.ofReal_log hμa.le, ← Complex.ofReal_log hμb.le] at hh
    simpa only [Complex.ofReal_mul, Complex.ofReal_neg] using hh
  · rw [rootMultiplier_of_real_value U s b x hx hm.1,
      rootMultiplier_of_real_value U s a (-x) (by simpa only [neg_sq] using hx) hm.2,
      ← Complex.ofReal_log hμb.le, ← Complex.ofReal_log hμa.le] at hh
    rw [Complex.ofReal_mul, Complex.ofReal_neg]
    exact hh.trans (by ring)

end Kneser.ActualCommonMultiplierParameter
