import Kneser.AllOrderHornExpansion
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-! Arbitrary finite expansions in the actual multiplier parameter.
The analytic inverse is constructed by the genuine inverse function
theorem from p'(0)=2. Its inverse identities and derivative 1/2 are
conclusions. Actual one-sided errors are converted to powers of norm p,
without asserting that the complex-valued parameter is real. -/

set_option autoImplicit false
noncomputable section

namespace Kneser.AllOrderParameterExpansion

open Filter Set Metric Complex
open scoped Topology BigOperators
open Kneser.AllOrderGateFourier Kneser.AllOrderScalarAnalytic Kneser.CauchyHigherTaylor

def ParameterExpansion (f : ℝ → ℂ) (p : ℂ → ℂ) (c : ℕ → ℂ) (m : ℕ) : Prop :=
  c 0 = f 0 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
    ‖f s - scalarPolynomial c m (p (s : ℂ))‖ ≤ C * ‖p (s : ℂ)‖ ^ (m + 1)

def parameterReference (c : ℕ → ℂ) (m : ℕ) (r : ℂ → ℂ) (z : ℂ) : ℂ :=
  scalarPolynomial c m (r z)

theorem exists_analytic_parameter_inverse (p : ℂ → ℂ) (hpa : AnalyticAt ℂ p 0)
    (hp0 : p 0 = 0) (hp : HasDerivAt p 2 0) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r 0 ∧ r 0 = 0 ∧ HasDerivAt r (1 / 2) 0 ∧
      (∀ᶠ z : ℂ in 𝓝 0, r (p z) = z) ∧ (∀ᶠ z : ℂ in 𝓝 0, p (r z) = z) := by
  have hdn : deriv p 0 ≠ 0 := by rw [hp.deriv]; norm_num
  let r := hpa.hasStrictDerivAt.localInverse p (deriv p 0) 0 hdn
  have ha : AnalyticAt ℂ r 0 := by simpa only [hp0] using hpa.analyticAt_localInverse hdn
  have hl : ∀ᶠ z : ℂ in 𝓝 0, r (p z) = z := hpa.hasStrictDerivAt.eventually_left_inverse hdn
  have hr : ∀ᶠ z : ℂ in 𝓝 0, p (r z) = z := by
    simpa only [hp0] using hpa.hasStrictDerivAt.eventually_right_inverse hdn
  have hzero : r 0 = 0 := by
    have hh : r (p 0) = 0 := mem_of_mem_nhds (s := {z : ℂ | r (p z) = z}) hl
    simpa only [hp0] using hh
  have hd : HasDerivAt r (1 / 2) 0 := by
    simpa only [hp0, hp.deriv, inv_eq_one_div] using
      (hpa.hasStrictDerivAt.to_localInverse hdn).hasDerivAt
  exact ⟨r, ha, hzero, hd, hl, hr⟩

theorem analytic_taylor_in_parameter (g p : ℂ → ℂ) (m : ℕ)
    (hga : AnalyticAt ℂ g 0) (hpa : AnalyticAt ℂ p 0) (hp0 : p 0 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖g (p (s : ℂ)) - scalarPolynomial (coefficient g) m (p (s : ℂ))‖ ≤
        C * ‖p (s : ℂ)‖ ^ (m + 1) := by
  obtain ⟨R, hRa, hR⟩ := hga.exists_eq_sum_add_pow_mul (m + 1)
  let C := ‖R 0‖ + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ht : Tendsto (fun s : ℝ => p (s : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    convert hpa.continuousAt.tendsto.comp tendsto_real_parameter using 1
    · rfl
    · rw [hp0]
  have hBound : ∀ᶠ s : ℝ in 𝓝[>] 0, ‖R (p (s : ℂ))‖ ≤ C :=
    (((hRa.continuousAt.tendsto.comp ht).norm).eventually
      (gt_mem_nhds (by dsimp [C]; linarith : ‖R 0‖ < C))).mono fun _ hs => hs.le
  refine ⟨C, hC, ?_⟩
  filter_upwards [hBound] with s hs
  have hpol : (∑ j ∈ Finset.range (m + 1), ((p (s : ℂ)) ^ j / (j.factorial : ℂ)) • iteratedDeriv j g 0) =
      scalarPolynomial (coefficient g) m (p (s : ℂ)) := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [coefficient, smul_eq_mul, div_eq_mul_inv]
    ring
  have heq : g (p (s : ℂ)) - scalarPolynomial (coefficient g) m (p (s : ℂ)) =
      (p (s : ℂ)) ^ (m + 1) * R (p (s : ℂ)) := by
    rw [hR, hpol, smul_eq_mul]
    ring
  rw [heq, norm_mul, norm_pow]
  exact (mul_le_mul_of_nonneg_left hs (pow_nonneg (norm_nonneg _) _)).trans_eq (by ring)

theorem parameterExpansion_of_scalarExpansion (f : ℝ → ℂ) (c : ℕ → ℂ) (m : ℕ)
    (hf : ScalarExpansion f c m) (p r : ℂ → ℂ)
    (hpa : AnalyticAt ℂ p 0) (hp0 : p 0 = 0) (hp : HasDerivAt p 2 0)
    (hra : AnalyticAt ℂ r 0) (hr0 : r 0 = 0)
    (hleft : ∀ᶠ z : ℂ in 𝓝 0, r (p z) = z) :
    ParameterExpansion f p (coefficient (parameterReference c m r)) m := by
  have hga : AnalyticAt ℂ (parameterReference c m r) 0 :=
    (analyticAt_scalarPolynomial c m (r 0)).comp hra
  obtain ⟨C, hC, he⟩ := hf.2
  obtain ⟨D, hD, hd⟩ := analytic_taylor_in_parameter (parameterReference c m r) p m hga hpa hp0
  have hleftreal := tendsto_real_parameter.eventually hleft
  refine ⟨?_, C + D, add_nonneg hC hD, ?_⟩
  · simpa only [coefficient, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      parameterReference, hr0, scalarPolynomial_zero] using hf.1
  · filter_upwards [he, hd, hleftreal,
      Kneser.QuantitativeHornExpansion.parameter_norm_comparison p hp0 hp,
      self_mem_nhdsWithin] with s hs hds hls hcomp hsp
    change 0 < s at hsp
    have hident : parameterReference c m r (p (s : ℂ)) = scalarPolynomial c m (s : ℂ) := by
      simp only [parameterReference, hls]
    rw [hident] at hds
    have htriangle : ‖f s - scalarPolynomial (coefficient (parameterReference c m r)) m (p (s : ℂ))‖ ≤
        ‖f s - scalarPolynomial c m (s : ℂ)‖ +
        ‖scalarPolynomial c m (s : ℂ) - scalarPolynomial (coefficient (parameterReference c m r)) m
          (p (s : ℂ))‖ := by
      convert norm_add_le (f s - scalarPolynomial c m (s : ℂ))
        (scalarPolynomial c m (s : ℂ) - scalarPolynomial (coefficient (parameterReference c m r)) m
          (p (s : ℂ))) using 1
      congr 1
      ring
    apply htriangle.trans
    apply (add_le_add hs hds).trans
    have hpow := pow_le_pow_left₀ hsp.le hcomp (m + 1)
    calc
      C * s ^ (m + 1) + D * ‖p (s : ℂ)‖ ^ (m + 1) ≤
          C * ‖p (s : ℂ)‖ ^ (m + 1) + D * ‖p (s : ℂ)‖ ^ (m + 1) :=
        add_le_add (mul_le_mul_of_nonneg_left hpow hC) le_rfl
      _ = _ := by ring

theorem parameterReference_first_coefficient (c : ℕ → ℂ) (m : ℕ) (hm : 1 ≤ m)
    (r : ℂ → ℂ) (hr0 : r 0 = 0) (hr : HasDerivAt r (1 / 2) 0) :
    coefficient (parameterReference c m r) 1 = c 1 / 2 := by
  have hp : HasDerivAt (scalarPolynomial c m) (c 1) (r 0) := by
    simpa only [hr0] using scalarPolynomial_hasDerivAt_zero c m hm
  have hd := hp.comp 0 hr
  simp only [coefficient, iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, div_one]
  exact hd.deriv.trans (by ring)

theorem exists_parameter_expansions (p : ℂ → ℂ) (hpa : AnalyticAt ℂ p 0)
    (hp0 : p 0 = 0) (hp : HasDerivAt p 2 0) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r 0 ∧ r 0 = 0 ∧ HasDerivAt r (1 / 2) 0 ∧
      (∀ᶠ z : ℂ in 𝓝 0, r (p z) = z) ∧ (∀ᶠ z : ℂ in 𝓝 0, p (r z) = z) ∧
      ∀ (f : ℝ → ℂ) (c : ℕ → ℂ) (m : ℕ), ScalarExpansion f c m →
        ParameterExpansion f p (coefficient (parameterReference c m r)) m := by
  obtain ⟨r, hra, hr0, hrd, hl, hright⟩ := exists_analytic_parameter_inverse p hpa hp0 hp
  exact ⟨r, hra, hr0, hrd, hl, hright, fun f c m hf =>
    parameterExpansion_of_scalarExpansion f c m hf p r hpa hp0 hp hra hr0 hl⟩

end Kneser.AllOrderParameterExpansion

end
